//! Optimization of boolean function representation using a MIP solver

use std::cmp::max;
use std::iter::zip;

use good_lp::default_solver;
use good_lp::variable;
use good_lp::variables;
use good_lp::Constraint;
use good_lp::Expression;
use good_lp::ProblemVariables;
use good_lp::Solution;
use good_lp::SolverModel;
use good_lp::Variable;

use crate::Cube;
use crate::Ecube;
use crate::Lut;
use crate::Soes;
use crate::Sop;

/// Enumerate cubes that can be used to implement the given function. That is, cubes that are imply the function
fn enumerate_valid_cubes(function: &Lut) -> Vec<Cube> {
    Cube::all(function.num_vars())
        .filter(|c| c.implies_lut(function))
        .collect()
}

/// Enumerate exclusive cubes that can be used to implement the given function. That is, cubes that are imply the function
fn enumerate_valid_ecubes(function: &Lut) -> Vec<Ecube> {
    Ecube::all(function.num_vars())
        .filter(|c| c.implies_lut(function))
        .collect()
}

/// Enumerate cubes that can be used to implement these functions
fn enumerate_valid_cubes_multi(functions: &[Lut]) -> Vec<Cube> {
    // TODO: define and eliminate dominated cubes
    let mut cubes = Vec::new();
    for f in functions {
        cubes.extend(enumerate_valid_cubes(f));
    }
    cubes.sort();
    cubes.dedup();
    cubes
}

/// Enumerate exclusive cubes that can be used to implement these functions
fn enumerate_valid_ecubes_multi(functions: &[Lut]) -> Vec<Ecube> {
    // TODO: define and eliminate dominated cubes
    let mut cubes = Vec::new();
    for f in functions {
        cubes.extend(enumerate_valid_ecubes(f));
    }
    cubes.sort();
    cubes.dedup();
    cubes
}

struct SopModeler<'a> {
    /// Functions of the problem
    functions: &'a [Lut],
    /// Cost of And gates
    and_cost: i32,
    /// Cost of Or gates
    or_cost: i32,
    /// All cubes considered for the problem
    cubes: Vec<Cube>,
    /// Whether the corresponding cube is used at all
    cube_used: Vec<Variable>,
    /// Whether the corresponding cube is used for this function
    cube_used_in_fn: Vec<Vec<Variable>>,
    /// Number of cubes used in the function
    num_cubes_in_fn: Vec<Expression>,
    /// Number of or used in the function
    num_or_in_fn: Vec<Variable>,
    /// All variables of the problem
    vars: ProblemVariables,
    /// All constraints of the problem
    constraints: Vec<Constraint>,
    /// Objective of the problem
    objective: Expression,
}

impl<'a> SopModeler<'a> {
    /// Initial creation of the modeler
    fn new(functions: &[Lut], and_cost: i32, or_cost: i32) -> SopModeler {
        SopModeler {
            functions,
            and_cost,
            or_cost,
            cubes: Vec::new(),
            cube_used: Vec::new(),
            cube_used_in_fn: Vec::new(),
            num_cubes_in_fn: Vec::new(),
            num_or_in_fn: Vec::new(),
            vars: variables!(),
            constraints: Vec::new(),
            objective: Expression::default(),
        }
    }

    /// Check the datastructure
    fn check(&self) {
        for f in self.functions {
            assert_eq!(f.num_vars(), self.functions[0].num_vars());
        }
        assert!(self.and_cost >= 1);
        assert!(self.or_cost >= 1);
    }

    /// Setup main decision variables
    fn setup_vars(&mut self) {
        self.cubes = enumerate_valid_cubes_multi(self.functions);
        for _ in &self.cubes {
            self.cube_used.push(self.vars.add(variable().binary()));
        }
        for _ in &self.cubes {
            let mut used_in_fn = Vec::new();
            for _ in self.functions {
                used_in_fn.push(self.vars.add(variable().binary()));
            }
            self.cube_used_in_fn.push(used_in_fn);
        }
        for j in 0..self.functions.len() {
            let mut num_cubes = Expression::from(0);
            for i in 0..self.cubes.len() {
                num_cubes += self.cube_used_in_fn[i][j];
            }
            let num_or = self.vars.add(variable().min(0));
            self.num_or_in_fn.push(num_or);
            self.constraints.push((num_or - &num_cubes + 1).geq(0));
            self.num_cubes_in_fn.push(num_cubes);
        }
    }

    /// Cost of a cube
    fn cube_cost(&self, i: usize) -> i32 {
        let c = self.cubes[i];
        (max(c.num_lits(), 1) - 1) as i32
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        let mut expr = Expression::from(0);
        // Cost of each used cube
        for i in 0..self.cubes.len() {
            expr += self.cube_cost(i) * self.cube_used[i];
        }
        // Cost of each Or
        for i in 0..self.functions.len() {
            expr += self.or_cost * self.num_or_in_fn[i];
        }
        self.objective = expr;
    }

    /// Propagate usage
    fn add_cover_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for i in 0..self.cubes.len() {
                self.constraints
                    .push((self.cube_used_in_fn[i][j] - self.cube_used[i]).leq(0));
            }
        }
    }

    /// Ensure that the function on-set is covered
    fn add_on_set_constraints(&mut self) {
        for (j, f) in self.functions.iter().enumerate() {
            for b in 0..f.num_bits() {
                if !f.value(b) {
                    continue;
                }
                let mut expr = Expression::from(0);
                for (i, c) in self.cubes.iter().enumerate() {
                    if c.value(b) {
                        expr += self.cube_used_in_fn[i][j];
                    }
                }
                self.constraints.push(expr.geq(1));
            }
        }
    }

    /// Ensure that the function off-set is not touched
    fn add_off_set_constraints(&mut self) {
        for (i, c) in self.cubes.iter().enumerate() {
            for (j, f) in self.functions.iter().enumerate() {
                if !c.implies_lut(f) {
                    self.constraints
                        .push((1.0 * self.cube_used_in_fn[i][j]).leq(0));
                }
            }
        }
    }

    /// Solve the problem
    fn solve(self) -> Vec<Sop> {
        let mut pb = self
            .vars
            .minimise(self.objective.clone())
            .using(default_solver);
        for c in self.constraints {
            pb.add_constraint(c);
        }
        let solution = pb.solve().unwrap();
        let mut ret = Vec::new();
        for j in 0..self.functions.len() {
            let mut cubes = Vec::new();
            for i in 0..self.cubes.len() {
                let is_used = solution.value(self.cube_used_in_fn[i][j]) > 0.5;
                if is_used {
                    cubes.push(self.cubes[i]);
                }
            }
            ret.push(Sop::from_cubes(self.functions[j].num_vars(), cubes));
        }
        ret
    }

    /// Run the whole optimization
    pub fn run(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
        let mut modeler = SopModeler::new(functions, and_cost, or_cost);
        modeler.setup_vars();
        modeler.check();
        modeler.setup_objective();
        modeler.add_cover_constraints();
        modeler.add_off_set_constraints();
        modeler.add_on_set_constraints();
        let ret = modeler.solve();
        for (sop, lut) in zip(&ret, functions) {
            assert_eq!(&Lut::from(sop), lut);
        }
        ret
    }
}

/// Optimize a Lut as a Sum of Products (Or of Ands)
///
/// This is a typical 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_sop(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
    SopModeler::run(functions, and_cost, or_cost)
}

/*
/// Optimize a Lut as a Sum of Products and Exclusive Sums (Or of Ands and Xors)
///
/// This is a more advanced form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And and Xor gates are ignored.
pub fn optimize_sopes(
    functions: &[Lut],
    and_cost: i32,
    xor_cost: i32,
    or_cost: i32,
) -> Vec<(Sop, Soes)> {
    let cubes = enumerate_valid_cubes_multi(functions);
    let ecubes = enumerate_valid_ecubes_multi(functions);

    // TODO: enumerate constraints
    let mut ret = Vec::new();
    for f in functions {
        ret.push((Sop::from(f), Soes::zero(f.num_vars())));
    }
    ret
}
*/

#[cfg(test)]
mod tests {
    use crate::{optim_mip::optimize_sop, Lut};

    #[test]
    #[cfg(feature = "rand")]
    fn test_random_optim() {
        for num_vars in 0..5 {
            for num_luts in 1..5 {
                for _ in 0..10 {
                    let mut luts = Vec::new();
                    for _ in 0..num_luts {
                        luts.push(Lut::random(num_vars));
                    }
                    optimize_sop(&luts, 1, 1);
                }
            }
        }
    }

    #[test]
    fn test_simple_optim() {
        let l1 = Lut::nth_var(5, 1) & Lut::nth_var(5, 2);
        let opt1 = optimize_sop(&[l1], 1, 1);
        assert_eq!(opt1[0].num_cubes(), 1);
        assert_eq!(opt1[0].num_lits(), 2);

        let l2 = Lut::nth_var(5, 1) | Lut::nth_var(5, 2);
        let opt2 = optimize_sop(&[l2], 1, 1);
        assert_eq!(opt2[0].num_cubes(), 2);
        assert_eq!(opt2[0].num_lits(), 2);

        let l3 = Lut::nth_var(5, 1) | (Lut::nth_var(5, 2) & !Lut::nth_var(5, 3));
        let opt3 = optimize_sop(&[l3], 1, 1);
        assert_eq!(opt3[0].num_cubes(), 2);
        assert_eq!(opt3[0].num_lits(), 3);
    }
}
