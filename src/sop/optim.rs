//! Optimization of boolean function representation using mathematical programming

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

use crate::sop::Cube;
use crate::sop::Ecube;
use crate::sop::Soes;
use crate::sop::Sop;
use crate::Lut;

use super::Esop;

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
    cubes.retain(|c| c.num_lits() >= 2);
    cubes.sort();
    cubes.dedup();
    cubes
}

struct SopModeler<'a> {
    /// Functions of the problem
    functions: &'a [Lut],
    /// Cost of And gates
    and_cost: i32,
    /// Cost of Xor gates
    xor_cost: i32,
    /// Cost of Or gates
    or_cost: i32,
    /// All cubes considered for the problem
    cubes: Vec<Cube>,
    /// All exclusive cubes considered for the problem
    ecubes: Vec<Ecube>,
    /// Whether the corresponding cube is used at all
    cube_used: Vec<Variable>,
    /// Whether the corresponding exclusive cube is used at all
    ecube_used: Vec<Variable>,
    /// Whether the corresponding cube is used for this function
    cube_used_in_fn: Vec<Vec<Variable>>,
    /// Whether the corresponding exclusive cube is used for this function
    ecube_used_in_fn: Vec<Vec<Variable>>,
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
    fn new(functions: &[Lut], and_cost: i32, xor_cost: i32, or_cost: i32) -> SopModeler {
        SopModeler {
            functions,
            and_cost,
            xor_cost,
            or_cost,
            cubes: Vec::new(),
            ecubes: Vec::new(),
            cube_used: Vec::new(),
            ecube_used: Vec::new(),
            cube_used_in_fn: Vec::new(),
            ecube_used_in_fn: Vec::new(),
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
        assert!(self.xor_cost == -1 || self.xor_cost >= 1);
    }

    /// Build a 2D array of binary variables (N x functions.len())
    fn build_function_variables(&mut self, n: usize) -> Vec<Vec<Variable>> {
        let mut ret = Vec::new();
        for _ in 0..n {
            let mut fn_vars = Vec::new();
            for _ in self.functions {
                fn_vars.push(self.vars.add(variable().binary()));
            }
            ret.push(fn_vars);
        }
        ret
    }

    /// Setup main decision variables
    fn setup_vars(&mut self) {
        self.cubes = enumerate_valid_cubes_multi(self.functions);
        if self.xor_cost >= 0 {
            self.ecubes = enumerate_valid_ecubes_multi(self.functions);
        }
        self.cube_used = self
            .cubes
            .iter()
            .map(|_| self.vars.add(variable().binary()))
            .collect();
        self.ecube_used = self
            .ecubes
            .iter()
            .map(|_| self.vars.add(variable().binary()))
            .collect();
        self.cube_used_in_fn = self.build_function_variables(self.cubes.len());
        self.ecube_used_in_fn = self.build_function_variables(self.ecubes.len());

        for j in 0..self.functions.len() {
            let mut num_cubes = Expression::from(0);
            for i in 0..self.cubes.len() {
                num_cubes += self.cube_used_in_fn[i][j];
            }
            for i in 0..self.ecubes.len() {
                num_cubes += self.ecube_used_in_fn[i][j];
            }
            let num_or = self.vars.add(variable().min(0));
            self.num_or_in_fn.push(num_or);
            self.constraints.push((num_or - &num_cubes + 1).geq(0));
            self.num_cubes_in_fn.push(num_cubes);
        }
    }

    /// Cost of a cube
    fn cube_cost(&self, i: usize) -> i32 {
        let num = self.cubes[i].num_gates() as i32;
        num * self.and_cost
    }

    /// Cost of an exclusive cube
    fn ecube_cost(&self, i: usize) -> i32 {
        let num = self.ecubes[i].num_gates() as i32;
        num * self.xor_cost
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        let mut expr = Expression::from(0);
        // Cost of each used cube
        for i in 0..self.cubes.len() {
            expr += self.cube_cost(i) * self.cube_used[i];
        }
        // Cost of each exclusive cube
        for i in 0..self.ecubes.len() {
            expr += self.ecube_cost(i) * self.ecube_used[i];
        }
        // Cost of each Or
        for i in 0..self.functions.len() {
            expr += self.or_cost * self.num_or_in_fn[i];
        }
        self.objective = expr;
    }

    /// Force cube_used if cube_used_in_fn is set
    fn add_cover_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for i in 0..self.cubes.len() {
                self.constraints
                    .push((self.cube_used_in_fn[i][j] - self.cube_used[i]).leq(0));
            }
            for i in 0..self.ecubes.len() {
                self.constraints
                    .push((self.ecube_used_in_fn[i][j] - self.ecube_used[i]).leq(0));
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
                for (i, c) in self.ecubes.iter().enumerate() {
                    if c.value(b) {
                        expr += self.ecube_used_in_fn[i][j];
                    }
                }
                self.constraints.push(expr.geq(1));
            }
        }
    }

    /// Ensure that the function off-set is not touched
    fn add_off_set_constraints(&mut self) {
        for (j, f) in self.functions.iter().enumerate() {
            for (i, c) in self.cubes.iter().enumerate() {
                if !c.implies_lut(f) {
                    self.constraints
                        .push((1.0 * self.cube_used_in_fn[i][j]).leq(0));
                }
            }
            for (i, c) in self.ecubes.iter().enumerate() {
                if !c.implies_lut(f) {
                    self.constraints
                        .push((1.0 * self.ecube_used_in_fn[i][j]).leq(0));
                }
            }
        }
    }

    /// Solve the problem
    fn solve(self) -> Vec<(Sop, Soes)> {
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
            let mut ecubes = Vec::new();
            for i in 0..self.ecubes.len() {
                let is_used = solution.value(self.ecube_used_in_fn[i][j]) > 0.5;
                if is_used {
                    ecubes.push(self.ecubes[i]);
                }
            }
            let sop = Sop::from_cubes(self.functions[j].num_vars(), cubes);
            let soes = Soes::from_cubes(self.functions[j].num_vars(), ecubes);
            if self.xor_cost < 0 {
                assert_eq!(soes.num_cubes(), 0);
            }
            ret.push((sop, soes));
        }
        ret
    }

    /// Run the whole optimization
    pub fn run(functions: &[Lut], and_cost: i32, xor_cost: i32, or_cost: i32) -> Vec<(Sop, Soes)> {
        let mut modeler = SopModeler::new(functions, and_cost, xor_cost, or_cost);
        modeler.setup_vars();
        modeler.check();
        modeler.setup_objective();
        modeler.add_cover_constraints();
        modeler.add_off_set_constraints();
        modeler.add_on_set_constraints();
        let ret = modeler.solve();
        for ((sop, soes), lut) in zip(&ret, functions) {
            let val = Lut::from(sop) | Lut::from(soes);
            assert_eq!(&val, lut);
        }
        ret
    }
}

struct EsopModeler<'a> {
    /// Functions of the problem
    functions: &'a [Lut],
    /// Cost of And gates
    and_cost: i32,
    /// Cost of Xor gates
    xor_cost: i32,
    /// All cubes considered for the problem
    cubes: Vec<Cube>,
    /// Whether the corresponding cube is used at all
    cube_used: Vec<Variable>,
    /// Whether the corresponding cube is used for this function
    cube_used_in_fn: Vec<Vec<Variable>>,
    /// Number of cubes used in the function
    num_cubes_in_fn: Vec<Expression>,
    /// Number of or used in the function
    num_xor_in_fn: Vec<Variable>,
    /// All variables of the problem
    vars: ProblemVariables,
    /// All constraints of the problem
    constraints: Vec<Constraint>,
    /// Objective of the problem
    objective: Expression,
}

impl<'a> EsopModeler<'a> {
    /// Initial creation of the modeler
    fn new(functions: &[Lut], and_cost: i32, xor_cost: i32) -> EsopModeler {
        EsopModeler {
            functions,
            and_cost,
            xor_cost,
            cubes: Vec::new(),
            cube_used: Vec::new(),
            cube_used_in_fn: Vec::new(),
            num_cubes_in_fn: Vec::new(),
            num_xor_in_fn: Vec::new(),
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
        assert!(self.xor_cost >= 1);
    }

    /// Build a 2D array of binary variables (N x functions.len())
    fn build_function_variables(&mut self, n: usize) -> Vec<Vec<Variable>> {
        let mut ret = Vec::new();
        for _ in 0..n {
            let mut fn_vars = Vec::new();
            for _ in self.functions {
                fn_vars.push(self.vars.add(variable().binary()));
            }
            ret.push(fn_vars);
        }
        ret
    }

    /// Setup main decision variables
    fn setup_vars(&mut self) {
        self.cubes = enumerate_valid_cubes_multi(self.functions);
        self.cube_used = self
            .cubes
            .iter()
            .map(|_| self.vars.add(variable().binary()))
            .collect();
        self.cube_used_in_fn = self.build_function_variables(self.cubes.len());

        for j in 0..self.functions.len() {
            let mut num_cubes = Expression::from(0);
            for i in 0..self.cubes.len() {
                num_cubes += self.cube_used_in_fn[i][j];
            }
            let num_xor = self.vars.add(variable().min(0));
            self.num_xor_in_fn.push(num_xor);
            self.constraints.push((num_xor - &num_cubes + 1).geq(0));
            self.num_cubes_in_fn.push(num_cubes);
        }
    }

    /// Cost of a cube
    fn cube_cost(&self, i: usize) -> i32 {
        let num = self.cubes[i].num_gates() as i32;
        num * self.and_cost
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        let mut expr = Expression::from(0);
        // Cost of each used cube
        for i in 0..self.cubes.len() {
            expr += self.cube_cost(i) * self.cube_used[i];
        }
        // Cost of each Xor
        for i in 0..self.functions.len() {
            expr += self.xor_cost * self.num_xor_in_fn[i];
        }
        self.objective = expr;
    }

    /// Force cube_used if cube_used_in_fn is set
    fn add_cover_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for i in 0..self.cubes.len() {
                self.constraints
                    .push((self.cube_used_in_fn[i][j] - self.cube_used[i]).leq(0));
            }
        }
    }

    /// Value constraint for a single bit of a function: the xor of the cubes must
    /// be equal to the expected value
    fn add_xor_constraint(&mut self, fn_index: usize, b: usize) {
        let val = self.functions[fn_index].value(b);
        let mut expr = Expression::from(if val { 1 } else { 0 });
        for (i, c) in self.cubes.iter().enumerate() {
            if c.value(b) {
                expr += self.cube_used_in_fn[i][fn_index];
            }
        }
        // One way to specify a Xor constraint is to force integrality of sum/2
        // TODO: use a better encoding for the constraints
        expr *= 0.5;
        let v = self.vars.add(variable().integer());
        expr += v;
        self.constraints.push(expr.eq(0));
    }

    /// Constrain the difference between two bits for a function; this makes the constraint much
    /// more sparse
    fn add_xor_constraint_diff(&mut self, fn_index: usize, b1: usize, b2: usize) {
        let val = self.functions[fn_index].value(b1) ^ self.functions[fn_index].value(b2);
        let mut expr = Expression::from(if val { 1 } else { 0 });
        for (i, c) in self.cubes.iter().enumerate() {
            if c.value(b1) != c.value(b2) {
                expr += self.cube_used_in_fn[i][fn_index];
            }
        }
        // One way to specify a Xor constraint is to force integrality of sum/2
        // TODO: use a better encoding for the constraints
        expr *= 0.5;
        let v = self.vars.add(variable().integer());
        expr += v;
        self.constraints.push(expr.eq(0));
    }

    /// Value constraints for each functions based on the cubes used
    fn add_xor_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for b in 0..self.functions[j].num_bits() {
                self.add_xor_constraint(j, b);
            }
        }
    }

    /// Value constraints for each functions based on the cubes used, with sparser method
    #[allow(dead_code)]
    fn add_xor_constraints_with_diff(&mut self) {
        for j in 0..self.functions.len() {
            self.add_xor_constraint(j, 0);
            for b1 in 1..self.functions[j].num_bits() {
                // Other mask with one bit flipped
                let b2 = b1 & (b1 - 1);
                self.add_xor_constraint_diff(j, b1, b2);
            }
        }
    }

    /// Solve the problem
    fn solve(self) -> Vec<Esop> {
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
            let esop = Esop::from_cubes(self.functions[j].num_vars(), cubes);
            ret.push(esop);
        }
        ret
    }

    /// Run the whole optimization
    pub fn run(functions: &[Lut], and_cost: i32, xor_cost: i32) -> Vec<Esop> {
        let mut modeler = EsopModeler::new(functions, and_cost, xor_cost);
        modeler.setup_vars();
        modeler.check();
        modeler.setup_objective();
        modeler.add_cover_constraints();
        modeler.add_xor_constraints();
        let ret = modeler.solve();
        for (esop, lut) in zip(&ret, functions) {
            assert_eq!(&Lut::from(esop), lut);
        }
        ret
    }
}

/// Optimize a Lut as a Sum of Products (Or of Ands) using Mixed-Integer Programming
///
/// This is a typical 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_sop_mip(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
    let opt = SopModeler::run(functions, and_cost, -1, or_cost);
    opt.into_iter()
        .map(|(sop, soes)| {
            assert_eq!(soes.num_cubes(), 0);
            sop
        })
        .collect()
}

/// Optimize a Lut as a Sum of Products and Exclusive Sums (Or of Ands and Xors) using Mixed-Integer Programming
///
/// This is a more advanced form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And and Xor gates are ignored.
pub fn optimize_sopes_mip(
    functions: &[Lut],
    and_cost: i32,
    xor_cost: i32,
    or_cost: i32,
) -> Vec<(Sop, Soes)> {
    SopModeler::run(functions, and_cost, xor_cost, or_cost)
}

/// Optimize a Lut as an Exclusive Sum of Products (Xor of Ands) using Mixed-Integer Programming
///
/// This is a less common form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_esop_mip(functions: &[Lut], and_cost: i32, xor_cost: i32) -> Vec<Esop> {
    EsopModeler::run(functions, and_cost, xor_cost)
}

#[cfg(test)]
mod tests {
    use crate::{
        sop::optim::optimize_esop_mip, sop::optim::optimize_sop_mip,
        sop::optim::optimize_sopes_mip, Lut,
    };

    #[test]
    #[cfg(feature = "rand")]
    fn test_random_sop_optim() {
        for num_vars in 0..5 {
            for num_luts in 1..5 {
                for _ in 0..10 {
                    let mut luts = Vec::new();
                    for _ in 0..num_luts {
                        luts.push(Lut::random(num_vars));
                    }
                    optimize_sop_mip(&luts, 1, 1);
                }
            }
        }
    }

    #[test]
    fn test_simple_sop_optim() {
        let l1 = Lut::nth_var(5, 1) & Lut::nth_var(5, 2);
        let opt1 = optimize_sop_mip(&[l1], 1, 1);
        assert_eq!(opt1[0].num_cubes(), 1);
        assert_eq!(opt1[0].num_lits(), 2);

        let l2 = Lut::nth_var(5, 1) | Lut::nth_var(5, 2);
        let opt2 = optimize_sop_mip(&[l2], 1, 1);
        assert_eq!(opt2[0].num_cubes(), 2);
        assert_eq!(opt2[0].num_lits(), 2);

        let l3 = Lut::nth_var(5, 1) | (Lut::nth_var(5, 2) & !Lut::nth_var(5, 3));
        let opt3 = optimize_sop_mip(&[l3], 1, 1);
        assert_eq!(opt3[0].num_cubes(), 2);
        assert_eq!(opt3[0].num_lits(), 3);

        let l4 = Lut::nth_var(5, 1) | Lut::nth_var(5, 2);
        let opt3 = optimize_sop_mip(&[l4], 1, 1);
        assert_eq!(opt3[0].num_cubes(), 2);
        assert_eq!(opt3[0].num_lits(), 2);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_random_sopes_optim() {
        for num_vars in 0..5 {
            for num_luts in 1..5 {
                for _ in 0..10 {
                    let mut luts = Vec::new();
                    for _ in 0..num_luts {
                        luts.push(Lut::random(num_vars));
                    }
                    optimize_sopes_mip(&luts, 1, 2, 1);
                }
            }
        }
    }

    #[test]
    fn test_simple_sopes_optim() {
        let l1 = Lut::nth_var(5, 1) ^ Lut::nth_var(5, 2) ^ Lut::nth_var(5, 3);
        let opt1 = optimize_sopes_mip(&[l1], 1, 1, 1);
        assert_eq!(opt1[0].0.num_cubes(), 0);
        assert_eq!(opt1[0].0.num_lits(), 0);
        assert_eq!(opt1[0].1.num_cubes(), 1);
        assert_eq!(opt1[0].1.num_lits(), 3);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_random_esop_optim() {
        for num_vars in 0..4 {
            for num_luts in 1..5 {
                for _ in 0..10 {
                    let mut luts = Vec::new();
                    for _ in 0..num_luts {
                        luts.push(Lut::random(num_vars));
                    }
                    optimize_esop_mip(&luts, 1, 2);
                }
            }
        }
    }
}
