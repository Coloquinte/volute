//! Optimization of boolean function representation using mathematical programming

use std::iter::zip;

use rustsat::instances::ManageVars;
use rustsat::instances::Objective;
use rustsat::instances::SatInstance;
use rustsat::solvers::Solve;
use rustsat::solvers::SolverResult;
use rustsat::types::Clause;
use rustsat::types::Lit;

use crate::sop::Cube;
use crate::sop::Ecube;
use crate::sop::Soes;
use crate::sop::Sop;
use crate::Lut;

use super::Esop;

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
    cube_used: Vec<Lit>,
    /// Whether the corresponding exclusive cube is used at all
    ecube_used: Vec<Lit>,
    /// Whether the corresponding cube is used for this function
    cube_used_in_fn: Vec<Vec<Lit>>,
    /// Whether the corresponding exclusive cube is used for this function
    ecube_used_in_fn: Vec<Vec<Lit>>,
    /// All variables of the problem
    instance: SatInstance,
    /// Objective of the problem
    objective: Objective,
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
            instance: SatInstance::new(),
            objective: Objective::new(),
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

    /// Build a 1D array of binary variables
    fn build_variables(&mut self, n: usize) -> Vec<Lit> {
        let mut ret = Vec::new();
        for i in 0..n {
            ret.push(self.instance.var_manager().new_var().pos_lit());
        }
        ret
    }
    /// Build a 2D array of binary variables (N x functions.len())
    fn build_function_variables(&mut self, n: usize) -> Vec<Vec<Lit>> {
        let mut ret = Vec::new();
        for _ in 0..n {
            let mut fn_vars = Vec::new();
            for _ in self.functions {
                fn_vars.push(self.instance.var_manager().new_var().pos_lit());
            }
            ret.push(fn_vars);
        }
        ret
    }

    /// Setup main decision variables
    fn setup_vars(&mut self) {
        self.cubes = super::enumerate_valid_cubes_multi(self.functions);
        if self.xor_cost >= 0 {
            self.ecubes = super::enumerate_valid_ecubes_multi(self.functions);
        }
        self.cube_used = self.build_variables(self.cubes.len());
        self.ecube_used = self.build_variables(self.ecubes.len());
        self.cube_used_in_fn = self.build_function_variables(self.cubes.len());
        self.ecube_used_in_fn = self.build_function_variables(self.ecubes.len());
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        todo!();
    }

    /// Force cube_used if cube_used_in_fn is set
    fn add_cover_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for i in 0..self.cubes.len() {
                self.instance
                    .add_binary(!self.cube_used_in_fn[i][j], self.cube_used[i]);
            }
            for i in 0..self.ecubes.len() {
                self.instance
                    .add_binary(!self.cube_used_in_fn[i][j], self.cube_used[i]);
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
                let mut cl = Clause::new();
                for (i, c) in self.cubes.iter().enumerate() {
                    if c.value(b) {
                        cl.add(self.cube_used_in_fn[i][j]);
                    }
                }
                for (i, c) in self.ecubes.iter().enumerate() {
                    if c.value(b) {
                        cl.add(self.ecube_used_in_fn[i][j]);
                    }
                }
                self.instance.add_clause(cl);
            }
        }
    }

    /// Ensure that the function off-set is not touched
    fn add_off_set_constraints(&mut self) {
        for (j, f) in self.functions.iter().enumerate() {
            for (i, c) in self.cubes.iter().enumerate() {
                if !c.implies_lut(f) {
                    self.instance.add_unit(!self.cube_used_in_fn[i][j]);
                }
            }
            for (i, c) in self.ecubes.iter().enumerate() {
                if !c.implies_lut(f) {
                    self.instance.add_unit(!self.ecube_used_in_fn[i][j]);
                }
            }
        }
    }

    /// Solve the problem
    fn solve(&mut self) -> Vec<(Sop, Soes)> {
        let mut solver = rustsat_kissat::Kissat::default();
        solver.add_cnf(self.instance.clone().as_cnf().0).unwrap();
        assert_eq!(solver.solve().unwrap(), SolverResult::Sat);
        let solution = solver
            .solution(self.instance.var_manager().max_var().unwrap())
            .unwrap();
        let mut ret = Vec::new();
        for j in 0..self.functions.len() {
            let mut cubes = Vec::new();
            for i in 0..self.cubes.len() {
                let is_used = solution
                    .lit_value(self.cube_used_in_fn[i][j])
                    .to_bool_with_def(false);
                if is_used {
                    cubes.push(self.cubes[i]);
                }
            }
            let mut ecubes = Vec::new();
            for i in 0..self.ecubes.len() {
                let is_used = solution
                    .lit_value(self.ecube_used_in_fn[i][j])
                    .to_bool_with_def(false);
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
        //modeler.setup_objective();
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

/// Optimize a Lut as a Sum of Products (Or of Ands) using a Satisfiability solver
///
/// This is a typical 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_sop_sat(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
    let opt = SopModeler::run(functions, and_cost, -1, or_cost);
    opt.into_iter()
        .map(|(sop, soes)| {
            assert_eq!(soes.num_cubes(), 0);
            sop
        })
        .collect()
}

/// Optimize a Lut as a Sum of Products and Exclusive Sums (Or of Ands and Xors) using a Satisfiability solver
///
/// This is a more advanced form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And and Xor gates are ignored.
pub fn optimize_sopes_sat(
    functions: &[Lut],
    and_cost: i32,
    xor_cost: i32,
    or_cost: i32,
) -> Vec<(Sop, Soes)> {
    SopModeler::run(functions, and_cost, xor_cost, or_cost)
}

/// Optimize a Lut as an Exclusive Sum of Products (Xor of Ands) using a Satisfiability solver
///
/// This is a less common form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_esop_sat(functions: &[Lut], and_cost: i32, xor_cost: i32) -> Vec<Esop> {
    todo!();
}

#[cfg(test)]
mod tests {
    use super::optimize_esop_sat;
    use super::optimize_sop_sat;
    use super::optimize_sopes_sat;
    use crate::Lut;

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
                    optimize_sop_sat(&luts, 1, 1);
                }
            }
        }
    }

    #[test]
    fn test_simple_sop_optim() {
        let l1 = Lut::nth_var(5, 1) & Lut::nth_var(5, 2);
        let opt1 = optimize_sop_sat(&[l1], 1, 1);
        assert_eq!(opt1[0].num_cubes(), 1);
        assert_eq!(opt1[0].num_lits(), 2);

        let l2 = Lut::nth_var(5, 1) | Lut::nth_var(5, 2);
        let opt2 = optimize_sop_sat(&[l2], 1, 1);
        assert_eq!(opt2[0].num_cubes(), 2);
        assert_eq!(opt2[0].num_lits(), 2);

        let l3 = Lut::nth_var(5, 1) | (Lut::nth_var(5, 2) & !Lut::nth_var(5, 3));
        let opt3 = optimize_sop_sat(&[l3], 1, 1);
        assert_eq!(opt3[0].num_cubes(), 2);
        assert_eq!(opt3[0].num_lits(), 3);

        let l4 = Lut::nth_var(5, 1) | Lut::nth_var(5, 2);
        let opt3 = optimize_sop_sat(&[l4], 1, 1);
        assert_eq!(opt3[0].num_cubes(), 2);
        assert_eq!(opt3[0].num_lits(), 2);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_random_sopes_optim() {
        for num_vars in 0..4 {
            for num_luts in 1..5 {
                for _ in 0..10 {
                    let mut luts = Vec::new();
                    for _ in 0..num_luts {
                        luts.push(Lut::random(num_vars));
                    }
                    optimize_sopes_sat(&luts, 1, 2, 1);
                }
            }
        }
    }

    #[test]
    fn test_simple_sopes_optim() {
        let l1 = Lut::nth_var(5, 1) ^ Lut::nth_var(5, 2) ^ Lut::nth_var(5, 3);
        let opt1 = optimize_sopes_sat(&[l1], 1, 1, 1);
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
                    optimize_esop_sat(&luts, 1, 2);
                }
            }
        }
    }
}
