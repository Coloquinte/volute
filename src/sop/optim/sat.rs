//! Optimization of boolean function representation using mathematical programming

use std::cmp::max;
use std::iter::zip;

use rustsat::instances::ManageVars;
use rustsat::instances::SatInstance;
use rustsat::solvers::Solve;
use rustsat::solvers::SolverResult;
use rustsat::types::constraints::PBConstraint;
use rustsat::types::Assignment;
use rustsat::types::Clause;
use rustsat::types::Lit;
use rustsat::types::Var;

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
    and_cost: isize,
    /// Cost of Xor gates
    xor_cost: isize,
    /// Cost of Or gates
    or_cost: isize,
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
    objective: Vec<(Lit, isize)>,
}

impl<'a> SopModeler<'a> {
    /// Initial creation of the modeler
    fn new(functions: &[Lut], and_cost: isize, xor_cost: isize, or_cost: isize) -> SopModeler {
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
            objective: Vec::new(),
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
        for _ in 0..n {
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

    /// Cost of a cube, including the Or gate it may create
    fn cube_cost(&self, i: usize) -> isize {
        self.and_cost * self.cubes[i].num_gates() as isize + self.or_cost
    }

    /// Cost of an exclusive cube, including the Or gate it may create
    fn ecube_cost(&self, i: usize) -> isize {
        self.xor_cost * self.ecubes[i].num_gates() as isize + self.or_cost
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        let mut obj = Vec::new();
        for i in 0..self.cubes.len() {
            obj.push((self.cube_used[i], self.cube_cost(i)));
        }
        for i in 0..self.ecubes.len() {
            obj.push((self.ecube_used[i], self.ecube_cost(i)));
        }
        self.objective = obj;
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

    /// Maximum variable for solution
    fn max_var(&self) -> Var {
        let mut ret = Var::new(0);
        for v in &self.cube_used {
            ret = max(v.var(), ret);
        }
        for v in &self.ecube_used {
            ret = max(v.var(), ret);
        }
        for vv in &self.cube_used_in_fn {
            for v in vv {
                ret = max(v.var(), ret);
            }
        }
        for vv in &self.ecube_used_in_fn {
            for v in vv {
                ret = max(v.var(), ret);
            }
        }
        ret
    }

    /// Solve the problem with a given limit on the objective
    fn solve_constrained(&self, max_obj: Option<isize>) -> Option<Assignment> {
        let mut inst = self.instance.clone();
        if let Some(max_obj) = max_obj {
            inst.add_pb_constr(PBConstraint::new_ub(
                self.objective.clone().into_iter(),
                max_obj,
            ));
        }
        let mut solver = rustsat_kissat::Kissat::default();
        solver.add_cnf(inst.clone().as_cnf().0).unwrap();
        if solver.solve().unwrap() == SolverResult::Sat {
            let sol = solver.solution(self.max_var()).unwrap();
            Some(sol)
        } else {
            None
        }
    }

    fn compute_obj(&self, solution: &Assignment) -> isize {
        let mut ret = 0;
        for (l, cost) in &self.objective {
            if solution.lit_value(*l).to_bool_with_def(false) {
                ret += cost;
            }
        }
        ret
    }

    /// Solve the problem with a given limit on the objective
    fn solve_optim(&self) -> Assignment {
        let mut best_sol = self.solve_constrained(None).unwrap();
        let mut best_obj = self.compute_obj(&best_sol);
        let mut min_obj = 0;
        while min_obj < best_obj {
            let mid = (min_obj + best_obj) / 2;
            assert!(mid < best_obj);
            match self.solve_constrained(Some(mid)) {
                Some(sol) => {
                    let obj = self.compute_obj(&sol);
                    assert!(obj <= mid);
                    best_sol = sol;
                    best_obj = obj
                }
                None => min_obj = mid + 1,
            }
        }
        best_sol
    }

    /// Solve the problem
    fn solve(&self) -> Vec<(Sop, Soes)> {
        let solution = self.solve_optim();
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
    pub fn run(
        functions: &[Lut],
        and_cost: isize,
        xor_cost: isize,
        or_cost: isize,
    ) -> Vec<(Sop, Soes)> {
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
    and_cost: isize,
    /// Cost of Xor gates
    xor_cost: isize,
    /// All cubes considered for the problem
    cubes: Vec<Cube>,
    /// Whether the corresponding cube is used at all
    cube_used: Vec<Lit>,
    /// Whether the corresponding cube is used for this function
    cube_used_in_fn: Vec<Vec<Lit>>,
    /// All variables of the problem
    instance: SatInstance,
    /// Objective of the problem
    objective: Vec<(Lit, isize)>,
}

impl<'a> EsopModeler<'a> {
    /// Initial creation of the modeler
    fn new(functions: &[Lut], and_cost: isize, xor_cost: isize) -> EsopModeler {
        EsopModeler {
            functions,
            and_cost,
            xor_cost,
            cubes: Vec::new(),
            cube_used: Vec::new(),
            cube_used_in_fn: Vec::new(),
            instance: SatInstance::new(),
            objective: Vec::new(),
        }
    }

    /// Number of variables
    fn num_vars(&self) -> usize {
        match self.functions.first() {
            Some(f) => f.num_vars(),
            _ => 0,
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

    /// Build a 1D array of binary variables
    fn build_variables(&mut self, n: usize) -> Vec<Lit> {
        let mut ret = Vec::new();
        for _ in 0..n {
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
        self.cubes = Cube::all(self.num_vars())
            .filter(|c| *c == Cube::one() || c.neg_vars().count() >= 1 || c.pos_vars().count() >= 2)
            .collect();
        self.cube_used = self.build_variables(self.cubes.len());
        self.cube_used_in_fn = self.build_function_variables(self.cubes.len());
    }

    /// Cost of a cube
    fn cube_cost(&self, i: usize) -> isize {
        self.and_cost * self.cubes[i].num_gates() as isize + self.xor_cost
    }

    /// Define the objective
    fn setup_objective(&mut self) {
        let mut obj = Vec::new();
        for i in 0..self.cubes.len() {
            obj.push((self.cube_used[i], self.cube_cost(i)));
        }
        self.objective = obj;
    }

    /// Force cube_used if cube_used_in_fn is set
    fn add_cover_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for i in 0..self.cubes.len() {
                self.instance
                    .add_binary(!self.cube_used_in_fn[i][j], self.cube_used[i]);
            }
        }
    }

    /// Add a xor constraint to the model using these variables
    fn add_xor_constraint(&mut self, vars: Vec<Lit>, value: bool) {
        assert!(vars.len() >= 1);
        let mut xor_val = vars[0];
        for i in 1..vars.len() {
            let v = vars[i];
            let next_val = self.instance.var_manager().new_var().pos_lit();
            self.instance.add_ternary(!xor_val, !next_val, !v);
            self.instance.add_ternary(!xor_val, next_val, v);
            self.instance.add_ternary(xor_val, !next_val, v);
            self.instance.add_ternary(xor_val, next_val, !v);
            xor_val = next_val
        }

        self.instance
            .add_unit(if value { xor_val } else { !xor_val });
    }

    /// Value constraint for a single bit of a function: the xor of the cubes must
    /// be equal to the expected value
    fn add_value_constraint(&mut self, fn_index: usize, b: usize) {
        let value = self.functions[fn_index].value(b);
        let mut vars = Vec::new();
        for (i, c) in self.cubes.iter().enumerate() {
            if c.value(b) {
                vars.push(self.cube_used_in_fn[i][fn_index]);
            }
        }
        self.add_xor_constraint(vars, value);
    }

    /// Constrain the difference between two bits for a function; this makes the constraint much
    /// more sparse
    fn add_value_constraint_diff(&mut self, fn_index: usize, b1: usize, b2: usize) {
        let value = self.functions[fn_index].value(b1) ^ self.functions[fn_index].value(b2);
        let mut vars = Vec::new();
        for (i, c) in self.cubes.iter().enumerate() {
            if c.value(b1) != c.value(b2) {
                vars.push(self.cube_used_in_fn[i][fn_index]);
            }
        }
        self.add_xor_constraint(vars, value);
    }

    /// Value constraints for each functions based on the cubes used
    fn add_value_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for b in 0..self.functions[j].num_bits() {
                self.add_value_constraint(j, b);
            }
        }
    }

    /// Redundant xor constraints for s stonger relaxation
    #[allow(dead_code)]
    fn add_redundant_value_constraints(&mut self) {
        for j in 0..self.functions.len() {
            for b1 in 0..self.functions[j].num_bits() {
                for flipped in 0..self.functions[j].num_vars() {
                    let b2 = b1 ^ (1 << flipped);
                    self.add_value_constraint_diff(j, b1, b2);
                }
            }
        }
    }

    /// Maximum variable for solution
    fn max_var(&self) -> Var {
        let mut ret = Var::new(0);
        for v in &self.cube_used {
            ret = max(v.var(), ret);
        }
        for vv in &self.cube_used_in_fn {
            for v in vv {
                ret = max(v.var(), ret);
            }
        }
        ret
    }

    /// Solve the problem with a given limit on the objective
    fn solve_constrained(&self, max_obj: Option<isize>) -> Option<Assignment> {
        let mut inst = self.instance.clone();
        if let Some(max_obj) = max_obj {
            inst.add_pb_constr(PBConstraint::new_ub(
                self.objective.clone().into_iter(),
                max_obj,
            ));
        }
        let mut solver = rustsat_kissat::Kissat::default();
        solver.add_cnf(inst.clone().as_cnf().0).unwrap();
        if solver.solve().unwrap() == SolverResult::Sat {
            let sol = solver.solution(self.max_var()).unwrap();
            Some(sol)
        } else {
            None
        }
    }

    fn compute_obj(&self, solution: &Assignment) -> isize {
        let mut ret = 0;
        for (l, cost) in &self.objective {
            if solution.lit_value(*l).to_bool_with_def(false) {
                ret += cost;
            }
        }
        ret
    }

    /// Solve the problem with a given limit on the objective
    fn solve_optim(&self) -> Assignment {
        let mut best_sol = self.solve_constrained(None).unwrap();
        let mut best_obj = self.compute_obj(&best_sol);
        let mut min_obj = 0;
        while min_obj < best_obj {
            let mid = (min_obj + best_obj) / 2;
            assert!(mid < best_obj);
            match self.solve_constrained(Some(mid)) {
                Some(sol) => {
                    let obj = self.compute_obj(&sol);
                    assert!(obj <= mid);
                    best_sol = sol;
                    best_obj = obj
                }
                None => min_obj = mid + 1,
            }
        }
        best_sol
    }

    /// Solve the problem
    fn solve(self) -> Vec<Esop> {
        let solution = self.solve_optim();
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
            let esop = Esop::from_cubes(self.functions[j].num_vars(), cubes);
            ret.push(esop);
        }
        ret
    }

    /// Run the whole optimization
    pub fn run(functions: &[Lut], and_cost: isize, xor_cost: isize) -> Vec<Esop> {
        let mut modeler = EsopModeler::new(functions, and_cost, xor_cost);
        modeler.setup_vars();
        modeler.check();
        modeler.setup_objective();
        modeler.add_cover_constraints();
        modeler.add_value_constraints();
        modeler.add_redundant_value_constraints();
        let ret = modeler.solve();
        for (esop, lut) in zip(&ret, functions) {
            assert_eq!(&Lut::from(esop), lut);
        }
        ret
    }
}

/// Optimize a Lut as a Sum of Products (Or of Ands) using a Satisfiability solver
///
/// This is a typical 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_sop_sat(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
    let opt = SopModeler::run(functions, and_cost as isize, -1, or_cost as isize);
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
    SopModeler::run(
        functions,
        and_cost as isize,
        xor_cost as isize,
        or_cost as isize,
    )
}

/// Optimize a Lut as an Exclusive Sum of Products (Xor of Ands) using a Satisfiability solver
///
/// This is a less common form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_esop_sat(functions: &[Lut], and_cost: i32, xor_cost: i32) -> Vec<Esop> {
    EsopModeler::run(functions, and_cost as isize, xor_cost as isize)
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
