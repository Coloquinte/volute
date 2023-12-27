//! Optimization of boolean function representation using a MIP solver

use crate::Lut;
use crate::Soes;
use crate::Sop;

/// Enumerate cubes that can be used to implement the given function
fn enumerate_valid_cubes(function: &Lut) -> Vec<Cube> {

}

/// Enumerate exclusive cubes that can be used to implement the given function
fn enumerate_valid_ecubes(function: &Lut) -> Vec<Ecube> {

}

/// Optimize a Lut as a Sum of Products (Or of Ands)
/// 
/// This is a typical 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And gates are ignored.
pub fn optimize_sop(functions: &[Lut], and_cost: i32, or_cost: i32) -> Vec<Sop> {
    let mut ret = Vec::new();
    for f in functions {
        ret.push(Sop::from(f));
    }
    ret
}

/// Optimize a Lut as a Sum of Products and Exclusive Sums (Or of Ands and Xors)
/// 
/// This is a more advanced form of 2-level optimization. The objective is to minimize the total cost of the
/// gates. Possible cost reductions by sharing intermediate And and Xor gates are ignored.
pub fn optimize_sopes(functions: &[Lut], and_cost: i32, xor_cost: i32, or_cost: i32) -> Vec<(Sop, Soes)> {
    let mut ret = Vec::new();
    for f in functions {
        ret.push((Sop::from(f), Soes::zero(f.num_vars())));
    }
    ret
}
