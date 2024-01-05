//! Optimization of boolean function representation using mathematical programming

#[cfg(feature = "optim-mip")]
#[cfg_attr(docsrs, doc(cfg(feature = "optim-mip")))]
mod mip;

use crate::sop::Cube;
use crate::sop::Ecube;
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

#[cfg(feature = "optim-mip")]
#[cfg_attr(docsrs, doc(cfg(feature = "optim-mip")))]
pub use mip::*;
