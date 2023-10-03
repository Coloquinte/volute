#![warn(missing_docs)]

//! Implementation of logic functions as truth tables (also called lookup tables, or Luts).
//!
//! The crate implements truth table datastructures, either arbitrary-size Luts ([`Lut`]), or more efficient fixed-size Luts ([`Lut2`] to [`Lut12`]).
//! They provide logical operators and utility functions for analysis, canonization and decomposition.
//!
//! API and documentation try to follow the same terminology as the C++ library [Kitty](https://libkitty.readthedocs.io/en/latest).
//!
//! # Examples
//!
//! Create a constant-one Lut with five variables.
//! Display its hexadecimal value.
//! ```
//! # use volute::Lut;
//! let lut = Lut::one(5);
//! assert_eq!(lut.to_string(), "Lut5(ffffffff)");
//! ```
//!
//! Create a Lut4 (four variables) which is the logical and of the 1st and 3rd.
//! Display its hexadecimal value.
//! ```
//! # use volute::Lut4;
//! let lut = Lut4::nth_var(0) & Lut4::nth_var(2);
//! assert_eq!(lut.to_string(), "Lut4(a0a0)");
//! ```
//!
//! Create the parity function on three variables, and check that in can be decomposed as a Xor.
//! Display its value in binary.
//! ```
//! # use volute::Lut;
//! # use volute::DecompositionType;
//! let lut = Lut::parity(3);
//! assert_eq!(lut.decomposition(0), DecompositionType::Xor);
//! assert_eq!(format!("{:b}", lut), "Lut3(10010110)");
//! ```
mod canonization;
mod lut;
mod operations;
mod static_lut;

pub use lut::Lut;
pub use operations::DecompositionType;
pub use static_lut::StaticLut;

pub use static_lut::{
    Lut0, Lut1, Lut10, Lut11, Lut12, Lut2, Lut3, Lut4, Lut5, Lut6, Lut7, Lut8, Lut9,
};