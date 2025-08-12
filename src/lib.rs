#![warn(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]

//! Logic function manipulation using truth tables (LUTs) that represent the value of the function for the 2<sup>n</sup> possible inputs.
//!
//! The crate implements truth table datastructures, either arbitrary-size truth tables
//! ([`Lut`](https://docs.rs/volute/latest/volute/struct.Lut.html)), or more efficient
//! fixed-size truth tables ([`Lut2` to `Lut12`](https://docs.rs/volute/latest/volute/struct.StaticLut.html)).
//! They provide logical operators and utility functions for analysis, canonization and decomposition.
//! Some support is available for other standard representation, such as Sum-of-Products
//! ([`Sop`](https://docs.rs/volute/latest/volute/sop/struct.Sop.html)).
//!
//! API and documentation try to follow the same terminology as the C++ library [Kitty](https://libkitty.readthedocs.io/en/latest).
//!
//! # Examples
//!
//! Create a constant-one Lut with five variables.
//! Check its hexadecimal value.
//! ```
//! # use volute::Lut;
//! let lut = Lut::one(5);
//! assert_eq!(lut.to_string(), "Lut5(ffffffff)");
//! ```
//!
//! Create a Lut4 (four variables) which is the logical and of the 1st and 3rd.
//! Check its hexadecimal value.
//! ```
//! # use volute::Lut4;
//! let lut = Lut4::nth_var(0) & Lut4::nth_var(2);
//! assert_eq!(lut.to_string(), "Lut4(a0a0)");
//! ```
//!
//! Create a random Lut6 (six variables).
//! Display its hexadecimal value.
//! ```
//! # use volute::Lut6;
//! # #[cfg(feature = "rand")]
//! let lut = Lut6::random();
//! # #[cfg(feature = "rand")]
//! print!("{}", lut);
//! ```
//!
//! Create the parity function on three variables, and check that in can be decomposed as a Xor.
//! Check its value in binary.
//! ```
//! # use volute::Lut;
//! # use volute::DecompositionType;
//! let lut = Lut::parity(3);
//! assert_eq!(lut.top_decomposition(0), DecompositionType::Xor);
//! assert_eq!(format!("{:b}", lut), "Lut3(10010110)");
//! ```
//!
//! Create a Lut2 and swap its inputs.
//! Check the result.
//! ```
//! # use volute::Lut2;
//! let lut = Lut2::nth_var(0);
//! assert_eq!(lut.swap(0, 1), Lut2::nth_var(1));
//! ```

mod bdd;
mod canonization;
mod decomposition;
mod lut;
mod operations;
pub mod sop;
mod static_lut;

pub use decomposition::DecompositionType;
pub use lut::Lut;
pub use static_lut::StaticLut;

pub use static_lut::{
    Lut0, Lut1, Lut10, Lut11, Lut12, Lut2, Lut3, Lut4, Lut5, Lut6, Lut7, Lut8, Lut9,
};
