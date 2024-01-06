//! Sum-of-Products representations
//!
//! This module provides two-level representations such as [Sum-of-Products](crate::sop::Sop)
//! and [Sum-of-Exclusive Sums](crate::sop::Soes).

mod cube;
mod ecube;
mod esop;
mod soes;
mod sop;

#[cfg(any(feature = "optim-mip", feature = "optim-sat"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "optim-mip", feature = "optim-sat"))))]
pub mod optim;

pub use cube::Cube;
pub use ecube::Ecube;
pub use esop::Esop;
pub use soes::Soes;
pub use sop::Sop;
