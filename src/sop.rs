//! Sum-of-Products representations
//!
//! This module provides two-level representations such as [Sumof-Products](crate::sop::Sop)
//! and [Sum-of-Exclusive Sums](crate::sop::Soes).

mod cube;
mod ecube;
mod soes;
mod sop;

#[cfg(feature = "optim-mip")]
#[cfg_attr(docsrs, doc(cfg(feature = "optim-mip")))]
pub mod optim;

pub use cube::Cube;
pub use ecube::Ecube;
pub use soes::Soes;
pub use sop::Sop;
