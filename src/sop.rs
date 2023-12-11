use std::{fmt, ops::BitAnd};

/// Representation of the and of variables (a cube in sum-of-products formulations)
///
/// Each variable is represented by a pair of bits. If none is set, the variable is unused.
/// If both are set, the cube is 0. Otherwise, LSB represents the variable and MSB its complement.
///
/// It only supports And operations. Anything else must be implemented by more complex
/// representations that use it, such as sum-of-products.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cube {
    a: u64,
}

/// Representation of a sum-of-products (an or of and)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sop {
    cubes: Vec<Cube>,
}

impl Cube {
    /// The empty cube
    pub fn one() -> Cube {
        Cube { a: 0 }
    }

    /// The zero cube (not strictly a cube, so it gets a special representation)
    pub fn zero() -> Cube {
        Cube { a: !0 }
    }

    /// Check whether the cube is a constant
    pub fn is_constant(&self) -> bool {
        self.is_one() || self.is_zero()
    }

    /// Check whether the cube is the constant one
    pub fn is_one(&self) -> bool {
        self.a == 0
    }

    /// Check whether the cube is a constant zero
    ///
    /// This can happen after And operations, so we check if any variable has the two bits set.
    pub fn is_zero(&self) -> bool {
        (self.a & 0xcccc_cccc_cccc_cccc) >> 1 & self.a == 0
    }

    /// Returns the variables that are positive in the cube
    pub fn pos_vars(&self) -> Vec<usize> {
        (0..32).filter(|v| (self.a >> (2 * v) & 1) != 0).collect()
    }

    /// Returns the variables that are negative in the cube
    pub fn neg_vars(&self) -> Vec<usize> {
        (0..32)
            .filter(|v| (self.a >> (2 * v + 1) & 1) != 0)
            .collect()
    }

    /// Returns whether the cube implies another. This is used for Sop simplification
    pub fn implies(&self, o: Cube) -> bool {
        //
        self.a | o.a == self.a
    }

    /// Perform the and operation on two cubes
    fn and(a: Cube, b: Cube) -> Cube {
        let ret = Cube { a: a.a | b.a };
        if ret.is_zero() {
            // Normalize any zero cube to the standard zero
            Cube::zero()
        } else {
            ret
        }
    }
}

impl BitAnd<Cube> for Cube {
    type Output = Cube;
    fn bitand(self, rhs: Cube) -> Self::Output {
        Cube::and(self, rhs)
    }
}

impl BitAnd<Cube> for &Cube {
    type Output = Cube;
    fn bitand(self, rhs: Cube) -> Self::Output {
        Cube::and(*self, rhs)
    }
}

impl BitAnd<&Cube> for &Cube {
    type Output = Cube;
    fn bitand(self, rhs: &Cube) -> Self::Output {
        Cube::and(*self, *rhs)
    }
}

impl BitAnd<&Cube> for Cube {
    type Output = Cube;
    fn bitand(self, rhs: &Cube) -> Self::Output {
        Cube::and(self, *rhs)
    }
}

impl fmt::Display for Cube {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_one() {
            write!(f, "1")?;
            return Ok(());
        }
        if self.is_zero() {
            write!(f, "0")?;
            return Ok(());
        }
        let mut a = self.a;
        let mut i = 0;
        while a != 0 {
            if a & 1 != 0 {
                write!(f, "x{}", a)?;
            } else if a & 2 != 0 {
                write!(f, "!x{}", a)?;
            }
            i += 1;
            a >>= 2;
        }
        Ok(())
    }
}

impl Sop {
    /// Return the constant zero Sop
    pub fn zero() -> Sop {
        Sop { cubes: vec![] }
    }

    /// Return the constant one Sop
    pub fn one() -> Sop {
        Sop {
            cubes: vec![Cube::one()],
        }
    }

    /// Returns whether the Sop is constant zero
    pub fn is_zero(&self) -> bool {
        self.cubes.is_empty()
    }

    /// Returns whether the Sop is constant one
    pub fn is_one(&self) -> bool {
        match self.cubes.first() {
            Some(c) => c.is_one(),
            None => false,
        }
    }

    /// Simplify the Sop, only keeping irredundant cubes
    fn simplify(&mut self) {
        // No need for zeros
        self.cubes.retain(|c| !c.is_zero());
        // Remove any cube that is implied by another
    }

    /// Compute the negation of an Sop
    fn not(&self) -> Sop {
        todo!();
    }

    /// Compute the or of two Sops
    fn or(a: &Sop, b: &Sop) -> Sop {
        let mut cubes = a.cubes.clone();
        cubes.extend(&b.cubes);
        Sop { cubes }
    }

    /// Compute the and of two Sops
    fn and(a: &Sop, b: &Sop) -> Sop {
        let mut cubes = Vec::new();
        for c1 in &a.cubes {
            for c2 in &b.cubes {
                let c = c1 & c2;
                if c != Cube::zero() {
                    cubes.push(c);
                }
            }
        }
        Sop { cubes }
    }
}

impl fmt::Display for Sop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")?;
            return Ok(());
        }
        let s = self
            .cubes
            .iter()
            .map(|c| c.to_string())
            .collect::<Vec<_>>()
            .join(" | ");
        write!(f, "{}", s)
    }
}
