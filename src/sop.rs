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

    /// Return the cube representing the nth variable
    pub fn nth_var(var: usize) -> Cube {
        Cube { a: 1 << (2 * var) }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(var: usize) -> Cube {
        Cube {
            a: 1 << (2 * var + 1),
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn from_vars(pos_vars: &[usize], neg_vars: &[usize]) -> Cube {
        let mut a = 0;
        for p in pos_vars {
            a |= 1 << (2 * p);
        }
        for p in neg_vars {
            a |= 1 << (2 * p + 1);
        }
        let c = Cube { a };
        if c.is_zero() {
            Cube::zero()
        } else {
            c
        }
    }

    /// Return the number of literals
    pub fn num_lits(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            self.a.count_ones() as usize
        }
    }

    /// Check whether the cube is a constant zero
    ///
    /// This can happen after And operations, so we check if any variable has the two bits set.
    pub fn is_zero(&self) -> bool {
        (self.a & 0xaaaa_aaaa_aaaa_aaaa) >> 1 & self.a != 0
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
                write!(f, "x{}", i)?;
            } else if a & 2 != 0 {
                write!(f, "!x{}", i)?;
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

    /// Number of cubes in the Sop
    pub fn num_cubes(&self) -> usize {
        self.cubes.len()
    }

    /// Number of literals in the Sop
    pub fn num_lits(&self) -> usize {
        let mut ret = 0;
        for c in &self.cubes {
            ret += c.num_lits();
        }
        ret
    }

    /// Returns whether the Sop is trivially constant zero
    pub fn is_zero(&self) -> bool {
        self.cubes.is_empty()
    }

    /// Returns whether the Sop is trivially constant one
    pub fn is_one(&self) -> bool {
        match self.cubes.first() {
            Some(c) => c.is_one(),
            None => false,
        }
    }

    /// Basic simplification of the Sop
    ///
    /// The following simplifications are performed:
    ///   * Zero cubes are removed
    ///   * Cubes that are implied by another are removed
    ///   * Some cubes that differ by one literal are merged
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

#[cfg(test)]
mod tests {
    use crate::Cube;

    #[test]
    fn test_cube_zero_one() {
        assert!(Cube::zero().is_zero());
        assert!(!Cube::one().is_zero());
        assert!(!Cube::zero().is_one());
        assert!(Cube::one().is_one());
        for i in 0..32 {
            assert!(!Cube::nth_var(i).is_zero());
            assert!(!Cube::nth_var(i).is_one());
            assert!(!Cube::nth_var_inv(i).is_zero());
            assert!(!Cube::nth_var_inv(i).is_one());
        }
    }

    #[test]
    fn test_cube_display() {
        assert_eq!(format!("{}", Cube::zero()), "0");
        assert_eq!(format!("{}", Cube::one()), "1");
        for i in 0..32 {
            assert_eq!(format!("{}", Cube::nth_var(i)), format!("x{}", i));
            assert_eq!(format!("{}", Cube::nth_var_inv(i)), format!("!x{}", i));
        }
        for i in 0..32 {
            for j in i + 1..32 {
                assert_eq!(
                    format!("{}", Cube::from_vars(&[i, j], &[])),
                    format!("x{}x{}", i, j)
                );
                assert_eq!(
                    format!("{}", Cube::from_vars(&[i], &[j])),
                    format!("x{}!x{}", i, j)
                );
                assert_eq!(
                    format!("{}", Cube::from_vars(&[j], &[i])),
                    format!("!x{}x{}", i, j)
                );
                assert_eq!(
                    format!("{}", Cube::from_vars(&[], &[i, j])),
                    format!("!x{}!x{}", i, j)
                );
            }
        }
    }

    #[test]
    fn test_num_lits() {
        assert_eq!(Cube::zero().num_lits(), 0);
        assert_eq!(Cube::one().num_lits(), 0);
        for i in 0..32 {
            assert_eq!(Cube::nth_var(i).num_lits(), 1);
            assert_eq!(Cube::nth_var_inv(i).num_lits(), 1);
        }
        for i in 0..32 {
            for j in i + 1..32 {
                assert_eq!(Cube::from_vars(&[i, j], &[]).num_lits(), 2);
                assert_eq!(Cube::from_vars(&[i], &[j]).num_lits(), 2);
                assert_eq!(Cube::from_vars(&[j], &[i]).num_lits(), 2);
                assert_eq!(Cube::from_vars(&[], &[i, j]).num_lits(), 2);
            }
        }
    }

    #[test]
    fn test_implies() {
        for i in 0..32 {
            assert!(!Cube::one().implies(Cube::nth_var(i)));
            assert!(!Cube::one().implies(Cube::nth_var_inv(i)));
            assert!(Cube::zero().implies(Cube::nth_var(i)));
            assert!(Cube::zero().implies(Cube::nth_var_inv(i)));
            assert!(Cube::nth_var(i).implies(Cube::one()));
            assert!(Cube::nth_var_inv(i).implies(Cube::one()));
            assert!(!Cube::nth_var(i).implies(Cube::zero()));
            assert!(!Cube::nth_var_inv(i).implies(Cube::zero()));
        }
        for i in 0..32 {
            for j in i + 1..32 {
                assert!(Cube::from_vars(&[i, j], &[]).implies(Cube::nth_var(i)));
                assert!(Cube::from_vars(&[i, j], &[]).implies(Cube::nth_var(j)));
                assert!(!Cube::from_vars(&[i, j], &[]).implies(Cube::nth_var_inv(i)));
                assert!(!Cube::from_vars(&[i, j], &[]).implies(Cube::nth_var_inv(j)));
                assert!(Cube::from_vars(&[], &[i, j]).implies(Cube::nth_var_inv(i)));
                assert!(Cube::from_vars(&[], &[i, j]).implies(Cube::nth_var_inv(j)));
                assert!(!Cube::from_vars(&[], &[i, j]).implies(Cube::nth_var(i)));
                assert!(!Cube::from_vars(&[], &[i, j]).implies(Cube::nth_var(j)));
            }
        }
    }
}
