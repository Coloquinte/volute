use std::{
    fmt,
    ops::{BitXor, Not},
};

use crate::sop::Cube;
use crate::Lut;

/// Exclusive Sum of Products representation (Xor of And)
///
/// Any boolean function can be represented this way, so that this can be used for
/// two-level circuit optimization.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Esop {
    num_vars: usize,
    cubes: Vec<Cube>,
}

impl Esop {
    /// Query the number of variables
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Return the constant zero Esop
    pub fn zero(num_vars: usize) -> Esop {
        Esop {
            num_vars,
            cubes: vec![],
        }
    }

    /// Return the constant one Esop
    pub fn one(num_vars: usize) -> Esop {
        Esop {
            num_vars,
            cubes: vec![Cube::one()],
        }
    }

    /// Number of cubes in the Esop
    pub fn num_cubes(&self) -> usize {
        self.cubes.len()
    }

    /// Number of literals in the Esop
    pub fn num_lits(&self) -> usize {
        let mut ret = 0;
        for c in &self.cubes {
            ret += c.num_lits();
        }
        ret
    }

    /// Returns whether the Esop is trivially constant zero
    pub fn is_zero(&self) -> bool {
        self.cubes.is_empty()
    }

    /// Returns whether the Esop is trivially constant one
    pub fn is_one(&self) -> bool {
        if self.cubes.len() != 1 {
            return false;
        }
        match self.cubes.first() {
            Some(c) => c.is_one(),
            _ => panic!(),
        }
    }

    /// Return the Esop representing the nth variable
    pub fn nth_var(num_vars: usize, var: usize) -> Esop {
        Esop {
            num_vars,
            cubes: vec![Cube::nth_var(var)],
        }
    }

    /// Return the Esop representing the nth variable, inverted
    pub fn nth_var_inv(num_vars: usize, var: usize) -> Esop {
        Esop {
            num_vars,
            cubes: vec![Cube::nth_var_inv(var)],
        }
    }

    /// Build an Esop from cubes
    pub fn from_cubes(num_vars: usize, cubes: Vec<Cube>) -> Esop {
        for c in &cubes {
            for v in c.pos_vars() {
                assert!(v < num_vars);
            }
            for v in c.neg_vars() {
                assert!(v < num_vars);
            }
        }
        Esop { num_vars, cubes }
    }

    /// Returns the cubes in the Esop
    pub fn cubes(&self) -> &[Cube] {
        &self.cubes
    }

    /// Get the value of the Esop for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        let mut ret = false;
        for c in &self.cubes {
            ret ^= c.value(mask);
        }
        ret
    }

    /// Compute the xor of two Esops
    fn xor(a: &Esop, b: &Esop) -> Esop {
        assert_eq!(a.num_vars, b.num_vars);
        let mut cubes = a.cubes.clone();
        cubes.extend(&b.cubes);
        Esop {
            num_vars: a.num_vars,
            cubes,
        }
    }
}

impl Not for Esop {
    type Output = Esop;
    fn not(self) -> Self::Output {
        !&self
    }
}

impl Not for &Esop {
    type Output = Esop;
    fn not(self) -> Self::Output {
        let mut ret = self.clone();
        ret.cubes.push(Cube::one());
        ret
    }
}

impl BitXor<Esop> for Esop {
    type Output = Esop;
    fn bitxor(self, rhs: Esop) -> Self::Output {
        Esop::xor(&self, &rhs)
    }
}

impl BitXor<Esop> for &Esop {
    type Output = Esop;
    fn bitxor(self, rhs: Esop) -> Self::Output {
        Esop::xor(self, &rhs)
    }
}

impl BitXor<&Esop> for &Esop {
    type Output = Esop;
    fn bitxor(self, rhs: &Esop) -> Self::Output {
        Esop::xor(self, rhs)
    }
}

impl BitXor<&Esop> for Esop {
    type Output = Esop;
    fn bitxor(self, rhs: &Esop) -> Self::Output {
        Esop::xor(&self, rhs)
    }
}

impl fmt::Display for Esop {
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
            .join(" ^ ");
        write!(f, "{}", s)
    }
}

impl From<&Esop> for Lut {
    fn from(value: &Esop) -> Self {
        let mut ret = Lut::zero(value.num_vars());
        let mx = ret.num_bits();
        for mask in 0..mx {
            if value.value(mask) {
                ret.set_bit(mask);
            }
        }
        ret
    }
}

impl From<Esop> for Lut {
    fn from(value: Esop) -> Self {
        Lut::from(&value)
    }
}

#[cfg(test)]
mod tests {
    use super::Cube;
    use super::Esop;

    #[test]
    fn test_zero_one() {
        assert!(Esop::zero(32).is_zero());
        assert!(!Esop::one(32).is_zero());
        assert!(!Esop::zero(32).is_one());
        assert!(Esop::one(32).is_one());
        for i in 0..32 {
            assert!(!Esop::nth_var(32, i).is_zero());
            assert!(!Esop::nth_var(32, i).is_one());
            assert!(!Esop::nth_var_inv(32, i).is_zero());
            assert!(!Esop::nth_var_inv(32, i).is_one());
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_xor() {
        use crate::Lut;

        for num_vars in 0..8 {
            for i in 0..num_vars {
                for j in 0..num_vars {
                    let s = Esop::nth_var(num_vars, i) ^ Esop::nth_var(num_vars, j);
                    let l = Lut::nth_var(num_vars, i) ^ Lut::nth_var(num_vars, j);
                    assert_eq!(l, s.into());
                }
            }
        }

        for num_vars in 0..8 {
            for i in 0..num_vars {
                for j in 0..num_vars {
                    let s = Esop::nth_var_inv(num_vars, i) ^ Esop::nth_var(num_vars, j);
                    let l = Lut::nth_var(num_vars, i) ^ !Lut::nth_var(num_vars, j);
                    assert_eq!(l, s.into());
                }
            }
        }
    }

    #[test]
    fn test_display() {
        let s = Esop::from_cubes(
            6,
            vec![
                Cube::from_vars(&[1, 2], &[3]),
                Cube::from_vars(&[2, 1], &[0, 4, 5]),
            ],
        );
        assert_eq!(format!("{:}", s), "x1x2!x3 ^ !x0x1x2!x4!x5");
    }
}
