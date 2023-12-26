use std::{fmt, ops::BitOr};

use crate::{ecube::Ecube, Lut};

/// Sum of Exclusive Sums representation (Or of Xor)
///
/// Not all boolean functions can be represented this way (for example, a & b cannot).
/// This can still be a useful representation to optimize logic containing Xor gates.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Soes {
    num_vars: usize,
    cubes: Vec<Ecube>,
}

impl Soes {
    /// Query the number of variables
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Return the constant zero Soes
    pub fn zero(num_vars: usize) -> Soes {
        Soes {
            num_vars,
            cubes: vec![],
        }
    }

    /// Return the constant one Soes
    pub fn one(num_vars: usize) -> Soes {
        Soes {
            num_vars,
            cubes: vec![Ecube::one()],
        }
    }

    /// Number of cubes in the Soes
    pub fn num_cubes(&self) -> usize {
        self.cubes.len()
    }

    /// Number of literals in the Soes
    pub fn num_lits(&self) -> usize {
        let mut ret = 0;
        for c in &self.cubes {
            ret += c.num_lits();
        }
        ret
    }

    /// Returns whether the Soes is trivially constant zero
    pub fn is_zero(&self) -> bool {
        self.cubes.is_empty()
    }

    /// Returns whether the Soes is trivially constant one
    pub fn is_one(&self) -> bool {
        match self.cubes.first() {
            Some(c) => c.is_one(),
            None => false,
        }
    }

    /// Return the Soes representing the nth variable
    pub fn nth_var(num_vars: usize, var: usize) -> Soes {
        Soes {
            num_vars,
            cubes: vec![Ecube::nth_var(var)],
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(num_vars: usize, var: usize) -> Soes {
        Soes {
            num_vars,
            cubes: vec![Ecube::nth_var_inv(var)],
        }
    }

    /// Returns the cubes in the Soes
    pub fn cubes(&self) -> &[Ecube] {
        &self.cubes
    }

    /// Get the value of the Soes for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        let mut ret = false;
        for c in &self.cubes {
            ret |= c.value(mask);
        }
        ret
    }

    /// Compute the or of two Soess
    fn or(a: &Soes, b: &Soes) -> Soes {
        assert_eq!(a.num_vars, b.num_vars);
        let mut cubes = a.cubes.clone();
        cubes.extend(&b.cubes);
        Soes {
            num_vars: a.num_vars,
            cubes,
        }
    }
}

impl BitOr<Soes> for Soes {
    type Output = Soes;
    fn bitor(self, rhs: Soes) -> Self::Output {
        Soes::or(&self, &rhs)
    }
}

impl BitOr<Soes> for &Soes {
    type Output = Soes;
    fn bitor(self, rhs: Soes) -> Self::Output {
        Soes::or(self, &rhs)
    }
}

impl BitOr<&Soes> for &Soes {
    type Output = Soes;
    fn bitor(self, rhs: &Soes) -> Self::Output {
        Soes::or(self, rhs)
    }
}

impl BitOr<&Soes> for Soes {
    type Output = Soes;
    fn bitor(self, rhs: &Soes) -> Self::Output {
        Soes::or(&self, rhs)
    }
}

impl fmt::Display for Soes {
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

impl From<Soes> for Lut {
    fn from(value: Soes) -> Self {
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

#[cfg(test)]
mod tests {
    use super::Soes;

    #[test]
    fn test_zero_one() {
        assert!(Soes::zero(32).is_zero());
        assert!(!Soes::one(32).is_zero());
        assert!(!Soes::zero(32).is_one());
        assert!(Soes::one(32).is_one());
        for i in 0..32 {
            assert!(!Soes::nth_var(32, i).is_zero());
            assert!(!Soes::nth_var(32, i).is_one());
            assert!(!Soes::nth_var_inv(32, i).is_zero());
            assert!(!Soes::nth_var_inv(32, i).is_one());
        }
    }
}
