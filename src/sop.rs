use std::{
    fmt,
    ops::{BitAnd, BitOr, Not},
};

use crate::{cube::Cube, Lut};

/// Sum of products representation (Or of And)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Sop {
    num_vars: usize,
    cubes: Vec<Cube>,
}

impl Sop {
    /// Query the number of variables
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Return the constant zero Sop
    pub fn zero(num_vars: usize) -> Sop {
        Sop {
            num_vars,
            cubes: vec![],
        }
    }

    /// Return the constant one Sop
    pub fn one(num_vars: usize) -> Sop {
        Sop {
            num_vars,
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

    /// Return the Sop representing the nth variable
    pub fn nth_var(num_vars: usize, var: usize) -> Sop {
        Sop {
            num_vars,
            cubes: vec![Cube::nth_var(var)],
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(num_vars: usize, var: usize) -> Sop {
        Sop {
            num_vars,
            cubes: vec![Cube::nth_var_inv(var)],
        }
    }

    /// Returns the cubes in the Sop
    pub fn cubes(&self) -> &[Cube] {
        &self.cubes
    }

    /// Get the value of the Sop for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        let mut ret = false;
        for c in &self.cubes {
            ret |= c.value(mask);
        }
        ret
    }

    /// Basic simplification of the Sop
    ///
    /// The following simplifications are performed:
    ///   * Zero cubes are removed
    ///   * Cubes that imply another are removed
    ///   * Some cubes that differ by one literal are merged
    fn simplify(&mut self) {
        // No need for zeros
        self.cubes.retain(|c| !c.is_zero());
        // Remove any duplicate cube the easy way
        self.cubes.sort();
        self.cubes.dedup();
        // Remove any cube that implies another
        // TODO
    }

    /// Compute the or of two Sops
    fn or(a: &Sop, b: &Sop) -> Sop {
        assert_eq!(a.num_vars, b.num_vars);
        let mut cubes = a.cubes.clone();
        cubes.extend(&b.cubes);
        let mut ret = Sop {
            num_vars: a.num_vars,
            cubes,
        };
        ret.simplify();
        ret
    }

    /// Compute the and of two Sops
    fn and(a: &Sop, b: &Sop) -> Sop {
        assert_eq!(a.num_vars, b.num_vars);
        let mut cubes = Vec::new();
        for c1 in &a.cubes {
            for c2 in &b.cubes {
                let c = c1 & c2;
                if c != Cube::zero() {
                    cubes.push(c);
                }
            }
        }
        let mut ret = Sop {
            num_vars: a.num_vars,
            cubes,
        };
        ret.simplify();
        ret
    }
}

impl Not for Sop {
    type Output = Sop;
    fn not(self) -> Self::Output {
        !&self
    }
}

impl Not for &Sop {
    type Output = Sop;
    fn not(self) -> Self::Output {
        let mut ret = Sop::one(self.num_vars);
        for c in &self.cubes {
            let mut v = Vec::new();
            for l in c.pos_vars() {
                v.push(Cube::nth_var_inv(l));
            }
            for l in c.neg_vars() {
                v.push(Cube::nth_var(l));
            }
            let s = Sop {
                num_vars: self.num_vars,
                cubes: v,
            };
            ret = ret & s;
        }
        ret
    }
}

impl BitAnd<Sop> for Sop {
    type Output = Sop;
    fn bitand(self, rhs: Sop) -> Self::Output {
        Sop::and(&self, &rhs)
    }
}

impl BitAnd<Sop> for &Sop {
    type Output = Sop;
    fn bitand(self, rhs: Sop) -> Self::Output {
        Sop::and(self, &rhs)
    }
}

impl BitAnd<&Sop> for &Sop {
    type Output = Sop;
    fn bitand(self, rhs: &Sop) -> Self::Output {
        Sop::and(self, rhs)
    }
}

impl BitAnd<&Sop> for Sop {
    type Output = Sop;
    fn bitand(self, rhs: &Sop) -> Self::Output {
        Sop::and(&self, rhs)
    }
}

impl BitOr<Sop> for Sop {
    type Output = Sop;
    fn bitor(self, rhs: Sop) -> Self::Output {
        Sop::or(&self, &rhs)
    }
}

impl BitOr<Sop> for &Sop {
    type Output = Sop;
    fn bitor(self, rhs: Sop) -> Self::Output {
        Sop::or(self, &rhs)
    }
}

impl BitOr<&Sop> for &Sop {
    type Output = Sop;
    fn bitor(self, rhs: &Sop) -> Self::Output {
        Sop::or(self, rhs)
    }
}

impl BitOr<&Sop> for Sop {
    type Output = Sop;
    fn bitor(self, rhs: &Sop) -> Self::Output {
        Sop::or(&self, rhs)
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

impl From<Lut> for Sop {
    fn from(value: Lut) -> Self {
        let mut ret = Sop::zero(value.num_vars());
        let mx = value.num_bits();
        for mask in 0..mx {
            if value.value(mask) {
                ret.cubes.push(Cube::minterm(value.num_vars(), mask));
            }
        }
        ret
    }
}

impl From<Sop> for Lut {
    fn from(value: Sop) -> Self {
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
    use crate::Sop;

    #[test]
    fn test_sop_zero_one() {
        assert!(Sop::zero(32).is_zero());
        assert!(!Sop::one(32).is_zero());
        assert!(!Sop::zero(32).is_one());
        assert!(Sop::one(32).is_one());
        for i in 0..32 {
            assert!(!Sop::nth_var(32, i).is_zero());
            assert!(!Sop::nth_var(32, i).is_one());
            assert!(!Sop::nth_var_inv(32, i).is_zero());
            assert!(!Sop::nth_var_inv(32, i).is_one());
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_sop_not() {
        use crate::Lut;

        for i in 0..8 {
            for _ in 0..10 {
                let l = Lut::random(i);
                let ln = !&l;
                let s: Sop = l.into();
                let sn = !&s;
                assert_eq!(ln, sn.into());
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_sop_or() {
        use crate::Lut;

        for i in 0..8 {
            for _ in 0..10 {
                let l1 = Lut::random(i);
                let l2 = Lut::random(i);
                let lo = &l1 | &l2;
                let s1: Sop = l1.into();
                let s2: Sop = l2.into();
                let so = s1 | s2;
                assert_eq!(lo, so.into());
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_sop_and() {
        use crate::Lut;

        for i in 0..8 {
            for _ in 0..10 {
                let l1 = Lut::random(i);
                let l2 = Lut::random(i);
                let lo = &l1 & &l2;
                let s1: Sop = l1.into();
                let s2: Sop = l2.into();
                let so = s1 & s2;
                assert_eq!(lo, so.into());
            }
        }
    }
}
