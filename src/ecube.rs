//! Compact representation of And and Xor functions

use std::{
    fmt,
    ops::{BitXor, Not},
};

/// Representation of the Xor of variables, similar to [`Cube`] for Xor
///
/// Each variable is represented by a bit, and the overall parity (xor or xnor) is represented
/// on the side.
///
/// It only supports Not and Xor operations. Anything else must be implemented by more complex
/// representations that use it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Ecube {
    vars: u32,
    xnor: bool,
}

impl Ecube {
    /// The empty cube
    pub fn one() -> Ecube {
        Ecube {
            vars: 0,
            xnor: true,
        }
    }

    /// The zero cube
    pub fn zero() -> Ecube {
        Ecube {
            vars: 0,
            xnor: false,
        }
    }

    /// Check whether the cube is a constant zero
    pub fn is_zero(&self) -> bool {
        self.vars == 0 && !self.xnor
    }

    /// Check whether the cube is the constant one
    pub fn is_one(&self) -> bool {
        self.vars == 0 && self.xnor
    }

    /// Return the cube representing the nth variable
    pub fn nth_var(var: usize) -> Ecube {
        Ecube {
            vars: 1 << var,
            xnor: false,
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(var: usize) -> Ecube {
        Ecube {
            vars: 1 << var,
            xnor: true,
        }
    }

    /// Get the value of the cube for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        let m = mask as u32;
        let xorv = (self.vars & m).count_ones() % 2;
        (xorv == 1) ^ self.xnor
    }

    /// Build a cube from its variables
    pub fn from_vars(vars: &[usize], xnor: bool) -> Ecube {
        let mut v = 0;
        for p in vars {
            v |= 1 << p;
        }
        Ecube { vars: v, xnor }
    }

    /// Return the number of literals
    pub fn num_lits(&self) -> usize {
        self.vars.count_ones() as usize
    }

    /// Returns the variables in the cube
    pub fn vars(&self) -> impl Iterator<Item = usize> + '_ {
        (0..32).filter(|v| (self.vars >> v & 1) != 0)
    }

    /// Return all possible cubes with a given number of variables
    pub fn all(vars: usize) -> impl Iterator<Item = Ecube> {
        let mx: u32 = 1 << vars;
        (0..mx)
            .flat_map(|i| [false, true].map(|x| (i, x)))
            .map(|(i, x)| Ecube { vars: i, xnor: x })
    }
}

impl Not for Ecube {
    type Output = Ecube;
    fn not(self) -> Self::Output {
        Ecube {
            vars: self.vars,
            xnor: !self.xnor,
        }
    }
}

impl Not for &Ecube {
    type Output = Ecube;
    fn not(self) -> Self::Output {
        Ecube {
            vars: self.vars,
            xnor: !self.xnor,
        }
    }
}

impl BitXor<Ecube> for Ecube {
    type Output = Ecube;
    fn bitxor(self, rhs: Ecube) -> Self::Output {
        Ecube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<Ecube> for &Ecube {
    type Output = Ecube;
    fn bitxor(self, rhs: Ecube) -> Self::Output {
        Ecube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<&Ecube> for &Ecube {
    type Output = Ecube;
    fn bitxor(self, rhs: &Ecube) -> Self::Output {
        Ecube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<&Ecube> for Ecube {
    type Output = Ecube;
    fn bitxor(self, rhs: &Ecube) -> Self::Output {
        Ecube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl fmt::Display for Ecube {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")?;
            return Ok(());
        }
        let mut v = Vec::new();
        if self.xnor {
            v.push("1".to_string());
        }
        let mut vars = self.vars;
        let mut i = 0;
        while vars != 0 {
            if vars & 1 != 0 {
                v.push(format!("x{}", i));
            }
            i += 1;
            vars >>= 1;
        }

        let s = v.join(" ^ ");
        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod tests {
    use super::Ecube;

    #[test]
    fn test_xcube_zero_one() {
        assert!(Ecube::zero().is_zero());
        assert!(!Ecube::one().is_zero());
        assert!(!Ecube::zero().is_one());
        assert!(Ecube::one().is_one());
        for i in 0..32 {
            assert!(!Ecube::nth_var(i).is_zero());
            assert!(!Ecube::nth_var(i).is_one());
            assert!(!Ecube::nth_var_inv(i).is_zero());
            assert!(!Ecube::nth_var_inv(i).is_one());
        }
    }

    #[test]
    fn test_xcube_display() {
        assert_eq!(format!("{}", Ecube::zero()), "0");
        assert_eq!(format!("{}", Ecube::one()), "1");
        for i in 0..32 {
            assert_eq!(format!("{}", Ecube::nth_var(i)), format!("x{}", i));
            assert_eq!(format!("{}", Ecube::nth_var_inv(i)), format!("1 ^ x{}", i));
        }
        for i in 0..32 {
            let vi = Ecube::nth_var(i);
            for j in i + 1..32 {
                let vj = Ecube::nth_var(j);
                assert_eq!(format!("{}", vi ^ vj), format!("x{} ^ x{}", i, j));
                assert_eq!(format!("{}", vi ^ !vj), format!("1 ^ x{} ^ x{}", i, j));
                assert_eq!(format!("{}", !vi ^ vj), format!("1 ^ x{} ^ x{}", i, j));
                assert_eq!(format!("{}", !vi ^ !vj), format!("x{} ^ x{}", i, j));
            }
        }
    }

    #[test]
    fn test_num_lits() {
        assert_eq!(Ecube::zero().num_lits(), 0);
        assert_eq!(Ecube::one().num_lits(), 0);
        for i in 0..32 {
            assert_eq!(Ecube::nth_var(i).num_lits(), 1);
            assert_eq!(Ecube::nth_var_inv(i).num_lits(), 1);
        }
        for i in 0..32 {
            for j in i + 1..32 {
                assert_eq!(Ecube::from_vars(&[i, j], false).num_lits(), 2);
            }
        }
    }

    #[test]
    fn test_xcube_xor() {
        for i in 0..32 {
            let vi = Ecube::nth_var(i);
            let vin = Ecube::nth_var_inv(i);
            assert_eq!(Ecube::zero(), vi ^ vi);
            assert_eq!(Ecube::one(), vi ^ vin);
            assert_eq!(Ecube::zero(), vin ^ vin);
            for j in i + 1..32 {
                let vj = Ecube::nth_var(j);
                let vjn = Ecube::nth_var_inv(j);
                assert_eq!(Ecube::from_vars(&[i, j], false), vi ^ vj);
                assert_eq!(Ecube::from_vars(&[i, j], true), vi ^ vjn);
                assert_eq!(Ecube::from_vars(&[i, j], true), vin ^ vj);
                assert_eq!(Ecube::from_vars(&[i, j], false), vin ^ vjn);
            }
        }
    }

    #[test]
    fn test_xcube_value() {
        for i in 0..32 {
            let vi = Ecube::nth_var(i);
            let vin = Ecube::nth_var_inv(i);
            assert!(vi.value(1 << i));
            assert!(!vi.value(!(1 << i)));
            assert!(!vin.value(1 << i));
            assert!(vin.value(!(1 << i)));
            for j in i + 1..32 {
                let vj = Ecube::nth_var(j);
                assert!(!(vi ^ vj).value(1 << i | 1 << j));
                assert!((vi ^ vj).value(1 << i));
                assert!((vi ^ vj).value(1 << j));
                assert!(!(vi ^ vj).value(0));
            }
        }
    }

    #[test]
    fn test_cube_num() {
        assert_eq!(Ecube::all(0).count(), 2);
        assert_eq!(Ecube::all(1).count(), 4);
        assert_eq!(Ecube::all(2).count(), 8);
        assert_eq!(Ecube::all(3).count(), 16);
    }
}
