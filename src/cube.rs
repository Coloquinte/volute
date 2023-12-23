//! Compact representation of And and Xor functions

use std::{
    fmt,
    ops::{BitAnd, BitXor, Not},
};

/// Representation of the And of variables (a cube in sum-of-products formulations)
///
/// Each variable is represented by a pair of bits, representing respectively the positive
/// and negative literal. If none is set, the variable is unused. If both are set, the cube is 0.
///
/// It only supports And operations. Anything else must be implemented by more complex
/// representations that use it, such as sum-of-products.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Cube {
    pos: u32,
    neg: u32,
}

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

impl Cube {
    /// The empty cube
    pub fn one() -> Cube {
        Cube { pos: 0, neg: 0 }
    }

    /// The zero cube (not strictly a cube, so it gets a special representation)
    pub fn zero() -> Cube {
        Cube { pos: !0, neg: !0 }
    }

    /// Check whether the cube is a constant
    pub fn is_constant(&self) -> bool {
        self.is_one() || self.is_zero()
    }

    /// Check whether the cube is a constant zero
    ///
    /// This can happen after And operations, so we check if any variable has the two bits set.
    pub fn is_zero(&self) -> bool {
        self.pos & self.neg != 0
    }

    /// Check whether the cube is the constant one
    pub fn is_one(&self) -> bool {
        self.pos == 0 && self.neg == 0
    }

    /// Return the cube representing the nth variable
    pub fn nth_var(var: usize) -> Cube {
        Cube {
            pos: 1 << var,
            neg: 0,
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(var: usize) -> Cube {
        Cube {
            pos: 0,
            neg: 1 << var,
        }
    }

    /// Obtain the minterm for a value of the variables
    pub fn minterm(num_vars: usize, mask: usize) -> Cube {
        let m = mask as u32;
        let tot = (1 << num_vars) - 1;
        Cube {
            pos: m & tot,
            neg: !m & tot,
        }
    }

    /// Get the value of the Cube for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        let m = mask as u32;
        (self.pos & m) | !self.pos == !0 && (self.neg & !m) | !self.neg == !0
    }

    /// Build a cube from the literals in it
    pub fn from_vars(pos_vars: &[usize], neg_vars: &[usize]) -> Cube {
        let mut pos = 0;
        for p in pos_vars {
            pos |= 1 << p;
        }
        let mut neg = 0;
        for p in neg_vars {
            neg |= 1 << p;
        }
        let c = Cube { pos, neg };
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
            self.pos.count_ones() as usize + self.neg.count_ones() as usize
        }
    }

    /// Returns the variables that are positive in the cube
    pub fn pos_vars(&self) -> impl Iterator<Item = usize> + '_ {
        (0..32).filter(|v| (self.pos >> v & 1) != 0)
    }

    /// Returns the variables that are negative in the cube
    pub fn neg_vars(&self) -> impl Iterator<Item = usize> + '_ {
        (0..32).filter(|v| (self.neg >> v & 1) != 0)
    }

    /// Returns whether the cube implies another. This is used for Sop simplification
    pub fn implies(&self, o: Cube) -> bool {
        self.pos | o.pos == self.pos && self.neg | o.neg == self.neg
    }

    /// Perform the and operation on two cubes
    fn and(a: Cube, b: Cube) -> Cube {
        let ret = Cube {
            pos: a.pos | b.pos,
            neg: a.neg | b.neg,
        };
        if ret.is_zero() {
            // Normalize any zero cube to the standard zero
            Cube::zero()
        } else {
            ret
        }
    }

    /// Return all possible cubes with a given number of variables
    pub fn all(vars: usize) -> impl Iterator<Item = Cube> {
        let mx: u32 = 1 << vars;
        (0..mx)
            .flat_map(move |i| (0..mx).map(move |j| (i, j)))
            .map(|(i, j)| Cube { pos: i, neg: j })
            .filter(|c| !c.is_zero())
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
        let mut pos = self.pos;
        let mut neg = self.neg;
        let mut i = 0;
        while pos != 0 || neg != 0 {
            if pos & 1 != 0 {
                write!(f, "x{}", i)?;
            }
            if neg & 1 != 0 {
                write!(f, "!x{}", i)?;
            }
            i += 1;
            pos >>= 1;
            neg >>= 1;
        }
        Ok(())
    }
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
    use super::{Cube, Ecube};

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

    #[test]
    fn test_cube_and() {
        for i in 0..32 {
            let vi = Cube::nth_var(i);
            let vin = Cube::nth_var_inv(i);
            assert_eq!(vi, vi & vi);
            assert_eq!(vin, vin & vin);
            assert_eq!(Cube::zero(), vi & vin);
            for j in i + 1..32 {
                let vj = Cube::nth_var(j);
                let vjn = Cube::nth_var_inv(j);
                assert_eq!(Cube::from_vars(&[i, j], &[]), vi & vj);
                assert_eq!(Cube::from_vars(&[i], &[j]), vi & vjn);
                assert_eq!(Cube::from_vars(&[j], &[i]), vin & vj);
                assert_eq!(Cube::from_vars(&[], &[i, j]), vin & vjn);
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
    fn test_cube_value() {
        for i in 0..32 {
            let vi = Cube::nth_var(i);
            let vin = Cube::nth_var_inv(i);
            assert!(vi.value(1 << i));
            assert!(!vi.value(!(1 << i)));
            assert!(!vin.value(1 << i));
            assert!(vin.value(!(1 << i)));
            for j in i + 1..32 {
                let vj = Cube::nth_var(j);
                let vjn = Cube::nth_var_inv(j);
                assert!((vi & vj).value(1 << i | 1 << j));
                assert!(!(vi & vj).value(1 << i));
                assert!(!(vi & vj).value(1 << j));
                assert!((vin & vjn).value(!(1 << i | 1 << j)));
                assert!(!(vin & vjn).value(!(1 << i)));
                assert!(!(vin & vjn).value(!(1 << j)));
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
        assert_eq!(Cube::all(0).count(), 1);
        assert_eq!(Cube::all(1).count(), 3);
        assert_eq!(Cube::all(2).count(), 9);
        assert_eq!(Cube::all(3).count(), 27);
        assert_eq!(Ecube::all(0).count(), 2);
        assert_eq!(Ecube::all(1).count(), 4);
        assert_eq!(Ecube::all(2).count(), 8);
        assert_eq!(Ecube::all(3).count(), 16);
    }
}
