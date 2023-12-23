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
pub struct XCube {
    vars: u32,
    xnor: bool,
}

/// Representation of a sum-of-products (or of and)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Sop {
    cubes: Vec<Cube>,
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

    /// Get the value of the Cube for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: u32) -> bool {
        (self.pos & mask) | !self.pos == !0 && (self.neg & !mask) | !self.neg == !0
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
    pub fn pos_vars(&self) -> Vec<usize> {
        (0..32).filter(|v| (self.pos >> v & 1) != 0).collect()
    }

    /// Returns the variables that are negative in the cube
    pub fn neg_vars(&self) -> Vec<usize> {
        (0..32).filter(|v| (self.neg >> v & 1) != 0).collect()
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

impl XCube {
    /// The empty cube
    pub fn one() -> XCube {
        XCube {
            vars: 0,
            xnor: true,
        }
    }

    /// The zero cube
    pub fn zero() -> XCube {
        XCube {
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
    pub fn nth_var(var: usize) -> XCube {
        XCube {
            vars: 1 << var,
            xnor: false,
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(var: usize) -> XCube {
        XCube {
            vars: 1 << var,
            xnor: true,
        }
    }

    /// Get the value of the cube for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: u32) -> bool {
        let xorv = (self.vars & mask).count_ones() % 2;
        (xorv == 1) ^ self.xnor
    }

    /// Build a cube from its variables
    pub fn from_vars(vars: &[usize], xnor: bool) -> XCube {
        let mut v = 0;
        for p in vars {
            v |= 1 << p;
        }
        XCube { vars: v, xnor }
    }

    /// Return the number of literals
    pub fn num_lits(&self) -> usize {
        self.vars.count_ones() as usize
    }

    /// Returns the variables in the cube
    pub fn vars(&self) -> Vec<usize> {
        (0..32).filter(|v| (self.vars >> v & 1) != 0).collect()
    }
}

impl Not for XCube {
    type Output = XCube;
    fn not(self) -> Self::Output {
        XCube {
            vars: self.vars,
            xnor: !self.xnor,
        }
    }
}

impl Not for &XCube {
    type Output = XCube;
    fn not(self) -> Self::Output {
        XCube {
            vars: self.vars,
            xnor: !self.xnor,
        }
    }
}

impl BitXor<XCube> for XCube {
    type Output = XCube;
    fn bitxor(self, rhs: XCube) -> Self::Output {
        XCube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<XCube> for &XCube {
    type Output = XCube;
    fn bitxor(self, rhs: XCube) -> Self::Output {
        XCube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<&XCube> for &XCube {
    type Output = XCube;
    fn bitxor(self, rhs: &XCube) -> Self::Output {
        XCube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl BitXor<&XCube> for XCube {
    type Output = XCube;
    fn bitxor(self, rhs: &XCube) -> Self::Output {
        XCube {
            vars: self.vars ^ rhs.vars,
            xnor: self.xnor ^ rhs.xnor,
        }
    }
}

impl fmt::Display for XCube {
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

    /// Return the Sop representing the nth variable
    pub fn nth_var(var: usize) -> Sop {
        Sop {
            cubes: vec![Cube::nth_var(var)],
        }
    }

    /// Return the cube representing the nth variable, inverted
    pub fn nth_var_inv(var: usize) -> Sop {
        Sop {
            cubes: vec![Cube::nth_var_inv(var)],
        }
    }

    /// Get the value of the Sop for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: u32) -> bool {
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
        // Remove any cube that implies another
    }

    /// Compute the negation of an Sop
    fn not(&self) -> Sop {
        todo!();
    }

    /// Compute the or of two Sops
    fn or(a: &Sop, b: &Sop) -> Sop {
        let mut cubes = a.cubes.clone();
        cubes.extend(&b.cubes);
        let mut ret = Sop { cubes };
        ret.simplify();
        ret
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
        let mut ret = Sop { cubes };
        ret.simplify();
        ret
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
    use crate::{Cube, XCube};

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
        assert!(XCube::zero().is_zero());
        assert!(!XCube::one().is_zero());
        assert!(!XCube::zero().is_one());
        assert!(XCube::one().is_one());
        for i in 0..32 {
            assert!(!XCube::nth_var(i).is_zero());
            assert!(!XCube::nth_var(i).is_one());
            assert!(!XCube::nth_var_inv(i).is_zero());
            assert!(!XCube::nth_var_inv(i).is_one());
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
        assert_eq!(format!("{}", XCube::zero()), "0");
        assert_eq!(format!("{}", XCube::one()), "1");
        for i in 0..32 {
            assert_eq!(format!("{}", XCube::nth_var(i)), format!("x{}", i));
            assert_eq!(format!("{}", XCube::nth_var_inv(i)), format!("1 ^ x{}", i));
        }
        for i in 0..32 {
            let vi = XCube::nth_var(i);
            for j in i + 1..32 {
                let vj = XCube::nth_var(j);
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
            let vi = XCube::nth_var(i);
            let vin = XCube::nth_var_inv(i);
            assert_eq!(XCube::zero(), vi ^ vi);
            assert_eq!(XCube::one(), vi ^ vin);
            assert_eq!(XCube::zero(), vin ^ vin);
            for j in i + 1..32 {
                let vj = XCube::nth_var(j);
                let vjn = XCube::nth_var_inv(j);
                assert_eq!(XCube::from_vars(&[i, j], false), vi ^ vj);
                assert_eq!(XCube::from_vars(&[i, j], true), vi ^ vjn);
                assert_eq!(XCube::from_vars(&[i, j], true), vin ^ vj);
                assert_eq!(XCube::from_vars(&[i, j], false), vin ^ vjn);
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
            let vi = XCube::nth_var(i);
            let vin = XCube::nth_var_inv(i);
            assert!(vi.value(1 << i));
            assert!(!vi.value(!(1 << i)));
            assert!(!vin.value(1 << i));
            assert!(vin.value(!(1 << i)));
            for j in i + 1..32 {
                let vj = XCube::nth_var(j);
                assert!(!(vi ^ vj).value(1 << i | 1 << j));
                assert!((vi ^ vj).value(1 << i));
                assert!((vi ^ vj).value(1 << j));
                assert!(!(vi ^ vj).value(0));
            }
        }
    }
}
