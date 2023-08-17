use core::fmt;
use std::cmp::Ordering;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Not;

use crate::canonization::n_canonization;
use crate::canonization::npn_canonization;
use crate::canonization::p_canonization;
use crate::operations::*;

/// Arbitrary-size truth table
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Lut {
    num_vars: usize,
    table: Box<[u64]>,
}

impl Lut {
    /// Query the number of variables of the Lut
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Query the number of bits in the Lut
    pub fn num_bits(&self) -> usize {
        1 << self.num_vars
    }

    /// Create a new Lut
    fn new(num_vars: usize) -> Lut {
        Lut {
            num_vars,
            table: vec![0; table_size(num_vars)].into_boxed_slice(),
        }
    }

    /// Check that an input is valid for an operation
    fn check_var(&self, ind: usize) {
        assert!(ind < self.num_vars());
    }

    /// Check that another Lut is valid for an operation
    fn check_lut(&self, rhs: &Self) {
        assert_eq!(self.num_vars(), rhs.num_vars());
    }

    /// Check that a bit is valid for an operation
    fn check_bit(&self, ind: usize) {
        assert!(ind < self.num_bits());
    }

    /// Create a constant true Lut
    pub fn one(num_vars: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_one(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a constant false Lut
    pub fn zero(num_vars: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_zero(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning the value of one of its variables
    pub fn nth_var(num_vars: usize, var: usize) -> Lut {
        assert!(var < num_vars);
        let mut ret = Lut::new(num_vars);
        fill_nth_var(num_vars, ret.table.as_mut(), var);
        ret
    }

    /// Create a Lut returning true if the number of true variables is even
    pub fn parity(num_vars: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_parity(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if the majority of the variables are true
    pub fn majority(num_vars: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_majority(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if at least k variables are true
    pub fn threshold(num_vars: usize, k: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_threshold(num_vars, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut returning true if exactly k variables are true
    pub fn equals(num_vars: usize, k: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_equals(num_vars, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut representing a symmetric function. Bit at position k gives the value when k variables are true
    pub fn symmetric(num_vars: usize, count_values: usize) -> Lut {
        let mut ret = Lut::new(num_vars);
        fill_symmetric(num_vars, ret.table.as_mut(), count_values);
        ret
    }

    /// Get the value of the Lut for these inputs (input bits packed in the mask)
    pub fn get_bit(&self, mask: usize) -> bool {
        self.check_bit(mask);
        get_bit(self.num_vars, self.table.as_ref(), mask)
    }

    /// Set the value of the Lut for these inputs to true (input bits packed in the mask)
    pub fn set_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        set_bit(self.num_vars, self.table.as_mut(), mask);
    }

    /// Set the value of the Lut for these inputs to false (input bits packed in the mask)
    pub fn unset_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        unset_bit(self.num_vars, self.table.as_mut(), mask);
    }

    /// Complement the Lut in place: f(x) --> !f(x)
    pub fn not_inplace(&mut self) {
        not_inplace(self.num_vars, self.table.as_mut());
    }

    /// And two Luts in place
    pub fn and_inplace(&mut self, rhs: &Self) {
        self.check_lut(rhs);
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }

    /// Or two Luts in place
    pub fn or_inplace(&mut self, rhs: &Self) {
        self.check_lut(rhs);
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }

    /// Xor two Luts in place
    pub fn xor_inplace(&mut self, rhs: &Self) {
        self.check_lut(rhs);
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }

    /// Flip a variable in place: f(x1, ... xi, ... xn) --> f(x1, ... !xi, ... xn)
    pub fn flip_inplace(&mut self, ind: usize) {
        self.check_var(ind);
        flip_inplace(self.num_vars, self.table.as_mut(), ind);
    }

    /// Swap two variables in place: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap_inplace(&mut self, ind1: usize, ind2: usize) {
        self.check_var(ind1);
        self.check_var(ind2);
        swap_inplace(self.num_vars, self.table.as_mut(), ind1, ind2);
    }

    /// Swap two adjacent variables in place: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent_inplace(&mut self, ind: usize) {
        self.check_var(ind);
        self.check_var(ind + 1);
        swap_adjacent_inplace(self.num_vars, self.table.as_mut(), ind);
    }

    /// Complement the Lut: f(x) --> !f(x)
    pub fn not(&self) -> Lut {
        let mut l = self.clone();
        l.not_inplace();
        l
    }

    /// And two Luts
    pub fn and(&self, rhs: &Lut) -> Lut {
        let mut l = self.clone();
        l.and_inplace(rhs);
        l
    }

    /// Or two Luts
    pub fn or(&self, rhs: &Lut) -> Lut {
        let mut l = self.clone();
        l.or_inplace(rhs);
        l
    }

    /// Xor two Luts
    pub fn xor(&self, rhs: &Lut) -> Lut {
        let mut l = self.clone();
        l.xor_inplace(rhs);
        l
    }

    /// Flip a variable: f(x1, ... xi, ... xn) --> f(x1, ... !xi, ... xn)
    pub fn flip(&self, ind: usize) -> Lut {
        let mut l = self.clone();
        l.flip_inplace(ind);
        l
    }

    /// Swap two variables: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap(&self, ind1: usize, ind2: usize) -> Lut {
        let mut l = self.clone();
        l.swap_inplace(ind1, ind2);
        l
    }

    /// Swap two adjacent variables: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent(&mut self, ind: usize) -> Lut {
        let mut l = self.clone();
        l.swap_adjacent_inplace(ind);
        l
    }

    /// Obtain the two cofactors with respect to a variable
    pub fn cofactors(&self, ind: usize) -> (Self, Self) {
        let mut c = (self.clone(), self.clone());
        cofactor0_inplace(self.num_vars(), c.0.table.as_mut(), ind);
        cofactor1_inplace(self.num_vars(), c.1.table.as_mut(), ind);
        c
    }

    /// Create a Lut from its two cofactors
    pub fn from_cofactors(c0: &Self, c1: &Self, ind: usize) -> Self {
        assert_eq!(c0.num_vars, c1.num_vars);
        let mut ret = Lut::new(c0.num_vars);
        from_cofactors_inplace(
            c0.num_vars,
            ret.table.as_mut(),
            c0.table.as_ref(),
            c1.table.as_ref(),
            ind,
        );
        ret
    }

    /// Find the smallest equivalent Lut up to permutation.
    /// Return the canonical representation and the input permutation to obtain it.
    pub fn p_canonization(&self) -> (Self, Vec<u8>) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let mut perm = vec![0; self.num_vars];
        p_canonization(
            self.num_vars,
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm)
    }

    /// Find the smallest equivalent Lut up to input flips and output flip.
    /// Return the canonical representation and the flips to obtain it.
    pub fn n_canonization(&self) -> (Self, u32) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let flip = n_canonization(self.num_vars, work.table.as_mut(), ret.table.as_mut());
        (ret, flip)
    }

    /// Find the smallest equivalent Lut up to permutation, input flips and output flip.
    /// Return the canonical representation and the permutation and flips to obtain it.
    pub fn npn_canonization(&self) -> (Self, Vec<u8>, u32) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let mut perm = vec![0; self.num_vars];
        let flip = npn_canonization(
            self.num_vars,
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm, flip)
    }

    /// Decomposition of the function with respect to this variable
    pub fn decomposition(&self, ind: usize) -> DecompositionType {
        decomposition(self.num_vars, self.table.as_ref(), ind)
    }

    /// Returns whether the function is positive unate
    pub fn is_pos_unate(&self, ind: usize) -> bool {
        input_pos_unate(self.num_vars, self.table.as_ref(), ind)
    }

    /// Returns whether the function is negative unate
    pub fn is_neg_unate(&self, ind: usize) -> bool {
        input_neg_unate(self.num_vars, self.table.as_ref(), ind)
    }

    /// Collection of all Luts of a given size
    pub fn all_functions(num_vars: usize) -> LutIterator {
        LutIterator {
            lut: Lut::zero(num_vars),
            ok: true,
        }
    }
}

#[doc(hidden)]
pub struct LutIterator {
    lut: Lut,
    ok: bool,
}

impl Iterator for LutIterator {
    type Item = Lut;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.ok {
            None
        } else {
            let ret = self.lut.clone();
            self.ok = next_inplace(self.lut.num_vars, self.lut.table.as_mut());
            Some(ret)
        }
    }
}

impl Default for Lut {
    fn default() -> Self {
        Lut::zero(0)
    }
}

impl Ord for Lut {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.num_vars != other.num_vars {
            return self.num_vars.cmp(&other.num_vars);
        }
        // Reverse iterator comparison, as Luts are compared by most-significant digits first
        return cmp(self.table.as_ref(), other.table.as_ref());
    }
}

impl PartialOrd for Lut {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Not for Lut {
    type Output = Lut;
    fn not(self) -> Self::Output {
        let mut l = self;
        l.not_inplace();
        l
    }
}

impl Not for &'_ Lut {
    type Output = Lut;
    fn not(self) -> Self::Output {
        let mut l = self.clone();
        l.not_inplace();
        l
    }
}

impl BitAndAssign for Lut {
    fn bitand_assign(&mut self, rhs: Self) {
        assert!(self.num_vars == rhs.num_vars);
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a> BitAndAssign<&'a Lut> for Lut {
    fn bitand_assign(&mut self, rhs: &'a Lut) {
        assert!(self.num_vars == rhs.num_vars);
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitAnd for Lut {
    type Output = Lut;
    fn bitand(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl<'a, 'b> BitAnd<&'b Lut> for &'a Lut {
    type Output = Lut;
    fn bitand(self, rhs: &'b Lut) -> Self::Output {
        let mut l = self.clone();
        l &= rhs;
        l
    }
}

impl BitOrAssign for Lut {
    fn bitor_assign(&mut self, rhs: Self) {
        assert!(self.num_vars == rhs.num_vars);
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a> BitOrAssign<&'a Lut> for Lut {
    fn bitor_assign(&mut self, rhs: &'a Lut) {
        assert!(self.num_vars == rhs.num_vars);
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitOr for Lut {
    type Output = Lut;
    fn bitor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl BitOr for &'_ Lut {
    type Output = Lut;
    fn bitor(self, rhs: Self) -> Self::Output {
        let mut l = self.clone();
        l |= rhs;
        l
    }
}

impl BitXorAssign for Lut {
    fn bitxor_assign(&mut self, rhs: Self) {
        assert!(self.num_vars == rhs.num_vars);
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a> BitXorAssign<&'a Lut> for Lut {
    fn bitxor_assign(&mut self, rhs: &'a Lut) {
        assert!(self.num_vars == rhs.num_vars);
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitXor for Lut {
    type Output = Lut;
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl BitXor for &'_ Lut {
    type Output = Lut;
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut l = self.clone();
        l ^= rhs;
        l
    }
}

impl fmt::Display for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(self.num_vars, self.table.as_ref(), f)
    }
}

impl fmt::LowerHex for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(self.num_vars, self.table.as_ref(), f)
    }
}

impl fmt::Binary for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bin(self.num_vars, self.table.as_ref(), f)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{operations::DecompositionType, Lut};

    #[test]
    fn test_basic_logic() {
        for lut_size in 1..10 {
            assert!(Lut::one(lut_size) == !&Lut::zero(lut_size));
            for i in 0..lut_size {
                for j in 0..lut_size {
                    let in_1 = Lut::nth_var(lut_size, i);
                    let in_2 = Lut::nth_var(lut_size, j);
                    let r1 = &in_1 & &in_2;
                    let r2 = !(!&in_1 | !&in_2);
                    assert_eq!(r1, r2);

                    let x1 = &in_1 ^ &in_2;
                    let x2 = &x1 ^ &in_2;
                    assert_eq!(&in_1, &x2);

                    let zero = Lut::zero(lut_size);
                    let x3 = &in_1 & &zero;
                    assert_eq!(&x3, &zero);

                    let one = Lut::one(lut_size);
                    let x4 = &in_1 | &one;
                    assert_eq!(&x4, &one);
                }
            }
        }
    }

    #[test]
    fn test_symmetric() {
        assert_eq!(Lut::majority(3).to_string(), "Lut3(e8)");
        assert_eq!(Lut::majority(4).to_string(), "Lut4(fee8)");
        assert_eq!(Lut::equals(3, 0).to_string(), "Lut3(01)");
        assert_eq!(Lut::equals(4, 0).to_string(), "Lut4(0001)");
        assert_eq!(Lut::equals(3, 1).to_string(), "Lut3(16)");
        assert_eq!(Lut::equals(4, 1).to_string(), "Lut4(0116)");
        assert_eq!(Lut::parity(3).to_string(), "Lut3(96)");
        assert_eq!(Lut::parity(4).to_string(), "Lut4(6996)");
    }

    #[test]
    fn test_display() {
        let mut l1 = Lut::zero(5);
        l1.set_bit(10);
        assert_eq!(format!("{:}", l1), "Lut5(00000400)");
        assert_eq!(format!("{:}", l1), format!("{:x}", l1));

        let mut l2 = Lut::one(5);
        l2.unset_bit(30);
        assert_eq!(format!("{:}", l2), "Lut5(bfffffff)");
        assert_eq!(format!("{:}", l2), format!("{:x}", l2));

        let mut l3 = Lut::zero(7);
        l3.set_bit(74);
        assert_eq!(format!("{:}", l3), "Lut7(00000000000004000000000000000000)");
        assert_eq!(format!("{:}", l3), format!("{:x}", l3));

        let mut l4 = Lut::one(7);
        l4.unset_bit(126);
        assert_eq!(format!("{:}", l4), "Lut7(bfffffffffffffffffffffffffffffff)");
        assert_eq!(format!("{:}", l4), format!("{:x}", l4));

        assert_eq!(format!("{:}", Lut::zero(0)), "Lut0(0)");
        assert_eq!(format!("{:}", Lut::one(0)), "Lut0(1)");
        assert_eq!(format!("{:}", Lut::zero(1)), "Lut1(0)");
        assert_eq!(format!("{:}", Lut::one(1)), "Lut1(3)");
        assert_eq!(format!("{:}", Lut::zero(2)), "Lut2(0)");
        assert_eq!(format!("{:}", Lut::one(2)), "Lut2(f)");
        assert_eq!(format!("{:}", Lut::zero(3)), "Lut3(00)");
        assert_eq!(format!("{:}", Lut::one(3)), "Lut3(ff)");

        assert_eq!(Lut::default(), Lut::zero(0));
    }

    #[test]
    fn test_bin_display() {
        let mut l1 = Lut::zero(5);
        l1.set_bit(10);
        assert_eq!(
            format!("{:b}", l1),
            "Lut5(00000000000000000000010000000000)"
        );

        assert_eq!(
            format!("{:b}", Lut::zero(7)),
            format!("Lut7({:})", "0".repeat(128))
        );

        assert_eq!(
            format!("{:b}", Lut::one(8)),
            format!("Lut8({:})", "1".repeat(256))
        );

        assert_eq!(format!("{:b}", Lut::zero(0)), "Lut0(0)");
        assert_eq!(format!("{:b}", Lut::one(0)), "Lut0(1)");
        assert_eq!(format!("{:b}", Lut::zero(1)), "Lut1(00)");
        assert_eq!(format!("{:b}", Lut::one(1)), "Lut1(11)");
        assert_eq!(format!("{:b}", Lut::zero(2)), "Lut2(0000)");
        assert_eq!(format!("{:b}", Lut::one(2)), "Lut2(1111)");
        assert_eq!(format!("{:b}", Lut::zero(3)), "Lut3(00000000)");
        assert_eq!(format!("{:b}", Lut::one(3)), "Lut3(11111111)");
    }

    #[test]
    fn test_swap() {
        // All luts that copy a single variable
        for lut_size in 1..10 {
            for i in 0..lut_size {
                for j in 0..lut_size {
                    let in1 = Lut::nth_var(lut_size, i);
                    let in2 = Lut::nth_var(lut_size, j);
                    assert_eq!(in2, in1.swap(i, j));
                }
            }
        }

        // All single-bit luts
        for lut_size in 1..8 {
            for i in 0..lut_size {
                for j in 0..lut_size {
                    for b1 in 0..(1 << lut_size) {
                        let mut l1 = Lut::zero(lut_size);
                        l1.set_bit(b1);
                        let mut b2 = b1 & !(1 << i) & !(1 << j);
                        if b1 & (1 << i) != 0 {
                            b2 |= 1 << j;
                        }
                        if b1 & (1 << j) != 0 {
                            b2 |= 1 << i;
                        }
                        let mut l2 = Lut::zero(lut_size);
                        l2.set_bit(b2);

                        assert_eq!(l2, l1.swap(i, j));
                        assert_eq!(l1, l2.swap(i, j));
                        assert_eq!(l2, l1.swap(j, i));
                        assert_eq!(l1, l2.swap(j, i));
                    }
                }
            }
        }
    }

    #[test]
    fn test_flip() {
        for lut_size in 1..10 {
            // All luts that copy a single variable
            for i in 0..lut_size {
                let l = Lut::nth_var(lut_size, i);
                assert_eq!(l, l.flip(i).flip(i));
            }
            // All single-bit luts
            for b in 0..(1 << lut_size) {
                let mut l1 = Lut::zero(lut_size);
                l1.set_bit(b);
                assert!(l1.get_bit(b));
                let mut l2 = Lut::one(lut_size);
                l2.unset_bit(b);
                assert!(!l2.get_bit(b));
                for i in 0..lut_size {
                    let l1c = l1.flip(i);
                    assert!(l1c.get_bit(b ^ (1 << i)));
                    assert_eq!(l1, l1c.flip(i));
                    let l2c = l2.flip(i);
                    assert!(!l2c.get_bit(b ^ (1 << i)));
                    assert_eq!(l2, l2c.flip(i));
                }
            }
        }
    }

    #[test]
    fn test_iter() {
        assert_eq!(Lut::all_functions(0).count(), 2);
        assert_eq!(Lut::all_functions(1).count(), 4);
        assert_eq!(Lut::all_functions(2).count(), 16);
        assert_eq!(Lut::all_functions(3).count(), 256);
    }

    #[test]
    fn test_canonization() {
        let expected: [usize; 7] = [1, 2, 4, 14, 222, 616126, 200253952527184];
        for i in 2..=3 {
            // We only test a few by default, but this was checked up to 5
            let mut repr = HashSet::<Lut>::new();
            for lut in Lut::all_functions(i) {
                repr.insert(lut.npn_canonization().0);
            }
            assert_eq!(repr.len(), expected[i]);
        }
    }

    #[test]
    fn test_decomposition() {
        for i in 0..=8 {
            for v1 in 1..i {
                for v2 in 0..v1 {
                    let l1 = Lut::nth_var(i, v1);
                    let l2 = Lut::nth_var(i, v2);
                    let and = &l1 & &l2;
                    let or = &l1 | &l2;
                    let nand = !&and;
                    let nor = !&or;
                    let xor = &l1 ^ &l2;
                    let xnor = !&xor;
                    for v in 0..i {
                        if v == v1 || v == v2 {
                            assert_eq!(and.decomposition(v), DecompositionType::And);
                            assert_eq!(or.decomposition(v), DecompositionType::Or);
                            assert_eq!(nand.decomposition(v), DecompositionType::Nand);
                            assert_eq!(nor.decomposition(v), DecompositionType::Nor);
                            assert_eq!(xor.decomposition(v), DecompositionType::Xor);
                            assert_eq!(xnor.decomposition(v), DecompositionType::Xor);
                            assert!(and.is_pos_unate(v));
                            assert!(or.is_pos_unate(v));
                            assert!(!and.is_neg_unate(v));
                            assert!(!or.is_neg_unate(v));
                            assert!(!nand.is_pos_unate(v));
                            assert!(!nor.is_pos_unate(v));
                            assert!(nand.is_neg_unate(v));
                            assert!(nor.is_neg_unate(v));
                            assert!(!xor.is_pos_unate(v));
                            assert!(!xor.is_neg_unate(v));
                            assert!(!xnor.is_pos_unate(v));
                            assert!(!xnor.is_neg_unate(v));
                        } else {
                            for l in [&l1, &l2, &and, &or, &nand, &nor, &xor, &xnor] {
                                assert_eq!(l.decomposition(v), DecompositionType::Independent);
                                assert!(l.is_pos_unate(v));
                                assert!(l.is_neg_unate(v));
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_cofactors() {
        for i in 0..=8 {
            for v1 in 1..i {
                for v2 in 0..v1 {
                    let l1 = Lut::nth_var(i, v1);
                    let l2 = Lut::nth_var(i, v2);
                    let and = &l1 & &l2;
                    let or = &l1 | &l2;
                    let nand = !&and;
                    let nor = !&or;
                    let xor = &l1 ^ &l2;
                    let xnor = !&xor;
                    for v in 0..i {
                        for l in [&l1, &l2, &and, &or, &nand, &nor, &xor, &xnor] {
                            assert_eq!(
                                &Lut::from_cofactors(&l.cofactors(v).0, &l.cofactors(v).1, v),
                                l
                            );
                        }
                        if v == v1 || v == v2 {
                            let ov = v1 ^ v2 ^ v;
                            assert_eq!(and.cofactors(v).0, Lut::zero(i));
                            assert_eq!(and.cofactors(v).1, Lut::nth_var(i, ov));
                            assert_eq!(nand.cofactors(v).0, Lut::one(i));
                            assert_eq!(nand.cofactors(v).1, !Lut::nth_var(i, ov));
                            assert_eq!(or.cofactors(v).1, Lut::one(i));
                            assert_eq!(or.cofactors(v).0, Lut::nth_var(i, ov));
                            assert_eq!(nor.cofactors(v).1, Lut::zero(i));
                            assert_eq!(nor.cofactors(v).0, !Lut::nth_var(i, ov));
                            assert_eq!(xor.cofactors(v).0, !xor.cofactors(v).1);
                            assert_eq!(xnor.cofactors(v).0, !xnor.cofactors(v).1);
                        } else {
                            for l in [&l1, &l2, &and, &or, &nand, &nor, &xor, &xnor] {
                                assert_eq!(&l.cofactors(v).0, l);
                                assert_eq!(&l.cofactors(v).1, l);
                            }
                        }
                    }
                }
            }
        }
    }
}
