use core::fmt;
use std::cmp::Ordering;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Not;

use crate::bdd::*;
use crate::canonization::*;
use crate::decomposition::*;
use crate::operations::*;

/// Arbitrary-size truth table, representing a N-input boolean function with 2^N bits, one for each input combination
#[derive(Clone, Hash, PartialEq, Eq)]
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
        1 << self.num_vars()
    }

    /// Query the number of 64-bit blocks in the Lut
    pub fn num_blocks(&self) -> usize {
        table_size(self.num_vars())
    }

    /// Create a new Lut
    fn new(num_vars: usize) -> Self {
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
    pub fn one(num_vars: usize) -> Self {
        Self {
            num_vars,
            table: vec![num_vars_mask(num_vars); table_size(num_vars)].into_boxed_slice(),
        }
    }

    /// Create a constant false Lut
    pub fn zero(num_vars: usize) -> Self {
        Self {
            num_vars,
            table: vec![0; table_size(num_vars)].into_boxed_slice(),
        }
    }

    /// Create a Lut returning the value of one of its variables
    pub fn nth_var(num_vars: usize, var: usize) -> Self {
        assert!(var < num_vars);
        let mut ret = Lut::new(num_vars);
        fill_nth_var(num_vars, ret.table.as_mut(), var);
        ret
    }

    /// Create a Lut returning true if the number of true variables is even
    pub fn parity(num_vars: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_parity(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if the majority of the variables are true
    pub fn majority(num_vars: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_majority(num_vars, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if at least k variables are true
    pub fn threshold(num_vars: usize, k: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_threshold(num_vars, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut returning true if exactly k variables are true
    pub fn equals(num_vars: usize, k: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_equals(num_vars, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut representing a symmetric function. Bit at position k gives the value when k variables are true
    pub fn symmetric(num_vars: usize, count_values: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_symmetric(num_vars, ret.table.as_mut(), count_values);
        ret
    }

    /// Create a random Lut
    #[cfg(feature = "rand")]
    pub fn random(num_vars: usize) -> Self {
        let mut ret = Lut::new(num_vars);
        fill_random(num_vars, ret.table.as_mut());
        ret
    }

    /// Get the value of the Lut for these inputs (input bits packed in the mask)
    pub fn value(&self, mask: usize) -> bool {
        self.get_bit(mask)
    }

    /// Get the value of the Lut for these inputs (input bits packed in the mask)
    pub fn get_bit(&self, mask: usize) -> bool {
        self.check_bit(mask);
        get_bit(self.num_vars(), self.table.as_ref(), mask)
    }

    /// Set the value of the Lut for these inputs (input bits packed in the mask)
    pub fn set_value(&mut self, mask: usize, value: bool) {
        if value {
            self.set_bit(mask)
        } else {
            self.unset_bit(mask)
        }
    }

    /// Set the value of the Lut for these inputs to true (input bits packed in the mask)
    pub fn set_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        set_bit(self.num_vars(), self.table.as_mut(), mask);
    }

    /// Set the value of the Lut for these inputs to false (input bits packed in the mask)
    pub fn unset_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        unset_bit(self.num_vars(), self.table.as_mut(), mask);
    }

    /// Count the number of one bits in the Lut
    pub fn count_ones(&self) -> usize {
        count_ones(self.num_vars(), self.table.as_ref())
    }

    /// Count the number of zero bits in the Lut
    pub fn count_zeros(&self) -> usize {
        count_zeros(self.num_vars(), self.table.as_ref())
    }

    /// Complement the Lut in place: f(x) --> !f(x)
    pub fn not_inplace(&mut self) {
        not_inplace(self.num_vars(), self.table.as_mut());
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
        flip_inplace(self.num_vars(), self.table.as_mut(), ind);
    }

    /// Flip multiple variables in a mask, as generated by canonization methods
    ///
    /// Bit `i` determines if variable `i` should be flipped, bit `num_var` if the output should be flipped
    pub fn flip_n_inplace(&mut self, mask: u32) {
        flip_n_inplace(self.num_vars(), self.table.as_mut(), mask);
    }

    /// Swap two variables in place: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap_inplace(&mut self, ind1: usize, ind2: usize) {
        self.check_var(ind1);
        self.check_var(ind2);
        swap_inplace(self.num_vars(), self.table.as_mut(), ind1, ind2);
    }

    /// Permute the variables: f(x1, ..., xi, ..., xn) --> f(xp\[1\], ..., xp\[i\], ..., xp\[n\])
    pub fn permute_inplace(&mut self, perm: &[u8]) {
        assert_eq!(self.num_vars(), perm.len());
        permute_inplace(self.num_vars(), self.table.as_mut(), perm);
    }

    /// Swap two adjacent variables in place: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent_inplace(&mut self, ind: usize) {
        self.check_var(ind);
        self.check_var(ind + 1);
        swap_adjacent_inplace(self.num_vars(), self.table.as_mut(), ind);
    }

    /// Complement the Lut: f(x) --> !f(x)
    pub fn not(&self) -> Self {
        let mut l = self.clone();
        l.not_inplace();
        l
    }

    /// And two Luts
    pub fn and(&self, rhs: &Lut) -> Self {
        let mut l = self.clone();
        l.and_inplace(rhs);
        l
    }

    /// Or two Luts
    pub fn or(&self, rhs: &Lut) -> Self {
        let mut l = self.clone();
        l.or_inplace(rhs);
        l
    }

    /// Xor two Luts
    pub fn xor(&self, rhs: &Lut) -> Self {
        let mut l = self.clone();
        l.xor_inplace(rhs);
        l
    }

    /// Flip a variable: f(x1, ... xi, ... xn) --> f(x1, ... !xi, ... xn)
    pub fn flip(&self, ind: usize) -> Self {
        let mut l = self.clone();
        l.flip_inplace(ind);
        l
    }

    /// Flip multiple variables in a mask, as generated by canonization methods
    ///
    /// Bit `i` determines if variable `i` should be flipped, bit `num_var` if the output should be flipped
    pub fn flip_n(&self, mask: u32) -> Self {
        let mut l = self.clone();
        l.flip_n_inplace(mask);
        l
    }

    /// Swap two variables: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap(&self, ind1: usize, ind2: usize) -> Self {
        let mut l = self.clone();
        l.swap_inplace(ind1, ind2);
        l
    }

    /// Permute the variables: f(x1, ..., xi, ..., xn) --> f(xp\[1\], ..., xp\[i\], ..., xp\[n\])
    pub fn permute(&self, perm: &[u8]) -> Self {
        let mut l = self.clone();
        l.permute_inplace(perm);
        l
    }

    /// Swap two adjacent variables: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent(&self, ind: usize) -> Self {
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
            c0.num_vars(),
            ret.table.as_mut(),
            c0.table.as_ref(),
            c1.table.as_ref(),
            ind,
        );
        ret
    }

    /// Return the internal representation as 64-bit blocks
    pub fn blocks(&self) -> &[u64] {
        self.table.as_ref()
    }

    /// Create a Lut from its internal representation as 64-bit blocks
    pub fn from_blocks(num_vars: usize, blocks: &[u64]) -> Self {
        let mut ret = Self::zero(num_vars);
        assert!(blocks.len() == ret.num_blocks());
        ret.table.clone_from_slice(blocks);
        ret
    }

    /// Find the smallest equivalent Lut up to permutation.
    /// Return the canonical representation and the input permutation to obtain it.
    pub fn p_canonization(&self) -> (Self, Vec<u8>) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let mut perm = vec![0; self.num_vars];
        p_canonization(
            self.num_vars(),
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm)
    }

    /// Returns whether the Lut is already p-canonical
    pub fn is_p_canonical(&self) -> bool {
        let mut work = self.clone();
        is_p_canonical(self.num_vars(), &self.table, work.table.as_mut())
    }

    /// Find the smallest equivalent Lut up to input flips and output flip.
    /// Return the canonical representation and the flips to obtain it.
    pub fn n_canonization(&self) -> (Self, u32) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let flip = n_canonization(self.num_vars(), work.table.as_mut(), ret.table.as_mut());
        (ret, flip)
    }

    /// Returns whether the Lut is already n-canonical
    pub fn is_n_canonical(&self) -> bool {
        let mut work = self.clone();
        is_n_canonical(self.num_vars(), &self.table, work.table.as_mut())
    }

    /// Find the smallest equivalent Lut up to permutation, input flips and output flip.
    /// Return the canonical representation and the permutation and flips to obtain it.
    pub fn npn_canonization(&self) -> (Self, Vec<u8>, u32) {
        let mut work = self.clone();
        let mut ret = self.clone();
        let mut perm = vec![0; self.num_vars()];
        let flip = npn_canonization(
            self.num_vars(),
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm, flip)
    }

    /// Returns whether the Lut is already npn-canonical
    pub fn is_npn_canonical(&self) -> bool {
        let mut work = self.clone();
        is_npn_canonical(self.num_vars(), &self.table, work.table.as_mut())
    }

    /// Top decomposition of the function with respect to this variable
    pub fn top_decomposition(&self, ind: usize) -> DecompositionType {
        top_decomposition(self.num_vars(), self.table.as_ref(), ind)
    }

    /// Returns whether the function is positive unate
    pub fn is_pos_unate(&self, ind: usize) -> bool {
        input_pos_unate(self.num_vars(), self.table.as_ref(), ind)
    }

    /// Returns whether the function is negative unate
    pub fn is_neg_unate(&self, ind: usize) -> bool {
        input_neg_unate(self.num_vars(), self.table.as_ref(), ind)
    }

    /// Collection of all Luts of a given size
    pub fn all_functions(num_vars: usize) -> LutIterator {
        LutIterator {
            lut: Lut::zero(num_vars),
            ok: true,
        }
    }

    /// Compute the number of nodes in the BDD representing these functions
    ///
    /// Equivalent functions (up to output complementation) are represented by a single BDD node.
    /// The natural variable order (0 to num_vars) is used: smaller BDDs may be possible with another ordering.
    pub fn bdd_complexity(luts: &[Self]) -> usize {
        if luts.is_empty() {
            return 0;
        }
        let num_vars = luts[0].num_vars();
        for lut in luts {
            assert_eq!(lut.num_vars(), num_vars);
        }

        let mut table = Vec::<u64>::new();
        for l in luts {
            table.extend(l.blocks().iter());
        }
        table_bdd_complexity(num_vars, table.as_slice())
    }

    /// Return the hexadecimal string representing the function
    ///
    /// Contrary to display, nothing else is printed: `a45b` instead of `Lut4(a45b)`
    pub fn to_hex_string(&self) -> String {
        to_hex(self.num_vars(), self.table.as_ref())
    }

    /// Return the binary string representing the function
    ///
    /// Contrary to display, nothing else is printed: `0101` instead of `Lut2(0101)`
    pub fn to_bin_string(&self) -> String {
        to_bin(self.num_vars(), self.table.as_ref())
    }

    /// Build a Lut from an hexadecimal string
    pub fn from_hex_string(num_vars: usize, s: &str) -> Result<Self, ParseLutError> {
        let mut ret = Lut::zero(num_vars);
        fill_hex(ret.num_vars(), ret.table.as_mut(), s)?;
        Ok(ret)
    }

    /// Build a Lut from a binary string
    pub fn from_bin_string(num_vars: usize, s: &str) -> Result<Self, ParseLutError> {
        let mut ret = Lut::zero(num_vars);
        fill_bin(ret.num_vars(), ret.table.as_mut(), s)?;
        Ok(ret)
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
        cmp(self.table.as_ref(), other.table.as_ref())
    }
}

impl PartialOrd for Lut {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Not for &Lut {
    type Output = Lut;
    fn not(self) -> Self::Output {
        let mut l = self.clone();
        l.not_inplace();
        l
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

impl BitAndAssign<&Lut> for Lut {
    fn bitand_assign(&mut self, rhs: &Lut) {
        assert!(self.num_vars == rhs.num_vars);
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitAndAssign<Lut> for Lut {
    fn bitand_assign(&mut self, rhs: Lut) {
        *self &= &rhs;
    }
}

impl BitAnd<Lut> for Lut {
    type Output = Lut;
    fn bitand(self, rhs: Lut) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl BitAnd<Lut> for &Lut {
    type Output = Lut;
    fn bitand(self, rhs: Lut) -> Self::Output {
        let mut l = self.clone();
        l &= rhs;
        l
    }
}

impl BitAnd<&Lut> for &Lut {
    type Output = Lut;
    fn bitand(self, rhs: &Lut) -> Self::Output {
        let mut l = self.clone();
        l &= rhs;
        l
    }
}

impl BitAnd<&Lut> for Lut {
    type Output = Lut;
    fn bitand(self, rhs: &Lut) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl BitOrAssign<&Lut> for Lut {
    fn bitor_assign(&mut self, rhs: &Lut) {
        assert!(self.num_vars == rhs.num_vars);
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitOrAssign<Lut> for Lut {
    fn bitor_assign(&mut self, rhs: Lut) {
        *self |= &rhs;
    }
}

impl BitOr<Lut> for Lut {
    type Output = Lut;
    fn bitor(self, rhs: Lut) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl BitOr<Lut> for &Lut {
    type Output = Lut;
    fn bitor(self, rhs: Lut) -> Self::Output {
        let mut l = self.clone();
        l |= rhs;
        l
    }
}

impl BitOr<&Lut> for &Lut {
    type Output = Lut;
    fn bitor(self, rhs: &Lut) -> Self::Output {
        let mut l = self.clone();
        l |= rhs;
        l
    }
}

impl BitOr<&Lut> for Lut {
    type Output = Lut;
    fn bitor(self, rhs: &Lut) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl BitXorAssign<&Lut> for Lut {
    fn bitxor_assign(&mut self, rhs: &Lut) {
        assert!(self.num_vars == rhs.num_vars);
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl BitXorAssign<Lut> for Lut {
    fn bitxor_assign(&mut self, rhs: Lut) {
        *self ^= &rhs;
    }
}

impl BitXor<Lut> for Lut {
    type Output = Lut;
    fn bitxor(self, rhs: Lut) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl BitXor<Lut> for &Lut {
    type Output = Lut;
    fn bitxor(self, rhs: Lut) -> Self::Output {
        let mut l = self.clone();
        l ^= rhs;
        l
    }
}

impl BitXor<&Lut> for &Lut {
    type Output = Lut;
    fn bitxor(self, rhs: &Lut) -> Self::Output {
        let mut l = self.clone();
        l ^= rhs;
        l
    }
}

impl BitXor<&Lut> for Lut {
    type Output = Lut;
    fn bitxor(self, rhs: &Lut) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl fmt::Display for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(self.num_vars(), self.table.as_ref(), f)
    }
}

impl fmt::Debug for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(self.num_vars(), self.table.as_ref(), f)
    }
}

impl fmt::LowerHex for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(self.num_vars(), self.table.as_ref(), f)
    }
}

impl fmt::Binary for Lut {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bin(self.num_vars(), self.table.as_ref(), f)
    }
}

#[cfg(test)]
mod tests {

    use crate::{decomposition::DecompositionType, Lut};

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
    #[allow(unused_must_use, clippy::no_effect, clippy::unnecessary_operation)]
    fn test_ops() {
        let mut a = Lut::nth_var(6, 0);
        let b = Lut::nth_var(6, 1);
        !a.clone();
        !&a;
        &a & &b;
        &a & b.clone();
        a.clone() & &b;
        a.clone() & b.clone();
        &a | &b;
        &a | b.clone();
        a.clone() | &b;
        a.clone() | b.clone();
        &a ^ &b;
        &a ^ b.clone();
        a.clone() ^ &b;
        a.clone() ^ b.clone();
        a &= b.clone();
        a &= &b;
        a |= b.clone();
        a |= &b;
        a ^= b.clone();
        a ^= &b;
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
    #[cfg(feature = "rand")]
    /// Test that the permutation function works using random swaps
    fn test_permute() {
        use rand::Rng;
        let mut rng = rand::rng();
        for lut_size in 1..10 {
            let lut = Lut::random(lut_size);
            let mut permuted = lut.clone();
            let mut perm = (0..lut_size as u8).collect::<Vec<u8>>();
            for _ in 0..10 {
                let i = rng.random_range(0..lut_size);
                let j = rng.random_range(0..lut_size);
                perm.swap(i, j);
                permuted.swap_inplace(i, j);
            }
            assert_eq!(lut.permute(&perm), permuted);
        }
    }

    #[test]
    fn test_not() {
        for lut_size in 1..10 {
            assert_eq!(Lut::zero(lut_size), !Lut::one(lut_size));
            assert_eq!(!Lut::zero(lut_size), Lut::one(lut_size));
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

    #[cfg(feature = "rand")]
    fn gen_random(max_size: usize) -> Vec<Lut> {
        let mut ret = Vec::new();
        for lut_size in 1..=max_size {
            ret.push(Lut::zero(lut_size));
            ret.push(Lut::one(lut_size));
            for i in 0..lut_size {
                ret.push(Lut::nth_var(lut_size, i));
            }
            for _ in 0..10 {
                ret.push(Lut::random(lut_size));
            }
        }
        ret
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_flip_n() {
        for lut in gen_random(8) {
            assert_eq!(!&lut, lut.flip_n(1 << lut.num_vars()));
            for i in 0..lut.num_vars() {
                assert_eq!(lut.flip(i), lut.flip_n(1 << i));
            }
        }
    }

    #[test]
    fn test_count() {
        for lut_size in 1..10 {
            // All luts that copy a single variable
            for i in 0..lut_size {
                let l = Lut::nth_var(lut_size, i);
                assert_eq!(l.count_ones(), l.num_bits() >> 1);
                assert_eq!(l.count_zeros(), l.num_bits() >> 1);
            }
            assert_eq!(Lut::zero(lut_size).count_ones(), 0);
            assert_eq!(Lut::zero(lut_size).count_zeros(), 1 << lut_size);
            assert_eq!(Lut::one(lut_size).count_ones(), 1 << lut_size);
            assert_eq!(Lut::one(lut_size).count_zeros(), 0);

            // Check potentially one MSBs
            assert_eq!((!Lut::zero(lut_size)).count_ones(), 1 << lut_size);
            assert_eq!((!Lut::zero(lut_size)).count_zeros(), 0);
            assert_eq!((!Lut::one(lut_size)).count_ones(), 0);
            assert_eq!((!Lut::one(lut_size)).count_zeros(), 1 << lut_size);
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
    fn test_lut_count() {
        for i in 0..=4 {
            assert_eq!(Lut::all_functions(i).count(), 1 << (1 << i));
        }
    }

    #[test]
    fn test_npn_canonization_classes() {
        // TODO: canonization is incorrect for 0 or 1 input
        let expected: [usize; 7] = [1, 2, 4, 14, 222, 616126, 200253952527184];
        for i in 2..=4 {
            // We only test a few by default, but this was checked up to 5
            assert_eq!(
                Lut::all_functions(i)
                    .filter(|x| x.is_npn_canonical())
                    .count(),
                expected[i]
            );
        }
    }

    #[test]
    fn test_n_canonization_classes() {
        // TODO: canonization is incorrect for 0 or 1 input
        let expected: [usize; 6] = [1, 2, 5, 30, 2288, 67172352];
        for i in 2..=4 {
            // We only test a few by default, but this was checked up to 5
            assert_eq!(
                Lut::all_functions(i).filter(|x| x.is_n_canonical()).count(),
                expected[i]
            );
        }
    }

    #[test]
    fn test_p_canonization_classes() {
        let expected: [usize; 6] = [2, 4, 12, 80, 3984, 37333248];
        for i in 0..=4 {
            // We only test a few by default, but this was checked up to 5
            assert_eq!(
                Lut::all_functions(i).filter(|x| x.is_p_canonical()).count(),
                expected[i]
            );
        }
    }

    #[test]
    fn test_n_canonization_full() {
        for i in 0..=3 {
            for lut in Lut::all_functions(i) {
                let (canon, flip) = lut.n_canonization();
                assert!(canon.is_n_canonical());
                assert_eq!(canon.flip_n(flip), lut);
                assert_eq!(lut.flip_n(flip), canon);
                assert_eq!(canon == lut, lut.is_n_canonical());
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_n_canonization() {
        for lut in gen_random(8) {
            let (canon, flip) = lut.n_canonization();
            assert_eq!(canon.flip_n(flip), lut);
            assert_eq!(lut.flip_n(flip), canon);
            assert_eq!(canon == lut, lut.is_n_canonical());
        }
    }

    #[test]
    fn test_p_canonization_full() {
        for i in 0..=3 {
            for lut in Lut::all_functions(i) {
                let (canon, perm) = lut.p_canonization();
                assert_eq!(lut.permute(&perm), canon);
                assert_eq!(canon == lut, lut.is_p_canonical());
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_p_canonization() {
        for lut in gen_random(7) {
            let (canon, perm) = lut.p_canonization();
            assert_eq!(lut.permute(&perm), canon);
            assert_eq!(canon == lut, lut.is_p_canonical());
        }
    }

    #[test]
    fn test_npn_canonization_full() {
        for i in 0..=3 {
            for lut in Lut::all_functions(i) {
                let (canon, perm, flip) = lut.npn_canonization();
                assert_eq!(lut.permute(&perm).flip_n(flip), canon);
                assert_eq!(canon == lut, lut.is_npn_canonical());
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_npn_canonization() {
        for lut in gen_random(5) {
            let (canon, perm, flip) = lut.npn_canonization();
            assert_eq!(lut.permute(&perm).flip_n(flip), canon);
            assert_eq!(canon == lut, lut.is_npn_canonical());
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
                            assert_eq!(and.top_decomposition(v), DecompositionType::And);
                            assert_eq!(or.top_decomposition(v), DecompositionType::Or);
                            assert_eq!(nand.top_decomposition(v), DecompositionType::Le);
                            assert_eq!(nor.top_decomposition(v), DecompositionType::Lt);
                            assert_eq!(xor.top_decomposition(v), DecompositionType::Xor);
                            assert_eq!(xnor.top_decomposition(v), DecompositionType::Xor);
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
                                assert_eq!(l.top_decomposition(v), DecompositionType::Independent);
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
    fn test_mux_decomposition() {
        for i in 3..=8 {
            for a in 0..i {
                for b in 0..i {
                    for s in 0..i {
                        if (a != b) && (a != s) && (b != s) {
                            let ai = Lut::nth_var(i, a);
                            let bi = Lut::nth_var(i, b);
                            let si = Lut::nth_var(i, s);
                            let mux = Lut::and(&ai, &si) | Lut::and(&bi, &si.not());
                            assert!(mux.top_decomposition(a) == DecompositionType::None);
                            assert!(mux.top_decomposition(b) == DecompositionType::None);
                            assert!(mux.top_decomposition(s) == DecompositionType::None);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_maj_decomposition() {
        for i in 3..=8 {
            for a in 0..i {
                for b in 0..i {
                    for c in 0..i {
                        if (a != b) && (a != c) && (b != c) {
                            let ai = Lut::nth_var(i, a);
                            let bi = Lut::nth_var(i, b);
                            let ci = Lut::nth_var(i, c);
                            let maj = Lut::and(&ai, &ci) | Lut::and(&ai, &bi) | Lut::and(&bi, &ci);
                            assert!(maj.top_decomposition(a) == DecompositionType::None);
                            assert!(maj.top_decomposition(b) == DecompositionType::None);
                            assert!(maj.top_decomposition(c) == DecompositionType::None);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_single_var_decomposition() {
        for i in 1..=8 {
            for v in 0..i {
                let lut = Lut::nth_var(i, v);
                assert_eq!(lut.top_decomposition(v), DecompositionType::Identity);
                assert_eq!(lut.not().top_decomposition(v), DecompositionType::Negation);
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

    #[test]
    #[cfg(feature = "rand")]
    fn test_random() {
        for i in 0..=8 {
            Lut::random(i);
        }
    }

    fn bdd_complexity_check(luts: &[Lut]) -> usize {
        if luts.is_empty() {
            return 0;
        }
        let num_vars = luts[0].num_vars();
        for lut in luts {
            assert_eq!(lut.num_vars(), num_vars);
        }

        let mut level: Vec<Lut> = luts.into();
        let mut count: usize = 0;

        for i in (1..num_vars).rev() {
            // Deduplicate functions that are identical or complement, and remove constants
            level = level
                .iter()
                .map(|c: &Lut| -> Lut {
                    if c.get_bit(0) {
                        !c
                    } else {
                        c.clone()
                    }
                })
                .filter(|c: &Lut| -> bool { *c != Lut::zero(num_vars) })
                .collect();
            level.sort();
            level.dedup();

            // Count the non-trivial functions
            for c in level.iter() {
                if !c.top_decomposition(i).is_trivial() {
                    count += 1;
                }
            }

            // Go to the next level
            let mut next_level = Vec::<Lut>::new();
            for c in level.iter() {
                let (c0, c1) = c.cofactors(i);
                next_level.push(c0);
                next_level.push(c1);
            }
            level = next_level.clone();
        }
        assert_eq!(count, Lut::bdd_complexity(luts));
        count
    }

    #[test]
    fn test_bdd() {
        for num_vars in 0..9 {
            // Check constant Luts
            assert_eq!(bdd_complexity_check(&[Lut::zero(num_vars)]), 0usize);
            assert_eq!(bdd_complexity_check(&[Lut::one(num_vars)]), 0usize);

            // Check trivial Luts
            for i in 0..num_vars {
                assert_eq!(bdd_complexity_check(&[Lut::nth_var(num_vars, i)]), 0usize);
                assert_eq!(bdd_complexity_check(&[!Lut::nth_var(num_vars, i)]), 0usize);
            }
            for i in 0..num_vars {
                for j in i + 1..num_vars {
                    let vi = Lut::nth_var(num_vars, i);
                    let vj = Lut::nth_var(num_vars, j);
                    assert_eq!(bdd_complexity_check(&[vi.clone() & vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[!vi.clone() & vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[vi.clone() & !vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[!vi.clone() & !vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[vi.clone() | vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[!vi.clone() | vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[vi.clone() | !vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[!vi.clone() | !vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[vi.clone() ^ vj.clone()]), 1usize);
                    assert_eq!(bdd_complexity_check(&[!vi.clone() ^ vj.clone()]), 1usize);
                }
            }

            for i in 0..num_vars {
                for j in i + 1..num_vars {
                    for k in j + 1..num_vars {
                        let vi = Lut::nth_var(num_vars, i);
                        let vj = Lut::nth_var(num_vars, j);
                        let vk = Lut::nth_var(num_vars, k);
                        assert_eq!(
                            bdd_complexity_check(&[vi.clone() & vj.clone() & vk.clone()]),
                            2usize
                        );
                        assert_eq!(
                            bdd_complexity_check(&[vi.clone() ^ vj.clone() & vk.clone()]),
                            2usize
                        );
                        assert_eq!(
                            bdd_complexity_check(&[vi.clone() ^ vj.clone() | vk.clone()]),
                            2usize
                        );
                        assert_eq!(
                            bdd_complexity_check(&[vi.clone() & vj.clone() | vk.clone()]),
                            2usize
                        );
                    }
                }
            }

            for i in 0..num_vars {
                for j in i + 1..num_vars {
                    for k in j + 1..num_vars {
                        let vi = Lut::nth_var(num_vars, i);
                        let vj = Lut::nth_var(num_vars, j);
                        let vk = Lut::nth_var(num_vars, k);
                        assert_eq!(
                            bdd_complexity_check(&[
                                (vk.clone() & vj.clone()) | (!vk.clone() & vi.clone())
                            ]),
                            1usize
                        );
                        assert_eq!(
                            bdd_complexity_check(&[
                                (vj.clone() & vk.clone()) | (!vj.clone() & vi.clone())
                            ]),
                            3usize
                        );
                        assert_eq!(
                            bdd_complexity_check(&[
                                (vi.clone() & vk.clone()) | (!vi.clone() & vj.clone())
                            ]),
                            3usize
                        );
                    }
                }
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_string_conversion() {
        for num_vars in 0..8 {
            for _ in 0..10 {
                let lut = Lut::random(num_vars);
                assert_eq!(
                    lut,
                    Lut::from_hex_string(num_vars, &lut.to_hex_string()).unwrap()
                );
                assert_eq!(
                    lut,
                    Lut::from_bin_string(num_vars, &lut.to_bin_string()).unwrap()
                );
            }
        }
    }
}
