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
use crate::canonization::n_canonization;
use crate::canonization::npn_canonization;
use crate::canonization::p_canonization;
use crate::decomposition::*;
use crate::operations::*;
use crate::Lut;

/// Fixed-size truth table
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct StaticLut<const N: usize, const T: usize> {
    table: [u64; T],
}

impl<const N: usize, const T: usize> Default for StaticLut<N, T> {
    fn default() -> Self {
        Self { table: [0u64; T] }
    }
}

impl<const N: usize, const T: usize> StaticLut<N, T> {
    /// Query the number of variables of the Lut
    pub fn num_vars(&self) -> usize {
        N
    }

    /// Query the number of bits in the Lut
    pub fn num_bits(&self) -> usize {
        1 << N
    }

    /// Query the number of 64-bit blocks in the Lut
    pub fn num_blocks(&self) -> usize {
        table_size(N)
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
    pub fn one() -> Self {
        let mut ret = Self::default();
        fill_one(N, ret.table.as_mut());
        ret
    }

    /// Create a constant false Lut
    pub fn zero() -> Self {
        Self::default()
    }

    /// Create a Lut returning the value of one of its variables
    pub fn nth_var(var: usize) -> Self {
        assert!(var < N);
        let mut ret = Self::default();
        fill_nth_var(N, ret.table.as_mut(), var);
        ret
    }

    /// Create a Lut returning true if the number of true variables is even
    pub fn parity() -> Self {
        let mut ret = Self::default();
        fill_parity(N, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if the majority of the variables are true
    pub fn majority() -> Self {
        let mut ret = Self::default();
        fill_majority(N, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if at least k variables are true
    pub fn threshold(k: usize) -> Self {
        let mut ret = Self::default();
        fill_threshold(N, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut returning true if exactly k variables are true
    pub fn equals(k: usize) -> Self {
        let mut ret = Self::default();
        fill_equals(N, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut representing a symmetric function. Bit at position k gives the value when k variables are true
    pub fn symmetric(count_values: usize) -> Self {
        let mut ret = Self::default();
        fill_symmetric(N, ret.table.as_mut(), count_values);
        ret
    }

    /// Create a random Lut
    #[cfg(feature = "rand")]
    pub fn random() -> Self {
        let mut ret = Self::default();
        fill_random(N, ret.table.as_mut());
        ret
    }

    /// Get the value of the Lut for these inputs (input bits packed in the mask)
    pub fn get_bit(&self, mask: usize) -> bool {
        self.check_bit(mask);
        get_bit(N, self.table.as_ref(), mask)
    }

    /// Set the value of the Lut for these inputs to true (input bits packed in the mask)
    pub fn set_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        set_bit(N, self.table.as_mut(), mask);
    }

    /// Set the value of the Lut for these inputs to false (input bits packed in the mask)
    pub fn unset_bit(&mut self, mask: usize) {
        self.check_bit(mask);
        unset_bit(N, self.table.as_mut(), mask);
    }

    /// Complement the Lut in place: f(x) --> !f(x)
    pub fn not_inplace(&mut self) {
        not_inplace(N, self.table.as_mut());
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
        flip_inplace(N, self.table.as_mut(), ind);
    }

    /// Swap two variables in place: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap_inplace(&mut self, ind1: usize, ind2: usize) {
        self.check_var(ind1);
        self.check_var(ind2);
        swap_inplace(N, self.table.as_mut(), ind1, ind2);
    }

    /// Swap two adjacent variables in place: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent_inplace(&mut self, ind: usize) {
        self.check_var(ind);
        self.check_var(ind + 1);
        swap_adjacent_inplace(N, self.table.as_mut(), ind);
    }

    /// Complement the Lut: f(x) --> !f(x)
    pub fn not(&self) -> StaticLut<N, T> {
        let mut l = *self;
        l.not_inplace();
        l
    }

    /// And two Luts
    pub fn and(&self, rhs: &Self) -> Self {
        let mut l = *self;
        l.and_inplace(rhs);
        l
    }

    /// Or two Luts
    pub fn or(&self, rhs: &Self) -> Self {
        let mut l = *self;
        l.or_inplace(rhs);
        l
    }

    /// Xor two Luts
    pub fn xor(&self, rhs: &Self) -> Self {
        let mut l = *self;
        l.xor_inplace(rhs);
        l
    }

    /// Flip a variable: f(x1, ... xi, ... xn) --> f(x1, ... !xi, ... xn)
    pub fn flip(&self, ind: usize) -> Self {
        let mut l = *self;
        l.flip_inplace(ind);
        l
    }

    /// Swap two variables: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap(&self, ind1: usize, ind2: usize) -> Self {
        let mut l = *self;
        l.swap_inplace(ind1, ind2);
        l
    }

    /// Swap two adjacent variables: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent(&mut self, ind: usize) -> Self {
        let mut l = *self;
        l.swap_adjacent_inplace(ind);
        l
    }

    /// Obtain the two cofactors with respect to a variable
    pub fn cofactors(&self, ind: usize) -> (Self, Self) {
        let mut c = (*self, *self);
        cofactor0_inplace(self.num_vars(), c.0.table.as_mut(), ind);
        cofactor1_inplace(self.num_vars(), c.1.table.as_mut(), ind);
        c
    }

    /// Create a Lut from its two cofactors
    pub fn from_cofactors(c0: &Self, c1: &Self, ind: usize) -> Self {
        let mut ret = Self::zero();
        from_cofactors_inplace(
            N,
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
    pub fn from_blocks(blocks: &[u64]) -> Self {
        let mut ret = Self::default();
        ret.table.clone_from_slice(blocks);
        ret
    }

    /// Find the smallest equivalent Lut up to permutation.
    /// Return the canonical representation and the input permutation to obtain it.
    pub fn p_canonization(&self) -> (Self, [u8; N]) {
        let mut work = *self;
        let mut ret = *self;
        let mut perm = [0; N];
        p_canonization(N, work.table.as_mut(), ret.table.as_mut(), perm.as_mut());
        (ret, perm)
    }

    /// Find the smallest equivalent Lut up to input flips and output flip.
    /// Return the canonical representation and the flips to obtain it.
    pub fn n_canonization(&self) -> (Self, u32) {
        let mut work = *self;
        let mut ret = *self;
        let flip = n_canonization(N, work.table.as_mut(), ret.table.as_mut());
        (ret, flip)
    }

    /// Find the smallest equivalent Lut up to permutation, input flips and output flip.
    /// Return the canonical representation and the permutation and flips to obtain it.
    pub fn npn_canonization(&self) -> (Self, [u8; N], u32) {
        let mut work = *self;
        let mut ret = *self;
        let mut perm = [0; N];
        let flip = npn_canonization(N, work.table.as_mut(), ret.table.as_mut(), perm.as_mut());
        (ret, perm, flip)
    }

    /// Decomposition of the function with respect to this variable
    pub fn decomposition(&self, ind: usize) -> DecompositionType {
        decomposition(N, self.table.as_ref(), ind)
    }

    /// Returns whether the function is positive unate
    pub fn is_pos_unate(&self, ind: usize) -> bool {
        input_pos_unate(N, self.table.as_ref(), ind)
    }

    /// Returns whether the function is negative unate
    pub fn is_neg_unate(&self, ind: usize) -> bool {
        input_neg_unate(N, self.table.as_ref(), ind)
    }

    /// Collection of all Luts of this size
    pub fn all_functions() -> StaticLutIterator<N, T> {
        StaticLutIterator {
            lut: StaticLut::zero(),
            ok: true,
        }
    }

    /// Compute the complexity of the BDD associated with multiple functions
    pub fn bdd_complexity(luts: &[Self]) -> usize {
        let mut table = Vec::<u64>::new();
        for l in luts {
            table.extend(l.blocks().iter());
        }
        table_complexity(N, table.as_slice())
    }
}

#[doc(hidden)]
pub struct StaticLutIterator<const N: usize, const T: usize> {
    lut: StaticLut<N, T>,
    ok: bool,
}

impl<const N: usize, const T: usize> Iterator for StaticLutIterator<N, T> {
    type Item = StaticLut<N, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.ok {
            None
        } else {
            let ret = self.lut;
            self.ok = next_inplace(N, self.lut.table.as_mut());
            Some(ret)
        }
    }
}

impl<const N: usize, const T: usize> Ord for StaticLut<N, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        return cmp(self.table.as_ref(), other.table.as_ref());
    }
}

impl<const N: usize, const T: usize> PartialOrd for StaticLut<N, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize, const T: usize> Not for StaticLut<N, T> {
    type Output = Self;
    fn not(self) -> Self::Output {
        let mut l = self;
        l.not_inplace();
        l
    }
}

impl<const N: usize, const T: usize> Not for &'_ StaticLut<N, T> {
    type Output = StaticLut<N, T>;
    fn not(self) -> Self::Output {
        let mut l = *self;
        l.not_inplace();
        l
    }
}

impl<const N: usize, const T: usize> BitAndAssign for StaticLut<N, T> {
    fn bitand_assign(&mut self, rhs: Self) {
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a, const N: usize, const T: usize> BitAndAssign<&'a StaticLut<N, T>> for StaticLut<N, T> {
    fn bitand_assign(&mut self, rhs: &'a Self) {
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const N: usize, const T: usize> BitAnd for StaticLut<N, T> {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl<'a, const N: usize, const T: usize> BitAnd<&'a StaticLut<N, T>> for StaticLut<N, T> {
    type Output = Self;
    fn bitand(self, rhs: &'a StaticLut<N, T>) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl<const N: usize, const T: usize> BitOrAssign for StaticLut<N, T> {
    fn bitor_assign(&mut self, rhs: Self) {
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a, const N: usize, const T: usize> BitOrAssign<&'a StaticLut<N, T>> for StaticLut<N, T> {
    fn bitor_assign(&mut self, rhs: &'a Self) {
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const N: usize, const T: usize> BitOr for StaticLut<N, T> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl<'a, const N: usize, const T: usize> BitOr<&'a StaticLut<N, T>> for StaticLut<N, T> {
    type Output = Self;
    fn bitor(self, rhs: &'a StaticLut<N, T>) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl<const N: usize, const T: usize> BitXorAssign for StaticLut<N, T> {
    fn bitxor_assign(&mut self, rhs: Self) {
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<'a, const N: usize, const T: usize> BitXorAssign<&'a StaticLut<N, T>> for StaticLut<N, T> {
    fn bitxor_assign(&mut self, rhs: &'a Self) {
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const N: usize, const T: usize> BitXor for StaticLut<N, T> {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl<'a, const N: usize, const T: usize> BitXor<&'a StaticLut<N, T>> for StaticLut<N, T> {
    type Output = Self;
    fn bitxor(self, rhs: &'a StaticLut<N, T>) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl<const N: usize, const T: usize> fmt::Display for StaticLut<N, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(N, self.table.as_ref(), f)
    }
}

impl<const N: usize, const T: usize> fmt::LowerHex for StaticLut<N, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(N, self.table.as_ref(), f)
    }
}

impl<const N: usize, const T: usize> fmt::Binary for StaticLut<N, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bin(N, self.table.as_ref(), f)
    }
}

impl<const N: usize, const T: usize> TryFrom<Lut> for StaticLut<N, T> {
    type Error = ();

    fn try_from(lut: Lut) -> Result<Self, Self::Error> {
        if lut.num_vars() != N {
            return Err(());
        }
        Ok(StaticLut::<N, T>::from_blocks(lut.blocks()))
    }
}

impl<const N: usize, const T: usize> From<StaticLut<N, T>> for Lut {
    fn from(lut: StaticLut<N, T>) -> Lut {
        Lut::from_blocks(lut.num_vars(), lut.blocks())
    }
}

/// 0-input Lut
pub type Lut0 = StaticLut<0, 1>;
/// 1-input Lut
pub type Lut1 = StaticLut<1, 1>;
/// 2-input Lut
pub type Lut2 = StaticLut<2, 1>;
/// 3-input Lut
pub type Lut3 = StaticLut<3, 1>;
/// 4-input Lut
pub type Lut4 = StaticLut<4, 1>;
/// 5-input Lut
pub type Lut5 = StaticLut<5, 1>;
/// 6-input Lut
pub type Lut6 = StaticLut<6, 1>;
/// 7-input Lut
pub type Lut7 = StaticLut<7, 2>;
/// 8-input Lut
pub type Lut8 = StaticLut<8, 4>;
/// 9-input Lut
pub type Lut9 = StaticLut<9, 8>;
/// 10-input Lut
pub type Lut10 = StaticLut<10, 16>;
/// 11-input Lut
pub type Lut11 = StaticLut<11, 32>;
/// 12-input Lut
pub type Lut12 = StaticLut<12, 64>;

#[cfg(test)]
mod tests {
    use crate::{Lut0, Lut1, Lut2, Lut3, Lut4, Lut5, Lut6, Lut7};

    #[test]
    fn test_symmetric() {
        assert_eq!(Lut3::majority().to_string(), "Lut3(e8)");
        assert_eq!(Lut4::majority().to_string(), "Lut4(fee8)");
        assert_eq!(Lut3::equals(0).to_string(), "Lut3(01)");
        assert_eq!(Lut4::equals(0).to_string(), "Lut4(0001)");
        assert_eq!(Lut3::equals(1).to_string(), "Lut3(16)");
        assert_eq!(Lut4::equals(1).to_string(), "Lut4(0116)");
        assert_eq!(Lut3::parity().to_string(), "Lut3(96)");
        assert_eq!(Lut4::parity().to_string(), "Lut4(6996)");
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{:}", Lut0::zero()), "Lut0(0)");
        assert_eq!(format!("{:}", Lut0::one()), "Lut0(1)");
        assert_eq!(format!("{:}", Lut1::zero()), "Lut1(0)");
        assert_eq!(format!("{:}", Lut1::one()), "Lut1(3)");
        assert_eq!(format!("{:}", Lut2::zero()), "Lut2(0)");
        assert_eq!(format!("{:}", Lut2::one()), "Lut2(f)");
        assert_eq!(format!("{:}", Lut3::zero()), "Lut3(00)");
        assert_eq!(format!("{:}", Lut3::one()), "Lut3(ff)");
        assert_eq!(format!("{:}", Lut4::zero()), "Lut4(0000)");
        assert_eq!(format!("{:}", Lut4::one()), "Lut4(ffff)");
        assert_eq!(format!("{:}", Lut5::zero()), "Lut5(00000000)");
        assert_eq!(format!("{:}", Lut5::one()), "Lut5(ffffffff)");
        assert_eq!(format!("{:}", Lut6::zero()), "Lut6(0000000000000000)");
        assert_eq!(format!("{:}", Lut6::one()), "Lut6(ffffffffffffffff)");
        assert_eq!(
            format!("{:}", Lut7::zero()),
            "Lut7(00000000000000000000000000000000)"
        );
        assert_eq!(
            format!("{:}", Lut7::one()),
            "Lut7(ffffffffffffffffffffffffffffffff)"
        );
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_random() {
        Lut0::random();
        Lut1::random();
        Lut2::random();
        Lut3::random();
        Lut4::random();
        Lut5::random();
        Lut6::random();
        Lut7::random();
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_conversion() {
        use crate::{Lut, Lut7};
        for _ in 0..10 {
            let lut = Lut3::random();
            assert_eq!(lut, Lut3::try_from(Lut::from(lut)).unwrap());
        }
        for _ in 0..10 {
            let lut = Lut7::random();
            assert_eq!(lut, Lut7::try_from(Lut::from(lut)).unwrap());
        }
    }
}
