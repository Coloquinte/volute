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
use crate::Lut;

/// Fixed-size truth table representing a N-input boolean function with 2^N bits; more compact than [`Lut`](crate::Lut) when the size is known
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct StaticLut<const NUM_VARS: usize, const NUM_WORDS: usize> {
    table: [u64; NUM_WORDS],
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> Default for StaticLut<NUM_VARS, NUM_WORDS> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> StaticLut<NUM_VARS, NUM_WORDS> {
    /// Query the number of variables of the Lut
    pub const fn num_vars(&self) -> usize {
        NUM_VARS
    }

    /// Query the number of bits in the Lut
    pub const fn num_bits(&self) -> usize {
        1 << self.num_vars()
    }

    /// Query the number of 64-bit blocks in the Lut
    pub const fn num_blocks(&self) -> usize {
        table_size(self.num_vars())
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
    pub const fn one() -> Self {
        Self {
            table: [num_vars_mask(NUM_VARS); NUM_WORDS],
        }
    }

    /// Create a constant false Lut
    pub const fn zero() -> Self {
        Self {
            table: [0; NUM_WORDS],
        }
    }

    /// Create a Lut returning the value of one of its variables
    pub fn nth_var(var: usize) -> Self {
        assert!(var < NUM_VARS);
        let mut ret = Self::default();
        fill_nth_var(NUM_VARS, ret.table.as_mut(), var);
        ret
    }

    /// Create a Lut returning true if the number of true variables is even
    pub fn parity() -> Self {
        let mut ret = Self::default();
        fill_parity(NUM_VARS, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if the majority of the variables are true
    pub fn majority() -> Self {
        let mut ret = Self::default();
        fill_majority(NUM_VARS, ret.table.as_mut());
        ret
    }

    /// Create a Lut returning true if at least k variables are true
    pub fn threshold(k: usize) -> Self {
        let mut ret = Self::default();
        fill_threshold(NUM_VARS, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut returning true if exactly k variables are true
    pub fn equals(k: usize) -> Self {
        let mut ret = Self::default();
        fill_equals(NUM_VARS, ret.table.as_mut(), k);
        ret
    }

    /// Create a Lut representing a symmetric function. Bit at position k gives the value when k variables are true
    pub fn symmetric(count_values: usize) -> Self {
        let mut ret = Self::default();
        fill_symmetric(NUM_VARS, ret.table.as_mut(), count_values);
        ret
    }

    /// Create a random Lut
    #[cfg(feature = "rand")]
    pub fn random() -> Self {
        let mut ret = Self::default();
        fill_random(NUM_VARS, ret.table.as_mut());
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

    /// Swap two adjacent variables in place: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent_inplace(&mut self, ind: usize) {
        self.check_var(ind);
        self.check_var(ind + 1);
        swap_adjacent_inplace(self.num_vars(), self.table.as_mut(), ind);
    }

    /// Complement the Lut: f(x) --> !f(x)
    pub fn not(&self) -> Self {
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

    /// Flip multiple variables in a mask, as generated by canonization methods
    ///
    /// Bit `i` determines if variable `i` should be flipped, bit `num_var` if the output should be flipped
    pub fn flip_n(&self, mask: u32) -> Self {
        let mut l = *self;
        l.flip_n_inplace(mask);
        l
    }

    /// Swap two variables: f(..., xi, ..., xj, ...) --> f(..., xj, ..., xi, ...)
    pub fn swap(&self, ind1: usize, ind2: usize) -> Self {
        let mut l = *self;
        l.swap_inplace(ind1, ind2);
        l
    }

    /// Swap two adjacent variables: f(..., xi, x+1, ...) --> f(..., xi+1, xi, ...)
    pub fn swap_adjacent(&self, ind: usize) -> Self {
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
            NUM_VARS,
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
    pub fn p_canonization(&self) -> (Self, [u8; NUM_VARS]) {
        let mut work = *self;
        let mut ret = *self;
        let mut perm = [0; NUM_VARS];
        p_canonization(
            NUM_VARS,
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm)
    }

    /// Find the smallest equivalent Lut up to input flips and output flip.
    /// Return the canonical representation and the flips to obtain it.
    pub fn n_canonization(&self) -> (Self, u32) {
        let mut work = *self;
        let mut ret = *self;
        let flip = n_canonization(self.num_vars(), work.table.as_mut(), ret.table.as_mut());
        (ret, flip)
    }

    /// Find the smallest equivalent Lut up to permutation, input flips and output flip.
    /// Return the canonical representation and the permutation and flips to obtain it.
    pub fn npn_canonization(&self) -> (Self, [u8; NUM_VARS], u32) {
        let mut work = *self;
        let mut ret = *self;
        let mut perm = [0; NUM_VARS];
        let flip = npn_canonization(
            self.num_vars(),
            work.table.as_mut(),
            ret.table.as_mut(),
            perm.as_mut(),
        );
        (ret, perm, flip)
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

    /// Collection of all Luts of this size
    pub fn all_functions() -> StaticLutIterator<NUM_VARS, NUM_WORDS> {
        StaticLutIterator {
            lut: StaticLut::zero(),
            ok: true,
        }
    }

    /// Compute the number of nodes in the BDD representing these functions
    ///
    /// This function uses the natural variable order (0 to num_vars) to build the BDD.
    /// This may not be the smallest possible BDD.
    pub fn bdd_complexity(luts: &[Self]) -> usize {
        let mut table = Vec::<u64>::new();
        for l in luts {
            table.extend(l.blocks().iter());
        }
        table_complexity(NUM_VARS, table.as_slice())
    }

    /// Return the hexadecimal string representing the function
    ///
    /// Contrary to display, nothing else in printed: `a45b` instead of `Lut4(a45b)`
    pub fn to_hex_string(&self) -> String {
        to_hex(self.num_vars(), self.table.as_ref())
    }

    /// Return the binary string representing the function
    ///
    /// Contrary to display, nothing else in printed: `0101` instead of `Lut2(0101)`
    pub fn to_bin_string(&self) -> String {
        to_bin(self.num_vars(), self.table.as_ref())
    }

    /// Build a Lut from an hexadecimal string
    pub fn from_hex_string(s: &str) -> Result<Self, ()> {
        let mut ret = Self::zero();
        fill_hex(ret.num_vars(), ret.table.as_mut(), s)?;
        Ok(ret)
    }

    /// Build a Lut from a binary string
    pub fn from_bin_string(s: &str) -> Result<Self, ()> {
        let mut ret = Self::zero();
        fill_bin(ret.num_vars(), ret.table.as_mut(), s)?;
        Ok(ret)
    }
}

#[doc(hidden)]
pub struct StaticLutIterator<const NUM_VARS: usize, const NUM_WORDS: usize> {
    lut: StaticLut<NUM_VARS, NUM_WORDS>,
    ok: bool,
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> Iterator
    for StaticLutIterator<NUM_VARS, NUM_WORDS>
{
    type Item = StaticLut<NUM_VARS, NUM_WORDS>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.ok {
            None
        } else {
            let ret = self.lut;
            self.ok = next_inplace(NUM_VARS, self.lut.table.as_mut());
            Some(ret)
        }
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> Ord for StaticLut<NUM_VARS, NUM_WORDS> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(self.table.as_ref(), other.table.as_ref())
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> PartialOrd for StaticLut<NUM_VARS, NUM_WORDS> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> Not for StaticLut<NUM_VARS, NUM_WORDS> {
    type Output = Self;
    fn not(self) -> Self::Output {
        let mut l = self;
        l.not_inplace();
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> Not for &StaticLut<NUM_VARS, NUM_WORDS> {
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn not(self) -> Self::Output {
        let mut l = *self;
        l.not_inplace();
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAndAssign<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitand_assign(&mut self, rhs: Self) {
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAndAssign<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitand_assign(&mut self, rhs: &Self) {
        and_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAnd<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAnd<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitand(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = self;
        l &= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAnd<StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitand(self, rhs: StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l &= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitAnd<&StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitand(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l &= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOrAssign<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitor_assign(&mut self, rhs: Self) {
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOrAssign<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitor_assign(&mut self, rhs: &Self) {
        or_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOr<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOr<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitor(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = self;
        l |= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOr<StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitor(self, rhs: StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l |= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitOr<&StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitor(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l |= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXorAssign<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitxor_assign(&mut self, rhs: Self) {
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXorAssign<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn bitxor_assign(&mut self, rhs: &Self) {
        xor_inplace(self.table.as_mut(), rhs.table.as_ref());
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXor<StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXor<&StaticLut<NUM_VARS, NUM_WORDS>>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = Self;
    fn bitxor(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = self;
        l ^= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXor<StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitxor(self, rhs: StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l ^= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> BitXor<&StaticLut<NUM_VARS, NUM_WORDS>>
    for &StaticLut<NUM_VARS, NUM_WORDS>
{
    type Output = StaticLut<NUM_VARS, NUM_WORDS>;
    fn bitxor(self, rhs: &StaticLut<NUM_VARS, NUM_WORDS>) -> Self::Output {
        let mut l = *self;
        l ^= rhs;
        l
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> fmt::Display
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(NUM_VARS, self.table.as_ref(), f)
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> fmt::Debug for StaticLut<NUM_VARS, NUM_WORDS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(NUM_VARS, self.table.as_ref(), f)
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> fmt::LowerHex
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_hex(NUM_VARS, self.table.as_ref(), f)
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> fmt::Binary for StaticLut<NUM_VARS, NUM_WORDS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_bin(NUM_VARS, self.table.as_ref(), f)
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> TryFrom<Lut>
    for StaticLut<NUM_VARS, NUM_WORDS>
{
    type Error = ();

    fn try_from(lut: Lut) -> Result<Self, Self::Error> {
        if lut.num_vars() != NUM_VARS {
            return Err(());
        }
        Ok(StaticLut::<NUM_VARS, NUM_WORDS>::from_blocks(lut.blocks()))
    }
}

impl<const NUM_VARS: usize, const NUM_WORDS: usize> From<StaticLut<NUM_VARS, NUM_WORDS>> for Lut {
    fn from(lut: StaticLut<NUM_VARS, NUM_WORDS>) -> Lut {
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

impl From<u8> for Lut3 {
    fn from(table: u8) -> Lut3 {
        Lut3::from_blocks(&[table as u64])
    }
}

impl From<u16> for Lut4 {
    fn from(table: u16) -> Lut4 {
        Lut4::from_blocks(&[table as u64])
    }
}

impl From<u32> for Lut5 {
    fn from(table: u32) -> Lut5 {
        Lut5::from_blocks(&[table as u64])
    }
}

impl From<u64> for Lut6 {
    fn from(table: u64) -> Lut6 {
        Lut6::from_blocks(&[table])
    }
}

impl From<u128> for Lut7 {
    fn from(table: u128) -> Lut7 {
        Lut7::from_blocks(&[(table & 0xffff_ffff_ffff_ffff) as u64, (table >> 64) as u64])
    }
}

impl From<Lut3> for u8 {
    fn from(lut: Lut3) -> u8 {
        (lut.table[0] & !VAR_MASK[3]) as u8
    }
}

impl From<Lut4> for u16 {
    fn from(lut: Lut4) -> u16 {
        (lut.table[0] & !VAR_MASK[4]) as u16
    }
}

impl From<Lut5> for u32 {
    fn from(lut: Lut5) -> u32 {
        (lut.table[0] & !VAR_MASK[5]) as u32
    }
}

impl From<Lut6> for u64 {
    fn from(lut: Lut6) -> u64 {
        lut.table[0]
    }
}

impl From<Lut7> for u128 {
    fn from(lut: Lut7) -> u128 {
        lut.table[0] as u128 + ((lut.table[1] as u128) << 64)
    }
}

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
    #[allow(
        unused_must_use,
        clippy::no_effect,
        clippy::unnecessary_operation,
        clippy::op_ref
    )]
    fn test_ops() {
        let mut a = Lut6::nth_var(0);
        let b = Lut6::nth_var(1);
        !a;
        !&a;
        &a & &b;
        &a & b;
        a & &b;
        a & b;
        &a | &b;
        &a | b;
        a | &b;
        a | b;
        &a ^ &b;
        &a ^ b;
        a ^ &b;
        a ^ b;
        a &= b;
        a &= &b;
        a |= b;
        a |= &b;
        a ^= b;
        a ^= &b;
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
    fn test_lut_conversion() {
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

    #[test]
    #[cfg(feature = "rand")]
    fn test_int_conversion() {
        for _ in 0..10 {
            let lut = Lut3::random();
            assert_eq!(lut, Lut3::from(u8::from(lut)));
            assert_eq!(lut.to_hex_string(), format!("{:02x}", u8::from(lut)));
        }
        for _ in 0..10 {
            let lut = Lut4::random();
            assert_eq!(lut, Lut4::from(u16::from(lut)));
            assert_eq!(lut.to_hex_string(), format!("{:04x}", u16::from(lut)));
        }
        for _ in 0..10 {
            let lut = Lut5::random();
            assert_eq!(lut, Lut5::from(u32::from(lut)));
            assert_eq!(lut.to_hex_string(), format!("{:08x}", u32::from(lut)));
        }
        for _ in 0..10 {
            let lut = Lut6::random();
            assert_eq!(lut, Lut6::from(u64::from(lut)));
            assert_eq!(lut.to_hex_string(), format!("{:016x}", u64::from(lut)));
        }
        for _ in 0..10 {
            let lut = Lut7::random();
            assert_eq!(lut, Lut7::from(u128::from(lut)));
            assert_eq!(lut.to_hex_string(), format!("{:032x}", u128::from(lut)));
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_string_conversion() {
        use crate::Lut8;

        for _ in 0..10 {
            let lut = Lut0::random();
            assert_eq!(lut, Lut0::from_hex_string(&lut.to_hex_string()).unwrap());
            assert_eq!(lut, Lut0::from_bin_string(&lut.to_bin_string()).unwrap());
        }
        for _ in 0..10 {
            let lut = Lut1::random();
            assert_eq!(lut, Lut1::from_hex_string(&lut.to_hex_string()).unwrap());
            assert_eq!(lut, Lut1::from_bin_string(&lut.to_bin_string()).unwrap());
        }
        for _ in 0..10 {
            let lut = Lut2::random();
            assert_eq!(lut, Lut2::from_hex_string(&lut.to_hex_string()).unwrap());
            assert_eq!(lut, Lut2::from_bin_string(&lut.to_bin_string()).unwrap());
        }
        for _ in 0..10 {
            let lut = Lut3::random();
            assert_eq!(lut, Lut3::from_hex_string(&lut.to_hex_string()).unwrap());
            assert_eq!(lut, Lut3::from_bin_string(&lut.to_bin_string()).unwrap());
        }
        for _ in 0..10 {
            let lut = Lut8::random();
            assert_eq!(lut, Lut8::from_hex_string(&lut.to_hex_string()).unwrap());
            assert_eq!(lut, Lut8::from_bin_string(&lut.to_bin_string()).unwrap());
        }
    }
}
