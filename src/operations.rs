// Mask to access the 1 cofactor for each variable of a LUT
pub const VAR_MASK: [u64; 6] = [
    0xaaaa_aaaa_aaaa_aaaa,
    0xcccc_cccc_cccc_cccc,
    0xf0f0_f0f0_f0f0_f0f0,
    0xff00_ff00_ff00_ff00,
    0xffff_0000_ffff_0000,
    0xffff_ffff_0000_0000,
];

// Mask to access the part of the LUT relevant for n variables
pub const NUM_VARS_MASK: [u64; 7] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0003,
    0x0000_0000_0000_000f,
    0x0000_0000_0000_00ff,
    0x0000_0000_0000_ffff,
    0x0000_0000_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

// Masks to swap two variables of a LUT
pub const SWAP_INPUT_MASKS: [[u64; 6]; 6] = [
    [
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ],
    [
        0x2222222222222222,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ],
    [
        0x0a0a0a0a0a0a0a0a,
        0x0c0c0c0c0c0c0c0c,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ],
    [
        0x00aa00aa00aa00aa,
        0x00cc00cc00cc00cc,
        0x00f000f000f000f0,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
    ],
    [
        0x0000aaaa0000aaaa,
        0x0000cccc0000cccc,
        0x0000f0f00000f0f0,
        0x0000ff000000ff00,
        0x0000000000000000,
        0x0000000000000000,
    ],
    [
        0x00000000aaaaaaaa,
        0x00000000cccccccc,
        0x00000000f0f0f0f0,
        0x00000000ff00ff00,
        0x00000000ffff0000,
        0x0000000000000000,
    ],
];

// Mask to generate equals-k Luts
pub const COUNT_MASKS: [u64; 7] = [
    0x0000000000000001,
    0x0000000100010116,
    0x0001011601161668,
    0x0116166816686880,
    0x1668688068808000,
    0x6880800080000000,
    0x8000000000000000,
];

/// u64 mask when the number of variables is smaller than 6
pub const fn num_vars_mask(num_vars: usize) -> u64 {
    NUM_VARS_MASK[if num_vars < 6 { num_vars } else { 6 }]
}

/// Size of the lookup table, in u64
pub const fn table_size(num_vars: usize) -> usize {
    let v = if num_vars > 6 { num_vars } else { 6 };
    1 << (v - 6)
}

/// Fill with the constant one value
pub fn fill_one(num_vars: usize, table: &mut [u64]) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    let mask = num_vars_mask(num_vars);
    for t in table {
        *t = mask;
    }
}

/// Fill with the constant zero value
pub fn fill_zero(num_vars: usize, table: &mut [u64]) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    for t in table {
        *t = 0u64;
    }
}

/// Fill with the function that returns the nth variable
pub fn fill_nth_var(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert!(ind < num_vars);
    if ind <= 5 {
        for t in table {
            *t = VAR_MASK[ind] & num_vars_mask(num_vars);
        }
    } else {
        let mask = 1 << (ind - 6);
        for (i, t) in table.iter_mut().enumerate() {
            *t = if i & mask != 0 { !0u64 } else { 0u64 };
        }
    }
}

/// Fill with a symmetric function
pub fn fill_symmetric(num_vars: usize, table: &mut [u64], count_values: usize) {
    for (i, t) in table.iter_mut().enumerate() {
        let cnt = usize::count_ones(i) as usize;
        *t = 0;
        for (c, mask) in COUNT_MASKS.iter().enumerate() {
            if (count_values >> (cnt + c)) & 1 != 0 {
                *t |= mask;
            }
        }
        *t &= num_vars_mask(num_vars);
    }
}

/// Fill with the parity function
pub fn fill_parity(num_vars: usize, table: &mut [u64]) {
    fill_symmetric(num_vars, table, 0xaaaa_aaaa_aaaa_aaaa);
}

/// Fill with an equals-k function
pub fn fill_equals(num_vars: usize, table: &mut [u64], k: usize) {
    fill_symmetric(num_vars, table, 1 << k);
}

/// Fill with a threshold function
pub fn fill_threshold(num_vars: usize, table: &mut [u64], k: usize) {
    if k == 0 {
        fill_one(num_vars, table);
    } else if k > num_vars {
        fill_zero(num_vars, table);
    } else {
        fill_symmetric(num_vars, table, !0usize - (1 << k) + 1);
    }
}

/// Fill with a majority function
pub fn fill_majority(num_vars: usize, table: &mut [u64]) {
    fill_threshold(num_vars, table, num_vars.div_ceil(2));
}

/// Fill with random data
#[cfg(feature = "rand")]
pub fn fill_random(num_vars: usize, table: &mut [u64]) {
    use rand::RngCore;
    for t in table {
        *t = rand::rng().next_u64() & num_vars_mask(num_vars);
    }
}

/// Get a single bit in a LUT from a mask
pub fn get_bit(num_vars: usize, table: &[u64], ind: usize) -> bool {
    debug_assert!(ind < 1 << num_vars);
    (table[ind >> 6] & (1 << (ind & 0x3f))) != 0
}

/// Set a single bit in a LUT from a mask
pub fn set_bit(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert!(ind < 1 << num_vars);
    table[ind >> 6] |= 1 << (ind & 0x3f);
}

/// Unset a single bit in a LUT from a mask
pub fn unset_bit(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert!(ind < 1 << num_vars);
    table[ind >> 6] &= !(1 << (ind & 0x3f));
}

/// Count the ones in a Lut
pub fn count_ones(_num_vars: usize, table: &[u64]) -> usize {
    table.iter().map(|t| t.count_ones() as usize).sum()
}

/// Count the zeros in a Lut
pub fn count_zeros(num_vars: usize, table: &[u64]) -> usize {
    (1 << num_vars) - count_ones(num_vars, table)
}

/// Logical not computation
#[inline(always)]
pub fn not_inplace(num_vars: usize, table: &mut [u64]) {
    let mask = num_vars_mask(num_vars);
    for t in table {
        *t = mask & !*t;
    }
}

/// Logical and computation
pub fn and_inplace(table1: &mut [u64], table2: &[u64]) {
    debug_assert_eq!(table1.len(), table2.len());
    for (t1, t2) in table1.iter_mut().zip(table2.iter()) {
        *t1 &= t2;
    }
}

/// Logical or computation
pub fn or_inplace(table1: &mut [u64], table2: &[u64]) {
    debug_assert_eq!(table1.len(), table2.len());
    for (t1, t2) in table1.iter_mut().zip(table2.iter()) {
        *t1 |= t2;
    }
}

/// Logical xor computation
pub fn xor_inplace(table1: &mut [u64], table2: &[u64]) {
    debug_assert_eq!(table1.len(), table2.len());
    for (t1, t2) in table1.iter_mut().zip(table2.iter()) {
        *t1 ^= t2;
    }
}

/// Ordering
pub fn cmp(table1: &[u64], table2: &[u64]) -> std::cmp::Ordering {
    debug_assert_eq!(table1.len(), table2.len());
    table1.iter().rev().cmp(table2.iter().rev())
}

/// Expected size of the string for one chunk
fn hex_str_size(num_vars: usize) -> usize {
    let i = num_vars;
    if i >= 6 {
        16
    } else if i <= 2 {
        1
    } else {
        1 << (i - 2)
    }
}

/// Expected size of the string for one chunk
fn bin_str_size(num_vars: usize) -> usize {
    let i = num_vars;
    if i >= 6 {
        64
    } else {
        1 << i
    }
}

/// Hexadecimal string representation of the function
pub fn to_hex(num_vars: usize, table: &[u64]) -> String {
    let width = hex_str_size(num_vars);
    let mut s = String::new();
    for t in table.iter().rev() {
        s.push_str(&format!("{:0width$x}", t));
    }
    s
}

/// Hexadecimal formatting
pub fn fmt_hex(
    num_vars: usize,
    table: &[u64],
    f: &mut core::fmt::Formatter<'_>,
) -> core::fmt::Result {
    write!(f, "Lut{:}({})", num_vars, to_hex(num_vars, table))
}

/// Binary string representation of the function
pub fn to_bin(num_vars: usize, table: &[u64]) -> String {
    let width = if num_vars >= 6 { 64 } else { 1 << num_vars };
    let mut s = String::new();
    for t in table.iter().rev() {
        s.push_str(&format!("{:0width$b}", t));
    }
    s
}

/// Binary formatting
pub fn fmt_bin(
    num_vars: usize,
    table: &[u64],
    f: &mut core::fmt::Formatter<'_>,
) -> core::fmt::Result {
    write!(f, "Lut{:}({})", num_vars, to_bin(num_vars, table))
}

/// An error that can be returned when parsing a Lut
#[derive(Debug, Clone)]
pub enum ParseLutError {
    /// String is the wrong length; it should be a power of 2 corresponding to the number of variables
    WrongLength {
        /// String length
        length: usize,
        /// Expected length
        expected: usize,
    },
    /// Error while parsing the string as an integer
    ParseIntError(std::num::ParseIntError),
}

/// Fill from the hexadecimal representation
pub fn fill_hex(num_vars: usize, table: &mut [u64], s: &str) -> Result<(), ParseLutError> {
    debug_assert_eq!(table.len(), table_size(num_vars));

    let width = hex_str_size(num_vars);
    if s.len() != width * table.len() {
        return Err(ParseLutError::WrongLength {
            length: s.len(),
            expected: width * table.len(),
        });
    }

    for (i, t) in table.iter_mut().rev().enumerate() {
        let ss = &s[i * width..(i + 1) * width];
        let v = u64::from_str_radix(ss, 16);
        match v {
            Ok(v) => {
                *t = v;
            }
            Err(e) => {
                return Err(ParseLutError::ParseIntError(e));
            }
        }
    }
    Ok(())
}

/// Fill from the binary representation
pub fn fill_bin(num_vars: usize, table: &mut [u64], s: &str) -> Result<(), ParseLutError> {
    debug_assert_eq!(table.len(), table_size(num_vars));

    let width = bin_str_size(num_vars);
    if s.len() != width * table.len() {
        return Err(ParseLutError::WrongLength {
            length: s.len(),
            expected: width * table.len(),
        });
    }

    for (i, t) in table.iter_mut().rev().enumerate() {
        let ss = &s[i * width..(i + 1) * width];
        let v = u64::from_str_radix(ss, 2);
        match v {
            Ok(v) => {
                *t = v;
            }
            Err(e) => {
                return Err(ParseLutError::ParseIntError(e));
            }
        }
    }
    Ok(())
}

/// Swap two variables in the LUT
#[inline(always)]
pub fn swap_inplace(num_vars: usize, table: &mut [u64], ind1: usize, ind2: usize) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert!(ind1 < num_vars);
    debug_assert!(ind2 < num_vars);
    if ind1 == ind2 {
        return;
    }
    let i = core::cmp::max(ind1, ind2);
    let j = core::cmp::min(ind1, ind2);
    if i <= 5 {
        let shift = (1 << i) - (1 << j);
        let mask_left = SWAP_INPUT_MASKS[i][j];
        let mask_right = mask_left << shift;
        for t in table {
            *t = (*t & !mask_left & !mask_right)
                + ((*t & mask_left) << shift)
                + ((*t & mask_right) >> shift);
        }
    } else if j <= 5 {
        let mi = 1 << (i - 6);
        for k in 0..table.len() {
            if k & mi == 0 {
                let t0 = table[k];
                let t1 = table[k + mi];
                let mask = VAR_MASK[j];
                let shift = 1 << j;
                let t00 = t0 & !mask;
                let t01 = (t0 & mask) >> shift;
                let t10 = t1 & !mask;
                let t11 = (t1 & mask) >> shift;
                table[k] = t00 + (t10 << shift);
                table[k + mi] = t01 + (t11 << shift);
            }
        }
    } else {
        let mi = 1 << (i - 6);
        let mj = 1 << (j - 6);
        for k in 0..table.len() {
            if mi & k == 0 && mj & k != 0 {
                table.swap(k, k - mj + mi);
            }
        }
    }
}

/// Swap two adjacent variables in the LUT
#[inline(always)]
pub fn swap_adjacent_inplace(num_vars: usize, table: &mut [u64], ind: usize) {
    swap_inplace(num_vars, table, ind, ind + 1);
}

/// Permute the variables in the LUT
pub fn permute_inplace(num_vars: usize, table: &mut [u64], perm: &[u8]) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert_eq!(perm.len(), num_vars);
    let mut order: Vec<u8> = (0..num_vars as u8).collect();
    for (i, &p) in perm.iter().enumerate() {
        for j in i..num_vars {
            if order[j] == p {
                swap_inplace(num_vars, table, i, j);
                order.swap(i, j);
                break;
            }
        }
    }
    debug_assert_eq!(order, perm);
}

#[inline(always)]
pub fn flip_inplace(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert!(ind < num_vars);
    if ind <= 5 {
        let shift = 1 << ind;
        let m1 = VAR_MASK[ind];
        let m0 = !VAR_MASK[ind];
        for t in table {
            *t = ((*t & m1) >> shift) + ((*t & m0) << shift);
        }
    } else {
        let stride = 1 << (ind - 6);
        for i in 0..table.len() {
            if i & stride == 0 {
                table.swap(i, i + stride);
            }
        }
    }
}

#[inline(always)]
pub fn flip_n_inplace(num_vars: usize, table: &mut [u64], mask: u32) {
    for i in 0..num_vars {
        if ((mask >> i) & 1) != 0 {
            flip_inplace(num_vars, table, i);
        }
    }
    if ((mask >> num_vars) & 1) != 0 {
        not_inplace(num_vars, table);
    }
}

#[inline(always)]
pub fn cofactor0_inplace(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert!(ind < num_vars);
    if ind <= 5 {
        let shift = 1 << ind;
        let m0 = !VAR_MASK[ind];
        for t in table {
            *t = (*t & m0) + ((*t & m0) << shift);
        }
    } else {
        let stride = 1 << (ind - 6);
        for i in 0..table.len() {
            if i & stride == 0 {
                table[i + stride] = table[i];
            }
        }
    }
}

#[inline(always)]
pub fn cofactor1_inplace(num_vars: usize, table: &mut [u64], ind: usize) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert!(ind < num_vars);
    if ind <= 5 {
        let shift = 1 << ind;
        let m1 = VAR_MASK[ind];
        for t in table {
            *t = ((*t & m1) >> shift) + (*t & m1);
        }
    } else {
        let stride = 1 << (ind - 6);
        for i in 0..table.len() {
            if i & stride == 0 {
                table[i] = table[i + stride];
            }
        }
    }
}
pub fn from_cofactors_inplace(
    num_vars: usize,
    table: &mut [u64],
    t0: &[u64],
    t1: &[u64],
    ind: usize,
) {
    debug_assert_eq!(table.len(), table_size(num_vars));
    debug_assert_eq!(t0.len(), table_size(num_vars));
    debug_assert_eq!(t1.len(), table_size(num_vars));
    debug_assert!(ind < num_vars);
    if ind <= 5 {
        let m1 = VAR_MASK[ind];
        let m0 = !VAR_MASK[ind];
        for i in 0..table.len() {
            table[i] = (t1[i] & m1) + (t0[i] & m0);
        }
    } else {
        let stride = 1 << (ind - 6);
        for i in 0..table.len() {
            if i & stride == 0 {
                table[i] = t0[i];
            } else {
                table[i] = t1[i];
            }
        }
    }
}

/// Advance to the next Lut, and return true if the Lut didn't roll back
pub fn next_inplace(num_vars: usize, table: &mut [u64]) -> bool {
    debug_assert_eq!(table.len(), table_size(num_vars));
    let mask = num_vars_mask(num_vars);
    for t in table {
        *t = (*t + 1) & mask;
        if *t != 0 {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_masks() {
        use super::VAR_MASK;
        for i in 0..6 {
            assert_eq!(u64::count_ones(VAR_MASK[i]), 32);
            assert_eq!((VAR_MASK[i] << (1 << i)) & VAR_MASK[i], 0);
            for j in 0..6 {
                if i != j {
                    assert_eq!(u64::count_ones(VAR_MASK[i] & VAR_MASK[j]), 16);
                }
            }
        }
    }

    /// This checks the masks used to swap variables
    #[test]
    fn test_swap_masks() {
        use super::SWAP_INPUT_MASKS;
        for i in 0..6 {
            for j in 0..6 {
                let mut mask_left: u64 = 0;
                if i > j {
                    for ind in 0..64 {
                        let iset = ind & (1 << i) != 0;
                        let jset = ind & (1 << j) != 0;
                        if jset && !iset {
                            mask_left |= 1 << ind;
                        }
                    }
                }
                assert!(mask_left == SWAP_INPUT_MASKS[i][j]);
            }
        }
    }

    /// This checks the masks used for bitcounts
    #[test]
    fn test_count_masks() {
        use super::COUNT_MASKS;
        for bitcount in 0..7 {
            let mut mask: u64 = 0;
            for ind in 0..64 {
                let cnt = i32::count_ones(ind);
                if cnt == bitcount {
                    mask |= 1 << ind;
                }
            }
            assert_eq!(mask, COUNT_MASKS[bitcount as usize]);
        }

        for i in 0..6 {
            for j in i + 1..7 {
                assert_eq!(COUNT_MASKS[i] & COUNT_MASKS[j], 0u64);
            }
        }

        let mut all = 0u64;
        for mask in COUNT_MASKS {
            all |= mask;
        }
        assert_eq!(all, !0u64);
    }
}
