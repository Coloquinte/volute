use crate::operations::{cmp, flip_inplace, not_inplace, swap_adjacent_inplace};

/// Single bit flips to visit all possible binary values (Gray code)
const FLIPS: &[&[u8]] = &[
    &[],
    &[0, 0],
    &[0, 1, 0, 1],
    &[0, 1, 0, 2, 0, 1, 0, 2],
    &[0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 3],
    &[
        0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1,
        0, 4,
    ],
    &[
        0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1,
        0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2,
        0, 1, 0, 5,
    ],
];

/// Adjacent swaps to visit all possible permutations (Steinhaus-Johnson-Trotter)
const SWAPS: &[&[u8]] = &[
    &[],
    &[],
    &[0, 0],
    &[0, 1, 0, 1, 0, 1],
    &[
        0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2,
    ],
    &[
        0, 1, 2, 3, 0, 3, 2, 1, 0, 2, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 2,
        0, 1, 2, 3, 0, 3, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 2, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1,
        0, 1, 2, 3, 2, 3, 2, 1, 0, 2, 0, 1, 2, 3, 0, 3, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 2,
        0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 2, 0, 1, 2, 3, 0, 3, 2, 1, 0, 3,
    ],
    &[
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 3,
        0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0,
        4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4,
    ],
];

/// Generate all flips to visit all N-bit gray code
pub fn generate_gray_flips(nb_bits: usize, rollback: bool) -> Vec<u8> {
    // Basically just a gray code count
    let mut flips: Vec<u8> = Vec::new();
    let end: usize = 1 << nb_bits;
    for i in 1..end {
        let j = i - 1;
        let pred = j ^ (j >> 1);
        let gray = i ^ (i >> 1);
        let diff = pred ^ gray;
        flips.push(diff.trailing_zeros() as u8);
    }
    if rollback {
        flips.push((nb_bits - 1) as u8);
    }
    flips
}

/// Find the position where a swap occurs in a permutation
fn find_permutation_swap(p1: &[u8], p2: &[u8]) -> u8 {
    assert_eq!(p1.len(), p2.len());
    for i in 0..p1.len() - 1 {
        if p1[i] != p2[i] {
            check_permutation_swap(p1, p2, i);
            return i as u8;
        }
    }
    panic!("No difference found between permutations")
}

/// Find the position where a swap occurs in a permutation
fn check_permutation_swap(p1: &[u8], p2: &[u8], ind: usize) {
    assert_eq!(p1.len(), p2.len());
    for i in 0..p1.len() - 1 {
        if i != ind && i != ind + 1 {
            assert_eq!(p1[i], p2[i]);
        }
    }
    assert_eq!(&p1[ind], &p2[ind + 1]);
    assert_eq!(&p1[ind + 1], &p2[ind]);
}

/// Generate all unique permutations, with a single adjacent swap between consecutive ones
fn generate_single_swap_permutations(num_vars: usize) -> Vec<Vec<u8>> {
    if num_vars == 0 {
        vec![vec![]]
    } else if num_vars == 1 {
        vec![vec![0]]
    } else if num_vars == 2 {
        vec![vec![1, 0], vec![0, 1]]
    } else {
        let all_perms = generate_single_swap_permutations(num_vars - 1);
        let mut next_perms: Vec<Vec<u8>> = vec![];
        for (i, cur) in all_perms.iter().enumerate() {
            if i % 2 == 0 {
                for j in 0..cur.len() + 1 {
                    let mut p = cur.clone();
                    p.insert(j, (num_vars - 1) as u8);
                    next_perms.push(p);
                }
            } else {
                for j in (0..cur.len() + 1).rev() {
                    let mut p = cur.clone();
                    p.insert(j, (num_vars - 1) as u8);
                    next_perms.push(p);
                }
            }
        }
        next_perms
    }
}

/// Generate all swaps for P canonization
pub fn generate_swaps(num_vars: usize, rollback: bool) -> Vec<u8> {
    let perms = generate_single_swap_permutations(num_vars);
    let mut swaps: Vec<u8> = Vec::new();
    for i in 0..perms.len() - 1 {
        swaps.push(find_permutation_swap(&perms[i], &perms[i + 1]));
    }
    if rollback && !swaps.is_empty() {
        swaps.push(find_permutation_swap(
            perms.last().unwrap(),
            perms.first().unwrap(),
        ));
    }
    swaps
}

/// Run all swaps on the P canonization, and return the index of the best result
#[inline(always)]
pub fn p_canonization_ind(
    num_vars: usize,
    table: &mut [u64],
    best: &mut [u64],
    all_swaps: &[u8],
) -> usize {
    debug_assert_eq!(best, table);
    let mut best_ind = usize::MAX;
    for (ind, &swap) in all_swaps.iter().enumerate() {
        swap_adjacent_inplace(num_vars, table, swap as usize);
        if cmp(table, best).is_lt() {
            best_ind = ind;
            best.clone_from_slice(table);
        }
    }
    best_ind
}

/// Find the corresponding permutation given the index of the best result
#[inline(always)]
pub fn p_canonization_res(num_vars: usize, res_perm: &mut [u8], all_swaps: &[u8], best_ind: usize) {
    debug_assert!(best_ind == usize::MAX || best_ind < all_swaps.len());
    debug_assert_eq!(res_perm.len(), num_vars);
    for (i, p) in res_perm.iter_mut().enumerate() {
        *p = i as u8;
    }
    if best_ind == usize::MAX {
        return;
    }
    for (ind, &swap) in all_swaps.iter().enumerate() {
        let swp = swap as usize;
        res_perm.swap(swp, swp + 1);
        if ind == best_ind {
            return;
        }
    }
    // Should never arrive there...
    panic!("P-canonization reached an invalid state");
}

/// Returns whether the Lut is p-canonical
pub fn is_p_canonical_helper(
    num_vars: usize,
    table: &[u64],
    work: &mut [u64],
    all_swaps: &[u8],
) -> bool {
    debug_assert_eq!(work, table);
    for &swap in all_swaps.iter() {
        swap_adjacent_inplace(num_vars, work, swap as usize);
        if cmp(work, table).is_lt() {
            return false;
        }
    }
    true
}

/// Run all flips on the N canonization, and return the best solution
#[inline(always)]
pub fn n_canonization_helper(
    num_vars: usize,
    table: &mut [u64],
    best: &mut [u64],
    all_flips: &[u8],
) -> u32 {
    let mut best_flip = 0;
    let mut cur_flip = 0;
    debug_assert_eq!(best, table);
    for &flip in all_flips {
        cur_flip ^= 1 << flip;
        flip_inplace(num_vars, table, flip as usize);
        for _ in 0..2 {
            cur_flip ^= 1 << num_vars;
            not_inplace(num_vars, table);
            if cmp(table, best).is_lt() {
                best_flip = cur_flip;
                best.clone_from_slice(table);
            }
        }
    }
    best_flip
}

/// Returns whether the Lut is n-canonical
pub fn is_n_canonical_helper(
    num_vars: usize,
    table: &[u64],
    work: &mut [u64],
    all_flips: &[u8],
) -> bool {
    debug_assert_eq!(work, table);
    for &flip in all_flips {
        flip_inplace(num_vars, work, flip as usize);
        for _ in 0..2 {
            not_inplace(num_vars, work);
            if cmp(work, table).is_lt() {
                return false;
            }
        }
    }
    true
}

/// Run all swaps on the P canonization and all flips on the N canonization,
/// and return the index of the best result
#[inline(always)]
pub fn npn_canonization_ind(
    num_vars: usize,
    table: &mut [u64],
    best: &mut [u64],
    all_swaps: &[u8],
    all_flips: &[u8],
) -> (usize, usize) {
    debug_assert_eq!(best, table);
    let mut best_flip_ind = usize::MAX;
    let mut best_swap_ind = usize::MAX;
    for (swap_ind, &swap) in all_swaps.iter().enumerate() {
        swap_adjacent_inplace(num_vars, table, swap as usize);
        let mut flip_ind = 0;
        for flip in all_flips {
            flip_inplace(num_vars, table, *flip as usize);
            for _ in 0..2 {
                not_inplace(num_vars, table);
                if cmp(table, best).is_lt() {
                    best_flip_ind = flip_ind;
                    best_swap_ind = swap_ind;
                    best.clone_from_slice(table);
                }
                flip_ind += 1;
            }
        }
    }
    (best_swap_ind, best_flip_ind)
}

/// Returns whether the Lut is npn-canonical
pub fn is_npn_canonical_helper(
    num_vars: usize,
    table: &[u64],
    work: &mut [u64],
    all_swaps: &[u8],
    all_flips: &[u8],
) -> bool {
    debug_assert_eq!(work, table);
    for swap in all_swaps {
        swap_adjacent_inplace(num_vars, work, *swap as usize);
        for flip in all_flips {
            flip_inplace(num_vars, work, *flip as usize);
            for _ in 0..2 {
                not_inplace(num_vars, work);
                if cmp(work, table).is_lt() {
                    return false;
                }
            }
        }
    }
    true
}

/// Find the corresponding complementation given the index of the best result
#[inline(always)]
pub fn n_canonization_res(num_vars: usize, all_flips: &[u8], best_ind: usize) -> u32 {
    let mut ind = 0;
    let mut cur_flip = 0;
    if best_ind == usize::MAX {
        return cur_flip;
    }
    for flip in all_flips {
        cur_flip ^= 1 << *flip;
        for _ in 0..2 {
            cur_flip ^= 1 << num_vars;
            if ind == best_ind {
                return cur_flip;
            }
            ind += 1;
        }
    }
    // Should never arrive there...
    panic!("N-canonization reached an invalid state");
}

pub fn p_canonization(num_vars: usize, table: &mut [u64], best: &mut [u64], res_perm: &mut [u8]) {
    best.clone_from_slice(table);
    if num_vars <= 6 {
        let best_ind =
            p_canonization_ind(num_vars, &mut table[0..1], &mut best[0..1], SWAPS[num_vars]);
        p_canonization_res(num_vars, res_perm, SWAPS[num_vars], best_ind);
    } else {
        let all_swaps = generate_swaps(num_vars, true);
        let best_ind = p_canonization_ind(num_vars, table, best, &all_swaps);
        p_canonization_res(num_vars, res_perm, &all_swaps, best_ind);
    }
}

pub fn is_p_canonical(num_vars: usize, table: &[u64], work: &mut [u64]) -> bool {
    work.clone_from_slice(table);
    if num_vars <= 6 {
        is_p_canonical_helper(num_vars, &table[0..1], &mut work[0..1], SWAPS[num_vars])
    } else {
        let all_swaps = generate_swaps(num_vars, true);
        is_p_canonical_helper(num_vars, table, work, &all_swaps)
    }
}

pub fn n_canonization(num_vars: usize, table: &mut [u64], best: &mut [u64]) -> u32 {
    best.clone_from_slice(table);
    if num_vars <= 6 {
        n_canonization_helper(num_vars, &mut table[0..1], &mut best[0..1], FLIPS[num_vars])
    } else {
        let all_flips = generate_gray_flips(num_vars, true);
        n_canonization_helper(num_vars, table, best, &all_flips)
    }
}

pub fn is_n_canonical(num_vars: usize, table: &[u64], work: &mut [u64]) -> bool {
    work.clone_from_slice(table);
    if num_vars <= 6 {
        is_n_canonical_helper(num_vars, &table[0..1], &mut work[0..1], FLIPS[num_vars])
    } else {
        let all_flips = generate_gray_flips(num_vars, true);
        is_n_canonical_helper(num_vars, table, work, &all_flips)
    }
}

pub fn npn_canonization(
    num_vars: usize,
    table: &mut [u64],
    best: &mut [u64],
    res_perm: &mut [u8],
) -> u32 {
    best.clone_from_slice(table);
    if num_vars <= 6 {
        let (best_swap, best_flip) = npn_canonization_ind(
            num_vars,
            &mut table[0..1],
            &mut best[0..1],
            SWAPS[num_vars],
            FLIPS[num_vars],
        );
        p_canonization_res(num_vars, res_perm, SWAPS[num_vars], best_swap);
        n_canonization_res(num_vars, FLIPS[num_vars], best_flip)
    } else {
        let all_swaps = generate_swaps(num_vars, true);
        let all_flips = generate_gray_flips(num_vars, true);
        let (best_swap, best_flip) =
            npn_canonization_ind(num_vars, table, best, &all_swaps, &all_flips);
        p_canonization_res(num_vars, res_perm, &all_swaps, best_swap);
        n_canonization_res(num_vars, &all_flips, best_flip)
    }
}

pub fn is_npn_canonical(num_vars: usize, table: &[u64], work: &mut [u64]) -> bool {
    work.clone_from_slice(table);
    if num_vars <= 6 {
        is_npn_canonical_helper(
            num_vars,
            &table[0..1],
            &mut work[0..1],
            SWAPS[num_vars],
            FLIPS[num_vars],
        )
    } else {
        let all_swaps = generate_swaps(num_vars, true);
        let all_flips = generate_gray_flips(num_vars, true);
        is_npn_canonical_helper(num_vars, table, work, &all_swaps, &all_flips)
    }
}

#[cfg(test)]
mod tests {
    use crate::canonization::{generate_gray_flips, generate_swaps};

    #[test]
    fn test_gray_flips() {
        for i in 1..=7 {
            let flips = generate_gray_flips(i, false);
            assert_eq!(flips.len(), (1 << i) - 1);
            for f in flips {
                assert!(f < (i as u8));
            }
            let flips_rollback = generate_gray_flips(i, true);
            assert_eq!(flips_rollback.len(), 1 << i);
            for f in flips_rollback.iter() {
                assert!(*f < (i as u8));
            }

            // Check that the rollback is OK
            let mut cnt = 0u64;
            for f in flips_rollback.iter() {
                cnt ^= 1 << f;
            }
            assert_eq!(cnt, 0u64);
        }
    }

    #[test]
    fn test_swaps() {
        let mut fact = 1;
        for i in 1..=7 {
            fact *= i;
            let swaps = generate_swaps(i, false);
            assert_eq!(swaps.len(), fact - 1);
            let swaps_rollback = generate_swaps(i, true);
            assert_eq!(swaps_rollback.len(), if i == 1 { 0 } else { fact });
            // Check that the rollback is OK
            let mut perm: Vec<usize> = (0..i).collect();
            for s in swaps_rollback {
                assert!(s < (i as u8));
                perm.swap(s as usize, (s + 1) as usize);
            }
            assert_eq!(perm, (0..i).collect::<Vec<usize>>());
        }
    }
}
