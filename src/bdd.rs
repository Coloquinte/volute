fn level_complexity(table: &[u64], level: usize) -> usize {
    assert!(level < 6);
    assert!(level >= 1);

    // Gather the Luts at this level and normalize
    let shift = 1 << (level + 1);
    let mask = !0u64 >> (64 - shift);
    let mut luts = Vec::<u64>::with_capacity(table.len() * (64 / shift));
    for t in table {
        let mut c = *t;
        for _i in (0..64).step_by(shift) {
            let mut lut = c;
            if lut & 1 != 0 {
                lut = !lut;
            }
            lut &= mask;
            if lut != 0 {
                luts.push(lut);
            }
            if level < 5 {
                c >>= shift;
            }
        }
    }

    // Filter to only keep non-trivial ones
    let mid_shift = 1 << level;
    let mid_mask = !0u64 >> (64 - mid_shift);
    luts.retain(|c: &u64| {
        let h = c >> mid_shift;
        let l = c & mid_mask;
        if l == h {
            // Independent from this variable
            return false;
        }
        if l == (!h & mid_mask) && (l == 0 || h == 0) {
            // Direct copy of this variable
            return false;
        }
        true
    });

    // Sort-uniquify
    luts.sort();
    luts.dedup();
    luts.len()
}

fn large_level_complexity(table: &[u64], level: usize) -> usize {
    assert!(level >= 6);

    // Gather the Luts at this level and normalize
    let nb = 1 << (level - 5);
    let mut luts = Vec::<Vec<u64>>::new();
    for i in (0..table.len()).step_by(nb) {
        let mut c = table[i..i + nb].to_vec();
        if c[0] & 1 != 0 {
            for t in &mut c {
                *t = !*t;
            }
        }
        if c.iter().any(|t: &u64| *t != 0) {
            luts.push(c);
        }
    }

    // Filter to only keep non-trivial ones
    let mid_nb = 1 << (level - 6);
    luts.retain(|c: &Vec<u64>| {
        let h = &c[mid_nb..];
        let l = &c[..mid_nb];
        if l == h {
            // Independent from this variable
            return false;
        }
        let opp = std::iter::zip(l, h).all(|t: (&u64, &u64)| *t.0 == !*t.1);
        let lz = l.iter().all(|t: &u64| *t == 0);
        let hz = h.iter().all(|t: &u64| *t == 0);
        if opp && (lz || hz) {
            // Direct copy of this variable
            return false;
        }
        true
    });

    // Sort-uniquify
    luts.sort();
    luts.dedup();
    luts.len()
}

pub fn table_complexity(num_vars: usize, table: &[u64]) -> usize {
    let mut complexity: usize = 0;
    for level in 1..std::cmp::min(num_vars, 6) {
        complexity += level_complexity(table, level);
    }
    for level in 6..num_vars {
        complexity += large_level_complexity(table, level);
    }
    complexity
}
