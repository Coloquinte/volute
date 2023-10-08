pub fn level_complexity( table: &[u64], level: usize) -> usize {
    assert!(level <= 6);
    assert!(level >= 2);

    // Gather the Luts at this level and normalize
    let shift = 1 << level;
    let mask = !0u64 >> (64 - shift);
    let mut luts = Vec::<u64>::new();
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
            c >>= shift;
        }
    }

    // Filter to only keep non-trivial ones
    let mid_shift = 1 << (level - 1);
    let mid_mask = !0u64 >> (64 - mid_shift);
    luts.retain(|c: &u64| -> bool { 
        let h = c >> mid_shift;
        let l = c & mid_mask;
        if l == h {
            // Independent from this variable
            return false;
        }
        if l == !h && (l == 0 || h == 0) {
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

pub fn table_complexity(num_vars: usize, table: &[u64])  -> usize{
    let mut complexity: usize = 0;
    for level in 2..6 {
        if level >= num_vars { return complexity; }
        complexity += level_complexity(table, level);
    }
    complexity
}
