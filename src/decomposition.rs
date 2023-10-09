use crate::operations::*;

/// A helper function to many properties of an input using the cofactors
/// * Insensitive to input: c0 == c1
/// * And/Or/Nand/Nor canalizing: c0 or c1 is 0 or 1
/// * Xor-separable: c0 == !c1
/// * Positive/negative unate: c0 | !c1 or !c0 | c1
///
/// The given operation takes two words of the cofactor and returns one word with a bit set for all positions that match
pub fn input_property_helper<F>(num_vars: usize, table: &[u64], ind: usize, op: F) -> bool
where
    F: Fn(u64, u64) -> u64,
{
    assert!(table.len() == table_size(num_vars));
    assert!(ind < num_vars);
    let mask = num_vars_mask(num_vars);
    let mut ret = true;
    if ind <= 5 {
        let shift = 1 << ind;
        let m1 = VAR_MASK[ind];
        let m0 = !VAR_MASK[ind];
        for t in table {
            let c1 = ((*t & m1) >> shift) | (*t & m1);
            let c0 = ((*t & m0) << shift) | (*t & m0);
            ret &= !op(c0, c1) & mask == 0;
        }
    } else {
        let stride = 1 << (ind - 6);
        for i in 0..table.len() {
            if i & stride == 0 {
                let c0 = table[i];
                let c1 = table[i + stride];
                ret &= !op(c0, c1) & mask == 0;
            }
        }
    }
    ret
}

pub fn input_independent(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, c1| !(c0 ^ c1))
}

pub fn input_and(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, _| !c0)
}

pub fn input_or(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |_, c1| c1)
}

pub fn input_nand(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, _| c0)
}

pub fn input_nor(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |_, c1| !c1)
}

pub fn input_xor(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, c1| c0 ^ c1)
}

pub fn input_pos_unate(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, c1| !c0 | c1)
}

pub fn input_neg_unate(num_vars: usize, table: &[u64], ind: usize) -> bool {
    input_property_helper(num_vars, table, ind, |c0, c1| !c1 | c0)
}

/// Basic boolean function families to describe decompositions
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum DecompositionType {
    /// No valid decomposition with this variable
    None,
    /// The function is independent of this variable
    Independent,
    /// The function returns this variable
    Identity,
    /// The function returns the negation of this variable
    Negation,
    /// Decomposition possible as And
    And,
    /// Decomposition possible as Or
    Or,
    /// Decomposition possible as Less-Or-Equal (equivalent to Nand for an output)
    Le,
    /// Decomposition possible as Less-Than (equivalent to Nor for an output)
    Lt,
    /// Decomposition possible as Xor
    Xor,
}

impl DecompositionType {
    /// Returns whether the decomposition is trivial (independent, x or !x)
    pub fn is_trivial(&self) -> bool {
        [Self::Independent, Self::Identity, Self::Negation].contains(self)
    }

    /// Returns whether the decomposition is based on an and gate or similar
    pub fn is_and_type(&self) -> bool {
        [Self::And, Self::Or, Self::Le, Self::Lt].contains(self)
    }

    /// Returns whether the decomposition is based on a xor gate
    pub fn is_xor_type(&self) -> bool {
        [Self::Xor].contains(self)
    }

    /// Returns whether the decomposition is based on any 2-input gate
    pub fn is_simple_gate(&self) -> bool {
        [Self::And, Self::Or, Self::Le, Self::Lt, Self::Xor].contains(self)
    }
}

pub fn top_decomposition(num_vars: usize, table: &[u64], ind: usize) -> DecompositionType {
    let indep: bool = input_independent(num_vars, table, ind);
    let and = input_and(num_vars, table, ind);
    let or = input_or(num_vars, table, ind);
    let nand = input_nand(num_vars, table, ind);
    let nor = input_nor(num_vars, table, ind);
    let xor = input_xor(num_vars, table, ind);

    if indep {
        DecompositionType::Independent
    } else if and && or {
        DecompositionType::Identity
    } else if nand && nor {
        DecompositionType::Negation
    } else if and {
        DecompositionType::And
    } else if or {
        DecompositionType::Or
    } else if nand {
        DecompositionType::Le
    } else if nor {
        DecompositionType::Lt
    } else if xor {
        DecompositionType::Xor
    } else {
        DecompositionType::None
    }
}
