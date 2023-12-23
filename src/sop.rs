use std::fmt;

use crate::cube::Cube;

/// Sum of products representation (Or of And)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Sop {
    cubes: Vec<Cube>,
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

    /// Returns the cubes in the Sop
    pub fn cubes(&self) -> &[Cube] {
        &self.cubes
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
    use crate::Sop;

    #[test]
    fn sop_zero_one() {
        assert!(Sop::zero().is_zero());
        assert!(!Sop::one().is_zero());
        assert!(!Sop::zero().is_one());
        assert!(Sop::one().is_one());
        for i in 0..32 {
            assert!(!Sop::nth_var(i).is_zero());
            assert!(!Sop::nth_var(i).is_one());
            assert!(!Sop::nth_var_inv(i).is_zero());
            assert!(!Sop::nth_var_inv(i).is_one());
        }
    }
}
