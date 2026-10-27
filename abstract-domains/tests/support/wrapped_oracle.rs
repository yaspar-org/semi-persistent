// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Independent finite-set oracle. Not a production domain or a Verus proof.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Repr {
    Empty,
    Full,
    Arc { lo: u32, hi: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Values {
    bits: Vec<bool>,
}

impl Values {
    pub fn contains(&self, x: u32) -> bool {
        self.bits.get(x as usize).copied().unwrap_or(false)
    }
    pub fn cardinality(&self) -> usize {
        self.bits.iter().filter(|&&b| b).count()
    }
    pub fn elements(&self) -> impl Iterator<Item = u32> + '_ {
        self.bits
            .iter()
            .enumerate()
            .filter(|(_, b)| **b)
            .map(|(i, _)| i as u32)
    }
    pub fn union(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a || b)
    }
    pub fn intersection(&self, other: &Self) -> Self {
        self.combine(other, |a, b| a && b)
    }
    fn combine(&self, other: &Self, op: impl Fn(bool, bool) -> bool) -> Self {
        assert_eq!(self.bits.len(), other.bits.len(), "different universes");
        Self {
            bits: self
                .bits
                .iter()
                .zip(&other.bits)
                .map(|(&a, &b)| op(a, b))
                .collect(),
        }
    }
    /// Soundness: every expected value must occur in the candidate result.
    pub fn check_contained_by(&self, candidate: &Self) -> Result<(), String> {
        if self.bits.len() != candidate.bits.len() {
            return Err("different universes".into());
        }
        let missing: Vec<_> = self
            .elements()
            .filter(|&x| !candidate.contains(x))
            .collect();
        if missing.is_empty() {
            Ok(())
        } else {
            Err(format!("missing values: {missing:?}"))
        }
    }
    /// Exactness is stronger than containment; useful for membership/normalization.
    pub fn check_exact(&self, candidate: &Self) -> Result<(), String> {
        self.check_contained_by(candidate)?;
        candidate
            .check_contained_by(self)
            .map_err(|e| format!("extra values ({e})"))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Oracle {
    size: u32,
}

impl Oracle {
    /// Test universes only: deliberately bounded to keep exhaustive runs practical.
    pub fn new(width: u32) -> Result<Self, String> {
        if !(1..=8).contains(&width) {
            return Err("oracle width must be 1..=8".into());
        }
        Ok(Self { size: 1 << width })
    }
    pub fn size(&self) -> u32 {
        self.size
    }
    pub fn empty(&self) -> Values {
        Values {
            bits: vec![false; self.size as usize],
        }
    }
    /// Enumerate by walking around the ring, independent of endpoint comparisons.
    pub fn values(&self, repr: Repr) -> Result<Values, String> {
        let mut result = self.empty();
        match repr {
            Repr::Empty => {}
            Repr::Full => result.bits.fill(true),
            Repr::Arc { lo, hi } => {
                if lo >= self.size || hi >= self.size {
                    return Err("endpoint outside universe".into());
                }
                let mut x = lo;
                loop {
                    result.bits[x as usize] = true;
                    if x == hi {
                        break;
                    }
                    x = (x + 1) % self.size;
                }
            }
        }
        Ok(result)
    }
    /// Current test convention: every full-circle arc normalizes to explicit Full.
    pub fn normalize(&self, repr: Repr) -> Result<Repr, String> {
        let values = self.values(repr)?;
        Ok(if values.cardinality() == self.size as usize {
            Repr::Full
        } else {
            repr
        })
    }
    pub fn raw_representations(&self) -> Vec<Repr> {
        let mut result = vec![Repr::Empty, Repr::Full];
        for lo in 0..self.size {
            for hi in 0..self.size {
                result.push(Repr::Arc { lo, hi });
            }
        }
        result
    }
    pub fn canonical_representations(&self) -> Vec<Repr> {
        self.raw_representations()
            .into_iter()
            .filter(|&r| self.normalize(r) == Ok(r))
            .collect()
    }
    /// Adapter boundary for a future executable membership implementation.
    pub fn sample_membership(&self, has: impl Fn(u32) -> bool) -> Values {
        Values {
            bits: (0..self.size).map(has).collect(),
        }
    }
    /// Concrete operation oracle. The callback defines semantics, including wrap.
    /// None denotes no successful value (e.g. zero division); alarms are separate.
    pub fn binary_image(
        &self,
        a: &Values,
        b: &Values,
        op: impl Fn(u32, u32) -> Option<u32>,
    ) -> Values {
        assert_eq!(a.bits.len(), self.size as usize);
        assert_eq!(b.bits.len(), self.size as usize);
        let mut result = self.empty();
        for x in a.elements() {
            for y in b.elements() {
                if let Some(z) = op(x, y) {
                    assert!(
                        z < self.size,
                        "concrete operation returned an out-of-range value"
                    );
                    result.bits[z as usize] = true;
                }
            }
        }
        result
    }
}
