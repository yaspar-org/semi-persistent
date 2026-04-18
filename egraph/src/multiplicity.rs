// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Multiplicities for AC multiset nodes — newtype over u32.

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct Multiplicity(pub u32);

impl From<u32> for Multiplicity {
    fn from(v: u32) -> Self {
        Self(v)
    }
}
impl From<Multiplicity> for u32 {
    fn from(m: Multiplicity) -> Self {
        m.0
    }
}
impl std::fmt::Display for Multiplicity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
