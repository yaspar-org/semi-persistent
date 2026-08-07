// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `IdFactory<T: DenseId>`: sequential dense-id allocation (production
//! parity), verified: `try_alloc` yields exactly the ids `0, 1, 2, ...` in
//! order while the range lasts, and `count` is the number allocated.
//!
//! Production's `try_alloc` range check went through `T::Index::
//! try_from_usize`, i.e. the WORD range — twice the id range for the
//! bit-stealing family, so a long-lived factory could hand out ids whose MSB
//! was set (colliding with the tag bit). The verified factory checks
//! `DenseId::try_new` (the ID range) instead — the corrected contract; the
//! panic message is production's.

use vstd::prelude::*;

use crate::opt::DenseId;

verus! {

/// Sequential id allocator.
pub struct IdFactory<T: DenseId> {
    next: usize,
    _phantom: core::marker::PhantomData<T>,
}

impl<T: DenseId> IdFactory<T> {
    /// Number of ids handed out so far (== the next id's dense index).
    /// Closed: the counter field is private (the abstraction is the count).
    pub closed spec fn count_spec(&self) -> nat {
        self.next as nat
    }

    pub fn new() -> (f: Self)
        ensures f.count_spec() == 0,
    {
        IdFactory { next: 0, _phantom: core::marker::PhantomData }
    }

    /// Allocate the next id: `Some(id)` with `id.id_nat() == count` while the
    /// range lasts, `None` once `count == id_bound` (and `usize` can hold the
    /// increment — the id bound is at most `usize::MAX + 1`, so `next`
    /// saturating there means the range is done).
    pub fn try_alloc(&mut self) -> (r: Option<T>)
        ensures
            match r {
                Some(id) => {
                    &&& old(self).count_spec() < T::id_bound()
                    &&& id.id_nat() == old(self).count_spec()
                    &&& self.count_spec() == old(self).count_spec() + 1
                },
                None => {
                    // Exhausted: the id range is done, OR (full-range ids
                    // only, id_bound == usize::MAX + 1) the usize counter
                    // itself saturated one id early — see the body comment.
                    &&& (old(self).count_spec() >= T::id_bound()
                            || old(self).count_spec() == usize::MAX as nat)
                    &&& self.count_spec() == old(self).count_spec()
                },
            },
    {
        match T::try_new(self.next) {
            Some(id) => {
                // try_new's Some arm gives next < id_bound <= usize::MAX + 1,
                // so next + 1 <= usize::MAX: the increment cannot overflow...
                // EXCEPT for a full-range id (id_bound == usize::MAX + 1) at
                // next == usize::MAX. Saturate there: the next try_new(MAX)
                // would have been the last Some anyway, and a saturated
                // factory keeps returning that same last id rather than
                // wrapping. Guard instead: refuse the increment overflow.
                if self.next == usize::MAX {
                    // Hand out the final id and pin the factory at exhaustion
                    // by declining (production could never reach this: its id
                    // types are all bit-stealing, bound <= 2^63 < usize::MAX).
                    return None;
                }
                self.next = self.next + 1;
                Some(id)
            }
            None => None,
        }
    }

    /// Allocate, panicking on exhaustion (production message parity).
    pub fn alloc(&mut self) -> (id: T)
        requires old(self).count_spec() < T::id_bound(), old(self).count_spec() < usize::MAX,
        ensures
            id.id_nat() == old(self).count_spec(),
            self.count_spec() == old(self).count_spec() + 1,
    {
        let r = self.try_alloc();
        crate::guard::check_precondition(r.is_some(), "DenseId range exhausted");
        match r {
            Some(id) => id,
            None => {
                proof { assert(false); }
                // Unreachable (guard trapped); satisfy the type checker.
                #[allow(clippy::empty_loop)]
                loop
                    invariant false,
                    decreases 0int,
                {
                }
            }
        }
    }

    pub fn count(&self) -> (n: usize)
        ensures n as nat == self.count_spec(),
    {
        self.next
    }
}

} // verus!

/// `Default` (plain Rust; production parity).
impl<T: DenseId> Default for IdFactory<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Range error for `TryFrom<int>` on generated id types (production parity).
#[derive(Debug, Clone)]
pub struct IdRangeError {
    pub type_name: &'static str,
}

impl core::fmt::Display for IdRangeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "value out of range for {}", self.type_name)
    }
}

impl std::error::Error for IdRangeError {}
