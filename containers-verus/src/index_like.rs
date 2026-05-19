// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `IndexLike`: the bijection-to-`[0, MAX)` contract.
//!
//! Every index type provides a spec function `as_nat: Self -> nat` together
//! with a bound `MAX_NAT` and proofs that:
//!   - `as_nat` is injective
//!   - `as_nat(self) < MAX_NAT`
//!   - `try_from_usize` is the inverse of `as_usize` on `[0, MAX_NAT)`
//!
//! The diff log stores `(T, I)` pairs; `IndexLike` keeps the index narrow so
//! diff entries stay compact.

use vstd::prelude::*;

verus! {

// Trait specification will land here in milestone M1.

} // verus!
