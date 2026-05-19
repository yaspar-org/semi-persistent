// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Tagged`: the bit-stealing contract.
//!
//! A `Tagged` impl provides an injective encoding `(T, bool) -> Repr` so that a
//! capture flag can be packed alongside the value. The `repr_wf` predicate
//! describes which `Repr` values are in the image of the encoding (the niche
//! obligation). Concrete impls (e.g., `DenseId<31>` over `u32`) discharge:
//!   - `encode_wf`        — every encoding is well-formed
//!   - `encode_roundtrip` — value/tag survive an encode
//!   - `decode_roundtrip` — well-formed reprs reconstruct their (value, tag)
//!
//! Once these axioms are proved for an impl, `InlineStore` can use that impl
//! as a faithful storage backend with zero extra space for the tag bit.

use vstd::prelude::*;

verus! {

// Trait specification will land here in milestone M1.

} // verus!
