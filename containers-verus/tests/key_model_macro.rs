// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end exercise of `declare_key_model_assumption!` (the group-D
//! forcing function): declares the assumption for a local canonical key
//! type exactly as a consumer crate would, and runs the generated
//! requirement-level fuzz. The axiom half expands a `verus!` block; under
//! plain `cargo test` it erases, and this test target is additionally what
//! keeps the macro's expansion COMPILING (a broken expansion fails the
//! build even though cargo cannot check the verus semantics).

#![cfg(feature = "literal-types")]

use semi_persistent_containers_verus::canonical_keys::CanonicalF64;
use semi_persistent_containers_verus::declare_key_model_assumption;

declare_key_model_assumption! {
    key = semi_persistent_containers_verus::canonical_keys::CanonicalF64;
    axiom = axiom_key_model_canonical_f64_macro_demo;
    test = key_model_fuzz_canonical_f64_macro_demo;
    justification = "CanonicalF64 is a crate-local struct { bits: u64 } whose only \
                     constructor canonicalizes (all NaNs -> one encoding, -0.0 -> +0.0); \
                     Eq/Hash are derived over the single u64 field, so == is bit identity.";
    generator = |raw: u64| CanonicalF64::new(f64::from_bits(raw));
    observable = |v: &CanonicalF64| v.bits();
}
