// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance tests for the `abs-class-storage` branch: per-class handles into
//! the semi-persistent abstract-value pool of `EClasses`. The specification is
//! `containers-verus/doc/design/21-abstract-value-pool.md`.
//!
//! Every test is ignored until the API exists. Each body states the target
//! sequence in comments and calls no new API, so the file compiles today. The
//! implementer writes the body with the `EC` type and helpers of
//! `eclasses_behavior.rs`, with a small `Copy + Default` entry type such as
//! `u64`, and removes the `#[ignore]`.

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn set_value_reads_back() {
    // ec = EC::new(); (a, ka) = ec.try_add_singleton();
    // ec.abs_handle(ka) == None and ec.abs_value(ka) == None.
    // ec.set_abs_value(ka, 7): ec.abs_value(ka) == Some(7), ec.abs_handle(ka) is Some.
    // ec.set_abs_value(ka, 9): ec.abs_value(ka) == Some(9), the handle is unchanged
    // (an overwrite allocates no new entry).
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn live_handles_are_distinct() {
    // Three singletons ka, kb, kc; set values 1, 2, 3.
    // The three handles are Some and pairwise distinct (W8c).
    // ec.set_abs_value(kb, 20) leaves ka at 1 and kc at 3 (the W8c frame condition).
    // A fourth singleton kd has no handle until its first write; after
    // ec.set_abs_value(kd, 4) its handle differs from the other three.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn merge_returns_absorbed_handle() {
    // (a, ka), (b, kb); set_abs_value(ka, 10), set_abs_value(kb, 20).
    // Record ha = abs_handle(ka), hb = abs_handle(kb).
    // mi = ec.merge(a, b).unwrap().
    // mi.absorbed_abs is the handle of the class of mi.absorbed (ha or hb).
    // ec.abs_value_at(mi.absorbed_abs) is that class's pre-merge value (10 or 20).
    // The survivor key's value is unchanged by the merge: the merge writes no
    // pool entry and leaves the survivor's handle as it was.
    // The caller writes the combined value: set_abs_value(survivor_key, 30);
    // abs_value(survivor_key) == Some(30).
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn merge_without_values_returns_none() {
    // Two singletons without values; mi = ec.merge(a, b).unwrap().
    // mi.absorbed_abs == None and ec.abs_value_at(None) == None.
    // The survivor still has no value.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn restore_rolls_back_value_write() {
    // ec = ForkHistory::new(EC::new()); (a, ka); set_abs_value(ka, 1).
    // token = ec.mark(ShrinkPolicy::Never).
    // set_abs_value(ka, 2); abs_value(ka) == Some(2).
    // ec.restore(token): abs_value(ka) == Some(1), and the handle equals its
    // value at the mark.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn restore_rolls_back_merge_and_combined_value() {
    // ec = ForkHistory::new(EC::new()); (a, ka), (b, kb); values 10 and 20.
    // token = ec.mark(ShrinkPolicy::Never).
    // mi = ec.merge(a, b); set_abs_value(survivor_key, 30).
    // ec.restore(token): num_classes == 2, both keys live again,
    // abs_value(ka) == Some(10), abs_value(kb) == Some(20), and both handles
    // equal their values at the mark (the semi-persistence theorem of §4).
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn restore_drops_entries_allocated_after_mark() {
    // ec = ForkHistory::new(EC::new()); (a, ka) without a value.
    // token = ec.mark(ShrinkPolicy::Never).
    // set_abs_value(ka, 5); (b, kb) = try_add_singleton(); set_abs_value(kb, 6).
    // ec.restore(token): abs_handle(ka) == None, b does not exist, and the
    // pool length equals its length at the mark (0).
    // set_abs_value(ka, 7) after the restore allocates a fresh handle and
    // reads back 7.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn nested_marks_restore_values_in_order() {
    // (a, ka); set 1; t1 = mark; set 2; t2 = mark; set 3.
    // restore(t2): abs_value(ka) == Some(2).
    // restore(t1): abs_value(ka) == Some(1).
    // Semantics B: restore(t1) again gives Some(1); pop_scope drops t1.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn restore_after_merge_with_handle_adoption() {
    // Only if the student chooses handle adoption (§8 decision 4).
    // (a, ka) without a value, (b, kb) with value 8; mark;
    // merge_directed_with(a, b, true) so that a survives.
    // After the merge the survivor reads 8 through its own handle.
    // restore: ka has no handle again, kb reads 8.
    // Without adoption, delete this test and record the decision in §8.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn dead_key_write_refuses() {
    // Final form: #[should_panic(expected = "class key is not live")].
    // (a, ka), (b, kb); mi = merge(a, b); the absorbed key is dead.
    // set_abs_value(absorbed_key, 1) refuses; abs_value(absorbed_key) refuses.
}

#[test]
#[ignore = "abs-class-storage: not implemented yet"]
fn bits63_value_round_trip() {
    // The same set, mark, merge, restore sequence as
    // restore_rolls_back_merge_and_combined_value, with EC64 (63-bit ids).
}
