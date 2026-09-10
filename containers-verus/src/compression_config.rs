// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-column compression configuration and the when-to-compress policy
//! (`doc/design/09-diff-stack-compression.md`, "Configuration object and when to
//! compress").
//!
//! An aggregate names, per column, both the encoder (`CompressionMode`) and the
//! policy that decides when the plain top is flushed into the compressed bottom.
//! One value, not a type: the SMT profile passes all-`None` and the eq-sat
//! profile passes a per-column table, from one binary.

use crate::diff_compress::CompressionMode;
use vstd::prelude::*;

verus! {

/// Compression configuration for one column: the encoder plus the flush policy.
///
/// `IndexRuns` is a planned third `CompressionMode` (the index-major
/// run-coalescing encoder and its bijection already exist at the `nat` index
/// level in `diff_compress`); integrating it into `FrameEncoding` needs an
/// `IndexLike` spec inverse to materialize `I` from a `usize` run start, so the
/// config's `scheme` today ranges over `{ None, ValueDict }`.
#[derive(Clone, Copy)]
pub struct ColumnConfig {
    /// How a finalized frame is encoded when flushed to the compressed bottom.
    pub scheme: CompressionMode,
    /// Flush the plain top only once its byte footprint reaches this percent of
    /// the live payload (base length times value size). `0` flushes on every
    /// eligible mark; the `None` scheme ignores the field (never flushes).
    pub compress_at_percent: u32,
    /// Keep this many most-recently-marked frames plain regardless of the
    /// trigger (the LRU floor), so an imminent backtrack pays no decode.
    pub keep_hot_frames: usize,
}

impl ColumnConfig {
    /// No compression (the SMT profile): the plain top is the whole history.
    pub const fn none() -> ColumnConfig {
        ColumnConfig { scheme: CompressionMode::None, compress_at_percent: 0, keep_hot_frames: 0 }
    }

    /// Value-dictionary compression with an explicit flush policy (eq-sat, on the
    /// union-find value columns once `dict_find` is hashed and codes narrowed).
    pub const fn value_dict(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::ValueDict,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Index-major run-coalescing with an explicit flush policy (eq-sat, on
    /// columns whose captured indices cluster into contiguous ranges — it drops
    /// the index column, the measured space win).
    pub const fn index_runs(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::IndexRuns,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Sort-first index-major run-coalescing with an explicit flush policy: sorts
    /// each flushed frame by index before coalescing, capturing all index
    /// contiguity (not just capture-order runs) for the smallest index-major
    /// encoding. The two-stack contract is the per-frame write multiset, so the
    /// reorder is sound; `compress_frame` falls back to write-order for the rare
    /// frame whose indices are not unique.
    pub const fn index_runs_sorted(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::IndexRunsSorted,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Per-frame automatic scheme selection (exact-size costing): each flushed
    /// frame is encoded in whichever of plain/value-dict/index-runs is smallest
    /// for that frame's own content. Use when a column's frames vary in shape.
    pub const fn auto(compress_at_percent: u32, keep_hot_frames: usize) -> ColumnConfig {
        ColumnConfig {
            scheme: CompressionMode::Auto,
            compress_at_percent,
            keep_hot_frames,
        }
    }

    /// Whether this column ever compresses (i.e. is not the `None` scheme).
    pub open spec fn compresses(self) -> bool {
        !matches!(self.scheme, CompressionMode::None)
    }

    /// The flush trigger: compress when the uncompressed trail has grown to
    /// `compress_at_percent` of the live payload. Reads two running sizes the
    /// two-stack already tracks: the uncompressed diff byte count and the base
    /// payload byte count (`base_len * value_size`). Saturating throughout, so a
    /// huge trail never wraps the comparison. `None` never fires.
    ///
    /// Exec mirror of `should_flush_spec`; both compute the same predicate so the
    /// policy is testable in isolation from the storage.
    pub fn should_flush(self, uncompressed_bytes: usize, base_bytes: usize) -> (r: bool)
        ensures r == self.should_flush_spec(uncompressed_bytes as nat, base_bytes as nat),
    {
        match self.scheme {
            CompressionMode::None => false,
            // All compressing modes share the size-fraction trigger.
            CompressionMode::ValueDict | CompressionMode::IndexRuns
            | CompressionMode::IndexRunsSorted | CompressionMode::Auto => {
                // Both products fit u128: `uncompressed_bytes`/`base_bytes` are
                // usize (< 2^64 here, `global size_of usize == 8`), the percent is
                // u32 (< 2^32), so each product is < 2^96 << u128::MAX. The
                // nonlinear step bounds the variable*variable product by the
                // per-operand maxima; the constant*variable product Verus bounds
                // itself.
                let ub = uncompressed_bytes as u128;
                let bb = base_bytes as u128;
                let pc = self.compress_at_percent as u128;
                proof {
                    assert(ub <= u64::MAX as u128);
                    assert(bb <= u64::MAX as u128);
                    assert(pc <= u32::MAX as u128);
                    assert(bb * pc <= (u64::MAX as u128) * (u32::MAX as u128)) by (nonlinear_arith)
                        requires bb <= u64::MAX as u128, pc <= u32::MAX as u128;
                    assert((u64::MAX as u128) * (u32::MAX as u128) < u128::MAX) by (compute);
                }
                let lhs = ub * 100u128;
                let rhs = bb * pc;
                lhs >= rhs
            }
        }
    }

    pub open spec fn should_flush_spec(self, uncompressed_bytes: nat, base_bytes: nat) -> bool {
        match self.scheme {
            CompressionMode::None => false,
            CompressionMode::ValueDict | CompressionMode::IndexRuns
            | CompressionMode::IndexRunsSorted | CompressionMode::Auto =>
                uncompressed_bytes * 100 >= base_bytes * (self.compress_at_percent as nat),
        }
    }

    /// How many of the current `num_frames` plain frames to flush into the
    /// compressed bottom: everything except the `keep_hot_frames` most recent
    /// (the LRU floor). Saturating: never asks to flush more frames than exist,
    /// and returns `0` when the hot floor already covers the whole stack.
    pub fn frames_to_compress(self, num_frames: usize) -> (r: usize)
        ensures
            r == self.frames_to_compress_spec(num_frames as nat),
            r <= num_frames,
    {
        num_frames.saturating_sub(self.keep_hot_frames)
    }

    pub open spec fn frames_to_compress_spec(self, num_frames: nat) -> nat {
        if num_frames > self.keep_hot_frames as nat {
            (num_frames - self.keep_hot_frames as nat) as nat
        } else {
            0
        }
    }
}


/// The SEMPER_COMPRESS experiment lever: `auto` (case-insensitive) flips
/// default-constructed memcpy-restorable columns to the per-frame-adaptive
/// representation. Read once, cached. `external_body`: environment access with no
/// spec content; both constructor branches carry the same contract, so the flag is
/// correctness-invisible by construction.
#[verifier::external_body]
pub fn env_compress_default() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("SEMPER_COMPRESS")
            .map(|v| v.eq_ignore_ascii_case("auto"))
            .unwrap_or(false)
    })
}

/// Experiment/deployment lever: `SEMPER_DIFF=trail|parallel|inline` selects
/// the store kind for `VecD` columns constructed through
/// `env_diff_store_kind`. Unset or unrecognized: `Inline` (the historical
/// default). Read once, cached. `external_body` for the same reason as
/// `env_compress_default`: environment access with no spec content — every
/// kind carries the same verified contract, so the flag is
/// correctness-invisible by construction.
#[verifier::external_body]
pub fn env_diff_store_kind() -> crate::dyn_store::StoreKind {
    static KIND: std::sync::OnceLock<crate::dyn_store::StoreKind> = std::sync::OnceLock::new();
    *KIND.get_or_init(|| {
        match std::env::var("SEMPER_DIFF").as_deref().map(str::trim) {
            Ok(v) if v.eq_ignore_ascii_case("trail") => crate::dyn_store::StoreKind::Trail,
            Ok(v) if v.eq_ignore_ascii_case("parallel") => crate::dyn_store::StoreKind::Parallel,
            _ => crate::dyn_store::StoreKind::Inline,
        }
    })
}

} // verus!
