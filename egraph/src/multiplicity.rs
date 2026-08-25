// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Multiplicities for AC multiset nodes.
//!
//! The multiplicity width is selected by [`crate::config::EGraphConfig::M`] and is an axis
//! *independent* of the id width: a 63-bit e-graph does not oblige a 64-bit
//! multiplicity, and a 31-bit e-graph may still want one. Three widths are
//! provided — [`Multiplicity16`], [`Multiplicity`], [`Multiplicity64`] — all
//! implementing [`MultiplicityLike`].
//!
//! ## Why the width is a parameter rather than a fixed `u32`
//!
//! A multiplicity counts occurrences of one child within one AC node, so its
//! domain is that node's child count. `EGraph::for_each_child`'s own safety cap
//! (`1 + 64 * node_count()`) puts that at 64·N — already 2^37 for a 31-bit
//! e-graph, i.e. wider than `u32`. The previous contract additionally required
//! `From<u32> + Into<u32>`, which made any width above 32 bits *unimplementable*
//! because every generic read went through a lossy `u32`.
//!
//! ## Conversions are checked in both directions
//!
//! Surface multiplicity literals are parsed as `u64` and stay `u64` through
//! resolution ([`crate::resolve::ResolvedMultExpr::Lit`]); they are narrowed to
//! the configured width only at `Cfg`-generic use sites, via
//! [`MultiplicityLike::try_from_u64`]. Narrowing with an unchecked `as` is what
//! made `x:4294967297` match multiplicity 1 and `(mult x 4294967296)` emit zero
//! copies. Summation goes through [`MultiplicityLike::checked_add`] so a wrap
//! cannot silently produce a multiplicity of 0, which would violate the
//! positivity invariant the multiset module asserts.

use core::hash::Hash;

/// A multiplicity width: a count of occurrences within one AC multiset node.
///
/// Implementors are newtypes over an unsigned primitive. Every supported width
/// fits in `u64`, so [`Self::to_u64`] is total and lossless; the reverse
/// direction is fallible.
pub trait MultiplicityLike:
    Copy + Clone + Eq + Ord + Hash + core::fmt::Debug + core::fmt::Display + Default
{
    /// Multiplicity zero. Not a legal stored multiplicity — the multiset
    /// representation is duplicate-free with every entry `>= ONE` — but needed
    /// as the identity for summation and as an "unbound" marker.
    const ZERO: Self;
    /// Multiplicity one: a child occurring exactly once.
    const ONE: Self;
    /// Largest representable multiplicity in this width.
    const MAX: Self;

    /// Widen to the surface width. Total and lossless.
    fn to_u64(self) -> u64;

    /// Narrow from the surface width, or `None` if `n` exceeds [`Self::MAX`].
    fn try_from_u64(n: u64) -> Option<Self>;

    /// Sum, or `None` on overflow of this width.
    fn checked_add(self, other: Self) -> Option<Self>;

    /// Difference, clamped at [`Self::ZERO`].
    fn saturating_sub(self, other: Self) -> Self;

    /// Reduce modulo a small algebraic order: the nilpotent count clamp
    /// (`x∘x∘…∘x = e` after `order` copies) and self-inverse cancellation
    /// (`order = 2`).
    ///
    /// Total at every width: the result is below `order`, hence below 256, which
    /// even the narrowest supported width represents. Panics on `order == 0`,
    /// like the `%` it stands for — no algebraic order is zero.
    fn rem_order(self, order: u8) -> Self {
        Self::try_from_u64(self.to_u64() % u64::from(order))
            .expect("a remainder mod a u8 is below 256 and fits every supported width")
    }

    /// Widen to `usize` for cost/size arithmetic. Saturates rather than
    /// truncating, which matters only for a 64-bit multiplicity on a 32-bit
    /// target — a configuration this crate does not otherwise support.
    fn to_usize(self) -> usize {
        usize::try_from(self.to_u64()).unwrap_or(usize::MAX)
    }
}

macro_rules! define_multiplicity {
    ($name:ident, $w:ty, $bits:literal) => {
        #[doc = concat!("AC multiplicity backed by `", stringify!($w), "` (", $bits, " bits).")]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
        #[repr(transparent)]
        pub struct $name(pub $w);

        impl From<$w> for $name {
            fn from(v: $w) -> Self {
                Self(v)
            }
        }
        impl From<$name> for $w {
            fn from(m: $name) -> Self {
                m.0
            }
        }
        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}", self.0)
            }
        }
        impl MultiplicityLike for $name {
            const ZERO: Self = Self(0);
            const ONE: Self = Self(1);
            const MAX: Self = Self(<$w>::MAX);

            #[inline]
            fn to_u64(self) -> u64 {
                u64::from(self.0)
            }
            #[inline]
            fn try_from_u64(n: u64) -> Option<Self> {
                <$w>::try_from(n).ok().map(Self)
            }
            #[inline]
            fn checked_add(self, other: Self) -> Option<Self> {
                self.0.checked_add(other.0).map(Self)
            }
            #[inline]
            fn saturating_sub(self, other: Self) -> Self {
                Self(self.0.saturating_sub(other.0))
            }
        }
    };
}

define_multiplicity!(Multiplicity16, u16, "16");
define_multiplicity!(Multiplicity, u32, "32");
define_multiplicity!(Multiplicity64, u64, "64");

#[cfg(test)]
mod tests {
    use super::*;

    /// Narrowing from the surface width rejects what it cannot represent
    /// instead of truncating. These are the exact values that used to alias:
    /// `2^32 + 1` truncated to 1, and `2^32` truncated to 0.
    #[test]
    fn try_from_u64_rejects_out_of_range() {
        assert_eq!(Multiplicity::try_from_u64(4_294_967_297), None);
        assert_eq!(Multiplicity::try_from_u64(4_294_967_296), None);
        assert_eq!(
            Multiplicity::try_from_u64(4_294_967_295),
            Some(Multiplicity(u32::MAX))
        );
        assert_eq!(Multiplicity16::try_from_u64(65_536), None);
        assert_eq!(
            Multiplicity16::try_from_u64(65_535),
            Some(Multiplicity16(u16::MAX))
        );
        // The widest configuration accepts the whole surface range.
        assert_eq!(
            Multiplicity64::try_from_u64(u64::MAX),
            Some(Multiplicity64(u64::MAX))
        );
    }

    /// `to_u64` round-trips every value the width can hold, so comparing a
    /// stored multiplicity against a surface literal is exact.
    #[test]
    fn to_u64_round_trips() {
        for m in [Multiplicity::ZERO, Multiplicity::ONE, Multiplicity::MAX] {
            assert_eq!(Multiplicity::try_from_u64(m.to_u64()), Some(m));
        }
        assert_eq!(Multiplicity16::MAX.to_u64(), 65_535);
        assert_eq!(Multiplicity64::MAX.to_u64(), u64::MAX);
    }

    /// Summation reports overflow rather than wrapping to a small (or zero)
    /// multiplicity, which would violate the multiset positivity invariant.
    #[test]
    fn checked_add_detects_overflow_at_each_width() {
        assert_eq!(
            Multiplicity16::MAX.checked_add(Multiplicity16::ONE),
            None,
            "u16 multiplicity must report overflow, not wrap to 0"
        );
        assert_eq!(Multiplicity::MAX.checked_add(Multiplicity::ONE), None);
        assert_eq!(Multiplicity64::MAX.checked_add(Multiplicity64::ONE), None);
        assert_eq!(
            Multiplicity::ONE.checked_add(Multiplicity::ONE),
            Some(Multiplicity(2))
        );
        // The narrower width overflows where the wider one does not.
        let n = u64::from(u16::MAX);
        assert_eq!(
            Multiplicity16::try_from_u64(n)
                .unwrap()
                .checked_add(Multiplicity16::ONE),
            None
        );
        assert_eq!(
            Multiplicity::try_from_u64(n)
                .unwrap()
                .checked_add(Multiplicity::ONE),
            Some(Multiplicity(65_536))
        );
    }

    /// Subtraction clamps, matching `multiset_subtract_into`'s behaviour.
    #[test]
    fn saturating_sub_clamps_at_zero() {
        assert_eq!(
            Multiplicity::ONE.saturating_sub(Multiplicity(5)),
            Multiplicity::ZERO
        );
        assert_eq!(
            Multiplicity(5).saturating_sub(Multiplicity(2)),
            Multiplicity(3)
        );
    }

    /// The stored representation is exactly the backing primitive, so making
    /// the width a parameter costs nothing per AC child.
    #[test]
    fn representation_is_the_backing_primitive() {
        assert_eq!(size_of::<Multiplicity16>(), size_of::<u16>());
        assert_eq!(size_of::<Multiplicity>(), size_of::<u32>());
        assert_eq!(size_of::<Multiplicity64>(), size_of::<u64>());
    }
}
