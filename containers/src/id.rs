// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Distinct identifier types with bit-packed `Markable` storage.
//!
//! [`define_id31!`] and [`define_id63!`] stamp out `#[repr(transparent)]`
//! newtypes around `u32` / `u64` with the MSB reserved for the capture flag
//! in [`vec::Inline`](crate::containers::Inline).
//!
//! Each invocation produces a **distinct** type.
//!
//! Range-checked conversions:
//! - `T::new(raw)` — panics if MSB is set
//! - `T::raw()` — always returns the clean value
//! - `From<T> for u32/u64` — infallible
//! - `TryFrom<u32/u64> for T` — returns `Err` if MSB is set

/// Error returned by `TryFrom` for ID types when the MSB is set.
#[derive(Debug, Clone)]
pub struct IdRangeError {
    pub type_name: &'static str,
}

impl core::fmt::Display for IdRangeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{}: value exceeds range (MSB must be zero)",
            self.type_name
        )
    }
}

impl std::error::Error for IdRangeError {}

/// 7-bit ID: `u8` backing, bit 7 reserved for capture flag.
#[macro_export]
macro_rules! define_id7 {
    ($(#[$meta:meta])* $vis:vis struct $Name:ident / $Stored:ident, $prefix:expr;) => {
        $crate::define_id_impl!(@impl $(#[$meta])* $vis, $Name, $Stored, $prefix, u8, 0x7F_u8, 0x80_u8);
    };
}

/// 15-bit ID: `u16` backing, bit 15 reserved for capture flag.
#[macro_export]
macro_rules! define_id15 {
    ($(#[$meta:meta])* $vis:vis struct $Name:ident / $Stored:ident, $prefix:expr;) => {
        $crate::define_id_impl!(@impl $(#[$meta])* $vis, $Name, $Stored, $prefix, u16, 0x7FFF_u16, 0x8000_u16);
    };
}

/// 31-bit ID: `u32` backing, bit 31 reserved for capture flag.
#[macro_export]
macro_rules! define_id31 {
    ($(#[$meta:meta])* $vis:vis struct $Name:ident / $Stored:ident, $prefix:expr;) => {
        $crate::define_id_impl!(@impl $(#[$meta])* $vis, $Name, $Stored, $prefix, u32, 0x7FFF_FFFF, 0x8000_0000);
    };
}

/// 63-bit ID: `u64` backing, bit 63 reserved for capture flag.
#[macro_export]
macro_rules! define_id63 {
    ($(#[$meta:meta])* $vis:vis struct $Name:ident / $Stored:ident, $prefix:expr;) => {
        $crate::define_id_impl!(@impl $(#[$meta])* $vis, $Name, $Stored, $prefix, u64, 0x7FFF_FFFF_FFFF_FFFF_u64, 0x8000_0000_0000_0000_u64);
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! define_id_impl {
    (@impl $(#[$meta:meta])* $vis:vis, $Name:ident, $Stored:ident, $prefix:expr, $Int:ty, $MASK:expr, $CAP:expr) => {
        $(#[$meta])*
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        $vis struct $Name($Int);

        impl PartialEq for $Name {
            #[inline(always)]
            fn eq(&self, other: &Self) -> bool { (self.0 & $MASK) == (other.0 & $MASK) }
        }
        impl Eq for $Name {}

        impl PartialOrd for $Name {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $Name {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                (self.0 & $MASK).cmp(&(other.0 & $MASK))
            }
        }

        impl core::hash::Hash for $Name {
            #[inline(always)]
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                (self.0 & $MASK).hash(state);
            }
        }

        #[derive(Clone, Copy)]
        #[repr(transparent)]
        $vis struct $Stored($Int);

        impl $Name {
            pub const MAX_RAW: $Int = $MASK;

            /// Sentinel value with MSB set. Not a valid ID.
            /// Compares unequal to all valid IDs.
            pub const INVALID: Self = Self($CAP);

            #[inline]
            pub fn new(raw: $Int) -> Self {
                assert!(raw <= Self::MAX_RAW, concat!(stringify!($Name), " exceeds range"));
                Self(raw)
            }

            #[inline(always)]
            pub fn raw(self) -> $Int { self.0 }

            /// Whether this is a valid (non-sentinel) ID.
            #[inline(always)]
            pub fn is_valid(self) -> bool { self.0 <= Self::MAX_RAW }

            /// Construct with an arbitrary raw value, including MSB set.
            /// Only available in tests.
            #[cfg(test)]
            pub fn from_raw_unchecked(raw: $Int) -> Self { Self(raw) }
        }

        impl From<$Name> for $Int {
            #[inline(always)]
            fn from(id: $Name) -> $Int { id.0 }
        }

        impl TryFrom<$Int> for $Name {
            type Error = $crate::id::IdRangeError;
            #[inline]
            fn try_from(raw: $Int) -> Result<Self, Self::Error> {
                if raw <= Self::MAX_RAW {
                    Ok(Self(raw))
                } else {
                    Err($crate::id::IdRangeError { type_name: stringify!($Name) })
                }
            }
        }

        impl $crate::dense_id::DenseId for $Name {
            type Index = $Int;

            #[inline(always)]
            fn to_usize(self) -> usize { self.0 as usize }

            #[inline(always)]
            fn from_usize(n: usize) -> Self { Self::new(n as $Int) }
        }

        impl $crate::IndexLike for $Name {
            const MIN: Self = Self(0);
            const MAX: Self = Self($MASK);
            #[inline(always)]
            fn as_usize(self) -> usize { (self.0 & $MASK) as usize }
            #[inline(always)]
            fn try_from_usize(n: usize) -> Option<Self> {
                if (n as $Int) <= $MASK { Some(Self(n as $Int)) } else { None }
            }
        }

        impl $crate::Tagged for $Name {
            type Repr = $Stored;
            #[inline(always)]
            fn into_repr(self) -> $Stored { $Stored(self.0) }
            #[inline(always)]
            fn from_repr(stored: &$Stored) -> Self { Self(stored.0 & $MASK) }
            #[inline(always)]
            fn tag(stored: &$Stored) -> bool { stored.0 & $CAP != 0 }
            #[inline(always)]
            fn set_tag(stored: &mut $Stored) { stored.0 |= $CAP; }
            #[inline(always)]
            fn clear_tag(stored: &mut $Stored) { stored.0 &= $MASK; }
        }

        impl ::core::default::Default for $Name {
            fn default() -> Self { Self(0) }
        }

        impl ::core::fmt::Debug for $Name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }

        impl ::core::fmt::Display for $Name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, "{}{}", $prefix, self.0)
            }
        }
    };
}

// --- Concrete ID types ---
// These are used by containers tests. Egraph-specific IDs are in the egraph crate.

define_id31! {
    /// A 31-bit sparse set key.
    pub struct SparseSetId / StoredSparseSetId, "s";
}

define_id31! {
    /// A 31-bit use-list identifier (indexes into ListArena heads).
    pub struct UseListId / StoredUseListId, "ul";
}

define_id31! {
    /// A 31-bit use-list node identifier (indexes into ListArena nodes).
    pub struct UseNodeId / StoredUseNodeId, "un";
}
