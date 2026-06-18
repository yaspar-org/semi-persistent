// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
/// A type with a stored representation carrying one control bit (tag).
///
/// `Self` is the clean user-facing value. `Self::Repr` is the internal
/// representation that carries a tag bit alongside the value.
///
/// Consumers decide what the tag means:
/// - `InlineStore` (VecI): tag = "captured" (modified since last mark)
/// - `Opt<T>`: tag = "None" (absent value)
///
/// Implementors choose how to represent the tag:
/// - **Bit-stealing:** `Repr` reuses a bit from the value (e.g. DenseId MSB).
/// - **Bool pair:** `Repr = (bool, T)`.
///
/// # Copy discipline
///
/// `Tagged` requires `Copy` (not just `Clone`) because it is used by
/// `InlineStore`, the hot-path storage backend where the tag bit is packed
/// directly into the value representation. All types stored this way —
/// node types, edge types, list nodes — are pool indices and bitfields,
/// not owners. Bitwise copy is the whole story; `Clone` would misleadingly
/// suggest deep duplication. This bound also prevents accidentally
/// introducing a heap-owning field into a performance-critical type.
pub trait Tagged: Copy {
    type Repr: Copy;

    /// Clean value → repr (tag = false).
    fn into_repr(self) -> Self::Repr;

    /// Repr → clean value (strips the tag).
    fn from_repr(r: &Self::Repr) -> Self;

    /// Read the tag.
    fn tag(r: &Self::Repr) -> bool;

    /// Set the tag.
    fn set_tag(r: &mut Self::Repr);

    /// Clear the tag.
    fn clear_tag(r: &mut Self::Repr);
}

// ---------------------------------------------------------------------------
// Opt<T> — nullable wrapper using the tag bit
// ---------------------------------------------------------------------------

/// `Opt<T>` does NOT implement `Tagged`. This is intentional: if it did,
/// `Opt<T>` could be stored directly in a `VecI`, and VecI would steal the
/// same tag bit that `Opt` uses for None encoding — corrupting both.
///
/// Instead, `Opt<T>` must only appear as a field inside a struct that
/// implements `Tagged` by delegating to a *different* field. The struct
/// provides the capture bit; `Opt` provides the option bit. They live on
/// separate fields, so no collision.
#[derive(Clone, Copy)]
pub struct Opt<T: Tagged>(T::Repr);

impl<T: Tagged + Default> Opt<T> {
    pub fn none() -> Self {
        let mut r = T::default().into_repr();
        T::set_tag(&mut r);
        Opt(r)
    }
}

impl<T: Tagged + Default> Default for Opt<T> {
    fn default() -> Self {
        Opt::none()
    }
}

impl<T: Tagged> Opt<T> {
    pub fn some(val: T) -> Self {
        Opt(val.into_repr())
    }

    pub fn get(&self) -> Option<T> {
        if T::tag(&self.0) {
            None
        } else {
            Some(T::from_repr(&self.0))
        }
    }

    pub fn is_none(&self) -> bool {
        T::tag(&self.0)
    }

    pub fn is_some(&self) -> bool {
        !T::tag(&self.0)
    }

    /// Consume into the raw repr, for embedding in struct Reprs.
    pub fn into_raw(self) -> T::Repr {
        self.0
    }

    /// Construct from a raw repr.
    pub fn from_raw(r: T::Repr) -> Self {
        Opt(r)
    }
}

impl<T: Tagged + core::fmt::Debug> core::fmt::Debug for Opt<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.get() {
            Some(v) => write!(f, "Some({:?})", v),
            None => write!(f, "None"),
        }
    }
}

// ---------------------------------------------------------------------------
// Primitive impls — use (bool, T) pair
// ---------------------------------------------------------------------------

macro_rules! impl_tagged_pair {
    ($T:ty) => {
        impl Tagged for $T {
            type Repr = (bool, $T);

            #[inline(always)]
            fn into_repr(self) -> Self::Repr {
                (false, self)
            }
            #[inline(always)]
            fn from_repr(r: &Self::Repr) -> Self {
                r.1
            }
            #[inline(always)]
            fn tag(r: &Self::Repr) -> bool {
                r.0
            }
            #[inline(always)]
            fn set_tag(r: &mut Self::Repr) {
                r.0 = true;
            }
            #[inline(always)]
            fn clear_tag(r: &mut Self::Repr) {
                r.0 = false;
            }
        }
    };
}

impl_tagged_pair!(u8);
impl_tagged_pair!(u16);
impl_tagged_pair!(u32);
impl_tagged_pair!(u64);
impl_tagged_pair!(usize);

// ---------------------------------------------------------------------------
// Pair: tag lives in first element's Repr
// ---------------------------------------------------------------------------

impl<A: Tagged, B: Copy> Tagged for (A, B) {
    type Repr = (A::Repr, B);

    #[inline(always)]
    fn into_repr(self) -> Self::Repr {
        (self.0.into_repr(), self.1)
    }
    #[inline(always)]
    fn from_repr(r: &Self::Repr) -> Self {
        (A::from_repr(&r.0), r.1)
    }
    #[inline(always)]
    fn tag(r: &Self::Repr) -> bool {
        A::tag(&r.0)
    }
    #[inline(always)]
    fn set_tag(r: &mut Self::Repr) {
        A::set_tag(&mut r.0);
    }
    #[inline(always)]
    fn clear_tag(r: &mut Self::Repr) {
        A::clear_tag(&mut r.0);
    }
}

// ---------------------------------------------------------------------------
// BoolTagged<T> — fallback for types without a spare bit
// ---------------------------------------------------------------------------

/// A `(bool, T)` storage form for types that cannot bit-pack.
#[derive(Clone, Debug)]
pub struct BoolTagged<T> {
    pub tagged: bool,
    pub value: T,
}

impl<T: Clone> BoolTagged<T> {
    pub fn new(value: T) -> Self {
        Self {
            tagged: false,
            value,
        }
    }
}
