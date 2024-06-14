//! copied from https://doc.rust-lang.org/src/core/ptr/alignment.rs.html

use core::num::NonZero;
use core::{cmp, fmt, hash, mem};

/// A type storing a `usize` which is a power of two.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct PowerOfTwo(PowerOfTwoEnum);

// Alignment is `repr(usize)`, but via extra steps.
const _: () = assert!(mem::size_of::<PowerOfTwo>() == mem::size_of::<usize>());
const _: () = assert!(mem::align_of::<PowerOfTwo>() == mem::align_of::<usize>());

fn _alignment_can_be_structurally_matched(a: PowerOfTwo) -> bool {
    /// The smallest possible power-of-two, 1.
    const MIN: PowerOfTwo = PowerOfTwo(PowerOfTwoEnum::_1Shl0);
    matches!(a, MIN)
}

impl PowerOfTwo {
    /// Creates an `PowerOfTwo` from a `usize`, or returns `None` if it's
    /// not a power of two.
    ///
    /// Note that `0` is not a power of two.
    #[inline]
    pub const fn new(value: usize) -> Option<Self> {
        if value.is_power_of_two() {
            // SAFETY: Just checked it only has one bit set
            Some(unsafe { Self::new_unchecked(value) })
        } else {
            None
        }
    }

    /// Creates an `PowerOfTwo` from a `usize`, or returns `None` if it's
    /// not a power of two.
    ///
    /// Note that `0` is not a power of two.
    #[inline]
    pub const fn next_power_of_two(value: usize) -> Self {
        // SAFETY: Just forced it to only have one bit set
        unsafe { Self::new_unchecked(value.next_power_of_two()) }
    }

    /// Creates an `PowerOfTwo` from a power-of-two `usize`.
    ///
    /// # Safety
    ///
    /// `value` must be a power of two.
    ///
    /// Equivalently, it must be `1 << exp` for some `exp` in `0..usize::BITS`.
    /// It must *not* be zero.
    #[inline]
    pub const unsafe fn new_unchecked(value: usize) -> Self {
        debug_assert!(value.is_power_of_two());

        // SAFETY: By precondition, this must be a power of two, and
        // our variants encompass all possible powers of two.
        unsafe { mem::transmute::<usize, PowerOfTwo>(value) }
    }

    /// Returns the power-of-two as a [`usize`].
    #[inline]
    pub const fn as_usize(self) -> usize {
        self.0 as usize
    }

    /// Returns the power-of-two as a <code>[NonZero]<[usize]></code>.
    #[inline]
    pub const fn as_nonzero(self) -> NonZero<usize> {
        // SAFETY: All the discriminants are non-zero.
        unsafe { NonZero::new_unchecked(self.as_usize()) }
    }

    /// Returns the base-2 logarithm of the power-of-two.
    ///
    /// This is always exact, as `self` represents a power of two.
    ///
    /// # Examples
    ///
    /// ```
    /// use shashmap_core::PowerOfTwo;
    ///
    /// assert_eq!(PowerOfTwo::new(1024).unwrap().log2(), 10);
    /// ```
    #[inline]
    pub const fn log2(self) -> u32 {
        self.as_nonzero().trailing_zeros()
    }
}

impl fmt::Debug for PowerOfTwo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} (1 << {:?})", self.as_nonzero(), self.log2())
    }
}

impl TryFrom<NonZero<usize>> for PowerOfTwo {
    type Error = NonPowerOfTwoError;

    #[inline]
    fn try_from(align: NonZero<usize>) -> Result<PowerOfTwo, Self::Error> {
        align.get().try_into()
    }
}

#[non_exhaustive]
pub struct NonPowerOfTwoError();

impl TryFrom<usize> for PowerOfTwo {
    type Error = NonPowerOfTwoError;

    #[inline]
    fn try_from(align: usize) -> Result<PowerOfTwo, Self::Error> {
        Self::new(align).ok_or(NonPowerOfTwoError())
    }
}

impl From<PowerOfTwo> for NonZero<usize> {
    #[inline]
    fn from(align: PowerOfTwo) -> NonZero<usize> {
        align.as_nonzero()
    }
}

impl From<PowerOfTwo> for usize {
    #[inline]
    fn from(align: PowerOfTwo) -> usize {
        align.as_usize()
    }
}

impl cmp::Ord for PowerOfTwo {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_nonzero().get().cmp(&other.as_nonzero().get())
    }
}

impl cmp::PartialOrd for PowerOfTwo {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl hash::Hash for PowerOfTwo {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_nonzero().hash(state)
    }
}

#[cfg(target_pointer_width = "16")]
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u16)]
enum PowerOfTwoEnum {
    _1Shl0 = 1 << 0,
    _1Shl1 = 1 << 1,
    _1Shl2 = 1 << 2,
    _1Shl3 = 1 << 3,
    _1Shl4 = 1 << 4,
    _1Shl5 = 1 << 5,
    _1Shl6 = 1 << 6,
    _1Shl7 = 1 << 7,
    _1Shl8 = 1 << 8,
    _1Shl9 = 1 << 9,
    _1Shl10 = 1 << 10,
    _1Shl11 = 1 << 11,
    _1Shl12 = 1 << 12,
    _1Shl13 = 1 << 13,
    _1Shl14 = 1 << 14,
    _1Shl15 = 1 << 15,
}

#[cfg(target_pointer_width = "32")]
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u32)]
enum PowerOfTwoEnum {
    _1Shl0 = 1 << 0,
    _1Shl1 = 1 << 1,
    _1Shl2 = 1 << 2,
    _1Shl3 = 1 << 3,
    _1Shl4 = 1 << 4,
    _1Shl5 = 1 << 5,
    _1Shl6 = 1 << 6,
    _1Shl7 = 1 << 7,
    _1Shl8 = 1 << 8,
    _1Shl9 = 1 << 9,
    _1Shl10 = 1 << 10,
    _1Shl11 = 1 << 11,
    _1Shl12 = 1 << 12,
    _1Shl13 = 1 << 13,
    _1Shl14 = 1 << 14,
    _1Shl15 = 1 << 15,
    _1Shl16 = 1 << 16,
    _1Shl17 = 1 << 17,
    _1Shl18 = 1 << 18,
    _1Shl19 = 1 << 19,
    _1Shl20 = 1 << 20,
    _1Shl21 = 1 << 21,
    _1Shl22 = 1 << 22,
    _1Shl23 = 1 << 23,
    _1Shl24 = 1 << 24,
    _1Shl25 = 1 << 25,
    _1Shl26 = 1 << 26,
    _1Shl27 = 1 << 27,
    _1Shl28 = 1 << 28,
    _1Shl29 = 1 << 29,
    _1Shl30 = 1 << 30,
    _1Shl31 = 1 << 31,
}

#[cfg(target_pointer_width = "64")]
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(u64)]
enum PowerOfTwoEnum {
    _1Shl0 = 1 << 0,
    _1Shl1 = 1 << 1,
    _1Shl2 = 1 << 2,
    _1Shl3 = 1 << 3,
    _1Shl4 = 1 << 4,
    _1Shl5 = 1 << 5,
    _1Shl6 = 1 << 6,
    _1Shl7 = 1 << 7,
    _1Shl8 = 1 << 8,
    _1Shl9 = 1 << 9,
    _1Shl10 = 1 << 10,
    _1Shl11 = 1 << 11,
    _1Shl12 = 1 << 12,
    _1Shl13 = 1 << 13,
    _1Shl14 = 1 << 14,
    _1Shl15 = 1 << 15,
    _1Shl16 = 1 << 16,
    _1Shl17 = 1 << 17,
    _1Shl18 = 1 << 18,
    _1Shl19 = 1 << 19,
    _1Shl20 = 1 << 20,
    _1Shl21 = 1 << 21,
    _1Shl22 = 1 << 22,
    _1Shl23 = 1 << 23,
    _1Shl24 = 1 << 24,
    _1Shl25 = 1 << 25,
    _1Shl26 = 1 << 26,
    _1Shl27 = 1 << 27,
    _1Shl28 = 1 << 28,
    _1Shl29 = 1 << 29,
    _1Shl30 = 1 << 30,
    _1Shl31 = 1 << 31,
    _1Shl32 = 1 << 32,
    _1Shl33 = 1 << 33,
    _1Shl34 = 1 << 34,
    _1Shl35 = 1 << 35,
    _1Shl36 = 1 << 36,
    _1Shl37 = 1 << 37,
    _1Shl38 = 1 << 38,
    _1Shl39 = 1 << 39,
    _1Shl40 = 1 << 40,
    _1Shl41 = 1 << 41,
    _1Shl42 = 1 << 42,
    _1Shl43 = 1 << 43,
    _1Shl44 = 1 << 44,
    _1Shl45 = 1 << 45,
    _1Shl46 = 1 << 46,
    _1Shl47 = 1 << 47,
    _1Shl48 = 1 << 48,
    _1Shl49 = 1 << 49,
    _1Shl50 = 1 << 50,
    _1Shl51 = 1 << 51,
    _1Shl52 = 1 << 52,
    _1Shl53 = 1 << 53,
    _1Shl54 = 1 << 54,
    _1Shl55 = 1 << 55,
    _1Shl56 = 1 << 56,
    _1Shl57 = 1 << 57,
    _1Shl58 = 1 << 58,
    _1Shl59 = 1 << 59,
    _1Shl60 = 1 << 60,
    _1Shl61 = 1 << 61,
    _1Shl62 = 1 << 62,
    _1Shl63 = 1 << 63,
}
