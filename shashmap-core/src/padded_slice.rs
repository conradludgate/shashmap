use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use alloc::{boxed::Box, collections::TryReserveError, vec::Vec};
use crossbeam_utils::CachePadded;

use crate::PowerOfTwo;

/// a boxed slice that can only be a power of two length.
/// all entries are also cache-padded.
pub(crate) struct PowTwoPaddedSlice<T> {
    ptr: NonNull<CachePadded<T>>,
    len: PowerOfTwo,
}

impl<T> FromIterator<T> for PowTwoPaddedSlice<T> {
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let b: Box<[CachePadded<T>]> = iter.into_iter().map(CachePadded::new).collect();
        let len = PowerOfTwo::new(b.len()).unwrap();

        // box pointers are non-null. citing the docs:
        // > Box<T> values will always be fully aligned, non-null pointers.
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(b).cast()) };

        Self { ptr, len }
    }
}

impl<T> Drop for PowTwoPaddedSlice<T> {
    fn drop(&mut self) {
        let _b = unsafe {
            Box::from_raw(core::ptr::slice_from_raw_parts_mut(
                self.ptr.as_ptr(),
                self.len.as_usize(),
            ))
        };
    }
}

impl<T: Default> PowTwoPaddedSlice<T> {
    pub(crate) fn try_default(len: PowerOfTwo) -> Result<Self, TryReserveError> {
        let mut v: Vec<CachePadded<T>> = Vec::new();
        v.try_reserve_exact(len.as_usize())?;
        v.resize_with(len.as_usize(), CachePadded::<T>::default);

        let b = v.into_boxed_slice();

        // box pointers are non-null. citing the docs:
        // > Box<T> values will always be fully aligned, non-null pointers.
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(b).cast()) };

        Ok(Self { ptr, len })
    }

    pub(crate) fn default(len: PowerOfTwo) -> Self {
        let mut v: Vec<CachePadded<T>> = Vec::new();
        v.reserve_exact(len.as_usize());
        v.resize_with(len.as_usize(), CachePadded::<T>::default);

        let b = v.into_boxed_slice();

        // box pointers are non-null. citing the docs:
        // > Box<T> values will always be fully aligned, non-null pointers.
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(b).cast()) };

        Self { ptr, len }
    }
}

impl<T> PowTwoPaddedSlice<T> {
    pub(crate) fn len(&self) -> PowerOfTwo {
        self.len
    }
}

impl<T> Deref for PowTwoPaddedSlice<T> {
    type Target = [CachePadded<T>];

    fn deref(&self) -> &Self::Target {
        unsafe {
            &*core::ptr::slice_from_raw_parts(self.ptr.as_ptr().cast_const(), self.len.as_usize())
        }
    }
}

impl<T> DerefMut for PowTwoPaddedSlice<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *core::ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len.as_usize()) }
    }
}
