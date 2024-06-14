#![no_std]
extern crate alloc;

use core::{
    fmt, mem,
    ops::{Deref, DerefMut},
};

use hashbrown::{raw::RawTable, TryReserveError};
use lock_api::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RawRwLock, RwLock, RwLockReadGuard,
    RwLockWriteGuard,
};

mod power_of_two;
pub use power_of_two::PowerOfTwo;

mod padded_slice;
use padded_slice::PowTwoPaddedSlice;

// Constant for h2 function that grabing the top 7 bits of the hash.
// taken from hashbrown
const MIN_HASH_LEN: usize = if mem::size_of::<usize>() < mem::size_of::<u64>() {
    mem::size_of::<usize>()
} else {
    mem::size_of::<u64>()
};

// hashbrown uses the top7 bits of the hash for control data
// and uses the bottom bits for the bucket.
// thus, we will take the middle bits for the shard index.
fn h3(hash: u64, shift: u32) -> usize {
    // remove the top7 bits. While the hash is normally a full 64-bit
    // value, some hash functions (such as FxHash) produce a usize result
    // instead, which means that the top 32 bits are 0 on 32-bit platforms.
    // So we use MIN_HASH_LEN constant to handle this.
    let removed_top7 = hash << (64 - MIN_HASH_LEN * 8 + 7);
    (removed_top7 >> shift) as usize
}

fn capacity_per_shard(shard_count: PowerOfTwo, capacity: usize) -> usize {
    let ctz = shard_count.as_nonzero().trailing_zeros();

    // because it's a power of two, these are equivalent to
    // let mut capacity_per_shard = capacity / shard_count.as_nonzero();
    // let remainder = capacity % shard_count.as_nonzero();
    let mut capacity_per_shard = capacity >> ctz;
    let remainder = capacity & (shard_count.as_usize() - 1);

    if remainder > 0 {
        // for remainder to be > 0, the scnz must be > 1.
        // capacity_per_shard must therefore be at most usize::MAX / 2.
        // usize::MAX/2+1 cannot overflow.
        capacity_per_shard = unsafe { capacity_per_shard.unchecked_add(1) };
    }

    capacity_per_shard
}

pub struct RawShardedHashTable<R, T> {
    shards: PowTwoPaddedSlice<RwLock<R, RawTable<T>>>,
    shift: u32,
}

impl<R: RawRwLock, T> RawShardedHashTable<R, T> {
    pub fn new(shard_count: PowerOfTwo) -> Self {
        Self {
            shards: PowTwoPaddedSlice::default(shard_count),
            shift: u64::BITS - shard_count.log2(),
        }
    }

    pub fn try_new(shard_count: PowerOfTwo) -> Result<Self, TryReserveError> {
        Ok(Self {
            shards: PowTwoPaddedSlice::try_default(shard_count)
                .map_err(|_| TryReserveError::CapacityOverflow)?,
            shift: u64::BITS - shard_count.log2(),
        })
    }

    pub fn with_capacity(shard_count: PowerOfTwo, capacity: usize) -> Self {
        let capacity_per_shard = capacity_per_shard(shard_count, capacity);
        let mut this = Self::new(shard_count);
        this.shards
            .iter_mut()
            .for_each(|s| *s.get_mut() = RawTable::with_capacity(capacity_per_shard));
        this
    }

    pub fn try_with_capacity(
        shard_count: PowerOfTwo,
        capacity: usize,
    ) -> Result<Self, TryReserveError> {
        let capacity_per_shard = capacity_per_shard(shard_count, capacity);
        let mut this = Self::try_new(shard_count)?;
        this.shards.iter_mut().try_for_each(|s| {
            *s.get_mut() = RawTable::try_with_capacity(capacity_per_shard)?;
            Result::<(), TryReserveError>::Ok(())
        })?;
        Ok(this)
    }
}

impl<R, T> RawShardedHashTable<R, T> {
    #[inline]
    pub fn determine_shard(&self, hash: u64) -> usize {
        let shard = h3(hash, self.shift);

        if shard >= self.shards.len().as_usize() {
            #[cfg(debug_assertions)]
            panic!("shard index out of bounds of the shards list");

            #[cfg(not(debug_assertions))]
            unsafe {
                core::hint::unreachable_unchecked()
            }
        }

        shard
    }

    #[inline]
    pub fn shard(&self, hash: u64) -> &RwLock<R, RawTable<T>> {
        &self.shards[self.determine_shard(hash)]
    }
}

impl<R: RawRwLock, T> RawShardedHashTable<R, T> {
    #[inline]
    pub fn shard_mut(&mut self, hash: u64) -> &mut RawTable<T> {
        let shard = self.determine_shard(hash);
        self.shards[shard].get_mut()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|x| x.read().is_empty())
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.shards.iter().map(|x| x.read().len()).sum()
    }

    /// Gets a reference to an element in the table.
    #[inline]
    pub fn get(&self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<ShardReadGuard<'_, R, T>> {
        Some(ShardReadGuard {
            map: RwLockReadGuard::try_map(self.shard(hash).read(), |s| s.get(hash, eq)).ok()?,
        })
    }

    /// Gets a mutable reference to an element in the table.
    #[inline]
    pub fn get_mut(
        &self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
    ) -> Option<ShardWriteGuard<'_, R, T>> {
        Some(ShardWriteGuard {
            map: RwLockWriteGuard::try_map(self.shard(hash).write(), |s| s.get_mut(hash, eq))
                .ok()?,
        })
    }
}

pub struct ShardReadGuard<'a, R: RawRwLock, T: ?Sized> {
    map: MappedRwLockReadGuard<'a, R, T>,
}
impl<'a, R: RawRwLock, T> ShardReadGuard<'a, R, T> {
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> ShardReadGuard<'a, R, U>
    where
        F: FnOnce(&T) -> &U,
    {
        ShardReadGuard {
            map: MappedRwLockReadGuard::map(s.map, f),
        }
    }

    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<ShardReadGuard<'a, R, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        MappedRwLockReadGuard::try_map(s.map, f)
            .map(|map| ShardReadGuard { map })
            .map_err(|map| ShardReadGuard { map })
    }
}

impl<R: RawRwLock, T> Deref for ShardReadGuard<'_, R, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<R: RawRwLock, T: fmt::Debug> fmt::Debug for ShardReadGuard<'_, R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(f)
    }
}


pub struct ShardWriteGuard<'a, R: RawRwLock, T: ?Sized> {
    map: MappedRwLockWriteGuard<'a, R, T>,
}

impl<'a, R: RawRwLock, T> ShardWriteGuard<'a, R, T> {
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> ShardWriteGuard<'a, R, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        ShardWriteGuard {
            map: MappedRwLockWriteGuard::map(s.map, f),
        }
    }

    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<ShardWriteGuard<'a, R, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        MappedRwLockWriteGuard::try_map(s.map, f)
            .map(|map| ShardWriteGuard { map })
            .map_err(|map| ShardWriteGuard { map })
    }
}

impl<R: RawRwLock, T> Deref for ShardWriteGuard<'_, R, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<R: RawRwLock, T> DerefMut for ShardWriteGuard<'_, R, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl<R: RawRwLock, T: fmt::Debug> fmt::Debug for ShardWriteGuard<'_, R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(f)
    }
}
