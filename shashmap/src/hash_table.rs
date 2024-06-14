use core::fmt;
use std::thread::available_parallelism;

use hashbrown::raw::{Bucket, InsertSlot, RawTable};
use lock_api::RwLockWriteGuard;
use shashmap_core::PowerOfTwo;

use crate::{RawRwLock, RawShardedHashTable, ShardReadGuard, ShardWriteGuard};

pub struct ShardedHashTable<T> {
    raw_table: RawShardedHashTable<T>,
}

impl<T> ShardedHashTable<T> {
    pub fn new() -> Self {
        ShardedHashTable {
            raw_table: RawShardedHashTable::new(PowerOfTwo::next_power_of_two(
                available_parallelism().map_or(1, |nz| nz.get()) * 4,
            )),
        }
    }

    pub fn find(&self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<ShardReadGuard<'_, T>> {
        self.raw_table.get(hash, eq)
    }

    pub fn find_mut(
        &self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
    ) -> Option<ShardWriteGuard<'_, T>> {
        self.raw_table.get_mut(hash, eq)
    }

    /// Inserts an element into the `HashTable` with the given hash value, but
    /// without checking whether an equivalent element already exists within the
    /// table.
    ///
    /// `hasher` is called if entries need to be moved or copied to a new table.
    /// This must return the same hash value that each entry was inserted with.
    ///
    /// # Examples
    ///
    /// ```
    /// use shashmap::hash_table::ShardedHashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let v = ShardedHashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// v.insert_unique(hasher(&1), 1, hasher);
    /// ```
    pub fn insert_unique(
        &self,
        hash: u64,
        value: T,
        hasher: impl Fn(&T) -> u64,
    ) -> OccupiedEntry<'_, T> {
        let mut shard = self.raw_table.shard(hash).write();
        let bucket = shard.insert(hash, value, hasher);
        OccupiedEntry {
            hash,
            bucket,
            table: shard,
        }
    }

    /// Returns an `OccupiedEntry` for an entry in the table with the given hash
    /// and which satisfies the equality function passed.
    ///
    /// This can be used to remove the entry from the table. Call
    /// [`HashTable::entry`] instead if you wish to insert an entry if the
    /// lookup fails.
    ///
    /// This method will call `eq` for all entries with the given hash, but may
    /// also call it for entries with a different hash. `eq` should only return
    /// true for the desired entry, at which point the search is stopped.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// table.insert_unique(hasher(&1), (1, "a"), |val| hasher(&val.0));
    /// if let Ok(entry) = table.find_entry(hasher(&1), |val| val.0 == 1) {
    ///     entry.remove();
    /// }
    /// assert_eq!(table.find(hasher(&1), |val| val.0 == 1), None);
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn find_entry(
        &self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
    ) -> Option<OccupiedEntry<'_, T>> {
        let shard = self.raw_table.shard(hash).write();
        shard.find(hash, eq).map(|bucket| OccupiedEntry {
            hash,
            bucket,
            table: shard,
        })
    }

    /// Returns an `Entry` for an entry in the table with the given hash
    /// and which satisfies the equality function passed.
    ///
    /// This can be used to remove the entry from the table, or insert a new
    /// entry with the given hash if one doesn't already exist.
    ///
    /// This method will call `eq` for all entries with the given hash, but may
    /// also call it for entries with a different hash. `eq` should only return
    /// true for the desired entry, at which point the search is stopped.
    ///
    /// This method may grow the table in preparation for an insertion. Call
    /// [`HashTable::find_entry`] if this is undesirable.
    ///
    /// `hasher` is called if entries need to be moved or copied to a new table.
    /// This must return the same hash value that each entry was inserted with.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// table.insert_unique(hasher(&1), (1, "a"), |val| hasher(&val.0));
    /// if let Entry::Occupied(entry) = table.entry(hasher(&1), |val| val.0 == 1, |val| hasher(&val.0))
    /// {
    ///     entry.remove();
    /// }
    /// if let Entry::Vacant(entry) = table.entry(hasher(&2), |val| val.0 == 2, |val| hasher(&val.0)) {
    ///     entry.insert((2, "b"));
    /// }
    /// assert_eq!(table.find(hasher(&1), |val| val.0 == 1), None);
    /// assert_eq!(table.find(hasher(&2), |val| val.0 == 2), Some(&(2, "b")));
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn entry(
        &self,
        hash: u64,
        eq: impl FnMut(&T) -> bool,
        hasher: impl Fn(&T) -> u64,
    ) -> Entry<'_, T> {
        let mut shard = self.raw_table.shard(hash).write();
        match shard.find_or_find_insert_slot(hash, eq, hasher) {
            Ok(bucket) => Entry::Occupied(OccupiedEntry {
                hash,
                bucket,
                table: shard,
            }),
            Err(insert_slot) => Entry::Vacant(VacantEntry {
                hash,
                insert_slot,
                table: shard,
            }),
        }
    }
}

impl<T> Default for ShardedHashTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A view into a single entry in a table, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`HashTable`].
///
/// [`HashTable`]: struct.HashTable.html
/// [`entry`]: struct.HashTable.html#method.entry
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "nightly")]
/// # fn test() {
/// use ahash::AHasher;
/// use hashbrown::hash_table::{Entry, HashTable, OccupiedEntry};
/// use std::hash::{BuildHasher, BuildHasherDefault};
///
/// let mut table = HashTable::new();
/// let hasher = BuildHasherDefault::<AHasher>::default();
/// let hasher = |val: &_| hasher.hash_one(val);
/// for x in ["a", "b", "c"] {
///     table.insert_unique(hasher(&x), x, hasher);
/// }
/// assert_eq!(table.len(), 3);
///
/// // Existing value (insert)
/// let entry: Entry<_> = table.entry(hasher(&"a"), |&x| x == "a", hasher);
/// let _raw_o: OccupiedEntry<_, _> = entry.insert("a");
/// assert_eq!(table.len(), 3);
/// // Nonexistent value (insert)
/// table.entry(hasher(&"d"), |&x| x == "d", hasher).insert("d");
///
/// // Existing value (or_insert)
/// table
///     .entry(hasher(&"b"), |&x| x == "b", hasher)
///     .or_insert("b");
/// // Nonexistent value (or_insert)
/// table
///     .entry(hasher(&"e"), |&x| x == "e", hasher)
///     .or_insert("e");
///
/// println!("Our HashTable: {:?}", table);
///
/// let mut vec: Vec<_> = table.iter().copied().collect();
/// // The `Iter` iterator produces items in arbitrary order, so the
/// // items must be sorted to test them against a sorted array.
/// vec.sort_unstable();
/// assert_eq!(vec, ["a", "b", "c", "d", "e"]);
/// # }
/// # fn main() {
/// #     #[cfg(feature = "nightly")]
/// #     test()
/// # }
/// ```
pub enum Entry<'a, T> {
    /// An occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::hash_table::{Entry, HashTable, OccupiedEntry};
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// for x in ["a", "b"] {
    ///     table.insert_unique(hasher(&x), x, hasher);
    /// }
    ///
    /// match table.entry(hasher(&"a"), |&x| x == "a", hasher) {
    ///     Entry::Vacant(_) => unreachable!(),
    ///     Entry::Occupied(_) => {}
    /// }
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    Occupied(OccupiedEntry<'a, T>),

    /// A vacant entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::hash_table::{Entry, HashTable, OccupiedEntry};
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table = HashTable::<&str>::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// match table.entry(hasher(&"a"), |&x| x == "a", hasher) {
    ///     Entry::Vacant(_) => {}
    ///     Entry::Occupied(_) => unreachable!(),
    /// }
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    Vacant(VacantEntry<'a, T>),
}

impl<T: fmt::Debug> fmt::Debug for Entry<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Entry::Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Entry::Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

impl<'a, T> Entry<'a, T> {
    /// Sets the value of the entry, replacing any existing value if there is
    /// one, and returns an [`OccupiedEntry`].
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<&str> = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// let entry = table
    ///     .entry(hasher(&"horseyland"), |&x| x == "horseyland", hasher)
    ///     .insert("horseyland");
    ///
    /// assert_eq!(entry.get(), &"horseyland");
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn insert(self, value: T) -> OccupiedEntry<'a, T> {
        match self {
            Entry::Occupied(mut entry) => {
                *entry.get_mut() = value;
                entry
            }
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    /// Ensures a value is in the entry by inserting if it was vacant.
    ///
    /// Returns an [`OccupiedEntry`] pointing to the now-occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<&str> = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// // nonexistent key
    /// table
    ///     .entry(hasher(&"poneyland"), |&x| x == "poneyland", hasher)
    ///     .or_insert("poneyland");
    /// assert!(table
    ///     .find(hasher(&"poneyland"), |&x| x == "poneyland")
    ///     .is_some());
    ///
    /// // existing key
    /// table
    ///     .entry(hasher(&"poneyland"), |&x| x == "poneyland", hasher)
    ///     .or_insert("poneyland");
    /// assert!(table
    ///     .find(hasher(&"poneyland"), |&x| x == "poneyland")
    ///     .is_some());
    /// assert_eq!(table.len(), 1);
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn or_insert(self, default: T) -> OccupiedEntry<'a, T> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty..
    ///
    /// Returns an [`OccupiedEntry`] pointing to the now-occupied entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<String> = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// table
    ///     .entry(hasher("poneyland"), |x| x == "poneyland", |val| hasher(val))
    ///     .or_insert_with(|| "poneyland".to_string());
    ///
    /// assert!(table
    ///     .find(hasher(&"poneyland"), |x| x == "poneyland")
    ///     .is_some());
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn or_insert_with(self, default: impl FnOnce() -> T) -> OccupiedEntry<'a, T> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the table.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use ahash::AHasher;
    /// use hashbrown::HashTable;
    /// use std::hash::{BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<(&str, u32)> = HashTable::new();
    /// let hasher = BuildHasherDefault::<AHasher>::default();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// table
    ///     .entry(
    ///         hasher(&"poneyland"),
    ///         |&(x, _)| x == "poneyland",
    ///         |(k, _)| hasher(&k),
    ///     )
    ///     .and_modify(|(_, v)| *v += 1)
    ///     .or_insert(("poneyland", 42));
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(k, _)| k == "poneyland"),
    ///     Some(&("poneyland", 42))
    /// );
    ///
    /// table
    ///     .entry(
    ///         hasher(&"poneyland"),
    ///         |&(x, _)| x == "poneyland",
    ///         |(k, _)| hasher(&k),
    ///     )
    ///     .and_modify(|(_, v)| *v += 1)
    ///     .or_insert(("poneyland", 42));
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(k, _)| k == "poneyland"),
    ///     Some(&("poneyland", 43))
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn and_modify(self, f: impl FnOnce(&mut T)) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

/// A view into an occupied entry in a `ShardedHashTable`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "nightly")]
/// # fn test() {
/// use shashmap::hash_table::{Entry, HashTable, OccupiedEntry};
/// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
///
/// let mut table = HashTable::new();
/// let hasher = RandomState::new();
/// let hasher = |val: &_| hasher.hash_one(val);
/// for x in ["a", "b", "c"] {
///     table.insert_unique(hasher(&x), x, hasher);
/// }
/// assert_eq!(table.len(), 3);
///
/// let _entry_o: OccupiedEntry<_, _> = table.find_entry(hasher(&"a"), |&x| x == "a").unwrap();
/// assert_eq!(table.len(), 3);
///
/// // Existing key
/// match table.entry(hasher(&"a"), |&x| x == "a", hasher) {
///     Entry::Vacant(_) => unreachable!(),
///     Entry::Occupied(view) => {
///         assert_eq!(view.get(), &"a");
///     }
/// }
///
/// assert_eq!(table.len(), 3);
///
/// // Existing key (take)
/// match table.entry(hasher(&"c"), |&x| x == "c", hasher) {
///     Entry::Vacant(_) => unreachable!(),
///     Entry::Occupied(view) => {
///         assert_eq!(view.remove().0, "c");
///     }
/// }
/// assert_eq!(table.find(hasher(&"c"), |&x| x == "c"), None);
/// assert_eq!(table.len(), 2);
/// # }
/// # fn main() {
/// #     #[cfg(feature = "nightly")]
/// #     test()
/// # }
/// ```
pub struct OccupiedEntry<'a, T> {
    hash: u64,
    bucket: Bucket<T>,
    table: RwLockWriteGuard<'a, RawRwLock, RawTable<T>>,
}

impl<T: fmt::Debug> fmt::Debug for OccupiedEntry<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("value", self.get())
            .finish()
    }
}

impl<'a, T> OccupiedEntry<'a, T> {
    /// Takes the value out of the entry, and returns it along with a
    /// `VacantEntry` that can be used to insert another value with the same
    /// hash as the one that was just removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<&str> = HashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// // The table is empty
    /// assert!(table.is_empty() && table.capacity() == 0);
    ///
    /// table.insert_unique(hasher(&"poneyland"), "poneyland", hasher);
    /// let capacity_before_remove = table.capacity();
    ///
    /// if let Entry::Occupied(o) = table.entry(hasher(&"poneyland"), |&x| x == "poneyland", hasher) {
    ///     assert_eq!(o.remove().0, "poneyland");
    /// }
    ///
    /// assert!(table
    ///     .find(hasher(&"poneyland"), |&x| x == "poneyland")
    ///     .is_none());
    /// // Now table hold none elements but capacity is equal to the old one
    /// assert!(table.len() == 0 && table.capacity() == capacity_before_remove);
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(mut self) -> (T, VacantEntry<'a, T>) {
        let (val, slot) = unsafe { self.table.remove(self.bucket) };
        (
            val,
            VacantEntry {
                hash: self.hash,
                insert_slot: slot,
                table: self.table,
            },
        )
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<&str> = HashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// table.insert_unique(hasher(&"poneyland"), "poneyland", hasher);
    ///
    /// match table.entry(hasher(&"poneyland"), |&x| x == "poneyland", hasher) {
    ///     Entry::Vacant(_) => panic!(),
    ///     Entry::Occupied(entry) => assert_eq!(entry.get(), &"poneyland"),
    /// }
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub fn get(&self) -> &T {
        unsafe { self.bucket.as_ref() }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: #method.into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<(&str, u32)> = HashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// table.insert_unique(hasher(&"poneyland"), ("poneyland", 12), |(k, _)| hasher(&k));
    ///
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(x, _)| x == "poneyland",),
    ///     Some(&("poneyland", 12))
    /// );
    ///
    /// if let Entry::Occupied(mut o) = table.entry(
    ///     hasher(&"poneyland"),
    ///     |&(x, _)| x == "poneyland",
    ///     |(k, _)| hasher(&k),
    /// ) {
    ///     o.get_mut().1 += 10;
    ///     assert_eq!(o.get().1, 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     o.get_mut().1 += 2;
    /// }
    ///
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(x, _)| x == "poneyland",),
    ///     Some(&("poneyland", 24))
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { self.bucket.as_mut() }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the table itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<(&str, u32)> = HashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    /// table.insert_unique(hasher(&"poneyland"), ("poneyland", 12), |(k, _)| hasher(&k));
    ///
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(x, _)| x == "poneyland",),
    ///     Some(&("poneyland", 12))
    /// );
    ///
    /// let value: &mut (&str, u32);
    /// match table.entry(
    ///     hasher(&"poneyland"),
    ///     |&(x, _)| x == "poneyland",
    ///     |(k, _)| hasher(&k),
    /// ) {
    ///     Entry::Occupied(entry) => value = entry.into_mut(),
    ///     Entry::Vacant(_) => panic!(),
    /// }
    /// value.1 += 10;
    ///
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&(x, _)| x == "poneyland",),
    ///     Some(&("poneyland", 22))
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    pub fn into_mut(self) -> &'a mut T {
        unsafe { self.bucket.as_mut() }
    }
}

/// A view into a vacant entry in a `HashTable`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "nightly")]
/// # fn test() {
/// use hashbrown::hash_table::{Entry, HashTable, VacantEntry};
/// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
///
/// let mut table: HashTable<&str> = HashTable::new();
/// let hasher = RandomState::new();
/// let hasher = |val: &_| hasher.hash_one(val);
///
/// let entry_v: VacantEntry<_, _> = match table.entry(hasher(&"a"), |&x| x == "a", hasher) {
///     Entry::Vacant(view) => view,
///     Entry::Occupied(_) => unreachable!(),
/// };
/// entry_v.insert("a");
/// assert!(table.find(hasher(&"a"), |&x| x == "a").is_some() && table.len() == 1);
///
/// // Nonexistent key (insert)
/// match table.entry(hasher(&"b"), |&x| x == "b", hasher) {
///     Entry::Vacant(view) => {
///         view.insert("b");
///     }
///     Entry::Occupied(_) => unreachable!(),
/// }
/// assert!(table.find(hasher(&"b"), |&x| x == "b").is_some() && table.len() == 2);
/// # }
/// # fn main() {
/// #     #[cfg(feature = "nightly")]
/// #     test()
/// # }
/// ```
pub struct VacantEntry<'a, T> {
    hash: u64,
    insert_slot: InsertSlot,
    table: RwLockWriteGuard<'a, RawRwLock, RawTable<T>>,
}

impl<T: fmt::Debug> fmt::Debug for VacantEntry<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VacantEntry")
    }
}

impl<'a, T> VacantEntry<'a, T> {
    /// Inserts a new element into the table with the hash that was used to
    /// obtain the `VacantEntry`.
    ///
    /// An `OccupiedEntry` is returned for the newly inserted element.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "nightly")]
    /// # fn test() {
    /// use hashbrown::hash_table::Entry;
    /// use hashbrown::HashTable;
    /// use std::hash::{RandomState, BuildHasher, BuildHasherDefault};
    ///
    /// let mut table: HashTable<&str> = HashTable::new();
    /// let hasher = RandomState::new();
    /// let hasher = |val: &_| hasher.hash_one(val);
    ///
    /// if let Entry::Vacant(o) = table.entry(hasher(&"poneyland"), |&x| x == "poneyland", hasher) {
    ///     o.insert("poneyland");
    /// }
    /// assert_eq!(
    ///     table.find(hasher(&"poneyland"), |&x| x == "poneyland"),
    ///     Some(&"poneyland")
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "nightly")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub fn insert(mut self, value: T) -> OccupiedEntry<'a, T> {
        let bucket = unsafe {
            self.table
                .insert_in_slot(self.hash, self.insert_slot, value)
        };
        OccupiedEntry {
            hash: self.hash,
            bucket,
            table: self.table,
        }
    }
}
