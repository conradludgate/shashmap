use std::{
    hash::{BuildHasher, Hash, RandomState},
    mem,
    thread::available_parallelism,
};

use hashbrown::Equivalent;
use shashmap_core::PowerOfTwo;

use crate::{RawShardedHashTable, ShardReadGuard, ShardWriteGuard};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeyValue<K, V>(K, V);

pub struct ShardedHashMap<K, V, S = RandomState> {
    hasher: S,
    raw_table: RawShardedHashTable<KeyValue<K, V>>,
}

impl<K, V> KeyValue<K, V> {
    pub fn new(k: K, v: V) -> Self {
        Self(k, v)
    }

    pub fn key(&self) -> &K {
        &self.0
    }

    pub fn value(&self) -> &V {
        &self.1
    }

    pub fn key_value_mut(&mut self) -> (&K, &mut V) {
        (&self.0, &mut self.1)
    }
}

impl<K: Hash + Eq, V> ShardedHashMap<K, V> {
    pub fn new() -> Self {
        ShardedHashMap {
            hasher: RandomState::new(),
            raw_table: RawShardedHashTable::new(PowerOfTwo::next_power_of_two(
                available_parallelism().map_or(1, |nz| nz.get()) * 4,
            )),
        }
    }
}

impl<K: Hash + Eq, V> Default for ShardedHashMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> ShardedHashMap<K, V, S> {
    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use shashmap::hash_map::ShardedHashMap;
    ///
    /// let map = ShardedHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1).as_deref(), Some(&"a"));
    /// assert_eq!(map.get(&2).as_deref(), None);
    /// ```
    pub fn get<Q: Hash + Equivalent<K> + ?Sized>(&self, q: &Q) -> Option<ShardReadGuard<'_, V>> {
        Some(ShardReadGuard::map(self.get_key_value(q)?, |kv| kv.value()))
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use shashmap::hash_map::ShardedHashMap;
    /// use shashmap::hash_map::KeyValue;
    ///
    /// let map = ShardedHashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1).as_deref(), Some(&KeyValue::new(1, "a")));
    /// assert_eq!(map.get_key_value(&2).as_deref(), None);
    /// ```
    pub fn get_key_value<Q: Hash + Equivalent<K> + ?Sized>(
        &self,
        q: &Q,
    ) -> Option<ShardReadGuard<'_, KeyValue<K, V>>> {
        self.raw_table
            .get(self.hasher.hash_one(q), |kv| q.equivalent(&kv.0))
    }

    pub fn get_mut<Q: Hash + Equivalent<K> + ?Sized>(
        &self,
        q: &Q,
    ) -> Option<ShardWriteGuard<'_, V>> {
        Some(ShardWriteGuard::map(self.get_key_value_mut(q)?, |kv| {
            kv.key_value_mut().1
        }))
    }

    pub fn get_key_value_mut<Q: Hash + Equivalent<K> + ?Sized>(
        &self,
        q: &Q,
    ) -> Option<ShardWriteGuard<'_, KeyValue<K, V>>> {
        self.raw_table
            .get_mut(self.hasher.hash_one(q), |kv| q.equivalent(&kv.0))
    }

    pub fn insert(&self, k: K, v: V) -> Option<V> {
        let hash = self.hasher.hash_one(&k);
        let mut shard = self.raw_table.shard(hash).write();
        let slot = shard.find_or_find_insert_slot(
            hash,
            |kv| kv.0 == k,
            |kv| self.hasher.hash_one(kv.key()),
        );
        match slot {
            Ok(bucket) => Some(mem::replace(unsafe { &mut bucket.as_mut().1 }, v)),
            Err(slot) => {
                unsafe {
                    shard.insert_in_slot(hash, slot, KeyValue(k, v));
                }
                None
            }
        }
    }
}
