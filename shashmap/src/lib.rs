extern crate alloc;

pub mod hash_table;
pub mod hash_map;

type RawRwLock = parking_lot::RawRwLock;
type RawShardedHashTable<T> = shashmap_core::RawShardedHashTable<RawRwLock, T>;
pub type ShardReadGuard<'a, T> = shashmap_core::ShardReadGuard<'a, RawRwLock, T>;
pub type ShardWriteGuard<'a, T> = shashmap_core::ShardWriteGuard<'a, RawRwLock, T>;
