use std::hash::{BuildHasher, Hash, RandomState};

use allocator_api2::alloc::{Allocator, Global};

use hashbrown::raw::RawTable;

use crate::list::{LinkedList, RawHandle};

pub struct LruCache<K, V, S = RandomState, A: Allocator = Global> {
    cache: LinkedList<(K, V), A>,
    map: RawTable<RawHandle<(K, V)>, A>,
    hasher: S,
    max_capacity: usize,
}

impl<K, V> LruCache<K, V> {
    pub fn with_capacity(cap: usize) -> Self {
        Self::with_capacity_and_hasher_in(cap, RandomState::new(), Global)
    }
}

impl<K, V, S> LruCache<K, V, S> {
    pub fn with_capacity_and_hasher(cap: usize, hasher: S) -> Self {
        Self::with_capacity_and_hasher_in(cap, hasher, Global)
    }
}

impl<K, V, A: Allocator + Clone> LruCache<K, V, RandomState, A> {
    pub fn with_capacity_in(cap: usize, alloc: A) -> Self {
        Self::with_capacity_and_hasher_in(cap, RandomState::new(), alloc)
    }
}

impl<K, V, S, A: Allocator + Clone> LruCache<K, V, S, A> {
    pub fn with_capacity_and_hasher_in(cap: usize, hasher: S, alloc: A) -> Self {
        Self {
            cache: LinkedList::new_in(alloc.clone()),
            map: RawTable::with_capacity_in(cap, alloc),
            hasher,
            max_capacity: cap,
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher, A: Allocator> LruCache<K, V, S, A> {}
