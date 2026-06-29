//! LFU（Least Frequently Used）缓存。
//!
//! 每次访问时增加键的使用频率；需要淘汰时，优先移除使用次数最少的键；
//! 使用次数相同时，按最久未使用（FIFO）顺序淘汰。
//!
//! 本实现使用 `BTreeMap<(freq, seq), K>` 维护淘汰顺序，`seq` 作为相同频率下的
//! 时间戳，整体操作复杂度为 O(log n)，足以演示 LFU 的核心语义。
use std::collections::{BTreeMap, HashMap};

use super::CachePolicy;

#[derive(Clone, Debug)]
pub struct LfuCache<K, V> {
    cap: usize,
    values: HashMap<K, (V, usize, usize)>, // value, frequency, sequence
    order: BTreeMap<(usize, usize), K>,    // (frequency, sequence) -> key
    seq: usize,
}

impl<K: std::hash::Hash + Eq + Clone, V> LfuCache<K, V> {
    pub fn new(cap: usize) -> Self {
        Self {
            cap,
            values: HashMap::new(),
            order: BTreeMap::new(),
            seq: 0,
        }
    }

    fn touch(&mut self, key: &K) {
        if let Some(node) = self.values.get_mut(key) {
            self.order.remove(&(node.1, node.2));
            node.1 += 1;
            node.2 = self.seq;
            self.order.insert((node.1, node.2), key.clone());
            self.seq += 1;
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.values.contains_key(key) {
            self.touch(key);
            self.values.get(key).map(|(v, _, _)| v)
        } else {
            None
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        if self.values.contains_key(&key) {
            if let Some(node) = self.values.get_mut(&key) {
                node.0 = value;
            }
            self.touch(&key);
            return;
        }

        if self.values.len() == self.cap
            && self.cap > 0
            && let Some((_, evicted_key)) = self.order.pop_first()
        {
            self.values.remove(&evicted_key);
        }

        let seq = self.seq;
        self.seq += 1;
        self.values.insert(key.clone(), (value, 1, seq));
        self.order.insert((1, seq), key);
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

impl<K: std::hash::Hash + Eq + Clone, V> CachePolicy<K, V> for LfuCache<K, V> {
    fn new(cap: usize) -> Self {
        LfuCache::new(cap)
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        LfuCache::get(self, key)
    }

    fn put(&mut self, key: K, value: V) {
        LfuCache::put(self, key, value)
    }

    fn len(&self) -> usize {
        LfuCache::len(self)
    }

    fn is_empty(&self) -> bool {
        LfuCache::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lfu_basic() {
        let mut cache = LfuCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        assert_eq!(cache.get(&1), Some(&"a"));
        cache.put(3, "c"); // 键 2 使用次数为 1 且更旧，被淘汰
        assert!(cache.get(&2).is_none());
        assert_eq!(cache.get(&3), Some(&"c"));
    }

    #[test]
    fn test_lfu_frequency_tie_break() {
        let mut cache = LfuCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        cache.get(&1); // 键 1 频率为 2
        cache.get(&1);
        cache.put(3, "c"); // 键 2 频率仍为 1，应被淘汰
        assert_eq!(cache.get(&1), Some(&"a"));
        assert!(cache.get(&2).is_none());
        assert_eq!(cache.get(&3), Some(&"c"));
    }

    #[test]
    fn test_lfu_update_existing() {
        let mut cache = LfuCache::new(2);
        cache.put(1, "a");
        cache.put(1, "aa");
        assert_eq!(cache.get(&1), Some(&"aa"));
    }
}
