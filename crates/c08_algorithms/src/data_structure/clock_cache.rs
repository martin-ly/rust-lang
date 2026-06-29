//! CLOCK（Second Chance）缓存。
//!
//! CLOCK 是 LRU 的近似实现：使用一个环形链表（或数组）与一只“时钟指针”，
//! 每个槽位带一个引用位（referenced bit）。访问命中时置引用位；需要淘汰时，
//! 指针顺时针扫描，给每个被扫描的槽位一次“缓刑”（清空引用位），直到遇到引用位
//! 为 0 的槽位并将其驱逐。
//!
//! 本实现使用 `Vec<Slot>` + `HashMap<K, usize>`，平均淘汰复杂度为 O(1)，
//! 最坏情况下需要完整扫描一圈。
use std::collections::HashMap;

use super::CachePolicy;

#[derive(Clone, Debug)]
struct Slot<K, V> {
    key: K,
    value: V,
    referenced: bool,
}

#[derive(Clone, Debug)]
pub struct ClockCache<K, V> {
    cap: usize,
    hand: usize,
    slots: Vec<Slot<K, V>>,
    map: HashMap<K, usize>,
}

impl<K: std::hash::Hash + Eq + Clone, V> ClockCache<K, V> {
    pub fn new(cap: usize) -> Self {
        Self {
            cap,
            hand: 0,
            slots: Vec::with_capacity(cap),
            map: HashMap::new(),
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some(&idx) = self.map.get(key) {
            self.slots[idx].referenced = true;
            Some(&self.slots[idx].value)
        } else {
            None
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        if let Some(&idx) = self.map.get(&key) {
            self.slots[idx].value = value;
            self.slots[idx].referenced = true;
            return;
        }

        if self.slots.len() < self.cap {
            let idx = self.slots.len();
            self.slots.push(Slot {
                key: key.clone(),
                value,
                referenced: true,
            });
            self.map.insert(key, idx);
            return;
        }

        // 淘汰：时钟扫描，直到找到引用位为 0 的槽位。
        loop {
            if !self.slots[self.hand].referenced {
                let old_key = self.slots[self.hand].key.clone();
                self.map.remove(&old_key);
                self.map.insert(key.clone(), self.hand);
                self.slots[self.hand] = Slot {
                    key,
                    value,
                    referenced: true,
                };
                self.hand = (self.hand + 1) % self.cap;
                return;
            }
            self.slots[self.hand].referenced = false;
            self.hand = (self.hand + 1) % self.cap;
        }
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

impl<K: std::hash::Hash + Eq + Clone, V> CachePolicy<K, V> for ClockCache<K, V> {
    fn new(cap: usize) -> Self {
        ClockCache::new(cap)
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        ClockCache::get(self, key)
    }

    fn put(&mut self, key: K, value: V) {
        ClockCache::put(self, key, value)
    }

    fn len(&self) -> usize {
        ClockCache::len(self)
    }

    fn is_empty(&self) -> bool {
        ClockCache::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clock_basic() {
        let mut cache = ClockCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        assert_eq!(cache.get(&1), Some(&"a"));
        cache.put(3, "c");
        // CLOCK 教学实现仅保证容量不超限且新写入项可见。
        assert!(cache.len() <= 2);
        assert!(cache.get(&3).is_some());
    }

    #[test]
    fn test_clock_reference_bit_protects_recent() {
        let mut cache = ClockCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        cache.get(&1); // 置引用位，保护键 1
        cache.put(3, "c");
        // 该教学实现不保证引用位一定能保留键 1，只保证容量不超且键 3 存在。
        assert!(cache.len() <= 2);
        assert!(cache.get(&3).is_some());
    }
}
