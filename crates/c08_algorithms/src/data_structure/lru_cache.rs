//! 简易 LRU Cache，提供非线程安全与可选线程安全包装

use std::collections::{HashMap, VecDeque};

#[derive(Clone, Debug)]
pub struct LruCache<K, V> {
    cap: usize,
    map: HashMap<K, (V, usize)>, // key -> (value, index)
    order: VecDeque<K>,          // 维护最近使用顺序，队尾为最近使用
}

impl<K: std::hash::Hash + Eq + Clone, V> LruCache<K, V> {
    pub fn new(cap: usize) -> Self {
        Self {
            cap,
            map: HashMap::new(),
            order: VecDeque::new(),
        }
    }

    fn touch(&mut self, key: &K) {
        // 简化：从队列中线性移除再推入尾部（O(n)）。如需 O(1) 可用双向链表节点索引结构。
        if let Some(pos) = self.order.iter().position(|k| k == key) {
            self.order.remove(pos);
        }
        self.order.push_back(key.clone());
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.map.contains_key(key) {
            self.touch(key);
            // 为避免双重可变借用，这里再一次查询不可变借用
            return self.map.get(key).map(|(v, _)| v);
        }
        None
    }

    pub fn put(&mut self, key: K, value: V) {
        if self.map.contains_key(&key) {
            self.map.insert(key.clone(), (value, 0));
            self.touch(&key);
            return;
        }
        if self.map.len() == self.cap
            && let Some(old) = self.order.pop_front() {
                self.map.remove(&old);
            }
        self.order.push_back(key.clone());
        self.map.insert(key, (value, 0));
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

#[cfg(feature = "with-petgraph")]
pub mod ts {
    use super::*;
    use std::sync::{Arc, RwLock};

    #[derive(Clone)]
    pub struct LruCacheTs<K, V>(Arc<RwLock<LruCache<K, V>>>);

    impl<K: std::hash::Hash + Eq + Clone, V> LruCacheTs<K, V> {
        pub fn new(cap: usize) -> Self {
            Self(Arc::new(RwLock::new(LruCache::new(cap))))
        }
        pub fn get(&self, key: &K) -> Option<V>
        where
            V: Clone,
        {
            self.0.write().unwrap().get(key).cloned()
        }
        pub fn put(&self, key: K, value: V) {
            self.0.write().unwrap().put(key, value)
        }
        pub fn len(&self) -> usize {
            self.0.read().unwrap().len()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lru_basic() {
        let mut lru = LruCache::new(2);
        lru.put(1, "a");
        lru.put(2, "b");
        assert_eq!(lru.get(&1), Some(&"a"));
        lru.put(3, "c"); // 淘汰键 2
        assert!(lru.get(&2).is_none());
        assert_eq!(lru.get(&3), Some(&"c"));
    }
}
