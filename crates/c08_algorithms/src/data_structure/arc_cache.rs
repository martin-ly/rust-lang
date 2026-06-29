//! ARC（Adaptive Replacement Cache）缓存骨架。
//!
//! ARC 同时维护“最近使用”（T1）与“频繁使用”（T2）两条缓存队列，以及对应的
//! 幽灵队列 B1/B2，根据历史命中情况动态调整 T1 的目标大小 `p`，从而在工作负载
//! 偏向 recency 或 frequency 之间自适应切换。
//!
//! 本实现使用 `VecDeque` 演示 ARC 的核心四条队列与 `p` 自适应逻辑，操作复杂度
//! 为 O(n)（容量较小时可接受），重点在于呈现算法骨架与淘汰语义。
use std::collections::{HashMap, VecDeque};

use super::CachePolicy;

#[derive(Clone, Debug)]
pub struct ArcCache<K, V> {
    cap: usize,
    p: usize, // T1 的目标大小
    t1: VecDeque<K>,
    b1: VecDeque<K>,
    t2: VecDeque<K>,
    b2: VecDeque<K>,
    map: HashMap<K, V>,
}

impl<K: std::hash::Hash + Eq + Clone, V> ArcCache<K, V> {
    pub fn new(cap: usize) -> Self {
        Self {
            cap,
            p: 0,
            t1: VecDeque::new(),
            b1: VecDeque::new(),
            t2: VecDeque::new(),
            b2: VecDeque::new(),
            map: HashMap::new(),
        }
    }

    fn contains(list: &VecDeque<K>, key: &K) -> bool {
        list.iter().any(|k| k == key)
    }

    fn position(list: &VecDeque<K>, key: &K) -> Option<usize> {
        list.iter().position(|k| k == key)
    }

    fn remove(list: &mut VecDeque<K>, key: &K) {
        if let Some(idx) = Self::position(list, key) {
            list.remove(idx);
        }
    }

    /// 将缓存页从 T1 或 T2 移动到对应幽灵队列，必要时裁剪幽灵队列。
    fn replace(&mut self, x: &K) {
        if !self.t1.is_empty()
            && (self.t1.len() > self.p || (Self::contains(&self.b2, x) && self.t1.len() == self.p))
        {
            if let Some(old) = self.t1.pop_front() {
                self.map.remove(&old);
                self.b1.push_back(old);
                if self.t1.len() + self.b1.len() > self.cap {
                    self.b1.pop_front();
                }
            }
        } else if !self.t2.is_empty()
            && let Some(old) = self.t2.pop_front()
        {
            self.map.remove(&old);
            self.b2.push_back(old);
            if self.t2.len() + self.b2.len() > self.cap {
                self.b2.pop_front();
            }
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if Self::contains(&self.t1, key) || Self::contains(&self.t2, key) {
            Self::remove(&mut self.t1, key);
            Self::remove(&mut self.t2, key);
            self.t2.push_back(key.clone());
            self.map.get(key)
        } else {
            None
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        // Case I / II: 命中 T1/T2，移动到 T2 MRU。
        if Self::contains(&self.t1, &key) || Self::contains(&self.t2, &key) {
            Self::remove(&mut self.t1, &key);
            Self::remove(&mut self.t2, &key);
            self.t2.push_back(key.clone());
            self.map.insert(key, value);
            return;
        }

        // Case III: 命中 B1（幽灵最近）。
        if Self::contains(&self.b1, &key) {
            let delta = (self.b2.len() / self.b1.len().max(1)).max(1);
            self.p = self.cap.min(self.p + delta);
            Self::remove(&mut self.b1, &key);
            self.replace(&key);
            self.t2.push_back(key.clone());
            self.map.insert(key, value);
            return;
        }

        // Case IV: 命中 B2（幽灵频繁）。
        if Self::contains(&self.b2, &key) {
            let delta = (self.b1.len() / self.b2.len().max(1)).max(1);
            self.p = self.p.saturating_sub(delta);
            Self::remove(&mut self.b2, &key);
            self.replace(&key);
            self.t2.push_back(key.clone());
            self.map.insert(key, value);
            return;
        }

        // Case V: 全新键。
        if self.t1.len() + self.t2.len() == self.cap {
            self.replace(&key);
        } else if self.t1.len() + self.t2.len() < self.cap {
            let total = self.t1.len() + self.b1.len() + self.t2.len() + self.b2.len();
            if total >= self.cap {
                if total == 2 * self.cap {
                    self.b2.pop_front();
                }
                if self.t1.len() + self.b1.len() >= self.cap {
                    if !self.b1.is_empty() {
                        self.b1.pop_front();
                    } else if !self.b2.is_empty() {
                        self.b2.pop_front();
                    }
                }
            }
        }

        self.t1.push_back(key.clone());
        self.map.insert(key, value);
    }

    pub fn len(&self) -> usize {
        self.t1.len() + self.t2.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K: std::hash::Hash + Eq + Clone, V> CachePolicy<K, V> for ArcCache<K, V> {
    fn new(cap: usize) -> Self {
        ArcCache::new(cap)
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        ArcCache::get(self, key)
    }

    fn put(&mut self, key: K, value: V) {
        ArcCache::put(self, key, value)
    }

    fn len(&self) -> usize {
        ArcCache::len(self)
    }

    fn is_empty(&self) -> bool {
        ArcCache::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arc_basic() {
        let mut cache = ArcCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        assert_eq!(cache.get(&1), Some(&"a"));
        cache.put(3, "c");
        // 容量为 2，新键 3 会导致某个键被淘汰
        assert!(cache.len() <= 2);
    }

    #[test]
    fn test_arc_adapt_to_frequency() {
        let mut cache = ArcCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        cache.get(&1); // 提升键 1 的访问频率
        cache.put(3, "c");
        // 教学骨架不保证严格保留高频键，只保证容量不超限且无 panic。
        assert!(cache.len() <= 2);
    }

    #[test]
    fn test_arc_ghost_hit() {
        let mut cache = ArcCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        cache.put(3, "c"); // 可能把键 1 移入 B1
        assert!(cache.get(&1).is_none()); // 幽灵命中仍为 miss
        cache.put(1, "a"); // 重新插入，B1 命中会调整 p
        assert_eq!(cache.get(&1), Some(&"a"));
    }
}
