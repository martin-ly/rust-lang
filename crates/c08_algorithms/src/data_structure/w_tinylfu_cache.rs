//! W-TinyLFU 缓存骨架。
//!
//! W-TinyLFU 将缓存划分为一个极小的“窗口”LRU（W）与一个由 TinyLFU 准入过滤器
//! 保护的“主”LRU（M）。新元素先进入窗口；窗口溢出时，候选者只有在 TinyLFU 预测
//! 其未来访问频率不低于主缓存受害者时才被晋升入主缓存。该策略兼顾 recency 与
//! frequency，对扫描型负载具有较强的鲁棒性。
//!
//! 本实现使用简化的频率表（`HashMap<K, u64>`）替代 Count-Min Sketch，并用
//! `VecDeque` 维护 LRU 顺序，用于演示算法骨架。
use std::collections::{HashMap, VecDeque};

use super::CachePolicy;

#[derive(Clone, Debug)]
pub struct WTinyLfuCache<K, V> {
    cap: usize,
    window_cap: usize,
    window: VecDeque<K>,
    window_map: HashMap<K, V>,
    main: VecDeque<K>,
    main_map: HashMap<K, V>,
    freq: HashMap<K, u64>,
}

impl<K: std::hash::Hash + Eq + Clone, V> WTinyLfuCache<K, V> {
    pub fn new(cap: usize) -> Self {
        let window_cap = if cap == 0 {
            0
        } else {
            (cap / 100).max(1).min(cap)
        };
        Self {
            cap,
            window_cap,
            window: VecDeque::new(),
            window_map: HashMap::new(),
            main: VecDeque::new(),
            main_map: HashMap::new(),
            freq: HashMap::new(),
        }
    }

    fn touch_window(&mut self, key: &K) {
        if self.window.back() == Some(key) {
            return;
        }
        if let Some(idx) = self.window.iter().position(|k| k == key) {
            let k = self.window.remove(idx).expect("W-TinyLFU: window key");
            self.window.push_back(k);
        }
    }

    fn touch_main(&mut self, key: &K) {
        if self.main.back() == Some(key) {
            return;
        }
        if let Some(idx) = self.main.iter().position(|k| k == key) {
            let k = self.main.remove(idx).expect("W-TinyLFU: main key");
            self.main.push_back(k);
        }
    }

    fn increment(&mut self, key: &K) {
        *self.freq.entry(key.clone()).or_insert(0) += 1;
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.window_map.contains_key(key) {
            self.increment(key);
            self.touch_window(key);
            return self.window_map.get(key);
        }
        if self.main_map.contains_key(key) {
            self.increment(key);
            self.touch_main(key);
            return self.main_map.get(key);
        }
        None
    }

    fn admit(&mut self, candidate: K, value: V) {
        let main_cap = self.cap.saturating_sub(self.window_cap);
        if self.main.len() < main_cap {
            self.main.push_back(candidate.clone());
            self.main_map.insert(candidate, value);
            return;
        }

        if main_cap == 0 {
            return;
        }

        let victim = self.main.front().cloned().expect("main not empty");
        let victim_freq = self.freq.get(&victim).copied().unwrap_or(0);
        let cand_freq = self.freq.get(&candidate).copied().unwrap_or(0);

        if cand_freq >= victim_freq {
            self.main.pop_front();
            self.main_map.remove(&victim);
            self.main.push_back(candidate.clone());
            self.main_map.insert(candidate, value);
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        if self.window_map.contains_key(&key) {
            self.window_map.insert(key.clone(), value);
            self.increment(&key);
            self.touch_window(&key);
            return;
        }
        if self.main_map.contains_key(&key) {
            self.main_map.insert(key.clone(), value);
            self.increment(&key);
            self.touch_main(&key);
            return;
        }

        self.increment(&key);
        self.window.push_back(key.clone());
        self.window_map.insert(key, value);

        if self.window.len() > self.window_cap && self.window_cap > 0 {
            let candidate = self.window.pop_front().expect("window not empty");
            let cand_value = self
                .window_map
                .remove(&candidate)
                .expect("candidate value exists");
            self.admit(candidate, cand_value);
        }
    }

    pub fn len(&self) -> usize {
        self.window_map.len() + self.main_map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K: std::hash::Hash + Eq + Clone, V> CachePolicy<K, V> for WTinyLfuCache<K, V> {
    fn new(cap: usize) -> Self {
        WTinyLfuCache::new(cap)
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        WTinyLfuCache::get(self, key)
    }

    fn put(&mut self, key: K, value: V) {
        WTinyLfuCache::put(self, key, value)
    }

    fn len(&self) -> usize {
        WTinyLfuCache::len(self)
    }

    fn is_empty(&self) -> bool {
        WTinyLfuCache::is_empty(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_w_tinylfu_basic() {
        let mut cache = WTinyLfuCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        assert_eq!(cache.get(&1), Some(&"a"));
        cache.put(3, "c");
        assert!(cache.len() <= 2);
    }

    #[test]
    fn test_w_tinylfu_frequency_filter() {
        let mut cache = WTinyLfuCache::new(2);
        cache.put(1, "a");
        cache.put(2, "b");
        cache.get(&1);
        cache.get(&1); // 键 1 频率较高
        cache.put(3, "c"); // 键 2 可能被淘汰
        assert_eq!(cache.get(&1), Some(&"a"));
    }
}
