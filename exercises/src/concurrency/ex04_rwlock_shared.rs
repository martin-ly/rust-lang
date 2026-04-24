//! # 练习 4: RwLock 共享状态
//!
//! **难度**: Medium  
//! **考点**: RwLock、读写锁、读多写少场景
//!
//! ## 题目描述
//!
//! 使用 RwLock 实现一个缓存，支持并发读取和独占写入。

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::thread;

/// 线程安全的缓存
pub type SharedCache<K, V> = Arc<RwLock<HashMap<K, V>>>;

/// 创建共享缓存
pub fn create_cache<K, V>() -> SharedCache<K, V>
where
    K: Eq + std::hash::Hash,
{
    Arc::new(RwLock::new(HashMap::new()))
}

/// 插入键值对
pub fn cache_insert<K, V>(cache: &SharedCache<K, V>, key: K, value: V)
where
    K: Eq + std::hash::Hash,
{
    let mut map = cache.write().unwrap();
    map.insert(key, value);
}

/// 读取键值
pub fn cache_get<K, V>(cache: &SharedCache<K, V>, key: &K) -> Option<V>
where
    K: Eq + std::hash::Hash,
    V: Clone,
{
    let map = cache.read().unwrap();
    map.get(key).cloned()
}

/// 并发读取缓存
pub fn concurrent_reads<K, V>(cache: &SharedCache<K, V>, keys: Vec<K>) -> Vec<Option<V>>
where
    K: Eq + std::hash::Hash + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    let mut handles = Vec::new();
    for key in keys {
        let cache = Arc::clone(cache);
        let handle = thread::spawn(move || cache_get(&cache, &key));
        handles.push(handle);
    }

    handles.into_iter().map(|h| h.join().unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_basic() {
        let cache: SharedCache<String, i32> = create_cache();
        cache_insert(&cache, "a".to_string(), 1);
        cache_insert(&cache, "b".to_string(), 2);
        assert_eq!(cache_get(&cache, &"a".to_string()), Some(1));
        assert_eq!(cache_get(&cache, &"c".to_string()), None);
    }

    #[test]
    fn test_concurrent_reads() {
        let cache: SharedCache<String, i32> = create_cache();
        cache_insert(&cache, "x".to_string(), 10);
        cache_insert(&cache, "y".to_string(), 20);

        let keys = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let results = concurrent_reads(&cache, keys);
        assert_eq!(results, vec![Some(10), Some(20), None]);
    }
}
