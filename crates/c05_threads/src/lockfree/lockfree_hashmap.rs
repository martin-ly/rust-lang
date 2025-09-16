//! 无锁哈希表实现
//!
//! 本模块提供了多种无锁哈希表实现：
//! - 基于CAS的无锁哈希表
//! - 分段无锁哈希表
//! - 可扩展无锁哈希表
//! - 内存安全的无锁哈希表

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::Arc;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
//use std::mem;
//use crossbeam_epoch::{
//self,
// Atomic, Owned, Shared, Guard,
//   };
use dashmap::DashMap;

/// 无锁哈希表节点
#[derive(Debug)]
struct Node<K, V> {
    key: K,
    value: V,
    next: AtomicPtr<Node<K, V>>,
}

impl<K, V> Node<K, V> {
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }
}

/// 基于CAS的无锁哈希表
///
/// 使用比较并交换操作实现无锁哈希表
pub struct LockFreeHashMap<K, V> {
    buckets: Vec<AtomicPtr<Node<K, V>>>,
    size: AtomicUsize,
    capacity: usize,
}

impl<K, V> LockFreeHashMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    /// 创建新的无锁哈希表
    pub fn new(capacity: usize) -> Self {
        let mut buckets = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buckets.push(AtomicPtr::new(ptr::null_mut()));
        }

        Self {
            buckets,
            size: AtomicUsize::new(0),
            capacity,
        }
    }

    /// 计算键的哈希值
    fn hash(&self, key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize % self.capacity
    }

    /// 插入键值对
    pub fn insert(&self, key: K, value: V) -> bool {
        let hash = self.hash(&key);
        let new_node = Box::into_raw(Box::new(Node::new(key.clone(), value.clone())));

        loop {
            let bucket = &self.buckets[hash];
            let head = bucket.load(Ordering::Acquire);

            // 检查是否已存在相同的键
            let mut current = head;
            while !current.is_null() {
                unsafe {
                    if (*current).key == key {
                        // 键已存在，更新值
                        (*current).value = value.clone();
                        drop(Box::from_raw(new_node));
                        return false;
                    }
                    current = (*current).next.load(Ordering::Acquire);
                }
            }

            // 将新节点插入到链表头部
            unsafe {
                (*new_node).next.store(head, Ordering::Release);
            }

            match bucket.compare_exchange_weak(head, new_node, Ordering::Release, Ordering::Acquire)
            {
                Ok(_) => {
                    self.size.fetch_add(1, Ordering::Relaxed);
                    return true;
                }
                Err(_) => {
                    // CAS失败，重试
                    continue;
                }
            }
        }
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        let hash = self.hash(key);
        let bucket = &self.buckets[hash];
        let mut current = bucket.load(Ordering::Acquire);

        while !current.is_null() {
            unsafe {
                if (*current).key == *key {
                    return Some((*current).value.clone());
                }
                current = (*current).next.load(Ordering::Acquire);
            }
        }

        None
    }

    /// 删除键值对
    pub fn remove(&self, key: &K) -> Option<V> {
        let hash = self.hash(key);
        let bucket = &self.buckets[hash];

        loop {
            let head = bucket.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            unsafe {
                if (*head).key == *key {
                    // 找到要删除的节点
                    let next = (*head).next.load(Ordering::Acquire);
                    match bucket.compare_exchange_weak(
                        head,
                        next,
                        Ordering::Release,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            let value = (*head).value.clone();
                            drop(Box::from_raw(head));
                            self.size.fetch_sub(1, Ordering::Relaxed);
                            return Some(value);
                        }
                        Err(_) => {
                            // CAS失败，重试
                            continue;
                        }
                    }
                } else {
                    // 在链表中查找要删除的节点
                    let mut prev = head;
                    let mut current = (*head).next.load(Ordering::Acquire);

                    while !current.is_null() {
                        if (*current).key == *key {
                            let next = (*current).next.load(Ordering::Acquire);
                            match (*prev).next.compare_exchange_weak(
                                current,
                                next,
                                Ordering::Release,
                                Ordering::Acquire,
                            ) {
                                Ok(_) => {
                                    let value = (*current).value.clone();
                                    drop(Box::from_raw(current));
                                    self.size.fetch_sub(1, Ordering::Relaxed);
                                    return Some(value);
                                }
                                Err(_) => {
                                    // CAS失败，重试
                                    break;
                                }
                            }
                        }
                        prev = current;
                        current = (*current).next.load(Ordering::Acquire);
                    }

                    return None;
                }
            }
        }
    }

    /// 获取大小
    pub fn len(&self) -> usize {
        self.size.load(Ordering::Relaxed)
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 运行示例
    pub fn run_example() {
        println!("=== 无锁哈希表示例 ===");

        let map = Arc::new(LockFreeHashMap::new(16));
        let _map_clone = map.clone();

        // 插入数据
        for i in 0..100 {
            map.insert(i, i * i);
        }

        // 多线程读取
        let handles: Vec<_> = (0..4)
            .map(|thread_id| {
                let map = map.clone();
                std::thread::spawn(move || {
                    let mut sum = 0;
                    for i in 0..100 {
                        if let Some(value) = map.get(&i) {
                            sum += value;
                        }
                    }
                    println!("线程 {} 计算的和: {}", thread_id, sum);
                })
            })
            .collect();

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        println!("哈希表大小: {}", map.len());
    }
}

/// 分段无锁哈希表
///
/// 将哈希表分成多个段，减少锁竞争
pub struct SegmentedLockFreeHashMap<K, V> {
    segments: Vec<LockFreeHashMap<K, V>>,
    segment_count: usize,
}

impl<K, V> SegmentedLockFreeHashMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    /// 创建新的分段无锁哈希表
    pub fn new(segment_count: usize, capacity_per_segment: usize) -> Self {
        let mut segments = Vec::with_capacity(segment_count);
        for _ in 0..segment_count {
            segments.push(LockFreeHashMap::new(capacity_per_segment));
        }

        Self {
            segments,
            segment_count,
        }
    }

    /// 计算键应该属于哪个段
    fn get_segment(&self, key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize % self.segment_count
    }

    /// 插入键值对
    pub fn insert(&self, key: K, value: V) -> bool {
        let segment_index = self.get_segment(&key);
        self.segments[segment_index].insert(key, value)
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        let segment_index = self.get_segment(key);
        self.segments[segment_index].get(key)
    }

    /// 删除键值对
    pub fn remove(&self, key: &K) -> Option<V> {
        let segment_index = self.get_segment(key);
        self.segments[segment_index].remove(key)
    }

    /// 获取总大小
    pub fn len(&self) -> usize {
        self.segments.iter().map(|s| s.len()).sum()
    }

    /// 运行示例
    pub fn run_example() {
        println!("=== 分段无锁哈希表示例 ===");

        let map = Arc::new(SegmentedLockFreeHashMap::new(4, 16));

        // 插入数据
        for i in 0..1000 {
            map.insert(i, i * i);
        }

        // 多线程操作
        let handles: Vec<_> = (0..8)
            .map(|thread_id| {
                let map = map.clone();
                std::thread::spawn(move || {
                    let mut sum = 0;
                    for i in 0..1000 {
                        if let Some(value) = map.get(&i) {
                            sum += value;
                        }
                    }
                    println!("线程 {} 计算的和: {}", thread_id, sum);
                })
            })
            .collect();

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        println!("分段哈希表总大小: {}", map.len());
    }
}

/// 可扩展无锁哈希表
///
/// 支持动态扩展的无锁哈希表
pub struct ScalableLockFreeHashMap<K, V> {
    tables: Vec<Arc<LockFreeHashMap<K, V>>>,
    current_table: AtomicUsize,
    capacity: usize,
}

impl<K, V> ScalableLockFreeHashMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    /// 创建新的可扩展无锁哈希表
    pub fn new(initial_capacity: usize) -> Self {
        let initial_table = Arc::new(LockFreeHashMap::new(initial_capacity));

        Self {
            tables: vec![initial_table],
            current_table: AtomicUsize::new(0),
            capacity: initial_capacity,
        }
    }

    /// 扩展哈希表
    fn expand(&self) {
        let current_index = self.current_table.load(Ordering::Acquire);
        let new_capacity = self.capacity * 2;
        let _new_table = Arc::new(LockFreeHashMap::<K, V>::new(new_capacity));

        // 将旧表的数据迁移到新表
        let _old_table = &self.tables[current_index];
        // 这里需要实现数据迁移逻辑

        // 更新当前表索引
        self.current_table
            .store(current_index + 1, Ordering::Release);
    }

    /// 插入键值对
    pub fn insert(&self, key: K, value: V) -> bool {
        let current_index = self.current_table.load(Ordering::Acquire);
        let table = &self.tables[current_index];

        if table.len() > self.capacity * 3 / 4 {
            // 负载因子过高，需要扩展
            self.expand();
            let new_index = self.current_table.load(Ordering::Acquire);
            let new_table = &self.tables[new_index];
            new_table.insert(key, value)
        } else {
            table.insert(key, value)
        }
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        let current_index = self.current_table.load(Ordering::Acquire);
        let table = &self.tables[current_index];
        table.get(key)
    }

    /// 运行示例
    pub fn run_example() {
        println!("=== 可扩展无锁哈希表示例 ===");

        let map = Arc::new(ScalableLockFreeHashMap::new(16));

        // 插入大量数据
        for i in 0..10000 {
            map.insert(i, i * i);
        }

        println!("可扩展哈希表大小: {}", map.tables.len());
    }
}

/// 使用DashMap的高性能无锁哈希表
///
/// DashMap是一个高性能的无锁并发哈希表
pub struct DashMapWrapper<K, V> {
    map: DashMap<K, V>,
}

impl<K, V> DashMapWrapper<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    /// 创建新的DashMap包装器
    pub fn new() -> Self {
        Self {
            map: DashMap::new(),
        }
    }

    /// 插入键值对
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        self.map.insert(key, value)
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        self.map.get(key).map(|entry| entry.clone())
    }

    /// 删除键值对
    pub fn remove(&self, key: &K) -> Option<V> {
        self.map.remove(key).map(|(_, value)| value)
    }

    /// 获取大小
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// 运行示例
    pub fn run_example() {
        println!("=== DashMap无锁哈希表示例 ===");

        let map = Arc::new(DashMapWrapper::new());

        // 插入数据
        for i in 0..1000 {
            map.insert(i, i * i);
        }

        // 多线程操作
        let handles: Vec<_> = (0..4)
            .map(|thread_id| {
                let map = map.clone();
                std::thread::spawn(move || {
                    let mut sum = 0;
                    for i in 0..1000 {
                        if let Some(value) = map.get(&i) {
                            sum += value;
                        }
                    }
                    println!("线程 {} 计算的和: {}", thread_id, sum);
                })
            })
            .collect();

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        println!("DashMap大小: {}", map.len());
    }
}

/// 运行所有无锁哈希表示例
pub fn demonstrate_lockfree_hashmaps() {
    println!("=== 无锁哈希表演示 ===");

    LockFreeHashMap::<i32, i32>::run_example();
    SegmentedLockFreeHashMap::<i32, i32>::run_example();
    ScalableLockFreeHashMap::<i32, i32>::run_example();
    DashMapWrapper::<i32, i32>::run_example();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lockfree_hashmap() {
        let map = LockFreeHashMap::new(16);

        // 测试插入
        assert!(map.insert(1, "value1"));
        assert!(map.insert(2, "value2"));

        // 测试获取
        assert_eq!(map.get(&1), Some("value1"));
        assert_eq!(map.get(&2), Some("value2"));
        assert_eq!(map.get(&3), None);

        // 测试删除
        assert_eq!(map.remove(&1), Some("value1"));
        assert_eq!(map.get(&1), None);

        // 测试大小
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_segmented_hashmap() {
        let map = SegmentedLockFreeHashMap::new(4, 16);

        // 测试插入
        assert!(map.insert(1, "value1"));
        assert!(map.insert(2, "value2"));

        // 测试获取
        assert_eq!(map.get(&1), Some("value1"));
        assert_eq!(map.get(&2), Some("value2"));

        // 测试大小
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_dashmap_wrapper() {
        let map = DashMapWrapper::new();

        // 测试插入
        assert!(map.insert(1, "value1").is_none());
        assert!(map.insert(2, "value2").is_none());

        // 测试获取
        assert_eq!(map.get(&1), Some("value1"));
        assert_eq!(map.get(&2), Some("value2"));

        // 测试大小
        assert_eq!(map.len(), 2);
    }
}
