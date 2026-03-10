# Rust 1.94: 并发编程模式更新

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10

---

## 目录

- [Rust 1.94: 并发编程模式更新](#rust-194-并发编程模式更新)
  - [目录](#目录)
  - [ControlFlow 在并发中的应用](#controlflow-在并发中的应用)
    - [1.1 并行搜索提前返回](#11-并行搜索提前返回)
  - [细粒度锁模式](#细粒度锁模式)
    - [2.1 RefCell 映射优化](#21-refcell-映射优化)
    - [2.2 读写锁分离](#22-读写锁分离)
  - [无锁数据结构](#无锁数据结构)
    - [3.1 基于 MaybeUninit 的无锁队列](#31-基于-maybeuninit-的无锁队列)
  - [异步与线程混合](#异步与线程混合)
    - [4.1 线程池与异步集成](#41-线程池与异步集成)
  - [相关文档](#相关文档)

---

## ControlFlow 在并发中的应用

### 1.1 并行搜索提前返回

```rust
use std::ops::ControlFlow;
use rayon::prelude::*;

/// 并行搜索，找到第一个匹配立即返回
fn parallel_find_first<T, P>(data: &[T], predicate: P) -> Option<&T>
where
    T: Sync,
    P: Fn(&T) -> bool + Sync,
{
    data.par_iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

/// 并行验证所有元素
fn parallel_all<T, P>(data: &[T], predicate: P) -> bool
where
    T: Sync,
    P: Fn(&T) -> bool + Sync,
{
    data.par_iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Continue(())
        } else {
            ControlFlow::Break(())
        }
    }).is_continue()
}
```

---

## 细粒度锁模式

### 2.1 RefCell 映射优化

```rust
use std::cell::{RefCell, Ref, RefMut};
use std::collections::HashMap;
use std::sync::Arc;

/// 使用 RefCell 映射的细粒度缓存
pub struct FineGrainedCache<K, V> {
    buckets: Vec<RefCell<HashMap<K, V>>>,
}

impl<K: Eq + std::hash::Hash, V: Clone> FineGrainedCache<K, V> {
    pub fn new(bucket_count: usize) -> Self {
        let mut buckets = Vec::with_capacity(bucket_count);
        for _ in 0..bucket_count {
            buckets.push(RefCell::new(HashMap::new()));
        }
        Self { buckets }
    }

    fn get_bucket(&self, key: &K) -> usize {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % self.buckets.len()
    }

    /// 获取值，不克隆
    pub fn get(&self, key: &K) -> Option<Ref<V>> {
        let bucket_idx = self.get_bucket(key);
        let bucket = self.buckets[bucket_idx].borrow();

        Ref::filter_map(bucket, |map| map.get(key)).ok()
    }

    /// 获取可变引用
    pub fn get_mut(&self, key: &K) -> Option<RefMut<V>> {
        let bucket_idx = self.get_bucket(key);
        let bucket = self.buckets[bucket_idx].borrow_mut();

        RefMut::filter(bucket, |map| map.get_mut(key)).ok()
    }

    pub fn insert(&self, key: K, value: V) {
        let bucket_idx = self.get_bucket(key);
        self.buckets[bucket_idx].borrow_mut().insert(key, value);
    }
}
```

### 2.2 读写锁分离

```rust
use std::sync::{Arc, RwLock};
use std::collections::BTreeMap;

/// 读写分离的并发索引
pub struct ConcurrentIndex<K, V> {
    index: RwLock<BTreeMap<K, Vec<V>>>,
    hot_cache: Arc<RwLock<Vec<(K, V)>>>,
}

impl<K: Ord + Clone, V: Clone> ConcurrentIndex<K, V> {
    pub fn new() -> Self {
        Self {
            index: RwLock::new(BTreeMap::new()),
            hot_cache: Arc::new(RwLock::new(Vec::with_capacity(1000))),
        }
    }

    /// 批量索引（写操作）
    pub fn batch_index(&self, items: Vec<(K, V)>) {
        let mut index = self.index.write().unwrap();

        for (key, value) in items {
            index.entry(key).or_insert_with(Vec::new).push(value);
        }
    }

    /// 范围查询（读操作）
    pub fn range_query(&self, start: &K, end: &K) -> Vec<(K, Vec<V>)> {
        let index = self.index.read().unwrap();

        index.range(start..=end)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    /// 热数据缓存
    pub fn cache_hot(&self, key: K, value: V) {
        let mut cache = self.hot_cache.write().unwrap();
        if cache.len() >= 1000 {
            cache.remove(0);
        }
        cache.push((key, value));
    }
}
```

---

## 无锁数据结构

### 3.1 基于 MaybeUninit 的无锁队列

```rust
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::cell::UnsafeCell;

/// 无锁单生产者单消费者队列
pub struct LockFreeQueue<T, const N: usize> {
    buffer: [UnsafeCell<MaybeUninit<T>>; N],
    head: AtomicUsize,
    tail: AtomicUsize,
}

unsafe impl<T: Send, const N: usize> Send for LockFreeQueue<T, N> {}
unsafe impl<T: Send, const N: usize> Sync for LockFreeQueue<T, N> {}

impl<T, const N: usize> LockFreeQueue<T, N> {
    pub fn new() -> Self {
        let buffer = unsafe {
            let mut arr: [UnsafeCell<MaybeUninit<T>>; N] =
                std::mem::zeroed();
            for i in 0..N {
                arr[i] = UnsafeCell::new(MaybeUninit::uninit());
            }
            arr
        };

        Self {
            buffer,
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
        }
    }

    /// 生产者：入队
    pub fn enqueue(&self, value: T) -> Result<(), T> {
        let tail = self.tail.load(Ordering::Relaxed);
        let next_tail = (tail + 1) % N;

        // 检查队列是否已满
        if next_tail == self.head.load(Ordering::Acquire) {
            return Err(value);
        }

        // 写入数据
        unsafe {
            (*self.buffer[tail].get()).write(value);
        }

        // 更新 tail
        self.tail.store(next_tail, Ordering::Release);

        Ok(())
    }

    /// 消费者：出队
    pub fn dequeue(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);

        // 检查队列是否为空
        if head == self.tail.load(Ordering::Acquire) {
            return None;
        }

        // 读取数据
        let value = unsafe {
            (*self.buffer[head].get()).assume_init_read()
        };

        // 更新 head
        self.head.store((head + 1) % N, Ordering::Release);

        Some(value)
    }
}

impl<T, const N: usize> Drop for LockFreeQueue<T, N> {
    fn drop(&mut self) {
        // 清理剩余元素
        while let Some(_) = self.dequeue() {}
    }
}
```

---

## 异步与线程混合

### 4.1 线程池与异步集成

```rust
use std::future::Future;
use tokio::task::JoinHandle;

/// 计算密集型任务在线程池执行
pub fn spawn_blocking<F, R>(f: F) -> JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    tokio::task::spawn_blocking(f)
}

/// 混合模式：异步 IO + 计算
async fn hybrid_processing(data: Vec<u8>) -> Result<Vec<u8>, String> {
    // 异步读取数据
    let data = tokio::fs::read("input.dat").await
        .map_err(|e| e.to_string())?;

    // 在线程池中执行计算
    let processed = spawn_blocking(move || {
        data.iter().map(|b| b.wrapping_mul(2)).collect::<Vec<_>>()
    }).await.map_err(|e| e.to_string())?;

    // 异步写入结果
    tokio::fs::write("output.dat", &processed).await
        .map_err(|e| e.to_string())?;

    Ok(processed)
}

/// 使用 ControlFlow 的批量处理
async fn batch_process_with_control_flow(
    items: Vec<i32>
) -> ControlFlow<String, Vec<i32>> {
    let mut results = Vec::with_capacity(items.len());

    for chunk in items.chunks(100) {
        // 每 100 个一组在线程池处理
        let chunk_results = spawn_blocking({
            let chunk = chunk.to_vec();
            move || {
                chunk.iter().map(|&x| x * x).collect::<Vec<_>>()
            }
        }).await;

        match chunk_results {
            Ok(processed) => results.extend(processed),
            Err(e) => return ControlFlow::Break(e.to_string()),
        }
    }

    ControlFlow::Continue(results)
}
```

---

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [C05 线程主索引](../00_MASTER_INDEX.md)
