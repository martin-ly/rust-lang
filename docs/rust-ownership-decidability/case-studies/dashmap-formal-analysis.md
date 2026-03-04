# DashMap并发HashMap形式化分析

> **主题**: 并发安全的HashMap
> **形式化框架**: 分片锁 + 读优化 + 迭代安全
> **参考**: DashMap Documentation (<https://docs.rs/dashmap>)

---

## 目录

- [DashMap并发HashMap形式化分析](#dashmap并发hashmap形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 分片架构](#2-分片架构)
    - [定义 SHARD-1 ( 分片结构 )](#定义-shard-1--分片结构-)
    - [定义 SHARD-2 ( 键分配 )](#定义-shard-2--键分配-)
    - [定理 SHARD-T1 ( 锁粒度 )](#定理-shard-t1--锁粒度-)
  - [3. 读写操作](#3-读写操作)
    - [定义 READ-1 ( 获取 )](#定义-read-1--获取-)
    - [定义 WRITE-1 ( 插入 )](#定义-write-1--插入-)
    - [定义 WRITE-2 ( 条件修改 )](#定义-write-2--条件修改-)
  - [4. 迭代安全](#4-迭代安全)
    - [定义 ITER-1 ( 快照迭代 )](#定义-iter-1--快照迭代-)
    - [定义 ITER-2 ( 迭代器一致性 )](#定义-iter-2--迭代器一致性-)
    - [定理 ITER-T1 ( 弱一致性 )](#定理-iter-t1--弱一致性-)
  - [5. 引用类型](#5-引用类型)
    - [定义 REF-1 ( Ref类型 )](#定义-ref-1--ref类型-)
    - [定义 REF-2 ( RefMut类型 )](#定义-ref-2--refmut类型-)
    - [定理 REF-T1 ( 自动释放 )](#定理-ref-t1--自动释放-)
  - [6. 性能保证](#6-性能保证)
    - [定义 PERF-1 ( 读优化 )](#定义-perf-1--读优化-)
    - [定理 PERF-T1 ( 扩展性 )](#定理-perf-t1--扩展性-)
  - [7. 定理与证明](#7-定理与证明)
    - [定理 DASHMAP-T1 ( 线程安全 )](#定理-dashmap-t1--线程安全-)
    - [定理 DASHMAP-T2 ( 死锁避免 )](#定理-dashmap-t2--死锁避免-)
  - [8. 代码示例](#8-代码示例)
    - [示例1: 并发计数器](#示例1-并发计数器)
    - [示例2: 缓存实现](#示例2-缓存实现)
    - [示例3: 条件更新](#示例3-条件更新)

---

## 1. 引言

DashMap特点：

- 并发HashMap
- 分片锁减少竞争
- 读优化（大部分无锁）
- 可升级读锁

---

## 2. 分片架构

### 定义 SHARD-1 ( 分片结构 )

```rust
DashMap<K, V, S> {
    shards: [RwLock<HashMap<K, V, S>>; N],
    hasher: S,
}
```

**形式化**:

$$
\text{DashMap} = \{ s_1, s_2, \ldots, s_n \} \text{ where } n = \text{shard\_count}
$$

### 定义 SHARD-2 ( 键分配 )

$$
\text{shard}(k) = \text{hash}(k) \mod n
$$

### 定理 SHARD-T1 ( 锁粒度 )

单个分片锁定不影响其他分片。

$$
\text{write}(s_i) \to \text{block}(s_i) \land \forall j \neq i.\ \text{available}(s_j)
$$

---

## 3. 读写操作

### 定义 READ-1 ( 获取 )

```rust
map.get(&key) -> Option<Ref<K, V>>
```

### 定义 WRITE-1 ( 插入 )

```rust
map.insert(key, value) -> Option<V>
```

### 定义 WRITE-2 ( 条件修改 )

```rust
map.entry(key).and_modify(|v| *v += 1).or_insert(0);
```

---

## 4. 迭代安全

### 定义 ITER-1 ( 快照迭代 )

```rust
for (k, v) in map.iter() { }
```

### 定义 ITER-2 ( 迭代器一致性 )

$$
\text{iter}() \to \text{snapshot\_at\_point\_in\_time}
$$

### 定理 ITER-T1 ( 弱一致性 )

迭代器看到快照，不反映并发修改。

$$
\text{concurrent\_insert} \notin \text{iteration\_results}
$$

---

## 5. 引用类型

### 定义 REF-1 ( Ref类型 )

```rust
Ref<K, V> {
    key: &K,
    value: &V,
    shard: RwLockReadGuard<'a>,
}
```

### 定义 REF-2 ( RefMut类型 )

```rust
RefMut<K, V> {
    key: &K,
    value: &mut V,
    shard: RwLockWriteGuard<'a>,
}
```

### 定理 REF-T1 ( 自动释放 )

Guard在Ref drop时释放。

$$
\text{drop}(\text{Ref}) \to \text{shard\_unlock}
$$

---

## 6. 性能保证

### 定义 PERF-1 ( 读优化 )

| 场景 | 复杂度 | 锁状态 |
| :--- | :--- | :--- |
| get | O(1) | 读锁 |
| insert | O(1) | 写锁 |
| iter | O(n) | 读锁 |

### 定理 PERF-T1 ( 扩展性 )

性能随分片数增加。

$$
\text{throughput}(n) \propto \min(n, \text{num\_cpus})
$$

---

## 7. 定理与证明

### 定理 DASHMAP-T1 ( 线程安全 )

所有操作线程安全。

$$
\forall ops.\ \text{thread\_safe}(ops) \land \text{no\_data\_race}
$$

### 定理 DASHMAP-T2 ( 死锁避免 )

不持有多个分片锁。

$$
\neg\exists t.\ \text{holds}(s_i) \land \text{holds}(s_j) \land i \neq j
$$

---

## 8. 代码示例

### 示例1: 并发计数器

```rust
use dashmap::DashMap;
use std::sync::Arc;

async fn concurrent_counter() {
    let map: Arc<DashMap<String, i32>> = Arc::new(DashMap::new());

    let handles: Vec<_> = (0..10)
        .map(|i| {
            let map = Arc::clone(&map);
            tokio::spawn(async move {
                for _ in 0..1000 {
                    map.entry(format!("key-{}", i % 5))
                        .and_modify(|v| *v += 1)
                        .or_insert(1);
                }
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }

    println!("Final counts: {:?}", map);
}
```

### 示例2: 缓存实现

```rust
use dashmap::DashMap;
use std::hash::Hash;

struct Cache<K, V> {
    inner: DashMap<K, V>,
    max_size: usize,
}

impl<K: Eq + Hash, V: Clone> Cache<K, V> {
    fn new(max_size: usize) -> Self {
        Cache {
            inner: DashMap::with_capacity(max_size),
            max_size,
        }
    }

    fn get(&self, key: &K) -> Option<V> {
        self.inner.get(key).map(|r| r.clone())
    }

    fn put(&self, key: K, value: V) {
        if self.inner.len() >= self.max_size {
            // 简单LRU: 移除任意条目
            if let Some(entry) = self.inner.iter().next() {
                let key = entry.key().clone();
                drop(entry);
                self.inner.remove(&key);
            }
        }
        self.inner.insert(key, value);
    }
}
```

### 示例3: 条件更新

```rust
use dashmap::DashMap;

fn conditional_update(map: &DashMap<String, i32>, key: &str) {
    // 获取可变引用进行修改
    if let Some(mut entry) = map.get_mut(key) {
        let current = *entry.value();
        if current > 0 {
            *entry.value_mut() = current - 1;
        }
    }

    // 或者使用entry API
    map.entry(key.to_string())
        .and_modify(|v| {
            if *v > 0 {
                *v -= 1;
            }
        })
        .or_insert(100);
}
```

---

**维护者**: Rust Concurrency Formal Methods Team
**创建日期**: 2026-03-05
**DashMap版本**: 6.x
**状态**: ✅ 已对齐
