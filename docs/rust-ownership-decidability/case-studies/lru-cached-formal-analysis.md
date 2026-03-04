# LRU/Cached 缓存形式化分析

> **主题**: 内存缓存的过期与驱逐
>
> **形式化框架**: 访问顺序 + 容量约束
>
> **参考**: lru crate; cached crate Documentation

---

## 目录

- [LRU/Cached 缓存形式化分析](#lrucached-缓存形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. LRU语义](#2-lru语义)
    - [定理 2.1 (最近最少使用)](#定理-21-最近最少使用)
  - [3. 并发缓存](#3-并发缓存)
    - [定理 3.1 (DashCache)](#定理-31-dashcache)
  - [4. 过期策略](#4-过期策略)
    - [定理 4.1 (TTL)](#定理-41-ttl)
  - [5. 反例](#5-反例)
    - [反例 5.1 (缓存穿透)](#反例-51-缓存穿透)
    - [反例 5.2 (大Value)](#反例-52-大value)

---

## 1. 引言

缓存库提供:

- LRU驱逐策略
- TTL过期
- 并发安全
- 内存限制

---

## 2. LRU语义

### 定理 2.1 (最近最少使用)

> 容量满时驱逐最久未访问项。

```rust
let mut cache = LruCache::new(NonZeroUsize::new(3).unwrap());
cache.put("a", 1);
cache.put("b", 2);
cache.put("c", 3);
cache.get("a");      // 访问a
cache.put("d", 4);   // 驱逐b (最久未用)
```

∎

---

## 3. 并发缓存

### 定理 3.1 (DashCache)

> 并发LRU使用分段锁。

```rust
let cache = DashCache::new(1000);
cache.insert(key, value).await;
let val = cache.get(&key).await;
```

∎

---

## 4. 过期策略

### 定理 4.1 (TTL)

> 时间过期独立于LRU。

```rust
#[cached(size = 100, time = 60)]  // 60秒过期
fn expensive_compute(input: u64) -> u64 {
    // 结果缓存60秒
}
```

∎

---

## 5. 反例

### 反例 5.1 (缓存穿透)

```rust
// 大量不存在的key查询
cache.get(&nonexistent_key);  // 每次miss

// 缓解: 缓存None或使用BloomFilter
```

### 反例 5.2 (大Value)

```rust
// 缓存超大对象可能导致OOM
cache.insert(key, huge_vec);  // 需限制value大小
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
