# Moka 并发缓存形式化分析

> **主题**: 高性能并发缓存
>
> **形式化框架**: 分段锁 + TTL驱逐
>
> **参考**: moka Documentation

---

## 目录

- [Moka 并发缓存形式化分析](#moka-并发缓存形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 架构设计](#2-架构设计)
    - [定理 2.1 (分段锁)](#定理-21-分段锁)
    - [定理 2.2 (无锁读取)](#定理-22-无锁读取)
  - [3. 驱逐策略](#3-驱逐策略)
    - [定理 3.1 (Window-TinyLFU)](#定理-31-window-tinylfu)
  - [4. TTL支持](#4-ttl支持)
    - [定理 4.1 (过期策略)](#定理-41-过期策略)
  - [5. 反例](#5-反例)
    - [反例 5.1 (缓存雪崩)](#反例-51-缓存雪崩)

---

## 1. 引言

Moka提供:

- 高性能并发缓存
- 类Caffeine设计
- TTL/TTI支持
- 异步支持

---

## 2. 架构设计

### 定理 2.1 (分段锁)

> 使用分段锁提高并发度。

```rust
let cache: Cache<String, Vec<u8>> = Cache::builder()
    .max_capacity(10000)
    .build();
```

∎

### 定理 2.2 (无锁读取)

> 读取路径无需锁定。

```rust
// 并发安全读取
if let Some(value) = cache.get(&key).await {
    return value;
}
```

∎

---

## 3. 驱逐策略

### 定理 3.1 (Window-TinyLFU)

> 使用Window-TinyLFU算法。

**策略**:

- 新项进入窗口缓存
- 溢出项进入SLRU主缓存
- 频率统计指导驱逐

∎

---

## 4. TTL支持

### 定理 4.1 (过期策略)

> 支持多种过期策略。

```rust
let cache = Cache::builder()
    .max_capacity(10000)
    .time_to_live(Duration::from_secs(60))   // TTL
    .time_to_idle(Duration::from_secs(30))   // TTI
    .build();
```

∎

---

## 5. 反例

### 反例 5.1 (缓存雪崩)

```rust
// 同时大量miss，后端压力
let value = cache.get(&key).await
    .unwrap_or_else(|| fetch_expensive(key).await);

// 正确: 使用get_with
let value = cache.get_with(key, async move {
    fetch_expensive(key).await
}).await;
// 只会有一个请求到达后端
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
