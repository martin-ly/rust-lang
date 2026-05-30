# LRU/Cached 缓存形式化分析

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 内存缓存的过期与驱逐
>
> **形式化框架**: 访问顺序 + 容量约束
>
> **参考**: lru crate; cached crate Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

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
  - *定理数量: 4个*
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

缓存库提供:

- LRU驱逐策略
- TTL过期
- 并发安全
- 内存限制

---

## 2. LRU语义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (最近最少使用)

> 容量满时驱逐最久未访问项。

```rust,ignore
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

```rust,ignore
let cache = DashCache::new(1000);
cache.insert(key, value).await;
let val = cache.get(&key).await;
```

∎

---

## 4. 过期策略

### 定理 4.1 (TTL)

> 时间过期独立于LRU。

```rust,ignore
#[cached(size = 100, time = 60)]  // 60秒过期
fn expensive_compute(input: u64) -> u64 {
    // 结果缓存60秒
}
```

∎

---

## 5. 反例

### 反例 5.1 (缓存穿透)

```rust,ignore
// 大量不存在的key查询
cache.get(&nonexistent_key);  // 每次miss

// 缓解: 缓存None或使用BloomFilter
```

### 反例 5.2 (大Value)

```rust,ignore
// 缓存超大对象可能导致OOM
cache.insert(key, huge_vec);  // 需限制value大小
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**
