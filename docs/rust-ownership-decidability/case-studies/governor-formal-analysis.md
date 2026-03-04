# Governor 限流形式化分析

> **主题**: 令牌桶/漏桶限流算法
>
> **形式化框架**: 速率约束 + 突发控制
>
> **参考**: governor Documentation

---

## 目录

- [Governor 限流形式化分析](#governor-限流形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 限流器类型](#2-限流器类型)
    - [定理 2.1 (两种限流器)](#定理-21-两种限流器)
  - [3. 令牌桶算法](#3-令牌桶算法)
    - [定理 3.1 (令牌桶语义)](#定理-31-令牌桶语义)
  - [4. 并发限流](#4-并发限流)
    - [定理 4.1 (共享限流器)](#定理-41-共享限流器)
  - [5. 反例](#5-反例)
    - [反例 5.1 (时钟回拨)](#反例-51-时钟回拨)
    - [反例 5.2 (内存增长)](#反例-52-内存增长)

---

## 1. 引言

governor提供:

- 令牌桶限流
- 漏桶限流
- 自适应限流
- 无锁实现

---

## 2. 限流器类型

### 定理 2.1 (两种限流器)

| 类型 | 特点 | 场景 |
|------|------|------|
| RateLimiter | 检查是否允许 | API限流 |
| DirectRateLimiter | 自动等待 | 任务调度 |

∎

---

## 3. 令牌桶算法

### 定理 3.1 (令牌桶语义)

> 以固定速率补充令牌，突发时可消耗桶内令牌。

```rust
let quota = Quota::per_second(nonzero!(10u32))  // 每秒10个
    .allow_burst(nonzero!(5u32));                // 桶容量5

let limiter = RateLimiter::direct(quota);
```

**形式化**:

$$
\text{tokens}_{t+1} = \min(capacity, \text{tokens}_t + rate \cdot \Delta t)
$$

∎

---

## 4. 并发限流

### 定理 4.1 (共享限流器)

> `Arc<RateLimiter>`可跨任务共享。

```rust
let limiter = Arc::new(RateLimiter::direct(quota));

for _ in 0..10 {
    let lim = Arc::clone(&limiter);
    spawn(async move {
        lim.until_ready().await;
        do_work().await;
    });
}
```

∎

---

## 5. 反例

### 反例 5.1 (时钟回拨)

```rust
// 系统时间回拨可能导致限流异常
// governor使用单调时钟避免
```

### 反例 5.2 (内存增长)

```rust
// 每个key一个限流器需限制数量
let mut limiters: HashMap<String, RateLimiter> = HashMap::new();
// 无限增长可能OOM
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
