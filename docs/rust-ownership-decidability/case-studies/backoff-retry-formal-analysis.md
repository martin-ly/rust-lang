# Backoff/Retry 重试策略形式化分析

> **主题**: 指数退避与重试语义
>
> **形式化框架**: 退避算法 + 抖动策略
>
> **参考**: backoff crate Documentation

---

## 目录

- [Backoff/Retry 重试策略形式化分析](#backoffretry-重试策略形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 指数退避](#2-指数退避)
    - [定理 2.1 (退避公式)](#定理-21-退避公式)
  - [3. 抖动策略](#3-抖动策略)
    - [定理 3.1 (全抖动)](#定理-31-全抖动)
    - [定理 3.2 (等抖动)](#定理-32-等抖动)
  - [4. 最大重试](#4-最大重试)
    - [定理 4.1 (限制条件)](#定理-41-限制条件)
  - [5. 反例](#5-反例)
    - [反例 5.1 (无退避重试)](#反例-51-无退避重试)
    - [反例 5.2 (幂等性假设)](#反例-52-幂等性假设)

---

## 1. 引言

backoff提供:

- 指数退避
- 全抖动/等抖动
- 最大时间限制
- 可组合重试

---

## 2. 指数退避

### 定理 2.1 (退避公式)

> 延迟按指数增长。

```rust
let backoff = ExponentialBackoff {
    initial_interval: Duration::from_millis(100),
    multiplier: 2.0,
    max_interval: Duration::from_secs(10),
    ..Default::default()
};
```

**公式**:

$$
delay_n = \min(initial \cdot multiplier^n, max\_interval)
$$

∎

---

## 3. 抖动策略

### 定理 3.1 (全抖动)

> 随机化延迟防止惊群。

```rust
// 延迟 = random(0, calculated_delay)
```

∎

### 定理 3.2 (等抖动)

> 平衡退避与延迟。

```rust
// 延迟 = calculated_delay/2 + random(0, calculated_delay/2)
```

∎

---

## 4. 最大重试

### 定理 4.1 (限制条件)

| 限制 | 语义 |
|------|------|
| max_elapsed_time | 总时间上限 |
| max_interval | 单次延迟上限 |

∎

---

## 5. 反例

### 反例 5.1 (无退避重试)

```rust
// 危险: 立即重试可能压垮服务
for _ in 0..10 {
    if let Err(e) = request().await {
        continue;  // 无延迟!
    }
}

// 正确: 使用退避
let backoff = ExponentialBackoff::default();
retry(backoff, request).await?;
```

### 反例 5.2 (幂等性假设)

```rust
// 非幂等操作重试可能导致重复
retry(backoff, || charge_credit_card()).await?;  // 危险!

// 使用idempotency key
retry(backoff, || charge_with_key(key)).await?;
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
