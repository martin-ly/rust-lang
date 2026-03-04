# Prometheus客户端形式化分析

> **主题**: 指标收集的线程安全
>
> **形式化框架**: 原子操作 + 标签一致性
>
> **参考**: prometheus crate Documentation

---

## 目录

- [Prometheus客户端形式化分析](#prometheus客户端形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 指标类型](#2-指标类型)
    - [定理 2.1 (Counter单调性)](#定理-21-counter单调性)
    - [定理 2.2 (Gauge双向)](#定理-22-gauge双向)
  - [3. 标签一致性](#3-标签一致性)
    - [定理 3.1 (标签集不变式)](#定理-31-标签集不变式)
  - [4. 原子性保证](#4-原子性保证)
    - [定理 4.1 (无锁计数)](#定理-41-无锁计数)
  - [5. 反例](#5-反例)
    - [反例 5.1 (Histogram桶配置)](#反例-51-histogram桶配置)
    - [反例 5.2 (标签基数)](#反例-52-标签基数)

---

## 1. 引言

Prometheus客户端提供:

- Counter/Gauge/Histogram/Summary
- 标签动态化
- 线程安全
- 高效导出

---

## 2. 指标类型

### 定理 2.1 (Counter单调性)

> Counter只增不减。

```rust
let counter = Counter::new("requests_total", "Total requests")?;
counter.inc();      // +1
counter.add(5.0);   // +5
// counter.sub(1.0);  // 编译错误!
```

∎

### 定理 2.2 (Gauge双向)

> Gauge可增可减。

```rust
let gauge = Gauge::new("temperature", "Current temp")?;
gauge.set(25.0);
gauge.inc();
gauge.dec();
gauge.add(2.0);
gauge.sub(1.0);
```

∎

---

## 3. 标签一致性

### 定理 3.1 (标签集不变式)

> 相同指标名必须有相同标签集。

```rust
// 正确: 相同标签
requests.with_label_values(&["/api", "200"]).inc();
requests.with_label_values(&["/health", "200"]).inc();

// 运行时错误: 标签数量不匹配
requests.with_label_values(&["/api"]).inc();  // panic!
```

∎

---

## 4. 原子性保证

### 定理 4.1 (无锁计数)

> Counter使用原子操作。

```rust
// 内部使用 AtomicU64
pub fn inc(&self) {
    self.inner.inc_by(1.0);
}
```

∎

---

## 5. 反例

### 反例 5.1 (Histogram桶配置)

```rust
// 桶边界必须递增
let buckets = vec![0.005, 0.01, 0.025, 0.05, 0.1,
                   0.25, 0.5, 1.0, 2.5, 5.0, 10.0];
let hist = Histogram::with_opts(
    HistogramOpts::new("latency", "Request latency")
        .buckets(buckets)
)?;
```

### 反例 5.2 (标签基数)

```rust
// 危险: 高基数标签
for user in users {
    requests
        .with_label_values(&[&user.id])  // 无限增长!
        .inc();
}

// 正确: 有限标签集
requests
    .with_label_values(&["/api/users"])
    .inc();
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
