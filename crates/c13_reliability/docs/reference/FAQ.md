# C13 可靠性框架: 常见问题解答 (FAQ)

> **文档定位**: 可靠性实践中的常见问题快速解答  
> **使用方式**: 遇到问题时快速查找解决方案  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](../README.md) | [Glossary](./Glossary.md)


## 📊 目录

- [📋 问题索引](#问题索引)
- [容错机制](#容错机制)
  - [Q1: 如何使用熔断器？](#q1-如何使用熔断器)
  - [Q2: 如何选择限流算法？](#q2-如何选择限流算法)
- [分布式系统](#分布式系统)
  - [Q3: Raft如何保证一致性？](#q3-raft如何保证一致性)
- [微服务](#微服务)
  - [Q4: 如何实现服务发现？](#q4-如何实现服务发现)
- [可观测性](#可观测性)
  - [Q5: 如何收集指标？](#q5-如何收集指标)
- [📚 延伸阅读](#延伸阅读)


**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 问题解答

---

## 📋 问题索引

- [C13 可靠性框架: 常见问题解答 (FAQ)](#c13-可靠性框架-常见问题解答-faq)
  - [📋 问题索引](#-问题索引)
  - [容错机制](#容错机制)
    - [Q1: 如何使用熔断器？](#q1-如何使用熔断器)
    - [Q2: 如何选择限流算法？](#q2-如何选择限流算法)
  - [分布式系统](#分布式系统)
    - [Q3: Raft如何保证一致性？](#q3-raft如何保证一致性)
  - [微服务](#微服务)
    - [Q4: 如何实现服务发现？](#q4-如何实现服务发现)
  - [可观测性](#可观测性)
    - [Q5: 如何收集指标？](#q5-如何收集指标)
  - [📚 延伸阅读](#-延伸阅读)

---

## 容错机制

### Q1: 如何使用熔断器？

**A**: 使用五状态熔断器：

```rust
use c13_reliability::fault_tolerance::CircuitBreaker;

let cb = CircuitBreaker::new();
let result = cb.call(|| async { /* 调用服务 */ }).await;
```

**相关**: `src/fault_tolerance/circuit_breaker.rs`

---

### Q2: 如何选择限流算法？

**A**: 根据场景选择：

- **令牌桶**: 允许突发流量
- **漏桶**: 平滑流量
- **固定窗口**: 简单实现
- **滑动窗口**: 精确控制
- **滑动日志**: 最精确

**相关**: `src/fault_tolerance/rate_limiter.rs`

---

## 分布式系统

### Q3: Raft如何保证一致性？

**A**: 通过 Leader选举 和 日志复制。

**相关**: `src/distributed_systems/raft.rs`

---

## 微服务

### Q4: 如何实现服务发现？

**A**: 使用注册中心模式。

**相关**: `src/microservices/service_discovery.rs`

---

## 可观测性

### Q5: 如何收集指标？

**A**: 使用 Metrics 模块：

```rust
use c13_reliability::observability::Metrics;

let metrics = Metrics::new();
metrics.counter("requests").inc();
```

**相关**: `src/observability/metrics.rs`

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md)
- [README](../README.md)
- [Glossary](./Glossary.md)
