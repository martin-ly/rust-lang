# C13 可靠性框架: 术语表 (Glossary)

> **文档定位**: 可靠性核心术语快速参考  
> **使用方式**: 通过术语索引快速查找定义  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](../README.md) | [FAQ](./FAQ.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 参考资料

---

## 术语索引

[C](#熔断器-circuit-breaker) | [R](#raft) | [S](#stm)

---

## 熔断器 (Circuit Breaker)

**定义**: 故障隔离模式，防止级联故障。

**五状态**:

- Closed: 正常
- Open: 熔断
- Half-Open: 半开
- Forced-Open: 强制熔断
- Disabled: 禁用

**相关**: `src/fault_tolerance/circuit_breaker.rs`

---

## 限流器 (Rate Limiter)

**定义**: 流量控制机制。

**算法**: 令牌桶、漏桶、固定窗口、滑动窗口、滑动日志

**相关**: `src/fault_tolerance/rate_limiter.rs`

---

## Raft

**定义**: 分布式共识算法。

**核心**: Leader选举、日志复制

**相关**: `src/distributed_systems/raft.rs`

---

## STM

**定义**: Software Transactional Memory，软件事务内存。

**用途**: 并发控制

**相关**: `src/concurrency_models/stm.rs`

---

## Actor 模型

**定义**: 消息传递并发模型。

**相关**: `src/concurrency_models/actor.rs`

---

## 服务发现 (Service Discovery)

**定义**: 服务注册与发现机制。

**相关**: `src/microservices/service_discovery.rs`

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md)
- [FAQ](./FAQ.md)
- [README](../README.md)
