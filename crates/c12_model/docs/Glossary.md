# C12 模型与架构: 术语表 (Glossary)

> **文档定位**: 模型与架构核心术语快速参考  
> **使用方式**: 通过术语索引快速查找定义  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)


## 📊 目录

- [术语索引](#术语索引)
- [Actor 模型](#actor-模型)
- [CSP](#csp)
- [Raft](#raft)
- [ML](#ml)
- [背压 (Backpressure)](#背压-backpressure)
- [📚 延伸阅读](#延伸阅读)


**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 参考资料

---

## 术语索引

[A](#actor-模型) | [C](#csp) | [M](#ml) | [R](#raft)

---

## Actor 模型

**定义**: 消息传递并发模型。

**特点**: 异步通信、独立状态

**相关**: `src/parallel_concurrent_models.rs`

---

## CSP

**定义**: Communicating Sequential Processes，通信顺序进程。

**特点**: Channel通信、进程同步

---

## Raft

**定义**: 分布式共识算法。

**用途**: 分布式一致性

**相关**: `src/distributed_models.rs`

---

## ML

**定义**: Machine Learning，机器学习。

**Rust支持**: tch-rs, ndarray

**相关**: `src/ml_models.rs`

---

## 背压 (Backpressure)

**定义**: 流量控制机制。

**实现**: 有界channel

**相关**: `examples/async_backpressure_demo.rs`

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md)
- [FAQ](./FAQ.md)
- [README](./README.md)
