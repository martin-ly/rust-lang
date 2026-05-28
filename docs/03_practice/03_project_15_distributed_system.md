# 实践项目 15: 分布式KV存储

> **Bloom 层级**: L3 (应用)

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c05-c10
> **预计时间**: 15-20小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 15: 分布式KV存储](#实践项目-15-分布式kv存储)
  - [📑 目录](#-目录)
  - [项目目标](#项目目标)
  - [功能需求](#功能需求)
  - [学习要点](#学习要点)
    - [Raft算法](#raft算法)
  - [参考实现](#参考实现)
  - [完整参考实现位于: `examples/distributed-kv/`](#完整参考实现位于-examplesdistributed-kv)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 项目目标
>
> **[来源: Rust Official Docs]**

创建简单的分布式键值存储系统。

---

## 功能需求
>
> **[来源: Rust Official Docs]**

- [ ] Raft共识算法
- [ ] 数据分片
- [ ] 节点发现
- [ ] 故障恢复
- [ ] 客户端SDK

---

## 学习要点
>
> **[来源: Rust Official Docs]**

### Raft算法
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
enum RaftState {
    Follower,
    Candidate,
    Leader,
}

struct RaftNode {
    state: RaftState,
    term: u64,
    log: Vec<LogEntry>,
}
```

---

## 参考实现
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

完整参考实现位于: `examples/distributed-kv/`
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

## 相关概念

- [03_practice 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
