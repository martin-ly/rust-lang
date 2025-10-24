# 🗺️ Rust 1.90 模型 - 综合思维导图

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20

---

## 📊 目录

- [🗺️ Rust 1.90 模型 - 综合思维导图](#️-rust-190-模型---综合思维导图)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🌳 整体架构](#-整体架构)
  - [📊 形式语义](#-形式语义)
    - [操作语义 (Operational Semantics)](#操作语义-operational-semantics)
    - [指称语义 (Denotational Semantics)](#指称语义-denotational-semantics)
    - [公理语义 (Axiomatic Semantics)](#公理语义-axiomatic-semantics)
  - [🌐 分布式模型](#-分布式模型)
    - [一致性算法](#一致性算法)
    - [分布式快照](#分布式快照)
  - [🔄 并发模型](#-并发模型)
    - [CSP vs Actor](#csp-vs-actor)
    - [共享内存 vs 消息传递](#共享内存-vs-消息传递)
  - [📚 学习路径](#-学习路径)
    - [Week 1-2: 形式语义](#week-1-2-形式语义)
    - [Week 3-4: 分布式](#week-3-4-分布式)
    - [Week 5-6: 并发](#week-5-6-并发)

## 📋 目录

- [🌳 整体架构](#-整体架构)
- [📊 形式语义](#-形式语义)
- [🌐 分布式模型](#-分布式模型)
- [🔄 并发模型](#-并发模型)
- [📚 学习路径](#-学习路径)

---

## 🌳 整体架构

```text
      Rust 模型体系
            │
   ┌────────┼────────┐
   │        │        │
形式语义 分布式  并发模型
   │        │        │
操作语义  Raft   CSP/Actor
指称语义  Paxos  STM/Fork-Join
公理语义  2PC    消息传递
```

---

## 📊 形式语义

### 操作语义 (Operational Semantics)

- 小步语义 (Small-step)
- 大步语义 (Big-step)
- 结构化操作语义 (SOS)

### 指称语义 (Denotational Semantics)

- 域理论 (Domain Theory)
- 连续函数
- 不动点语义

### 公理语义 (Axiomatic Semantics)

- Hoare逻辑
- 前置/后置条件
- 不变式

---

## 🌐 分布式模型

### 一致性算法

- **Raft**: 领导选举、日志复制
- **Paxos**: 多数派协议
- **2PC/3PC**: 两阶段/三阶段提交
- **Gossip**: 最终一致性

### 分布式快照

- Chandy-Lamport算法
- 向量时钟 (Vector Clocks)

---

## 🔄 并发模型

### CSP vs Actor

- **CSP**: Channel通信
- **Actor**: 消息传递

### 共享内存 vs 消息传递

- 锁/原子操作
- Channel/消息队列

---

## 📚 学习路径

### Week 1-2: 形式语义

- 操作语义基础
- 类型系统形式化

### Week 3-4: 分布式

- Raft/Paxos原理
- 一致性模型

### Week 5-6: 并发

- CSP/Actor模型
- 形式化验证

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20

---

🗺️ **掌握理论模型，深入理解Rust！** 🚀✨
