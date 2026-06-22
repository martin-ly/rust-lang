# 形式化内容总索引
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L2 (理解)
> **创建日期**: 2026-05-12
> **版本**: 1.0
> **状态**: ✅ 已完成
> **维护者**: 项目文档维护团队

---

## 📑 目录

- [形式化内容总索引](#形式化内容总索引)
  - [📑 目录](#-目录)
  - [1. 索引说明](#1-索引说明)
  - [2. 按主题索引](#2-按主题索引)
    - [2.1 所有权与借用形式化](#21-所有权与借用形式化)
    - [2.2 类型理论](#22-类型理论)
    - [2.3 并发与异步形式化](#23-并发与异步形式化)
    - [2.4 设计模式形式化](#24-设计模式形式化)
    - [2.5 验证工具](#25-验证工具)
    - [2.6 案例研究](#26-案例研究)
  - [3. 快速决策树](#3-快速决策树)
  - [4. 维护记录](#4-维护记录)
  - [5. 相关文档](#5-相关文档)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 索引说明
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本项目包含两个主要的形式化内容体系：

- **`docs/rust-ownership-decidability/`**: Rust 所有权系统的完整、严格、可机械化形式化理论（600K+ 字，642 文件）
- **`docs/research_notes/`**: 通用研究笔记（形式化方法、类型理论、软件设计理论，150+ 文件）

本索引提供**统一导航**，避免读者在两个体系间迷失。

---

## 2. 按主题索引
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 所有权与借用形式化
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 深度 | 位置 | 说明 |
|------|------|------|
| ⭐⭐⭐ 完整理论 | [`rust-ownership-decidability/01-core-concepts/`](../rust-ownership-decidability/01-core-concepts/) | 所有权规则、借用系统、生命周期、内部可变性 |
| ⭐⭐⭐ Coq 证明 | [`rust-ownership-decidability/formal-foundations/proofs/`](../rust-ownership-decidability/formal-foundations/proofs/) | 类型安全、进展性、保持性、可判定性 |
| ⭐⭐ 研究笔记 | [`research_notes/formal_methods/10_ownership_model.md`](../research_notes/formal_methods/10_ownership_model.md) | 所有权模型概述 |
| ⭐⭐ 研究笔记 | [`research_notes/formal_methods/10_borrow_checker_proof.md`](../research_notes/formal_methods/10_borrow_checker_proof.md) | 借用检查器证明 |

**建议**: 优先阅读 `rust-ownership-decidability/` 侧内容，更系统、更完整。

### 2.2 类型理论

| 深度 | 位置 | 说明 |
|------|------|------|
| ⭐⭐ 通用基础 | [`research_notes/type_theory/`](../research_notes/type_theory/) | 类型系统基础、方差、常量求值 |
| ⭐⭐⭐ Rust 特定 | [`rust-ownership-decidability/01-core-concepts/`](../rust-ownership-decidability/01-core-concepts/) | Rust 类型系统的形式化语义 |
| ⭐⭐⭐ 前沿特性 | [`rust-ownership-decidability/08-advanced-topics/`](../rust-ownership-decidability/08-advanced-topics/) | 常量泛型、异步 Rust、过程宏 |

**建议**: 类型理论通用基础读 `research_notes/`，Rust 特定深入读 `rust-ownership-decidability/`。

### 2.3 并发与异步形式化

| 深度 | 位置 | 说明 |
|------|------|------|
| ⭐⭐⭐ 并发模式 | [`rust-ownership-decidability/12-concurrency-patterns/`](../rust-ownership-decidability/12-concurrency-patterns/) | 并发架构、消息传递、数据并行、锁自由模式 |
| ⭐⭐⭐ Actor 模型 | [`rust-ownership-decidability/actor-specialty/`](../rust-ownership-decidability/actor-specialty/) | Actor 框架、分布式 Actor |
| ⭐⭐ 异步状态机 | [`research_notes/formal_methods/10_async_state_machine.md`](../research_notes/formal_methods/10_async_state_machine.md) | 异步状态机形式化 |
| ⭐⭐ Send/Sync | [`research_notes/formal_methods/10_send_sync_formalization.md`](../research_notes/formal_methods/10_send_sync_formalization.md) | Send/Sync 形式化 |

### 2.4 设计模式形式化

| 深度 | 位置 | 说明 |
|------|------|------|
| ⭐⭐⭐ Rust 特定 | [`rust-ownership-decidability/11-design-patterns/`](../rust-ownership-decidability/11-design-patterns/) | Rust 设计模式深度分析 |
| ⭐⭐ 通用形式化 | [`research_notes/software_design_theory/01_design_patterns_formal/`](../research_notes/software_design_theory/01_design_patterns_formal/) | 23 种设计模式形式化 |
| ⭐⭐ 工作流引擎 | [`research_notes/software_design_theory/02_workflow/`](../research_notes/software_design_theory/02_workflow/) | 工作流状态机、补偿链、长事务 |

### 2.5 验证工具

| 工具 | 位置 | 状态 |
|------|------|------|
| Coq 形式化 | [`rust-ownership-decidability/coq-formalization/`](../rust-ownership-decidability/coq-formalization/) | 11,980+ 行，300+ Qed |
| Miri | `research_notes/formal_methods/MIRI_EXECUTION_MODEL.md` | 执行模型分析 |
| Tree Borrows | `research_notes/formal_methods/tree_borrows_analysis.md` | 别名模型 |

### 2.6 案例研究

| 领域 | 位置 |
|------|------|
| 游戏开发 | [`rust-ownership-decidability/case-studies/gamedev/`](../rust-ownership-decidability/case-studies/gamedev/) |
| 区块链 | [`rust-ownership-decidability/case-studies/blockchain/`](../rust-ownership-decidability/case-studies/blockchain/) |
| 云原生 | [`rust-ownership-decidability/case-studies/cloud/`](../rust-ownership-decidability/case-studies/cloud/) |
| CLI 工具 | [`rust-ownership-decidability/case-studies/cli/`](../rust-ownership-decidability/case-studies/cli/) |
| 数据库 | [`rust-ownership-decidability/case-studies/database/`](../rust-ownership-decidability/case-studies/database/) |
| 嵌入式 | [`rust-ownership-decidability/case-studies/embedded/`](../rust-ownership-decidability/case-studies/embedded/) |
| ML/AI | [`rust-ownership-decidability/case-studies/ml-ai/`](../rust-ownership-decidability/case-studies/ml-ai/) |
| Serde | [`rust-ownership-decidability/case-studies/serde-formal-analysis-deep.md`](../rust-ownership-decidability/case-studies/serde-formal-analysis-deep.md) |
| Tokio | [`rust-ownership-decidability/case-studies/tokio-runtime-deep.md`](../rust-ownership-decidability/case-studies/tokio-runtime-deep.md) |

---

## 3. 快速决策树

```text
你想找什么？
├── Rust 所有权/借用/生命周期的完整形式化理论
│   └── → rust-ownership-decidability/01-core-concepts/
├── 类型理论通用基础（不限于 Rust）
│   └── → research_notes/type_theory/
├── 并发/异步的形式化证明
│   └── → rust-ownership-decidability/12-concurrency-patterns/
├── 设计模式的形式化分析
│   ├── Rust 特定 → rust-ownership-decidability/11-design-patterns/
│   └── 通用理论 → research_notes/software_design_theory/
├── 实际案例中的所有权分析
│   └── → rust-ownership-decidability/case-studies/
├── Coq 证明代码
│   └── → rust-ownership-decidability/coq-formalization/
└── 工作流/分布式系统的形式化
    └── → research_notes/software_design_theory/02_workflow/
```

---

## 4. 维护记录

| 日期 | 操作 | 负责人 |
|------|------|--------|
| 2026-05-12 | 创建本索引，统一 rust-ownership-decidability/ 与 research_notes/ 导航 | 项目维护团队 |

---

## 5. 相关文档

- [`00_rust_ownership_decidability_integration_plan.md`](./00_rust_ownership_decidability_integration_plan.md) — 整合计划详情
- [`00_documentation_division_of_labor.md`](./00_documentation_division_of_labor.md) — 文档体系分工协议
- [`rust-ownership-decidability/README.md`](../rust-ownership-decidability/README.md) — 所有权知识库入口
- [`research_notes/README.md`](../research_notes/README.md) — 研究笔记入口

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference Manual](https://coq.inria.fr/doc/)**
> **来源: [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**
