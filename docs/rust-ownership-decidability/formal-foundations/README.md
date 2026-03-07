# 形式化理论基础

> **Rust 版本**: 1.94+ (Edition 2024)
> **难度级别**: 🔴 高级
> **目标**: Rust 所有权系统的严格形式化理论

---

## 📋 目录

- [形式化理论基础](#形式化理论基础)
  - [📋 目录](#-目录)
  - [🎯 模块概述](#-模块概述)
  - [📁 子模块导航](#-子模块导航)
    - [models/ - 形式化模型](#models---形式化模型)
    - [semantics/ - 语义定义](#semantics---语义定义)
    - [proofs/ - 形式化证明](#proofs---形式化证明)
  - [🔗 与其他模块的关联](#-与其他模块的关联)
  - [🎓 学习路径](#-学习路径)
    - [理论基础路径](#理论基础路径)
    - [证明技术路径](#证明技术路径)
  - [📚 核心定理索引](#-核心定理索引)
  - [🌍 国际权威资料索引](#-国际权威资料索引)
    - [顶级会议论文 (POPL/PLDI)](#顶级会议论文-poplpldi)
    - [学位论文](#学位论文)
    - [工具实现](#工具实现)

---

## 🎯 模块概述

本模块提供 Rust 所有权系统的严格形式化理论，包括：

1. **形式化模型** - RustBelt、所有权类型、借用语义、生命周期逻辑
2. **语义定义** - 操作语义、内存模型、逻辑关系、类型系统形式化
3. **形式化证明** - 可判定性定理、内存安全证明、分离逻辑可靠性

---

## 📁 子模块导航

### models/ - 形式化模型

| 文档 | 主题 | 关键内容 | 来源 |
|:-----|:-----|:---------|:-----|
| [`02-01-rustbelt.md`](models/02-01-rustbelt.md) | RustBelt 模型 | Iris 框架、协议、资源 | MPI-SWS, POPL 2018 |
| [`02-02-ownership-types.md`](models/02-02-ownership-types.md) | 所有权类型 | 线性类型、仿射类型、资源管理 | 类型理论 |
| [`02-03-borrow-semantics.md`](models/02-03-borrow-semantics.md) | 借用语义 | 共享借用、可变借用、生命周期 | RustBelt |
| [`02-04-lifetime-logic.md`](models/02-04-lifetime-logic.md) | 生命周期逻辑 | 区域、包含关系、约束系统 | 区域理论 |
| [`02-05-move-analysis.md`](models/02-05-move-analysis.md) | 移动分析 | 移动语义、复制语义、Drop | Rust 参考 |
| [`tree-borrows-comprehensive.md`](models/tree-borrows-comprehensive.md) | Tree Borrows | 最新别名模型、PLDI 2025 | ETH Zürich, PLDI 2025 |
| [`executable-semantics-comparison.md`](models/executable-semantics-comparison.md) | 可执行语义对比 | KRust, RustSEM, Aeneas | 国际研究综述 |
| [`drop-elaboration-formal.md`](models/drop-elaboration-formal.md) | Drop Elaboration | Drop 展开形式化 | ETH Zürich, 2024 |
| [`symbolic-borrow-checking.md`](models/symbolic-borrow-checking.md) | 符号借用检查 | LLBC, 符号执行 | MSR, POPL 2024 |
| [`refinedrust-type-system.md`](models/refinedrust-type-system.md) | RefinedRust | 细化类型、高保证验证 | MPI-SWS, PLDI 2024 |
| [`relaxed-memory-model.md`](models/relaxed-memory-model.md) | Relaxed Memory | ORC11, iRC11, 弱内存 | MPI-SWS, POPL 2020 |

### semantics/ - 语义定义

| 文档 | 主题 | 关键内容 |
|:-----|:-----|:---------|
| [`operational-semantics.md`](semantics/operational-semantics.md) | 操作语义 | 大步/小步语义、求值上下文 |
| [`memory-model-semantics.md`](semantics/memory-model-semantics.md) | 内存模型 | Stacked Borrows、内存布局 |
| [`logical-relations.md`](semantics/logical-relations.md) | 逻辑关系 | 语义等价、兼容性 |
| [`type-system-formalization.md`](semantics/type-system-formalization.md) | 类型系统形式化 | 类型规则、推断算法 |
| [`semantics-equivalence-proof.md`](semantics/semantics-equivalence-proof.md) | 语义等价性证明 | 大步/小步语义等价 |
| [`mechanized-proofs.md`](semantics/mechanized-proofs.md) | 机械化证明 | Coq 证明策略、技术 |

### proofs/ - 形式化证明

| 文档 | 主题 | 关键内容 |
|:-----|:-----|:---------|
| [`decidability-theorem.md`](proofs/decidability-theorem.md) | 可判定性定理 | 借用检查可判定性 |
| [`memory-safety-proof.md`](proofs/memory-safety-proof.md) | 内存安全证明 | 所有权保证内存安全 |
| [`affine-logic-decidability.md`](proofs/affine-logic-decidability.md) | 仿射逻辑可判定性 | 类型系统可判定性 |
| [`separation-logic-soundness.md`](proofs/separation-logic-soundness.md) | 分离逻辑可靠性 | 分离逻辑规则可靠性 |
| [`rustbelt-formalization.md`](proofs/rustbelt-formalization.md) | RustBelt 形式化 | RustBelt 核心引理 |
| [`type-ownership-unified-theory.md`](proofs/type-ownership-unified-theory.md) | 类型-所有权统一理论 | 类型与所有权联系 |

---

## 🔗 与其他模块的关联

```text
formal-foundations/
    │
    ├── 基于 meta-model/ 的语法和语义域
    │   └── 抽象语法、语义域、判断形式
    │
    ├── 支撑 coq-formalization/ 的理论基础
    │   └── Coq 证明基于这些形式化定义
    │
    ├── 为 16-program-semantics/ 提供理论支撑
    │   └── 程序语义分析的理论基础
    │
    └── 验证 01-core-concepts/ 的概念正确性
        └── 核心概念的形式化验证
```

---

## 🎓 学习路径

### 理论基础路径

```
1. models/02-02-ownership-types.md
   └── 理解所有权类型的数学基础

2. semantics/operational-semantics.md
   └── 理解程序如何执行

3. semantics/type-system-formalization.md
   └── 理解类型规则的形式化

4. proofs/memory-safety-proof.md
   └── 理解内存安全的形式化保证
```

### 证明技术路径

```
1. semantics/mechanized-proofs.md
   └── 理解 Coq 证明技术

2. proofs/decidability-theorem.md
   └── 理解可判定性证明

3. proofs/type-ownership-unified-theory.md
   └── 理解综合证明策略
```

---

## 📚 核心定理索引

| 定理 | 位置 | 状态 |
|:-----|:-----|:----:|
| 借用检查可判定性 | proofs/decidability-theorem.md | ✅ |
| 内存安全 | proofs/memory-safety-proof.md | ✅ |
| 类型-所有权联系 | proofs/type-ownership-unified-theory.md | ✅ |
| 分离逻辑可靠性 | proofs/separation-logic-soundness.md | ✅ |
| 仿射逻辑可判定性 | proofs/affine-logic-decidability.md | ✅ |
| 语义等价性 | semantics/semantics-equivalence-proof.md | ✅ |
| Tree Borrows 优化正确性 | models/tree-borrows-comprehensive.md | ✅ |
| Drop Elaboration 正确性 | models/drop-elaboration-formal.md | ✅ |
| 符号借用检查声音性 | models/symbolic-borrow-checking.md | ✅ |
| RefinedRust 类型安全 | models/refinedrust-type-system.md | ✅ |
| Relaxed Memory 安全性 | models/relaxed-memory-model.md | ✅ |

---

## 🌍 国际权威资料索引

本模块全面对标以下国际权威研究：

### 顶级会议论文 (POPL/PLDI)

| 年份 | 会议 | 论文 | 文档 |
|------|------|------|------|
| 2025 | PLDI | Tree Borrows: A new aliasing model for Rust | tree-borrows-comprehensive.md |
| 2024 | PLDI | RefinedRust: A Type System for High-Assurance Verification | refinedrust-type-system.md |
| 2024 | POPL | Sound Borrow-Checking for Rust via Symbolic Semantics | symbolic-borrow-checking.md |
| 2024 | FMSD | Formally Understanding Rust's OBS at the Memory Level | executable-semantics-comparison.md |
| 2020 | POPL | RustBelt Meets Relaxed Memory | relaxed-memory-model.md |
| 2020 | POPL | Stacked Borrows: An aliasing model for Rust | memory-model-semantics.md |
| 2018 | POPL | RustBelt: Securing the foundations of Rust | 02-01-rustbelt.md |

### 学位论文

| 年份 | 机构 | 论文 | 文档 |
|------|------|------|------|
| 2024 | ETH Zürich | Formalization of Rust Drop Elaboration | drop-elaboration-formal.md |
| 2020 | Saarland University | Understanding and evolving the Rust programming language | 综合 |

### 工具实现

| 工具 | 机构 | 用途 | 文档 |
|------|------|------|------|
| Miri | Rust 团队 | UB 检测 | tree-borrows-comprehensive.md |
| Aeneas | MSR | 函数式验证 | symbolic-borrow-checking.md |
| KRust | 上海科技大学 | 可执行语义 | executable-semantics-comparison.md |
| RustSEM | 新加坡理工大学 | 内存级语义 | executable-semantics-comparison.md |

---

**最后更新**: 2026-03-07
**状态**: ✅ 100% 完成 - 全面对标国际权威资料
