# 核心定理集

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **Rust 版本**: 1.96.0+ (Edition 2024)
> **对齐日期**: 2026-05-12+ (Edition 2024)
> **难度级别**: 🔴 高级
> **目标**: Rust 所有权系统的核心形式化定理

---

## 📋 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [核心定理集](#核心定理集)
  - [📋 目录](#-目录)
  - [🎯 定理集概述](#-定理集概述)
  - [📁 文档导航](#-文档导航)
  - [🔑 核心定理清单](#-核心定理清单)
    - [可判定性定理](#可判定性定理)
    - [安全性定理](#安全性定理)
    - [正确性定理](#正确性定理)
  - [🔗 与其他模块的关联](#-与其他模块的关联)
  - [**状态**: ✅ 完成](#状态--完成)
  - [权威来源索引](#权威来源索引)

---

## 🎯 定理集概述
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

本模块收集 Rust 所有权系统的核心形式化定理，提供：

1. **可判定性定理** - 借用检查和类型系统的可判定性
2. **安全性定理** - 内存安全、线程安全的形式化保证
3. **正确性定理** - 类型系统保持性和进展性

---

## 📁 文档导航
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 文档 | 主题 | 关键定理 |
|:-----|:-----|:---------|
| [`decidability_theorems.md`](./decidability_theorems.md) | 可判定性定理 | 借用检查终止性、类型推断可判定性 |

---

## 🔑 核心定理清单

### 可判定性定理

| 定理 | 陈述 | 位置 |
|:-----|:-----|:-----|
| **BorrowChecking_Termination** | 借用检查算法终止 | decidability_theorems.md |
| **TypeInference_Decidability** | 类型推断可判定 (Hindley-Milner) | decidability_theorems.md |
| **LifetimeConstraint_Satisfiability** | 生命周期约束可满足性 | decidability_theorems.md |

### 安全性定理

| 定理 | 陈述 | 位置 |
|:-----|:-----|:-----|
| **Memory_Safety** | 所有权保证内存安全 | formal-foundations/proofs/memory-safety-proof.md |
| **Type_Safety** | 类型安全 (Progress + Preservation) | coq-formalization/theories/Metatheory/ |
| **Thread_Safety** | Send/Sync 保证线程安全 | 12-concurrency-patterns/12-02-thread-safety-patterns.md |

### 正确性定理

| 定理 | 陈述 | 位置 |
|:-----|:-----|:-----|
| **Progress** | 良类型程序不停滞 | coq-formalization/theories/Metatheory/ |
| **Preservation** | 规约保持类型 | coq-formalization/theories/Metatheory/ |
| **Semantic_Equivalence** | 大步/小步语义等价 | formal-foundations/semantics/semantics-equivalence-proof.md |

---

## 🔗 与其他模块的关联

```text
theorems/
    │
    ├── 基于 formal-foundations/ 的形式化定义
    │   └── 模型、语义、证明技术
    │
    ├── 在 coq-formalization/ 中实现证明
    │   └── 300+ Qed 证明
    │
    └── 验证 01-core-concepts/ 的直觉正确性
        └── 概念与形式化的对应
```

---

**最后更新**: 2026-03-07
**状态**: ✅ 完成
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
