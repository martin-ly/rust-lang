# 定理链全局注册表（Theorem Registry）

> **EN**: Global Theorem Chain Registry
> **Summary**: Central registry for all `T-xxx` theorem identifiers used across the concept layer, ensuring global uniqueness and semantic consistency.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: Meta
> **权威来源**: 本文件为 `concept/` 权威页。

---

## 📑 目录

- [定理链全局注册表（Theorem Registry）](#定理链全局注册表theorem-registry)
  - [📑 目录](#-目录)
  - [1. 注册表目的](#1-注册表目的)
  - [2. 编号范围分配](#2-编号范围分配)
  - [3. 已注册定理清单](#3-已注册定理清单)
    - [3.1 所有权域（T-001 – T-009）](#31-所有权域t-001--t-009)
    - [3.2 借用域（T-010 – T-019）](#32-借用域t-010--t-019)
    - [3.3 生命周期域（T-020 – T-029）](#33-生命周期域t-020--t-029)
    - [3.4 类型系统域（T-030 – T-039）](#34-类型系统域t-030--t-039)
    - [3.5 并发域（T-040 – T-049）](#35-并发域t-040--t-049)
    - [3.6 异步域（T-050 – T-059）](#36-异步域t-050--t-059)
    - [3.7 Trait 工程扩展域（T-200 – T-229）](#37-trait-工程扩展域t-200--t-229)
    - [3.8 泛型工程扩展域（T-230 – T-259）](#38-泛型工程扩展域t-230--t-259)
    - [3.9 形式化域（T-100 – T-159）](#39-形式化域t-100--t-159)
  - [4. 冲突解决记录](#4-冲突解决记录)
  - [5. 使用规范](#5-使用规范)
  - [6. 维护责任](#6-维护责任)
  - [7. 权威来源（References · 国际权威对齐）](#7-权威来源references--国际权威对齐)
  - [国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp0-官方--p1-学术--p2-生态)

## 1. 注册表目的

本项目在 `concept/` 层使用 `T-xxx` 编号标注定理链（theorem chains）。历史上，不同概念文件独立分配编号，导致同一 `T-xxx` 在不同文件中指向不同命题（例如 `T-020` 既被用作“特质一致性（Coherence）”，也被用作“生命周期偏序约束可满足性”）。

本注册表统一规范：

- 每个 `T-xxx` 全局唯一对应一个命题。
- 编号范围按主题域划分，便于扩展。
- 冲突编号已在注册表中标记并修正。

---

## 2. 编号范围分配

| 范围 | 主题域 | 说明 |
|---|---|---|
| T-001 – T-009 | 所有权（Ownership） | 所有权唯一性、Move、Drop 安全 |
| T-010 – T-019 | 借用（Borrowing） | AXM、悬垂引用、可变性规则 |
| T-020 – T-029 | 生命周期（Lifetimes） | 区域约束、NLL、Polonius、Elision |
| T-030 – T-039 | 类型系统（Type System） | 类型推断、约束求解、类型安全 |
| T-040 – T-049 | 并发（Concurrency） | Send/Sync、数据竞争、死锁 |
| T-050 – T-059 | 异步（Async） | Pin、Future、async/await 转换 |
| T-060 – T-069 | Unsafe | UB 边界、Unsafe 契约 |
| T-070 – T-079 | 宏与元编程 | 宏展开、过程宏 |
| T-080 – T-089 | 错误处理 | Result、panic、must_use |
| T-090 – T-099 | 模块与构建 | 模块系统、Cargo、 Edition |
| T-100 – T-119 | 形式化类型论 | System F、子类型、语义 |
| T-120 – T-139 | 形式化操作语义 / 公理语义 | 操作语义、公理语义 |
| T-140 – T-159 | 形式化内存模型 | RustBelt、分离逻辑 |
| T-160 – T-199 | 预留（形式化扩展） | 待分配 |
| T-200 – T-229 | Trait 与泛型工程扩展 | _traits.md_ 等工程视角定理 |
| T-230 – T-259 | 泛型与单态化工程扩展 | _generics.md_ 等工程视角定理 |
| T-260 – T-299 | 预留（语言特性扩展） | 待分配 |

> **历史修正**：
>
> - `concept/02_intermediate/00_traits/01_traits.md` 原使用 `T-020`–`T-022`，已修正为 `T-200`–`T-202`。
> - `concept/02_intermediate/01_generics/01_generics.md` 原使用 `T-030`–`T-032`，已修正为 `T-230`–`T-232`。

---

## 3. 已注册定理清单

「已注册定理清单」涉及所有权域（T-001 – T-009）、借用域（T-010 – T-019）、生命周期域（T-020 – T-029）、类型系统域（T-030 – T-039）等9个方面，本节逐一说明其要点。

### 3.1 所有权域（T-001 – T-009）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-001 | 所有权唯一性 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ✅ 已注册 |
| T-002 | Move 语义完备性 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ✅ 已注册 |
| T-003 | Drop 安全性 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ✅ 已注册 |

### 3.2 借用域（T-010 – T-019）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-010 | 借用可变性互斥（AXM） | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | ✅ 已注册 |
| T-011 | 悬垂引用不可达 | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | ✅ 已注册 |
| T-012 | 别名-可变性规则 | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | ✅ 已注册 |

### 3.3 生命周期域（T-020 – T-029）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-020 | 生命周期偏序约束可满足性 | `concept/00_meta/00_framework/theorem_inference_forest.md` | ✅ 已注册 |
| T-021 | NLL 流敏感安全 | `concept/00_meta/00_framework/theorem_inference_forest.md` | ✅ 已注册 |
| T-022 | 悬垂引用不可达（推论） | `concept/00_meta/00_framework/theorem_inference_forest.md` | ✅ 已注册 |
| T-025 | Polonius 流敏感安全 | `concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` | ✅ 已注册 |
| T-026 | Elision 完备性 | `concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` | ✅ 已注册 |

### 3.4 类型系统域（T-030 – T-039）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-030 | 局部类型推断可判定性 | `concept/00_meta/00_framework/theorem_inference_forest.md` | ✅ 已注册 |
| T-031 | Trait 约束求解受限可判定性 | `concept/00_meta/00_framework/theorem_inference_forest.md` | ✅ 已注册 |

### 3.5 并发域（T-040 – T-049）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-040 | Send 类型安全 | `concept/03_advanced/00_concurrency/01_concurrency.md` | ✅ 已注册 |
| T-041 | Sync 数据竞争自由 | `concept/03_advanced/00_concurrency/01_concurrency.md` | ✅ 已注册 |
| T-042 | 死锁不可判定但可检测 | `concept/03_advanced/00_concurrency/01_concurrency.md` | ✅ 已注册 |

### 3.6 异步域（T-050 – T-059）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-050 | Pin 安全性 | `concept/03_advanced/01_async/01_async.md` | ✅ 已注册 |
| T-051 | 轮询一致性（Poll Coherence） | `concept/03_advanced/01_async/01_async.md` | ✅ 已注册 |
| T-052 | async/await 转换正确性 | `concept/03_advanced/01_async/01_async.md` | ✅ 已注册 |

### 3.7 Trait 工程扩展域（T-200 – T-229）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-200 | 特质一致性（Coherence） | `concept/02_intermediate/00_traits/01_traits.md` | ✅ 已注册 |
| T-201 | 孤儿规则（Orphan Rule）完备性 | `concept/02_intermediate/00_traits/01_traits.md` | ✅ 已注册 |
| T-202 | 关联类型规范化 | `concept/02_intermediate/00_traits/01_traits.md` | ✅ 已注册 |

### 3.8 泛型工程扩展域（T-230 – T-259）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-230 | 参数多态保持 | `concept/02_intermediate/01_generics/01_generics.md` | ✅ 已注册 |
| T-231 | 单态化（Monomorphization）正确性 | `concept/02_intermediate/01_generics/01_generics.md` | ✅ 已注册 |
| T-232 | 约束满足可判定 | `concept/02_intermediate/01_generics/01_generics.md` | ✅ 已注册 |

### 3.9 形式化域（T-100 – T-159）

| 编号 | 命题 | 所在文件 | 状态 |
|---|---|---|---|
| T-100 – T-102 | 类型语义相关命题 | `concept/04_formal/00_type_theory/06_type_semantics.md` | ✅ 已注册 |
| T-110 – T-112 | 操作语义相关命题 | `concept/04_formal/03_operational_semantics/05_axiomatic_semantics.md` | ✅ 已注册 |
| T-120 – T-129 | 公理语义相关命题 | `concept/04_formal/03_operational_semantics/05_axiomatic_semantics.md` | ✅ 已注册 |
| T-130 – T-132 | 形式化扩展命题 | `concept/04_formal/00_type_theory/06_type_semantics.md` | ✅ 已注册 |

---

## 4. 冲突解决记录

| 原编号 | 原文件中的含义 | 现编号 | 说明 |
|---|---|---|---|
| T-020 | 特质一致性（Coherence） | **T-200** | 避免与生命周期域 `T-020` 冲突 |
| T-021 | 孤儿规则完备性 | **T-201** | 避免与 NLL 安全 `T-021` 冲突 |
| T-022 | 关联类型规范化 | **T-202** | 避免与悬垂引用推论 `T-022` 冲突 |
| T-030 | 参数多态保持 | **T-230** | 避免与类型推断 `T-030` 冲突 |
| T-031 | 单态化正确性 | **T-231** | 避免与 Trait 约束求解 `T-031` 冲突 |
| T-032 | 约束满足可判定 | **T-232** | 避免与类型系统域 `T-032` 冲突 |
| T-015 | Polonius 流敏感安全 | **T-025** | 从借用域迁移到生命周期域 |
| T-016 | Elision 完备性 | **T-026** | 从借用域迁移到生命周期域 |

---

## 5. 使用规范

1. **新增定理编号前必须查表**：确保不与已注册编号冲突。
2. **优先使用主题域内的连续编号**：避免跨域复用。
3. **在概念文件头部标注定理链**：格式建议为：

   ```markdown
   > **定理链编号**: T-200 特质一致性（Coherence） → T-201 孤儿规则完备性 → T-202 关联类型规范化
   ```

4. **引用他人定理时使用完整编号**：例如“由 T-020（生命周期可满足性）可得 …”。

---

## 6. 维护责任

- 新增 `T-xxx` 时同步更新本注册表。
- 每季度运行一次定理编号审计脚本，检测冲突。
- 本注册表由 `concept/00_meta/00_framework/theorem_inference_forest.md` 维护者负责最终审核。

---

## 7. 权威来源（References · 国际权威对齐）

> 本注册表规范的 `T-xxx` 定理编号，其命题出处对齐下列国际权威来源（仅作来源登记，不改正文事实）：

- **P0 官方**: [Rust Reference — Type System / Traits / Lifetimes](https://doc.rust-lang.org/reference/) · [The Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust RFCs](https://rust-lang.github.io/rfcs/)
- **P1 学术/形式化**: Ralf Jung et al. _RustBelt: Securing the Foundations of the Rust Programming Language_ (POPL 2018) · _Stacked Borrows: An Aliasing Model for Rust_ (POPL 2019) · Villani / Hostert / Dreyer / Jung _Tree Borrows: A New Aliasing Model for Rust_ (PLDI 2025, Distinguished Paper)
- **映射维护**: 见 [`concept/00_meta/02_sources/01_authority_source_map.md`](../02_sources/01_authority_source_map.md)

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Hogan et al.: Knowledge Graphs (ACM Comput. Surv. 2021)](https://dl.acm.org/doi/10.1145/3447772)
