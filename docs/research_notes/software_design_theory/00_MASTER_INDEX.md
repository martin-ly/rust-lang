# 软件设计理论体系：主索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 100% 完成

---

## 一、层次化索引

### 1.1 理论层次

```text
应用与边界层（本体系所在）
├── 01_design_patterns_formal     ← 设计模式形式化（公理/定义/定理）
├── 02_workflow_safe_complete_models ← 23 安全 / 43 完全模型
├── 03_execution_models           ← 同步/异步/并发/并行/分布式
├── 04_compositional_engineering  ← 组合工程有效性
├── 05_boundary_system            ← 三维边界矩阵
├── 06_rust_idioms                ← Rust 惯用模式（RAII、Newtype、类型状态）
└── 07_anti_patterns              ← 反模式与边界
```

### 1.2 依赖关系

本体系依赖以下已有形式化基础：

| 依赖 | 文档 |
| :--- | :--- |
| 所有权 | [ownership_model](../formal_methods/ownership_model.md) |
| 借用 | [borrow_checker_proof](../formal_methods/borrow_checker_proof.md) |
| 生命周期 | [lifetime_formalization](../formal_methods/lifetime_formalization.md) |
| 类型系统 | [type_system_foundations](../type_theory/type_system_foundations.md) |
| 型变 | [variance_theory](../type_theory/variance_theory.md) |
| 异步 | [async_state_machine](../formal_methods/async_state_machine.md) |
| Pin | [pin_self_referential](../formal_methods/pin_self_referential.md) |
| Trait | [trait_system_formalization](../type_theory/trait_system_formalization.md) |

---

## 二、边界化索引

### 2.1 三维边界

| 维度 | 内容 | 文档 |
| :--- | :--- | :--- |
| **安全 vs 非安全** | 纯 Safe / 需 unsafe / 无法表达 | [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md) |
| **支持 vs 不支持** | 原生支持 / 库支持 / 需 FFI | [supported_unsupported_matrix](05_boundary_system/supported_unsupported_matrix.md) |
| **充分 vs 非充分表达** | 等价表达 / 近似表达 / 不可表达 | [expressive_inexpressive_matrix](05_boundary_system/expressive_inexpressive_matrix.md) |

### 2.2 边界原则

- **安全边界**：每个模式/模型标注「纯 Safe / 需 unsafe / 无法表达」
- **支持边界**：在 Rust 1.93+ 下的「原生支持 / 库支持 / 需 FFI」
- **表达边界**：相对 GoF/OOP 的「等价表达 / 近似表达 / 不可表达」

---

## 三、扩展化路线

### 3.1 设计模式扩展

- GoF 23 模式（当前）✅
- **Rust Idioms** ✅ [06_rust_idioms](06_rust_idioms.md)：RAII、Newtype、类型状态、Builder 变体；含 Def/Axiom/定理、典型场景、常见陷阱、与 GoF 衔接
- **Anti-patterns** ✅ [07_anti_patterns](07_anti_patterns.md)：13 反例索引、反模式分类、与 FORMAL_PROOF_SYSTEM_GUIDE 衔接、三维边界
- 扩展 20（43 完全）：Repository、DTO、Event Sourcing 等已纳入 02_complete_43_catalog

### 3.2 执行模型扩展

- 五模型（同步、异步、并发、并行、分布式）✅
- 可选扩展：Actor（actix）、CSP（channel）、事件溯源（02_complete_43 Event Sourcing）

### 3.3 工作流模型扩展

- 23 安全：GoF 23 纯安全子集
- 43 完全：GoF 23 + 扩展 20（Fowler EAA/DDD，已明确）

---

## 四、内容概览

本体系各文档已充实为实质内容：

- **设计模式**：每模式含 Def/Axiom/定理、Rust 代码示例、证明思路、**典型场景**、**相关模式**、**实现变体**、**反例**、与理论衔接（23 模式均有典型场景、相关模式、实现变体；13 反例）
- **执行模型**：形式化定义、操作语义、Rust 示例、**典型场景**、与 async/borrow 衔接（五模型）
- **组合工程**：CE-T1–T3 完整证明思路、模块/Crate 组合代码示例、**设计模式组合示例**、与 ownership/borrow/trait 衔接
- **边界体系**：安全/支持/表达三维矩阵、决策树、反例、扩展模式详情、**模式选取示例**
- **Rust Idioms**：RAII、Newtype、类型状态（Def/Axiom/定理、典型场景、常见陷阱、与 GoF 衔接）
- **反模式**：13 反例索引、反模式分类、与 FORMAL_PROOF_SYSTEM_GUIDE 衔接、规避策略

---

## 五、学习与选型

| 阶段 | 内容 |
| :--- | :--- |
| 入门 | Factory Method、Strategy、Adapter |
| 结构 | Composite、Decorator、Facade |
| 行为 | Observer、Command、State |
| 进阶 | Visitor、Chain、Mediator |

选模式时：需求 → [03_semantic_boundary_map](02_workflow_safe_complete_models/03_semantic_boundary_map.md) 模式选取示例；判安全 → [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md)。

---

## 六、文档快速导航

| 需求 | 入口文档 |
| :--- | :--- |
| 设计模式形式化分析 | [01_design_patterns_formal/README](01_design_patterns_formal/README.md) |
| 23 安全 / 43 完全模型 | [02_workflow_safe_complete_models/README](02_workflow_safe_complete_models/README.md) |
| 同步/异步/并发/分布式 | [03_execution_models/README](03_execution_models/README.md) |
| 组合工程有效性 | [04_compositional_engineering/README](04_compositional_engineering/README.md) |
| 边界体系总览 | [05_boundary_system/README](05_boundary_system/README.md) |
| **Rust 惯用模式** | [06_rust_idioms](06_rust_idioms.md) — RAII、Newtype、类型状态、与设计模式衔接 |
| **反模式与边界** | [07_anti_patterns](07_anti_patterns.md) — 13 反例、反模式分类、规避策略 |

---

## 七、扩展阅读

- [Refactoring.Guru](https://refactoring.guru/design-patterns)：各模式结构图
- [rust-unofficial/patterns](https://rust-unofficial.github.io/patterns/)：Rust 惯用模式
- [Fowler EAA](https://martinfowler.com/eaaCatalog/)：43 完全扩展模式来源

---

## 八、推进阶段

| 阶段 | 内容 | 状态 |
| :--- | :--- | :--- |
| 第一阶段 | 框架与边界 | 100% 完成 |
| 第二阶段 | 设计模式形式化 | 100% 完成（23 模式） |
| 第三阶段 | 工作流与执行模型 | 100% 完成（23/43、五执行模型） |
| 第四阶段 | 组合工程与证明 | 100% 完成（CE-T1–T3） |
| 第五阶段 | Rust Idioms 与反模式 | 100% 完成（06、07） |
