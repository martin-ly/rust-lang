# 架构语义（Architecture Semantics）

> **EN**: Architecture Semantics
> **Summary**: Formal semantics of software architecture — architectural description languages, architectural styles, connector semantics, architecture refinement, and Rust-specific constraints.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本目录为 `concept/` 权威层；`semantic_space.md` 的架构语义子空间。
> **定位**: 从形式化视角分析软件架构的描述、风格、精化与实现约束，连接高层架构设计（`06_ecosystem/03_design_patterns/`）与 Rust 模块/crate/ABI 机制。
> **前置概念**:
> [Architecture Patterns](../../06_ecosystem/03_design_patterns/08_architecture_patterns.md) ·
> [System Composability](../../06_ecosystem/03_design_patterns/04_system_composability.md) ·
> [Microservice Patterns](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) ·
> [Semantic Space](../../00_meta/00_framework/semantic_space.md)
> **后置概念**:
> [Pattern Composition Algebra](../00_type_theory/12_pattern_composition_algebra.md) ·
> [ABI](../05_rustc_internals/05_application_binary_interface.md)

---

## 目录定位

`semantic_space.md` 与 `expressiveness_multiview.md` 讨论了 Rust 的抽象语义和跨语言对比，但尚未从**软件架构**层面给出形式化语义。

本目录负责回答：

1. 软件架构描述语言（ADL）如何形式化组件、连接件与配置？
2. Layered、Hexagonal、Microkernel、Event-Driven 等架构风格的语义不变量是什么？
3. 抽象架构如何精化为 Rust 的 crate/module/trait 结构而不丢失语义？
4. Rust 的模块系统、crate 边界、ABI 对架构语义有哪些约束？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_software_architecture_formalization.md` | 软件架构形式化：ADL、组件/连接件/配置、架构风格 | ✅ 已创建，含国际权威来源与 Rust 示例 |
| 02 | `02_architecture_pattern_semantics.md` | 常见架构模式的语义：Layered、Hexagonal、Microkernel、Event-Driven | ✅ 已创建，含架构模式不变量与编译期反例 |
| 03 | `03_architecture_refinement.md` | 架构精化：从抽象架构到 Rust 实现的保持性 | ✅ 已创建，含精化映射与违约反例 |
| 04 | `04_rust_architecture_constraints.md` | Rust 模块系统、crate 边界、ABI 对架构语义的约束 | ✅ 已创建，含模块/crate/ABI 约束与编译期反例 |

---

## 国际权威来源索引

- **P0 经典**: M. Shaw & D. Garlan, "Software Architecture: Perspectives on an Emerging Discipline" (1996)
- **P1 论文**: M. Wermelinger, "Formal Specification of Software Architecture" (1994)
- **P1 框架**: BIP (Behavior, Interaction, Priority) — J. Sifakis
- **P1 架构**: D. Garlan & M. Shaw, "An Introduction to Software Architecture" (1993)
- **P2 生态**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) · [Architecture Patterns in Rust](https://rust-unofficial.github.io/patterns/intro.html)

---

## 与表征空间的关系

```text
semantic_space.md §5 机制组合 / §6 跨语言对比
    └── 架构语义层（本目录）
            ├── ADL：架构描述的形式化语言
            ├── 架构风格：Layered / Hexagonal / Microkernel 的语义不变量
            ├── 架构精化：从高层设计到 Rust 实现的保持
            └── Rust 约束：模块/crate/ABI 对架构的塑造
```
