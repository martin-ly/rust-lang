# 算法语义（Algorithm Semantics）

**EN**: Algorithm Semantics
**Summary**: Formal semantics of algorithms in Rust — Hoare logic, refinement calculus, iterator correctness, unsafe algorithm invariants, and observational equivalence of algorithmic implementations.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4
> **权威来源**: 本目录为 `concept/` 权威层；`semantic_space.md` 的算法语义子空间。
> **定位**: 从形式化视角分析 Rust 算法的规范、实现、精化与等价性，连接 `00_meta/00_framework/semantic_space.md` 的“能表达边界”与具体算法实现。
> **前置概念**:
> [Operational Semantics](../03_operational_semantics/03_operational_semantics.md) ·
> [Hoare Logic](../03_operational_semantics/02_hoare_logic.md) ·
> [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) ·
> [Semantic Space](../../00_meta/00_framework/semantic_space.md)
> **后置概念**:
> [Formal Algorithm Theory](../00_type_theory/13_formal_algorithm_theory.md) ·
> [Data Structures in Rust](../../06_ecosystem/11_domain_applications/09_data_structures_in_rust.md)

---

## 目录定位

`concept/00_meta/00_framework/semantic_space.md` 将 Rust 的表征空间定义为若干子系统的组合。其中“能且高效表达”与“能但低效表达”的边界，最终要落实到**算法层面**的语义保证。

本目录负责回答：

1. 如何用形式化方法描述 Rust 算法的正确性？
2. 从规范到实现，算法精化如何保持语义？
3. `Iterator`、`Vec::sort`、`unsafe` 算法库的不变量是什么？
4. 同一算法的不同 Rust 实现是否观察等价？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_hoare_logic_for_rust.md` | Hoare 逻辑在 Rust 算法中的实践入口；完整理论见 [`03_operational_semantics/02_hoare_logic.md`](../03_operational_semantics/02_hoare_logic.md) | ⏳ 待创建（stub） |
| 02 | `02_refinement_calculus.md` | 算法精化：从规范到实现的逐步推导 | ⏳ 待创建 |
| 03 | `03_iterator_correctness.md` | `Iterator` trait 的语义规范与正确性证明 | ⏳ 待创建 |
| 04 | `04_unsafe_algorithm_invariants.md` | `unsafe` 算法内部的前置/后置条件与不变量 | ⏳ 待创建 |
| 05 | `05_algorithm_equivalence.md` | 算法实现的观察等价性与复杂度语义 | ⏳ 待创建 |

---

## 国际权威来源索引

- **P0 经典**: C. A. R. Hoare, "An Axiomatic Basis for Computer Programming" (1969)
- **P0 教材**: [Cambridge Hoare Logic Lecture Notes](https://www.cl.cam.ac.uk/archive/mjcg/HL/Lectures/)
- **P1 论文**: Back, "A Calculus of Refinements for Program Derivations" (1988)
- **P1 论文**: arXiv 2025, "A Formal Framework for Naturally Specifying and Verifying Sequential Algorithms"
- **P1 工具**: [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) / [Creusot](https://github.com/creusot-rs/creusot) 对 Rust 算法的契约式验证

---

## 与表征空间的关系

```text
semantic_space.md §5 机制组合
    └── 算法语义层（本目录）
            ├── Hoare 逻辑：safe/unsafe 算法的规范语言
            ├── 精化演算：从抽象规范到 Rust 实现
            ├── Iterator 语义：Rust 核心抽象的正确性
            └── 算法等价：同一语义的不同表达是否观察等价
```
