> **内容分级**: [专家级]

# 计算模型与可计算性（Computational Models & Computability）

> **EN**: Computational Models and Computability
> **Summary**: Formal foundations of computation — unifying operational, denotational, axiomatic and type semantics; computability theory; formal languages and automata; and mathematical functions as computation.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本目录为 `concept/` 权威层；`semantic_space.md` 的计算语义子空间。
> **定位**: 从**可计算性、形式语言、语义模型统一框架**三个维度，建立 Rust 程序语义在通用 PL 理论坐标系中的位置。连接 `00_meta/00_framework/semantic_space.md` 的「能表达边界」与 `04_formal/` 各形式化子页。
> **前置概念**: [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) · [Operational Semantics](../03_operational_semantics/03_operational_semantics.md) · [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md) · [Axiomatic Semantics](../03_operational_semantics/05_axiomatic_semantics.md)
> **后置概念**: [Algorithm Equivalence](../08_algorithm_semantics/05_algorithm_equivalence.md) · [Concurrency Models](../12_concurrency_models/README.md) · [Semantic Space](../../00_meta/00_framework/semantic_space.md)

---

## 目录定位

`semantic_space.md` 指出：所有图灵完备语言在计算能力上等价，但**表达特定概念所需的变换复杂度**不同。本目录负责把这一直觉落地为可教授、可引用的形式理论：

1. 如何用统一框架理解操作/指称/公理/类型四种语义？
2. 图灵机、递归函数、λ 演算、形式语言层级如何刻画「可计算」？
3. 可计算函数作为数学对象与 Rust 函数/闭包有何对应与差异？
4. 不同计算模型之间的等价性与表达能力边界是什么？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_computational_semantics_framework.md` | 计算语义统一框架：操作/指称/公理/类型语义及其关系 | ✅ 已创建 |
| 02 | `02_computability_theory.md` | 可计算性理论：图灵机、递归函数、停机问题、Church-Turing 论题 | ✅ 已创建 |
| 03 | `03_formal_languages_and_automata.md` | 形式语言与自动机：正则/上下文无关/图灵可识别层级 | ✅ 已创建 |
| 04 | `04_mathematical_functions_of_computation.md` | 计算的数学函数：μ-递归、λ-可定义、Scott 域与指称语义 | ✅ 已创建 |
| 05 | `05_equivalence_of_computational_models.md` | 计算模型等价性：图灵等价、表达能力、Felleisen 框架 | ✅ 已创建 |

---

## 国际权威来源索引

- **P0 经典**: A. Turing, "On Computable Numbers" (1936)
- **P0 经典**: A. Church, "An Unsolvable Problem of Elementary Number Theory" (1936)
- **P1 教材**: M. Sipser, *Introduction to the Theory of Computation* (3rd Ed.)
- **P1 教材**: J. Hopcroft, R. Motwani, J. Ullman, *Introduction to Automata Theory, Languages, and Computation*
- **P1 专著**: G. Plotkin, "A Structural Approach to Operational Semantics" (1981)
- **P1 专著**: G. Winskel, *The Formal Semantics of Programming Languages* (1993)
- **P1 专著**: B. Pierce, *Types and Programming Languages* (2002)
- **P1 论文**: M. Felleisen, "On the Expressive Power of Programming Languages" (1991)

---

## 与表征空间的关系

```text
semantic_space.md §3 能表达边界 / §4 等价表达
    └── 计算模型层（本目录）
            ├── 语义框架：四种语义如何刻画同一程序
            ├── 可计算性：图灵机 / 递归函数 / 停机问题
            ├── 形式语言：自动机层级与 Rust 语法子集
            ├── 数学函数：可计算函数的数学模型
            └── 模型等价：图灵等价与 Felleisen 表达力
```
