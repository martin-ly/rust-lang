> **内容分级**: [专家级]

# Hoare 逻辑 for Rust 算法

> **EN**: Hoare Logic for Rust Algorithms
> **Summary**: Algorithm-semantics entry point for Hoare-style contracts in Rust — linking preconditions, postconditions, loop invariants, and termination arguments to concrete algorithm implementations.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页：Hoare 逻辑在 Rust 算法层面的应用入口。
> **定位**: 将 Hoare 逻辑从通用程序验证工具聚焦到**算法语义**——排序、搜索、迭代、unsafe 算法库的不变量与终止性。完整 Hoare 逻辑理论及推理规则见 [`04_formal/03_operational_semantics/02_hoare_logic.md`](../03_operational_semantics/02_hoare_logic.md)。
> **前置概念**: [Hoare Logic](../03_operational_semantics/02_hoare_logic.md) · [Ownership Formalization](../01_ownership_logic/02_ownership_formal.md)
> **后置概念**: [Refinement Calculus](02_refinement_calculus.md) · [Unsafe Algorithm Invariants](04_unsafe_algorithm_invariants.md)

---

> **来源**: [Hoare 1969 — An Axiomatic Basis](https://doi.org/10.1093/comjnl/12.4.576) · [Cambridge Hoare Logic Notes](https://www.cl.cam.ac.uk/archive/mjcg/HL/Lectures/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)

## 一、算法语义的 Hoare 视角

算法 = 输入域 + 输出规范 + 终止性 + 复杂度。Hoare 三元组 `{P} C {Q}` 给算法提供了**可验证的语义契约**：

```text
{ P(n) }            // 前置：输入满足的问题约束
  algorithm(C)      // 算法体
{ Q(n, result) }    // 后置：输出与输入的关系
∧ termination(n)    // 终止性：对合法输入必停机
```

在 Rust 中，类型系统已经编码了部分前置/后置条件（如 `NonZeroU32`、`&[T]` 非空切片），但**算法级语义**仍需文档化契约或形式化注解。

## 二、与通用 Hoare 逻辑页的关系

| 维度 | 本页（算法语义） | [`02_hoare_logic.md`](../03_operational_semantics/02_hoare_logic.md)（操作语义） |
|---|---|---|
| 视角 | 算法正确性、终止性、复杂度 | 程序命令式语义的公理化 |
| 示例 | `Iterator::find`、`Vec::sort`、`binary_search` | 赋值、顺序、条件、循环规则 |
| 工具 | Creusot/Prusti/Kani 算法契约 | 通用霍尔逻辑与最弱前置条件 |
| 定位 | 应用/算法层 | 理论/操作语义层 |

> **权威来源**: 通用 Hoare 逻辑的理论、规则、 weakest precondition 演算统一维护在 [`04_formal/03_operational_semantics/02_hoare_logic.md`](../03_operational_semantics/02_hoare_logic.md)。本页只保留算法语义的入口说明与交叉链接。
