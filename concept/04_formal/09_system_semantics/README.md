# 系统语义（System Semantics）

**EN**: System Semantics
**Summary**: Formal semantics of concurrent, distributed, and reactive systems in Rust — Actor model, π-calculus, component-based semantics, distributed consensus, and reactive streams.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4
> **权威来源**: 本目录为 `concept/` 权威层；`semantic_space.md` 的系统语义子空间。
> **定位**: 从进程代数、组件组合与分布式一致性等角度，形式化分析 Rust 并发/分布式/反应式系统的语义基础。
> **前置概念**:
> [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) ·
> [Concurrency Patterns](../../03_advanced/00_concurrency/03_concurrency_patterns.md) ·
> [Distributed Consensus](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) ·
> [Semantic Space](../../00_meta/00_framework/semantic_space.md)
> **后置概念**:
> [Reactive Programming](../../06_ecosystem/04_web_and_networking/09_reactive_programming.md) ·
> [Microservice Patterns](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md)

---

## 目录定位

Rust 的并发与分布式表达能力是其核心卖点之一。`semantic_space.md` 将“fearless 并发”列为 Rust 的 Sweet Spot，但“能表达”不等于“语义清晰”。

本目录负责回答：

1. Actor、CSP、π 演算如何为 Rust 的消息传递系统提供语义模型？
2. 组件化系统（如 BIP）的组合语义是什么？
3. 分布式一致性、容错、反应式系统的形式化语义如何在 Rust 中落地？
4. `tokio::sync`、`actix`、`tonic` 等框架与这些形式模型有何对应关系？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_actor_model_semantics.md` | Actor 模型系统语义入口；权威形式化见 [`07_concurrency_semantics/03_actor_semantics.md`](../07_concurrency_semantics/03_actor_semantics.md) | ⏳ 待创建（stub） |
| 02 | `02_pi_calculus_for_rust.md` | π 演算系统语义入口；权威形式化见 [`07_concurrency_semantics/01_process_calculi_for_rust.md`](../07_concurrency_semantics/01_process_calculi_for_rust.md) | ⏳ 待创建（stub） |
| 03 | `03_component_based_semantics.md` | 组件化系统语义：BIP、接口、组合与涌现行为 | ⏳ 待创建 |
| 04 | `04_distributed_systems_semantics.md` | 分布式系统语义：共识、一致性、容错的形式化 | ⏳ 待创建 |
| 05 | `05_reactive_systems_semantics.md` | 反应式系统语义：Reactive streams、backpressure、时态逻辑 | ✅ 已创建 |

---

## 国际权威来源索引

- **P0 经典**: C. Hewitt, "Actor Model of Computation" (2017)
- **P0 专著**: R. Milner, "Communicating and Mobile Systems: The π-Calculus" (1999)
- **P0 专著**: C. A. R. Hoare, "Communicating Sequential Processes" (1985)
- **P1 框架**: J. Sifakis, "A Framework for Component-based Construction" (2005) / BIP framework
- **P1 论文**: Rouhi et al., "Towards a formal model of patterns and pattern languages" (2018)
- **P1 生态**: [Tokio](https://tokio.rs/) · [Actix](https://actix.rs/) · [Tonic](https://github.com/hyperium/tonic)

---

## 与表征空间的关系

```text
semantic_space.md §5 机制组合
    └── 系统语义层（本目录）
            ├── Actor 模型：异步消息传递的通用语义
            ├── π 演算：动态拓扑与 channel 移动
            ├── 组件组合：从局部组件到系统涌现行为
            ├── 分布式语义：共识与一致性
            └── 反应式语义：流与背压
```
