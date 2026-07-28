> **内容分级**: [专家级]

# 并发模型比较（Concurrency Model Comparison）

> **EN**: Concurrency Model Comparison
> **Summary**: Formal comparison of concurrent, parallel, asynchronous and distributed computation models — shared memory, message passing, CSP, Actor, π-calculus, Petri nets, and their expressive power boundaries.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本目录为 `concept/` 权威层；与 `07_concurrency_semantics/`、`09_system_semantics/` 形成「模型细节 → 系统语义 → 模型比较」三层结构。
> **定位**: 从**形式模型间比较**的角度，刻画同步/并发/并行/异步/分布式五种计算范式的语义边界、表达能力与互编码关系，避免把 Rust 的并发原语误当成某一模型的同构实现。
> **前置概念**: [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) · [Actor Semantics](../07_concurrency_semantics/03_actor_semantics.md) · [Distributed Systems Semantics](../09_system_semantics/04_distributed_systems_semantics.md) · [Five Models Definition Matrix](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md)
> **后置概念**: [Reactive Systems Semantics](../09_system_semantics/05_reactive_systems_semantics.md) · [Stream Algebra](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) · [Semantic Space](../../00_meta/00_framework/semantic_space.md)

---

## 目录定位

`07_concurrency_semantics/` 深入单个模型（CSP/Actor/π/STM），`09_system_semantics/` 从系统角度分析组合与涌现行为。本目录回答：**这些模型之间是什么关系？** 它们能否互相编码？哪些语义性质在编码中保持、哪些必然丢失？

1. 共享内存、消息传递、CSP、Actor、π、Petri 网的形式骨架是什么？
2. 同步、并发、并行、异步、分布式在形式语义上如何精确定义？
3. 模型间的表达能力如何比较（编码、互模拟、Felleisen 表达力）？
4. Rust 的 `thread::spawn`、`mpsc`、`tokio::select!`、`async/await` 分别落在哪些模型的工程投影上？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_models_of_concurrency.md` | 并发模型谱系：共享内存、消息传递、CSP、Actor、π、Petri 网 | ✅ 已创建 |
| 02 | `02_expressiveness_of_concurrent_models.md` | 并发模型表达能力比较与编码关系 | ✅ 已创建 |
| 03 | `03_parallel_concurrent_async_distributed_semantics.md` | 同步/并发/并行/异步/分布式的形式语义边界 | ✅ 已创建 |

---

## 国际权威来源索引

- **P0 经典**: C. Hoare, *Communicating Sequential Processes* (1985)
- **P0 经典**: R. Milner, *Communicating and Mobile Systems: The π-Calculus* (1999)
- **P0 经典**: C. Hewitt, "Actor Model of Computation" (2017)
- **P1 专著**: W. Reisig, *Petri Nets: An Introduction* (1985)
- **P1 论文**: M. Felleisen, "On the Expressive Power of Programming Languages" (1991)
- **P1 论文**: R. van Glabbeek, "The Linear Time – Branching Time Spectrum" (1990)
- **P1 论文**: D. Sangiorgi, *Introduction to Bisimulation and Coinduction* (2011)

---

## 与表征空间的关系

```text
semantic_space.md §5 机制组合
    └── 并发模型比较层（本目录）
            ├── 模型谱系：共享内存 / 消息传递 / CSP / Actor / π
            ├── 表达能力：编码、互模拟、不可表达性
            └── 五范式边界：同步 / 并发 / 并行 / 异步 / 分布式
```
