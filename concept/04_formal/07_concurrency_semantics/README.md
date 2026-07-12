# 并发形式语义子层（Concurrency Semantics）

> **EN**: Concurrency Semantics (Formal Models of Concurrent Computation)
> **Summary**: Navigation page for the L4 concurrency-semantics sublayer: process calculi (CSP/CCS/pi-calculus), linearizability and the consistency spectrum, and Actor formal semantics — the formal foundations beneath Rust's concurrency primitives.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/04_formal/07_concurrency_semantics/` 子层导览页（索引，非概念正文）。

---

## 一、子层定位

Rust 的并发原语（`mpsc`、`select!`、`Atomic*`、actor 框架）在工程文档中各自为政，但它们共享一套 1970–1990 年代建立的形式根基。本子层把这些根基整理为三个权威页，回答三类问题：

| 问题 | 权威页 | 形式工具 |
|:---|:---|:---|
| 通道与通信的结构从哪来？Rust channel 与 CSP 到底「像」到什么程度？ | [01 进程代数与 Rust](01_process_calculi_for_rust.md) | CSP / CCS / π 演算、互模拟、移动性 |
| 并发对象「正确」的精确定义是什么？怎么证明？ | [02 线性化与一致性谱系](02_linearizability_and_consistency.md) | Herlihy-Wing 历史/线性化点、一致性谱系、CAP |
| 命名进程 + 邮箱模型的语义是什么？监督树如何形式化？ | [03 Actor 形式语义](03_actor_semantics.md) | Hewitt 三公理、Agha 配置语义、OTP 监督树 |

## 二、学习路径

```text
L3 并发编程（mpsc/Atomic 工程用法）
   │
   ▼
01 进程代数（通信结构的形式血统）
   ├──► 02 线性化（共享内存对象的正确性条件）
   └──► 03 Actor 语义（命名进程对偶模型 + 监督容错）
            │
            ▼
   L6 分布式延伸：08 CRDT 谱系 · 09 因果序与向量时钟
   L5 对比视角：02 执行模型同构性矩阵 · 04 五模型定义矩阵
```

## 三、分工声明（Canonical）

- 本子层是并发**形式语义**的权威层；[L3 并行与分布式模式谱系](../../03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md) 保留**工程谱系导航**视角（§6.2 已声明分工）；
- [L5 执行模型同构性矩阵](../../05_comparative/00_paradigms/02_execution_model_isomorphism.md) 保留**跨语言对比**视角（§六 CSP/§七 Actor 已加「形式化见」链接，两页头部互相声明分工）；
- 分布式延伸页（CRDT、因果序）归属 [L6 数据与分布式](../../06_ecosystem/06_data_and_distributed/)，与本子层互链。

## 四、文件清单

| 文件 | 主题 | 关键来源 |
|:---|:---|:---|
| [01_process_calculi_for_rust.md](01_process_calculi_for_rust.md) | CSP/CCS/π 演算骨架与 Rust 原语对应（含四条不同构边界） | Hoare 1978/1985 · Milner 1980/1992/1999 |
| [02_linearizability_and_consistency.md](02_linearizability_and_consistency.md) | Herlihy-Wing 线性化定义、证明方法、一致性谱系与 CAP | Herlihy-Wing 1990 · Lamport 1979 · Brewer 2012 |
| [03_actor_semantics.md](03_actor_semantics.md) | Actor 三公理、Agha 配置语义、OTP 监督树、actix/ractor/kameo 映射 | Hewitt 1973 · Agha 1986 · Erlang/OTP |

> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-12 ｜ **状态**: ✅ W5-7 新建（Rust 1.97 对齐）
