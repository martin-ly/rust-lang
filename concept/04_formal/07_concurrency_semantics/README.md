# 并发形式语义子层（Concurrency Semantics）

> **EN**: Concurrency Semantics (Formal Models of Concurrent Computation)
> **Summary**: Navigation page for the L4 concurrency-semantics sublayer: process calculi (CSP/CCS/pi-calculus), linearizability and the consistency spectrum, and Actor formal semantics — the formal foundations beneath Rust's concurrency primitives.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/04_formal/07_concurrency_semantics/` 子层导览页（索引，非概念正文）。

---

## 一、子层定位

Rust 的并发原语（`mpsc`、`select!`、`Atomic*`、actor 框架）在工程文档中各自为政，但它们共享一套 1970–1990 年代建立的形式根基。本子层把这些根基整理为六个权威页，回答六类问题：

| 问题 | 权威页 | 形式工具 |
|:---|:---|:---|
| 通道与通信的结构从哪来？Rust channel 与 CSP 到底「像」到什么程度？ | [01 进程代数与 Rust](01_process_calculi_for_rust.md) | CSP / CCS / π 演算、互模拟、移动性 |
| 并发对象「正确」的精确定义是什么？怎么证明？ | [02 线性化与一致性（Coherence）谱系](02_linearizability_and_consistency.md) | Herlihy-Wing 历史/线性化点、一致性谱系、CAP |
| 命名进程 + 邮箱模型的语义是什么？监督树如何形式化？ | [03 Actor 形式语义](03_actor_semantics.md) | Hewitt 三公理、Agha 配置语义、OTP 监督树 |
| 代数效应、效应处理器与 Rust 关键字效果的关系是什么？ | [04 代数效应与效应处理器](04_algebraic_effects.md) | Plotkin & Pretnar、自由单子、限定控制、行多态 |
| 事务内存（STM）的正确性如何定义？为什么 Rust 没有原生 STM？ | [05 STM 形式语义](05_stm_semantics.md) | Herlihy-Moss、opacity/TMS2、retry/orElse、乐观并发控制 |
| 分布式共识为什么「不可能」又如何「可行」？FLP/CAP/Paxos/Raft/BFT 的形式边界在哪？ | [06 分布式共识与不可能性理论](06_distributed_consensus_theory.md) | FLP 1985、Gilbert & Lynch 2002、Paxos、Raft 不变量、PBFT 3f+1 |

## 二、学习路径

```text
L3 并发编程（mpsc/Atomic 工程用法）
   │
   ▼
01 进程代数（通信结构的形式血统）
   ├──► 02 线性化（共享内存对象的正确性条件）
   ├──► 03 Actor 语义（命名进程对偶模型 + 监督容错）
   ├──► 04 代数效应（计算请求与其解释的形式分离）
   ├──► 05 STM 语义（原子块正确性 + Rust「无 STM」论证）
   └──► 06 分布式共识理论（FLP/CAP 不可能性 + Paxos/Raft/BFT 不变量）
            │
            ▼
   L6 分布式延伸：06 共识生态 · 08 CRDT 谱系 · 09 因果序与向量时钟
   L5 对比视角：02 执行模型同构性矩阵 · 04 五模型定义矩阵
```

## 三、分工声明（Canonical）

- 本子层是并发**形式语义**的权威层；[L3 并行与分布式模式谱系](../../03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md) 保留**工程谱系导航**视角（§6.2 已声明分工）；
- [L5 执行模型同构性矩阵](../../05_comparative/00_paradigms/02_execution_model_isomorphism.md) 保留**跨语言对比**视角（§六 CSP/§七 Actor 已加「形式化见」链接，两页头部互相声明分工）；
- 分布式延伸页（共识生态、CRDT、因果序）归属 [L6 数据与分布式](../../06_ecosystem/06_data_and_distributed/)，与本子层互链；其中 [06 分布式共识与不可能性理论](06_distributed_consensus_theory.md) 与 [L6 分布式共识生态页](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) 有显式分工：本页权威于**形式理论**（FLP/CAP/PACELC、协议不变量与安全性论证），生态页权威于**机制教程、Rust 生态与选型**（见该页 §5.5 分工声明）。

## 四、文件清单

| 文件 | 主题 | 关键来源 |
|:---|:---|:---|
| [01_process_calculi_for_rust.md](01_process_calculi_for_rust.md) | CSP/CCS/π 演算骨架与 Rust 原语对应（含四条不同构边界） | Hoare 1978/1985 · Milner 1980/1992/1999 |
| [02_linearizability_and_consistency.md](02_linearizability_and_consistency.md) | Herlihy-Wing 线性化定义、证明方法、一致性谱系与 CAP | Herlihy-Wing 1990 · Lamport 1979 · Brewer 2012 |
| [03_actor_semantics.md](03_actor_semantics.md) | Actor 三公理、Agha 配置语义、OTP 监督树、actix/ractor/kameo 映射 | Hewitt 1973 · Agha 1986 · Erlang/OTP |
| [04_algebraic_effects.md](04_algebraic_effects.md) | 代数效应、效应处理器、自由单子、Rust 关键字效果与跨语言对比 | Plotkin & Pretnar 2009 · Leijen 2014 · OCaml 5 · Koka · Eff |
| [05_stm_semantics.md](05_stm_semantics.md) | STM 起源谱系、opacity/TMS2 正确性、retry/orElse、Rust「无 STM」设计分析与 `stm` crate 局限 | Herlihy & Moss 1993 · Shavit & Touitou 1995 · Harris et al. 2005 · Guerraoui & Kapalka 2008 · DGLM 2013 · docs.rs/stm |
| [06_distributed_consensus_theory.md](06_distributed_consensus_theory.md) | FLP/CAP/PACELC 不可能性理论、Paxos/Raft/PBFT 不变量、所有权 ⟹ 共识实现安全 | FLP 1985 · Brewer 2000/2012 · Gilbert & Lynch 2002 · Lamport 1998/2001 · Ongaro & Ousterhout 2014 · Castro & Liskov 1999 |

> **文档版本**: 1.2 ｜ **最后更新**: 2026-07-16 ｜ **状态**: ✅ 新增 05 STM 语义页、06 分布式共识理论页（Rust 1.97 对齐）
