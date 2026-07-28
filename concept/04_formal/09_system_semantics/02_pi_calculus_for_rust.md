> **内容分级**: [专家级]

# π 演算 for Rust 系统语义

> **EN**: Pi-Calculus for Rust System Semantics
> **Summary**: System-semantics entry point for the π-calculus — mobile processes, channel passing, and their relationship to Rust's dynamic communication topology.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页：π 演算系统语义入口。
> **定位**: 从**系统语义**（动态拓扑、channel 移动性、名称传递作为结构演化机制）角度为 π 演算提供导航入口。完整形式化骨架、CSP/CCS/π 与 Rust 原语对应见 [`04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md`](../07_concurrency_semantics/01_process_calculi_for_rust.md)。
> **前置概念**: [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) · [Actor Model Semantics](01_actor_model_semantics.md)
> **后置概念**: [Component-Based Semantics](03_component_based_semantics.md) · [Distributed Systems Semantics](04_distributed_systems_semantics.md)

---

> **来源**: [Milner, *Communicating and Mobile Systems: The π-Calculus*, CUP 1999](https://www.research.ed.ac.uk/en/publications/communicating-and-mobile-systems-the-%CF%80-calculus/) · [Milner, *The Polyadic π-Calculus: a Tutorial*, LFCS 1992](https://www.lfcs.inf.ed.ac.uk/reports/91/ECS-LFCS-91-180/) · [std::sync::mpsc](https://doc.rust-lang.org/std/sync/mpsc/)

## 系统语义要点

π 演算对系统语义的核心贡献是**移动性（mobility）**：通道名本身可以作为值在通道上传输，从而动态改变系统通信拓扑。

```text
P,Q ::= 0 | α.P | P|Q | (νa)P | !P
α   ::= a⟨b⟩  (在通道 a 上发送名 b)
      | a(b)  (在通道 a 上接收名，绑定为 b)
      | τ     (内部动作)
```

Rust 中 `Sender<Sender<T>>` 或 `Sender<Receiver<T>>` 的传递，是 π 演算移动性在工程中的有限投影。

## 权威来源链接

完整形式化、与 Rust 原语对应、反例与边界分析见：

> [`concept/04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md`](../07_concurrency_semantics/01_process_calculi_for_rust.md)
