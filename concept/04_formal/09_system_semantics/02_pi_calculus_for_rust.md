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

> **来源**: [Milner, *Communicating and Mobile Systems: The π-Calculus*, CUP 1999](https://www.cambridge.org/core/books/communicating-and-mobile-systems-the-pi-calculus/) · [Milner, *The Polyadic π-Calculus: a Tutorial*, LFCS 1992](https://www.lfcs.inf.ed.ac.uk/reports/91/ECS-LFCS-91-180/) · [std::sync::mpsc](https://doc.rust-lang.org/std/sync/mpsc/)
>
> **权威来源 / Provenance**: Milner, R. (1999). *Communicating and Mobile Systems: The π-Calculus*. Cambridge University Press. 这是 π 演算的系统语义奠基专著，定义了通道名作为一等值传递与名字限制 `(νx)` 的动态拓扑演化机制。[CUP](https://www.cambridge.org/core/books/communicating-and-mobile-systems-the-pi-calculus/)

## 系统语义要点

π 演算对系统语义的核心贡献是**移动性（mobility）**：通道名本身可以作为值在通道上传输，从而动态改变系统通信拓扑。

```text
P,Q ::= 0 | α.P | P|Q | (νa)P | !P
α   ::= a⟨b⟩  (在通道 a 上发送名 b)
      | a(b)  (在通道 a 上接收名，绑定为 b)
      | τ     (内部动作)
```

- **名字限制 `(νa)P`**：创建仅作用于 `P` 的私有通道名 `a`，对应 Rust 中在闭包/线程作用域内创建的 `mpsc` 通道。
- **移动性 `a⟨b⟩`**：把通道名 `b` 当作消息在通道 `a` 上发送，使接收方获得原本不可达的通信能力。
- **复制 `!P`**：无限多个 `P` 并行，对应 Rust 中循环 `spawn` 的进程族。

Rust 中 `Sender<Sender<T>>` 或 `Sender<Receiver<T>>` 的传递，是 π 演算移动性在工程中的有限投影。

## Rust 投影：通道传递与动态拓扑

下面是一个可运行的 Rust 程序，展示 π 演算「把通道名作为消息传递」的核心思想：工作节点 A 创建一个私有工作通道，把发送端交给协调者，协调者再把它移交给工作节点 B。

```rust
use std::sync::mpsc::{self, Receiver, Sender};

fn main() {
    // 控制通道：用于交接新的工作通道（对应 π 演算中的 a）
    let (ctrl_tx, ctrl_rx): (Sender<Sender<i32>>, Receiver<Sender<i32>>) =
        mpsc::channel();

    // 工作节点 A 创建私有工作通道（对应 (νb) 新建名 b）
    let (work_tx, work_rx): (Sender<i32>, Receiver<i32>) = mpsc::channel();

    // A 把 work_tx 作为消息发到控制通道上：a⟨b⟩
    std::thread::spawn(move || {
        ctrl_tx.send(work_tx).unwrap();
    });

    // 协调者从控制通道接收 work_tx，再移交给 B
    let delegated_tx: Sender<i32> = ctrl_rx.recv().unwrap();
    std::thread::spawn(move || {
        delegated_tx.send(42).unwrap(); // B 现在拥有与 A 私下通信的能力
    });

    assert_eq!(work_rx.recv().unwrap(), 42);
}
```

> **边界**: Rust 的 `Sender<T>` 是可克隆的，而 π 演算中的通道名在线性语义下通常不可复制；因此 Rust 只能近似 π 演算的线性移动性。完整形式化、反例与边界见 [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md)。

## 权威来源链接

完整形式化、与 Rust 原语对应、反例与边界分析见：

> [`concept/04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md`](../07_concurrency_semantics/01_process_calculi_for_rust.md)
