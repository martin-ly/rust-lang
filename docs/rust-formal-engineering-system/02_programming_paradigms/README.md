# 编程范式

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至研究笔记，请参见：

| 主题 | 链接 |
| :--- | :--- |
| 执行模型 | [software_design_theory/03_execution_models/](../../research_notes/software_design_theory/03_execution_models/README.md) |
| 异步编程 | [formal_methods/10_async_state_machine.md](../../research_notes/formal_methods/10_async_state_machine.md) |
| 并发模型 | [formal_methods/10_send_sync_formalization.md](../../research_notes/formal_methods/10_send_sync_formalization.md) |

---

## 目录结构
>
> **[来源: Rust Official Docs]**

| 子目录 | 内容 |
| :--- | :--- |
| [01_synchronous/](01_synchronous/README.md) | 同步编程范式 |
| [02_async/](02_async/README.md) | 异步编程模型 |
| [09_actor_model/](09_actor_model/README.md) | Actor 模型实现 |

### 文档
>
> **[来源: Rust Official Docs]**

| 文档 | 说明 |
| :--- | :--- |
| [11_benchmark_minimal_guide.md](./11_benchmark_minimal_guide.md) | 基准测试最小化指南 |

---

## 编程范式概览
>
> **[来源: Rust Official Docs]**

### 同步编程

```rust,ignore
// 顺序执行，确定性行为
fn synchronous_example() {
    let result1 = compute_step1();
    let result2 = compute_step2(result1);
    let final_result = compute_step3(result2);
    println!("Result: {}", final_result);
}
```

### 异步编程

```rust,ignore
use tokio::time::{sleep, Duration};

// 异步/等待：非阻塞 I/O
async fn asynchronous_example() {
    let task1 = async_operation1();
    let task2 = async_operation2();

    // 并发执行
    let (result1, result2) = tokio::join!(task1, task2);
    println!("Results: {:?}, {:?}", result1, result2);
}

async fn async_operation1() -> String {
    sleep(Duration::from_millis(100)).await;
    "Operation 1 complete".to_string()
}

async fn async_operation2() -> String {
    sleep(Duration::from_millis(100)).await;
    "Operation 2 complete".to_string()
}
```

### 并发编程

```rust
use std::thread;
use std::sync::mpsc;

// 多线程与消息传递
fn concurrent_example() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        tx.send("Hello from thread").unwrap();
    });

    let message = rx.recv().unwrap();
    println!("{}", message);
}
```

---

## 与核心文档的关联

| 本文档 | 核心文档 | 关系 |
| :--- | :--- | :--- |
| 本README | research_notes/software_design_theory/03_execution_models/ | 索引/重定向 |

[返回主索引](../00_master_index.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**
