# 专题指南

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 专题指南提供 Rust 特定领域的深入实践指导，涵盖异步编程、线程与并发、设计模式、宏系统、WASM、Unsafe Rust 等高级主题，每个指南都包含理论说明、代码示例和最佳实践。

---

## 快速示例

```rust
// 异步编程示例
use tokio::time::{sleep, Duration};

async fn fetch_data() -> String {
    sleep(Duration::from_millis(100)).await;
    "data".to_string()
}

#[tokio::main]
async fn main() {
    let data = fetch_data().await;
    println!("Got: {}", data);
}

// 并发示例
use std::thread;
use std::sync::mpsc;

fn concurrent_example() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        tx.send("Hello from thread").unwrap();
    });

    let msg = rx.recv().unwrap();
    println!("{}", msg);
}

// 设计模式：构建者模式
#[derive(Debug)]
struct Config {
    host: String,
    port: u16,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self { host: None, port: None }
    }

    fn host(mut self, host: &str) -> Self {
        self.host = Some(host.to_string());
        self
    }

    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    fn build(self) -> Result<Config, &'static str> {
        Ok(Config {
            host: self.host.ok_or("Host required")?,
            port: self.port.unwrap_or(8080),
        })
    }
}
```

---

## 文档列表

| 文档 | 描述 | 难度 |
| :--- | :--- | :--- |
| [ASYNC_PROGRAMMING_USAGE_GUIDE.md](./ASYNC_PROGRAMMING_USAGE_GUIDE.md) | 异步编程 | ⭐⭐⭐ |
| [THREADS_CONCURRENCY_USAGE_GUIDE.md](./THREADS_CONCURRENCY_USAGE_GUIDE.md) | 线程与并发 | ⭐⭐⭐ |
| [DESIGN_PATTERNS_USAGE_GUIDE.md](./DESIGN_PATTERNS_USAGE_GUIDE.md) | 设计模式 | ⭐⭐⭐ |
| [MACRO_SYSTEM_USAGE_GUIDE.md](./MACRO_SYSTEM_USAGE_GUIDE.md) | 宏系统 | ⭐⭐⭐⭐ |
| [WASM_USAGE_GUIDE.md](./WASM_USAGE_GUIDE.md) | WASM | ⭐⭐⭐ |
| [UNSAFE_RUST_GUIDE.md](./UNSAFE_RUST_GUIDE.md) | Unsafe Rust | ⭐⭐⭐⭐ |
| [TROUBLESHOOTING_GUIDE.md](./TROUBLESHOOTING_GUIDE.md) | 故障排查 | ⭐⭐ |
| [BEST_PRACTICES.md](./BEST_PRACTICES.md) | 最佳实践 | ⭐⭐⭐ |
| [workflow/](./workflow/README.md) | 工作流理论与模型 | ⭐⭐⭐ |

---

## 指南概览

### 异步编程

```rust
// Future trait 基础
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct Delay {
    duration: Duration,
}

impl Future for Delay {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 检查时间是否到期
        Poll::Ready(())
    }
}
```

### 线程与并发

```rust
// 使用 Arc + Mutex 共享状态
use std::sync::{Arc, Mutex};
use std::thread;

fn shared_state() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            *c.lock().unwrap() += 1;
        }));
    }

    for h in handles { h.join().unwrap(); }
    println!("Result: {}", *counter.lock().unwrap());
}
```

### Unsafe Rust

```rust
// 原始指针操作
unsafe fn raw_pointer_example() {
    let mut num = 5;
    let r1 = &num as *const i32;
    let r2 = &mut num as *mut i32;

    // 必须在 unsafe 块中解引用
    unsafe {
        println!("r1: {}", *r1);
        *r2 = 10;
        println!("r2: {}", *r2);
    }
}
```

### 宏系统

```rust
// 声明宏
macro_rules! vec_mac {
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
}

// 使用
let v = vec_mac![1, 2, 3];
```

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../research_notes/formal_methods/README.md](../research_notes/formal_methods/README.md) |
| 异步形式化 | 异步运行时形式化 | [../research_notes/formal_methods/async_state_machine.md](../research_notes/formal_methods/async_state_machine.md) |
| Send/Sync 形式化 | 线程安全形式化定义 | [../research_notes/formal_methods/send_sync_formalization.md](../research_notes/formal_methods/send_sync_formalization.md) |
| 证明索引 | 形式化证明集合 | [../research_notes/PROOF_INDEX.md](../research_notes/PROOF_INDEX.md) |

---

## 主索引

[00_MASTER_INDEX.md](../00_MASTER_INDEX.md)

---

[返回文档中心](../README.md)

---

## 🆕 Rust 1.94 指南更新

本目录下的所有指南已完成 Rust 1.94 深度语义整合。

### 整合统计

| 类别 | 数量 | 状态 |
|------|------|------|
| 核心指南 | 15 份 | ✅ 100% |
| 工作流文档 | 3 份 | ✅ 100% |
| 其他文档 | 10 份 | ✅ 100% |
| **总计** | **28 份** | ✅✅✅ **100%** |

### 核心特性覆盖

- ✅ **array_windows()**: 18 份文档深度覆盖
- ✅ **ControlFlow**: 17 份文档深度覆盖
- ✅ **LazyLock/LazyCell**: 16 份文档深度覆盖
- ✅ **数学常量**: 10 份文档深度覆盖

### 代码示例

- 3 个可运行示例文件 (~920 行代码)
- 40+ 生产场景示例
- 20+ 性能基准对比表

**最后更新**: 2026-03-14 (Rust 1.94 深度整合 100% 完成)

---

**维护者**: Rust 学习项目团队
**状态**: ✅✅✅ **100% 深度整合完成**
