# 执行模型形式化框架

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录 {#-目录}

- [执行模型形式化框架](#执行模型形式化框架)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [宗旨](#宗旨)
  - [执行模型分类](#执行模型分类)
  - [执行模型多维对比矩阵](#执行模型多维对比矩阵)
  - [依赖引用](#依赖引用)
  - [边界分析](#边界分析)
  - [模型选型决策（实质内容）](#模型选型决策实质内容)
  - [模型选择速查](#模型选择速查)
  - [典型场景与设计模式组合（实质内容）](#典型场景与设计模式组合实质内容)
    - [场景 1：批处理流水线（同步 + 策略）](#场景-1批处理流水线同步--策略)
    - [场景 2：高并发 Web 服务（异步 + Observer + 通道）](#场景-2高并发-web-服务异步--observer--通道)
    - [场景 3：图像处理（并行 + Iterator）](#场景-3图像处理并行--iterator)
    - [场景 4：多服务编排（分布式 + Proxy + DTO）](#场景-4多服务编排分布式--proxy--dto)
    - [选型决策流程（层次推进）](#选型决策流程层次推进)
  - [常见陷阱与规避（执行模型）](#常见陷阱与规避执行模型)
  - [可运行示例（层次推进）](#可运行示例层次推进)
    - [示例 1：批处理 + Strategy（同步）](#示例-1批处理--strategy同步)
    - [示例 2：并发 + Observer（std::thread + mpsc）](#示例-2并发--observerstdthread--mpsc)
    - [示例 3：并行 + Strategy（rayon，需 `cargo add rayon`）](#示例-3并行--strategyrayon需-cargo-add-rayon)

---

## 宗旨

对同步、异步、并发、并行、分布式五类执行模型进行形式化分析，并与 Rust 形式化基础（async_state_machine、pin、Send/Sync、ownership、borrow）衔接。

---

## 执行模型分类

| 模型 | 定义 | 形式化文档 |
| :--- | :--- | :--- |
| 同步 | 顺序执行，单线程 | [01_synchronous](01_synchronous.md) |
| 异步 | Future、async/await、单线程协作式多任务 | [02_async](02_async.md) |
| 并发 | 多线程、Send/Sync、消息传递/共享状态 | [03_concurrent](03_concurrent.md) |
| 并行 | 数据并行、任务并行 | [04_parallel](04_parallel.md) |
| 分布式 | 跨进程/跨节点、Actor、RPC | [05_distributed](05_distributed.md) |

---

## 执行模型多维对比矩阵

下表为同步/异步/并发/并行/分布式的**概念定义/属性关系/选型**多维对比；与 [HIERARCHICAL_MAPPING_AND_SUMMARY](../../research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md) 文档↔思维表征映射衔接。各子文档在本矩阵中的位置见「形式化文档」列。

| 模型 | 确定性 | 数据竞争 | 表达力/典型用途 | 选型条件 | 形式化文档 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **同步** | 顺序确定 | 单线程无竞争 | 顺序执行、批处理、脚本 | 单线程、无 I/O 等待 | [01_synchronous](01_synchronous.md) |
| **异步** | 单线程交错确定 | 单线程无竞争 | I/O 多路复用、高并发连接 | 多 I/O、高并发连接 | [02_async](02_async.md) |
| **并发** | 交错非确定 | Send/Sync 保证无数据竞争 | 多线程、消息传递、共享状态 | 多线程、生产者-消费者 | [03_concurrent](03_concurrent.md) |
| **并行** | 数据/任务并行 | 无共享或同步 | CPU 密集、批量计算 | CPU 密集、rayon 风格 | [04_parallel](04_parallel.md) |
| **分布式** | 跨节点、最终一致 | 跨进程无共享内存 | 跨节点通信、Actor、RPC | 跨节点、微服务 | [05_distributed](05_distributed.md) |

**边界与选型决策树**：[06_boundary_analysis](06_boundary_analysis.md) 含并发选型决策树（Actor/channel/async/Mutex）及与本矩阵的衔接。

**分布式模式扩展**：Event Sourcing、Saga、CQRS、Circuit Breaker、Bulkhead、CAP/BASE 形式化见 [05_distributed § 分布式专用模式形式化](05_distributed.md#分布式专用模式形式化d21-扩展)。

---

## 依赖引用

| 依赖 | 文档 |
| :--- | :--- |
| 异步状态机 | [async_state_machine](../../formal_methods/async_state_machine.md) |
| Pin | [pin_self_referential](../../formal_methods/pin_self_referential.md) |
| 借用 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) |
| 所有权 | [ownership_model](../../formal_methods/ownership_model.md) |
| Rust Book Ch16 | 线程、消息传递、Send/Sync |
| Async Book | Future、async/await、Pin |

---

## 边界分析

[06_boundary_analysis](06_boundary_analysis.md)：各模型的安全/支持/表达边界。

---

## 模型选型决策（实质内容）

| 需求组合 | 推荐模型 | 典型场景 |
| :--- | :--- | :--- |
| 单线程、无 I/O 等待 | 同步 | 批处理、脚本、算法核心 |
| 多 I/O、高并发连接 | 异步 | Web 服务、数据库、网络 |
| 多线程、消息传递 | 并发 | 生产者-消费者、多工作者 |
| CPU 密集、批量计算 | 并行 | 图像处理、数据分析、rayon |
| 跨节点通信 | 分布式 | tonic、actix、RPC |

**与设计模式映射**：同步—全部 23；异步—Observer、Command、State；并发—Singleton、Observer、Mediator；并行—Strategy、Iterator；分布式—Proxy、Gateway、DTO。详见 [06_boundary_analysis](06_boundary_analysis.md)。

---

## 模型选择速查

| 需求 | 推荐模型 | crate |
| :--- | :--- | :--- |
| 顺序执行 | 同步 | std |
| I/O 密集、高并发连接 | 异步 | tokio、async-std |
| 多线程、消息传递 | 并发 | std::thread、mpsc |
| CPU 密集、批量计算 | 并行 | rayon |
| 跨节点通信 | 分布式 | tonic、actix |

---

## 典型场景与设计模式组合（实质内容）

### 场景 1：批处理流水线（同步 + 策略）

**需求**：对一批数据按可配置策略处理。

```rust
trait ProcessStrategy { fn process(&self, data: &[i32]) -> Vec<i32>; }
struct FilterPositive;
impl ProcessStrategy for FilterPositive {
    fn process(&self, data: &[i32]) -> Vec<i32> {
        data.iter().filter(|&x| *x > 0).cloned().collect()
    }
}
fn process_batch<S: ProcessStrategy>(data: Vec<i32>, strategy: &S) -> Vec<i32> {
    strategy.process(&data)  // 同步、顺序
}
```

### 场景 2：高并发 Web 服务（异步 + Observer + 通道）

**需求**：请求处理 → 发事件 → 多订阅者（日志、通知、库存）。

```rust
// 异步 + broadcast channel
let (tx, _) = tokio::sync::broadcast::channel::<OrderEvent>(32);
tokio::spawn(async move {
    let mut rx = tx.subscribe();
    while let Ok(ev) = rx.recv().await { log_event(&ev); }
});
// 处理请求后 tx.send(event)
```

### 场景 3：图像处理（并行 + Iterator）

**需求**：对像素块并行处理。

```rust
use rayon::prelude::*;
let processed: Vec<u8> = pixels
    .par_chunks_mut(chunk_size)
    .map(|chunk| apply_filter(chunk))
    .flatten()
    .collect();
```

### 场景 4：多服务编排（分布式 + Proxy + DTO）

**需求**：订单服务调用库存服务、支付服务。

```rust
trait InventoryService { fn reserve(&self, req: ReserveDto) -> Result<(), String>; }
trait PaymentService { fn charge(&self, req: ChargeDto) -> Result<(), String>; }
struct OrderOrchestrator<I: InventoryService, P: PaymentService> {
    inventory: I,
    payment: P,
}
```

### 选型决策流程（层次推进）

```text
1. 有 I/O 等待？ → 是 → 异步（tokio）
2. 需 CPU 并行？ → 是 → 并行（rayon）
3. 需跨进程？ → 是 → 分布式（tonic）
4. 否 → 同步（std）
```

---

## 常见陷阱与规避（执行模型）

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 同步中阻塞 I/O | 整个线程卡住 | 用 async 或 spawn |
| 异步中阻塞操作 | 阻塞 executor | 用 `spawn_blocking` |
| 并发用 Rc | 编译错误 | 用 Arc |
| 并行中共享可变 | 数据竞争 | 用 channel 或 Arc\<Mutex> |
| 分布式无超时 | 请求挂起 | 设置超时、重试策略 |

---

## 可运行示例（层次推进）

以下示例可直接复制到 `main.rs` 运行（示例 1–2 仅 std；示例 3 需 `rayon`）。

### 示例 1：批处理 + Strategy（同步）

```rust
fn main() {
    trait ProcessStrategy {
        fn process(&self, data: &[i32]) -> Vec<i32>;
    }
    struct FilterPositive;
    impl ProcessStrategy for FilterPositive {
        fn process(&self, data: &[i32]) -> Vec<i32> {
            data.iter().filter(|&x| *x > 0).cloned().collect()
        }
    }
    struct Double;
    impl ProcessStrategy for Double {
        fn process(&self, data: &[i32]) -> Vec<i32> {
            data.iter().map(|x| x * 2).collect()
        }
    }

    let data = vec![-1, 2, -3, 4, 5];
    let out = FilterPositive.process(&data);
    assert_eq!(out, vec![2, 4, 5]);
    let out2 = Double.process(&out);
    assert_eq!(out2, vec![4, 8, 10]);
}
```

### 示例 2：并发 + Observer（std::thread + mpsc）

```rust
fn main() {
    use std::sync::mpsc;
    use std::thread;

    let (tx, rx) = mpsc::channel::<i32>();

    let tx2 = tx.clone();
    thread::spawn(move || {
        for i in 1..=3 {
            tx2.send(i).unwrap();
        }
    });

    let mut results = vec![];
    while let Ok(v) = rx.recv() {
        results.push(v);
        if results.len() >= 3 { break; }
    }
    assert_eq!(results, vec![1, 2, 3]);
}
```

### 示例 3：并行 + Strategy（rayon，需 `cargo add rayon`）

```rust
// Cargo.toml: rayon = "1.10"
fn main() {
    use rayon::prelude::*;

    trait FilterStrategy: Sync {
        fn keep(&self, x: i32) -> bool;
    }
    struct Positive;
    impl FilterStrategy for Positive {
        fn keep(&self, x: i32) -> bool { x > 0 }
    }

    let data: Vec<i32> = (-100..100).collect();
    let filtered: Vec<i32> = data.par_iter()
        .filter(|&&x| Positive.keep(x))
        .cloned()
        .collect();
    assert_eq!(filtered.len(), 99);
}
```
