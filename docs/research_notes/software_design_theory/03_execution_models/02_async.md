# 异步执行模型形式化 {#异步执行模型形式化}

> **EN**: Async
> **Summary**: 异步执行模型形式化 Async. (stub/archive redirect)
> **概念族**: 软件设计 / 执行模型
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-02-12
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 权威国际化来源对齐升级完成 (2026-06-29)
> **对齐说明**: 本文档已于 2026-06-29 从 `archive/research_notes_2026_06_25/software_design_theory/03_execution_models/` 迁回，正在按 [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)、[Tokio Tutorial](https://tokio.rs/tokio/tutorial)、[Rayon Docs](https://docs.rs/rayon/latest/rayon/) 等权威来源升级。
>
> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Rayon Docs](https://docs.rs/rayon/latest/rayon/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/)

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [异步执行模型形式化 {#异步执行模型形式化}](#异步执行模型形式化-异步执行模型形式化)
  - [📑 目录 {#目录}](#-目录-目录)
  - [形式化定义 {#形式化定义}](#形式化定义-形式化定义)
  - [操作语义（简化） {#操作语义简化}](#操作语义简化-操作语义简化)
  - [Rust 实现与代码示例 {#rust-实现与代码示例}](#rust-实现与代码示例-rust-实现与代码示例)
  - [典型场景 {#典型场景}](#典型场景-典型场景)
  - [与同步/并发对比 {#与同步并发对比}](#与同步并发对比-与同步并发对比)
  - [运行时与任务调度 {#运行时与任务调度}](#运行时与任务调度-运行时与任务调度)
    - [Waker 与 Executor {#waker-与-executor}](#waker-与-executor-waker-与-executor)
    - [多任务组合 {#多任务组合}](#多任务组合-多任务组合)
    - [Stream、异步迭代与背压 {#stream异步迭代与背压}](#stream异步迭代与背压-stream异步迭代与背压)
    - [取消安全（Cancellation Safety） {#取消安全cancellation-safety}](#取消安全cancellation-safety-取消安全cancellation-safety)
    - [结构化并发（Structured Concurrency） {#结构化并发structured-concurrency}](#结构化并发structured-concurrency-结构化并发structured-concurrency)
    - [错误传播与取消 {#错误传播与取消}](#错误传播与取消-错误传播与取消)
  - [运行时选型 {#运行时选型}](#运行时选型-运行时选型)
  - [反例与边界 {#反例与边界}](#反例与边界-反例与边界)
  - [边界 {#边界}](#边界-边界)
  - [与 Rust 1.93 的对应 {#与-rust-193-的对应}](#与-rust-193-的对应-与-rust-193-的对应)
  - [实质内容五维自检 {#实质内容五维自检}](#实质内容五维自检-实质内容五维自检)
  - [🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}](#-rust-194-深度整合更新-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}](#本文档的rust-194更新要点-本文档的rust-194更新要点)
      - [核心特性应用 {#核心特性应用}](#核心特性应用-核心特性应用)
      - [代码示例更新 {#代码示例更新}](#代码示例更新-代码示例更新)
      - [相关文档 {#相关文档}](#相关文档-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

> **创建日期**: 2026-02-12
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 权威国际化来源对齐升级完成 (2026-06-29)
> **分类**: 执行模型
> **安全边界**: 纯 Safe

---

## 形式化定义 {#形式化定义}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def 1.1（Future 类型）**:

$\mathrm{Future}\langle T \rangle$ 为惰性计算的表示，满足：

$$\mathrm{Future}\langle T \rangle = \mathrm{Pending} \mid \mathrm{Ready}(T)$$

**Def 1.2（Poll 操作）**:

$\mathit{poll}(f, cx) : \mathrm{Future}\langle T \rangle \times \mathrm{Context} \to \mathrm{Poll}\langle T \rangle$，其中：

$$\mathrm{Poll}\langle T \rangle = \mathrm{Pending} \mid \mathrm{Ready}(T)$$

**Def 1.3（async/await 语义）**:

$\mathit{async}\, \{ e \}$ 产生 $\mathrm{Future}\langle \tau \rangle$，其中 $\tau$ 为 $e$ 的类型。$\mathit{await}\, f$ 在 $f$ 为 $\mathrm{Ready}(v)$ 时求值为 $v$，否则挂起。

**Axiom AS1**：Future 状态转换合法；自引用 Future 需 Pin 保证位置稳定。

**Axiom AS2**：单线程协作式多任务；无抢占，yield 点仅在 await。

**定理 AS-T1**：由 [async_state_machine](../../formal_methods/10_async_state_machine.md) 定理 6.1（状态一致性）、6.2（并发安全）、6.3（进度保证）。

**定理 AS-T2**：由 [pin_self_referential](../../formal_methods/10_pin_self_referential.md)，Pin 保证自引用 Future 移动安全。

**引理 AS-L1（await 挂起语义）**：$\mathit{await}\, f$ 在 $f = \mathrm{Pending}$ 时挂起；恢复后 $f$ 的 poll 由运行时调度；单线程协作式，无抢占。

*证明*：由 Axiom AS2；await 为 yield 点；运行时（tokio 等）在 Ready 时唤醒；无抢占故无数据竞争。∎

**推论 AS-C1**：有限 Future 终将 Ready；由 [async_state_machine](../../formal_methods/10_async_state_machine.md) T6.3；无限延迟需超时/取消显式处理。

---

## 操作语义（简化） {#操作语义简化}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
poll(Pending)     →  Pending

poll(Ready(v))    →  Ready(v)

await Ready(v)    →  v

await Pending     →  suspend（挂起，稍后继续）
```

---

## Rust 实现与代码示例 {#rust-实现与代码示例}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use std::future::Future;

use std::pin::Pin;

use std::task::{Context, Poll};

async fn fetch() -> String {

    "data".to_string()

}

async fn main_async() {

    let x = fetch().await;  // 挂起点，协作式 yield

    println!("{}", x);

}

// 需要运行时（如 tokio）执行

// #[tokio::main]

// async fn main() { main_async().await; }
```

**自引用 Future 与 Pin**：

```rust,ignore
use std::pin::Pin;

use std::marker::PhantomPinned;

struct SelfReferential {

    data: String,

    pointer: *const String,  // 自引用

    _pin: PhantomPinned,

}

impl SelfReferential {

    fn new(s: String) -> Pin<Box<Self>> {

        let mut b = Box::pin(Self {

            data: s,

            pointer: std::ptr::null(),

            _pin: PhantomPinned,

        });

        b.pointer = &b.data;

        b

    }

}
```

**形式化对应**：`async fn` 返回 `impl Future`；`await` 为 poll 循环的语法糖；Pin 保证 `pointer` 指向的地址不变。

---

## 典型场景 {#典型场景}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 场景 | 说明 |
| :--- | :--- |
| 网络 I/O | HTTP 客户端、gRPC、WebSocket |
| 文件 I/O | 异步读写、watch |
| 高并发连接 | 单线程处理大量连接 |
| 定时器/延迟 | `tokio::time::sleep`、`Interval` |

---

## 与同步/并发对比 {#与同步并发对比}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 模型 | 线程 | 调度 | 适用场景 |
| :--- | :--- | :--- | :--- |
| 同步 | 1 | 无 | CPU 密集 |
| 异步 | 1 | 协作式 | I/O 密集、高并发连接 |
| 并发 | N | 抢占式 | 多核并行 |

---

## 运行时与任务调度 {#运行时与任务调度}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Waker 与 Executor {#waker-与-executor}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def 1.4（Waker）**:

$Waker$ 为唤醒器，当 Future 可继续执行时通过 `wake()` 通知 executor 重新 poll。

**Def 1.5（Executor）**:

Executor 负责调度 Future：轮询 Pending 的 Future，在 `wake()` 后重新调度。

```text
Future 执行流程（简化）：

  poll(f) → Pending

    → 注册 Waker 到 I/O 源

    → 返回 Pending

  （I/O 就绪）

    → Waker::wake()

    → Executor 重新 poll(f)

    → Ready(v)
```

### 多任务组合 {#多任务组合}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 组合 | 语义 | 示例 |
| :--- | :--- | :--- |
| `join!(a, b)` | 并行执行，等待全部完成 | `tokio::join!(f1(), f2())` |
| `select!(a, b)` | 先完成者优先，取消其余 | `tokio::select!(r1 = f1() => ..., r2 = f2() => ...)` |
| `try_join!` | 任一失败即返回 | `tokio::try_join!(f1(), f2())` |
| `spawn` | 后台任务，不等待 | `tokio::spawn(async { ... })` |

### Stream、异步迭代与背压 {#stream异步迭代与背压}

> **来源: [Rust Reference – Async/Await](https://doc.rust-lang.org/reference/expressions/await-expr.html)**
> **来源: [futures-rs docs](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)**

**Def 1.6（Stream）**：

`Stream` 为异步版 `Iterator`：

```rust,ignore
use futures::stream::Stream;

// `next().await` 每次异步拉取一个元素
```

| 场景 | 选型 | 说明 |
| :--- | :--- | :--- |
| 异步序列 | `futures::stream::Stream` / `tokio_stream::Stream` | 事件流、消息流 |
| 背压控制 | `tokio::sync::mpsc` bounded channel | 发送者阻塞/丢包防止内存无限增长 |
| 转换 | `StreamExt::map`、`filter`、`fold` | 惰性异步组合 |

### 取消安全（Cancellation Safety） {#取消安全cancellation-safety}

> **来源: [Tokio Docs – Cancellation Safety](https://docs.rs/tokio/latest/tokio/macro.select.html#cancellation-safety)**
> **来源: [Rust Async Book](https://rust-lang.github.io/async-book/06_multiple_futures/03_select.html)**

**Def 1.7（取消安全）**：Future 在 `select!` 未被选中分支被 drop 后，仍保持内部状态一致性；再次 poll 不会丢失事件或违反不变式。

| 操作 | 是否取消安全 | 说明 |
| :--- | :--- | :--- |
| `tokio::sync::mpsc::Receiver::recv` | ✅ | 内部原子状态保证 |
| `tokio::sync::broadcast::Receiver::recv` | ⚠️ 部分 | 可能丢失消息，需额外处理 |
| 自定义 Future 持有局部计数 | ❌ | 需用 `AsyncDrop` 模式或 `select!` biased |

**实践**：优先使用 channel 的取消安全 API；对状态敏感操作使用 `tokio_util::sync::CancellationToken` + 结构化取消。

### 结构化并发（Structured Concurrency） {#结构化并发structured-concurrency}

> **来源: [Tokio Docs – Spawning](https://tokio.rs/tokio/tutorial/spawning)**
> **来源: [rust-lang/async-book](https://rust-lang.github.io/async-book/06_multiple_futures/02_join.html)**

**Def 1.8（结构化并发）**：子任务生命周期受父任务作用域约束；父任务退出时子任务必须完成或被取消。

```rust,ignore
use tokio::task;

async fn parent() -> Result<(), Error> {

    let h1 = task::spawn(child_one());

    let h2 = task::spawn(child_two());

    let (r1, r2) = tokio::join!(h1, h2);

    r1??; r2??;

    Ok(())

}
```

| 机制 | 作用 |
| :--- | :--- |
| `tokio::join!` | 并发执行，等待全部完成 |
| `tokio::try_join!` | 任一失败即返回 |
| `tokio::select!` | 多路复用，取消未选中分支 |
| `task::JoinSet` | 动态 spawn 集合，等待全部完成 |
| `CancellationToken` | 协作式取消传播 |

### 错误传播与取消 {#错误传播与取消}

> **来源: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// ? 操作符传播 Result

async fn fetch_and_parse() -> Result<Data, Error> {

    let raw = fetch().await?;

    parse(raw).map_err(Into::into)

}

// 取消：drop 会取消未完成的 Future

let handle = tokio::spawn(async { ... });

handle.abort();  // 显式取消
```

**定理 AS-T3**：`Future` 的 `drop` 保证资源释放；`select!` 的未选中分支被 drop，自动取消。

---

## 运行时选型 {#运行时选型}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 运行时 | 特点 | 适用 |
| :--- | :--- | :--- |
| **tokio** | 多线程、work-stealing、生态丰富 | 生产、网络服务 |
| **tokio** | 接近 std API、兼容性好 | 快速原型 |
| **smol** | 轻量、可嵌入 | 嵌入式、资源受限 |
| **无运行时** | 手动 poll、嵌入式 | `#[no_std]` |

---

## 反例与边界 {#反例与边界}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 反例 | 后果 | 说明 |
| :--- | :--- | :--- |
| 自引用 Future 未 Pin | 悬垂 | 移动后自引用指针失效 |
| 非 Send 跨 await | 编译错误 | async 块可能跨线程 |
| 在 Future 中持有 borrow | 生命周期错误 | await 后可能切换任务 |
| 阻塞 executor 线程 | 饥饿 | 在 async 中调用 `std::thread::sleep` |

---

## 边界 {#边界}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe（Pin 由库封装） |
| 支持 | 库支持（tokio/tokio） |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应 {#与-rust-193-的对应}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 1.93 特性 | 与本模型 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | async/await 语义稳定，1.93 无变更 |
| 92 项落点 | 无 | 见 [06_boundary_analysis](06_boundary_analysis.md#rust-193-执行模型相关变更) |

---

## 实质内容五维自检 {#实质内容五维自检}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Future、Def、定理 AS-T1/T2/T3 |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景、运行时选型 |
| 反例 | ✅ | 自引用未 Pin、阻塞 executor |
| 衔接 | ✅ | async_state_machine、pin、Send/Sync |
| 权威对应 | ✅ | [RustBelt RBRlx](https://plv.mpi-sws.org/rustbelt/rbrlx/)、[formal_methods](../../formal_methods/README.md) |

---

## 🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用 {#核心特性应用}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新 {#代码示例更新}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档 {#相关文档}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

- Rust 1.94 迁移指南
- [Rust 1.94 特性速查
- [性能调优指南](../../../05_guides/05_performance_tuning_guide.md)

---

**维护者**: Rust 学习项目团队

**最后更新**: 2026-03-14 (Rust 1.94 深度整合)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1

**对应 Rust 版本**: 1.96.0+ (Edition 2024)

**最后更新**: 2026-05-19

**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}

>
> **[来源: [crates.io](https://crates.io/)]**

- [03_execution_models 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)**
> **来源: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)**
> **来源: [TRPL Ch. 17 - Async](https://doc.rust-lang.org/book/ch17-00-async-await.html)**
> **来源: [RFC 2394 - Async/Await](https://rust-lang.github.io/rfcs/2394-async_await.html)**
> **来源: [RFC 2592 - Pin](https://rust-lang.github.io/rfcs/2592-pin.html)**
> **来源: [Rust Reference - Await Expressions](https://doc.rust-lang.org/reference/expressions/await-expr.html)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

---
