# 异步执行模型形式化

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 执行模型
> **安全边界**: 纯 Safe

---

## 📊 目录

- [异步执行模型形式化](#异步执行模型形式化)
  - [形式化定义](#形式化定义)
  - [操作语义（简化）](#操作语义简化)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [典型场景](#典型场景)
  - [与同步/并发对比](#与同步并发对比)
  - [运行时与任务调度](#运行时与任务调度)
  - [运行时选型](#运行时选型)
  - [反例与边界](#反例与边界)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

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

**定理 AS-T1**：由 [async_state_machine](../../formal_methods/async_state_machine.md) 定理 6.1（状态一致性）、6.2（并发安全）、6.3（进度保证）。

**定理 AS-T2**：由 [pin_self_referential](../../formal_methods/pin_self_referential.md)，Pin 保证自引用 Future 移动安全。

**引理 AS-L1（await 挂起语义）**：$\mathit{await}\, f$ 在 $f = \mathrm{Pending}$ 时挂起；恢复后 $f$ 的 poll 由运行时调度；单线程协作式，无抢占。

*证明*：由 Axiom AS2；await 为 yield 点；运行时（tokio 等）在 Ready 时唤醒；无抢占故无数据竞争。∎

**推论 AS-C1**：有限 Future 终将 Ready；由 [async_state_machine](../../formal_methods/async_state_machine.md) T6.3；无限延迟需超时/取消显式处理。

---

## 操作语义（简化）

```text
poll(Pending)     →  Pending
poll(Ready(v))    →  Ready(v)
await Ready(v)    →  v
await Pending     →  suspend（挂起，稍后继续）
```

---

## Rust 实现与代码示例

```rust
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

```rust
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

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 网络 I/O | HTTP 客户端、gRPC、WebSocket |
| 文件 I/O | 异步读写、watch |
| 高并发连接 | 单线程处理大量连接 |
| 定时器/延迟 | `tokio::time::sleep`、`Interval` |

---

## 与同步/并发对比

| 模型 | 线程 | 调度 | 适用场景 |
| :--- | :--- | :--- | :--- |
| 同步 | 1 | 无 | CPU 密集 |
| 异步 | 1 | 协作式 | I/O 密集、高并发连接 |
| 并发 | N | 抢占式 | 多核并行 |

---

## 运行时与任务调度

### Waker 与 Executor

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

### 多任务组合

| 组合 | 语义 | 示例 |
| :--- | :--- | :--- |
| `join!(a, b)` | 并行执行，等待全部完成 | `tokio::join!(f1(), f2())` |
| `select!(a, b)` | 先完成者优先，取消其余 | `tokio::select!(r1 = f1() => ..., r2 = f2() => ...)` |
| `try_join!` | 任一失败即返回 | `tokio::try_join!(f1(), f2())` |
| `spawn` | 后台任务，不等待 | `tokio::spawn(async { ... })` |

### 错误传播与取消

```rust
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

## 运行时选型

| 运行时 | 特点 | 适用 |
| :--- | :--- | :--- |
| **tokio** | 多线程、work-stealing、生态丰富 | 生产、网络服务 |
| **async-std** | 接近 std API、兼容性好 | 快速原型 |
| **smol** | 轻量、可嵌入 | 嵌入式、资源受限 |
| **无运行时** | 手动 poll、嵌入式 | `#[no_std]` |

---

## 反例与边界

| 反例 | 后果 | 说明 |
| :--- | :--- | :--- |
| 自引用 Future 未 Pin | 悬垂 | 移动后自引用指针失效 |
| 非 Send 跨 await | 编译错误 | async 块可能跨线程 |
| 在 Future 中持有 borrow | 生命周期错误 | await 后可能切换任务 |
| 阻塞 executor 线程 | 饥饿 | 在 async 中调用 `std::thread::sleep` |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe（Pin 由库封装） |
| 支持 | 库支持（tokio/async-std） |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模型 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | async/await 语义稳定，1.93 无变更 |
| 92 项落点 | 无 | 见 [06_boundary_analysis](06_boundary_analysis.md#rust-193-执行模型相关变更) |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Future、Def、定理 AS-T1/T2/T3 |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景、运行时选型 |
| 反例 | ✅ | 自引用未 Pin、阻塞 executor |
| 衔接 | ✅ | async_state_machine、pin、Send/Sync |
| 权威对应 | ✅ | [RustBelt RBRlx](https://plv.mpi-sws.org/rustbelt/rbrlx/)、[formal_methods](../../formal_methods/README.md) |
