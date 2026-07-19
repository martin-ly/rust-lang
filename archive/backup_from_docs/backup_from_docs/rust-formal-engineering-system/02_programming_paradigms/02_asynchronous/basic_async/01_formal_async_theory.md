# Rust 异步理论（形式化与工程结合）

## 目录

- [Rust 异步理论（形式化与工程结合）](#rust-异步理论形式化与工程结合)
  - [目录](#目录)
  - [1. 批判性分析](#1-批判性分析)
  - [2. 形式化基础](#2-形式化基础)
    - [2.1 Future 与 Poll 语义 {#future-poll}](#21-future-与-poll-语义-future-poll)
    - [2.2 状态机降级与生成器 {#state-machine}](#22-状态机降级与生成器-state-machine)
    - [2.3 Pin/Unpin 与内存迁移 {#pin-semantics}](#23-pinunpin-与内存迁移-pin-semantics)
  - [3. 类型与边界](#3-类型与边界)
    - [3.1 async fn 降级与返回类型 {#async-fn-lowering}](#31-async-fn-降级与返回类型-async-fn-lowering)
    - [3.2 Send/Sync 与 .await 边界 {#send-sync-await}](#32-sendsync-与-await-边界-send-sync-await)
    - [3.3 Drop 顺序与借用跨 await {#drop-borrow-await}](#33-drop-顺序与借用跨-await-drop-borrow-await)
  - [4. 执行与调度](#4-执行与调度)
    - [4.1 运行时与Waker协议 {#runtime-waker}](#41-运行时与waker协议-runtime-waker)
    - [4.2 取消、超时与背压 {#cancel-backpressure}](#42-取消超时与背压-cancel-backpressure)
    - [4.3 I/O与多路复用集成 {#io-integration}](#43-io与多路复用集成-io-integration)
  - [5. 抽象与工程化](#5-抽象与工程化)
    - [5.1 async trait 与对象安全 {#async-trait}](#51-async-trait-与对象安全-async-trait)
    - [5.2 Stream/AsyncRead/AsyncWrite 语义 {#stream-io}](#52-streamasyncreadasyncwrite-语义-stream-io)
    - [5.3 错误传播与结构化并发 {#structured-concurrency}](#53-错误传播与结构化并发-structured-concurrency)
  - [6. 典型案例](#6-典型案例)
  - [附：索引锚点与导航](#附索引锚点与导航)
    - [异步生命周期 {#异步生命周期}](#异步生命周期-异步生命周期)
    - [状态机 {#状态机}](#状态机-状态机)
    - [类型规则 {#类型规则}](#类型规则-类型规则)
    - [操作语义 {#操作语义}](#操作语义-操作语义)
    - [await操作符 {#await操作符}](#await操作符-await操作符)

---

## 1. 批判性分析

- Rust 异步基于 Future/`poll` 的零成本抽象，性能优越，但心智负担较高（Pin、借用跨 await、Send/!Send）。
- 无内置运行时，生态以 Tokio、async-std 为主，需关注运行时兼容与阻塞边界。
- 可观测性、调试（如任务泄漏、死锁）、与同步世界的交错仍是工程痛点。

---

## 2. 形式化基础

### 2.1 Future 与 Poll 语义 {#future-poll}

定义：

```text
trait Future { type Output; fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>; }
```

- 语义：`poll` 为非阻塞推进；返回 `Pending` 表示注册 `Waker` 后挂起；返回 `Ready(v)` 表示完成并产出值。
- 不变式：在未 `Ready` 前不得多次完成；`Waker` 唤醒保证后续 `poll` 发生。

小步语义草图：

```text
⟨F, σ⟩ ─poll→ Pending, σ'  或  ⟨F, σ⟩ ─poll→ Ready(v), σ'
```

### 2.2 状态机降级与生成器 {#state-machine}

- `async fn` 经编译器 CPS/生成器降级为匿名 `Future`，携带局部变量快照与程序计数器 pc。
- 每个 `await` 处是可挂起边界；恢复时依据 pc 继续执行。

形式化建模：

```text
State = { pc: usize, locals: Env, waker: Option<Waker> }
step: State × Input → State
```

### 2.3 Pin/Unpin 与内存迁移 {#pin-semantics}

- Pin 不变式：被 Pin 的 `Future` 在未完成前不可移动，确保自引用安全。
- `Unpin` 类型可安全移动；`!Unpin` 需放置于 `Pin<Box<_>>`/`Pin<&mut _>`。

逻辑约束：

```text
Pinned(x) ∧ !Unpin(x) ⇒ ¬Move(x)
```

---

## 3. 类型与边界

### 3.1 async fn 降级与返回类型 {#async-fn-lowering}

- `async fn f(...) -> T` ≈ `fn f(...) -> impl Future<Output = T>`。
- 返回的匿名 Future 可能 `!Send`，取决于内部捕获与借用；跨线程需要显式保证 `Send`。

### 3.2 Send/Sync 与 .await 边界 {#send-sync-await}

- 借用跨 `await`：在挂起点上，悬而未决的借用将被保存于状态机，可能使 `Future: !Send`。
- 规则：
  - 若 `async fn` 内部持有 `!Send` 值跨 `await`，则返回 `Future: !Send`。
  - 在线程池 `spawn`（要求 `Send+'static`）中使用需满足相应边界。

### 3.3 Drop 顺序与借用跨 await {#drop-borrow-await}

- `await` 处发生暂时 drop/保存局部的语义转换；需避免跨 `await` 持有对栈上数据的引用导致悬垂风险。
- 编译器静态拒绝非法借用跨 `await` 的情形；建议在 `await` 前完成借用作用域。

---

## 4. 执行与调度

### 4.1 运行时与Waker协议 {#runtime-waker}

- 运行时驱动 `poll` 循环；I/O 就绪时通过 `Waker::wake` 安排任务重排队。
- 多运行时问题：不要在不同运行时间直接 `await` 彼此对象；使用兼容层或边界 API。

### 4.2 取消、超时与背压 {#cancel-backpressure}

- 取消：通过 `Drop` 传播；需清理注册、释放资源，避免悬挂唤醒。
- 超时：`timeout(dur, fut)` 作为组合子；确保未完成分支被正确取消。
- 背压：`Stream`/通道在满载时应返回 `Pending` 或错误，调用侧应采用窗口/限速策略。

### 4.3 I/O与多路复用集成 {#io-integration}

- 与 epoll/kqueue/IOCP/io_uring 集成由运行时封装；业务侧遵循 `AsyncRead/AsyncWrite` 协议。

---

## 5. 抽象与工程化

### 5.1 async trait 与对象安全 {#async-trait}

- trait 中 `async fn` 目前通常经宏（如 `async-trait`）或 GAT/返回 `impl Future` 变体实现。
- 对象安全：返回 `impl Future` 的方法不对象安全；需采用参数化/装箱 `Pin<Box<dyn Future<...>>>`。

### 5.2 Stream/AsyncRead/AsyncWrite 语义 {#stream-io}

- `Stream` 类似 `Iterator` 的异步对偶：

```text
trait Stream { type Item; fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>; }
```

- I/O traits 保证非阻塞前进、不丢事件、正确的 `Pending` 语义与唤醒配对。

### 5.3 错误传播与结构化并发 {#structured-concurrency}

- 采用 `Result` 显式传播；在 `join!`, `try_join!`, 作用域任务中确保资源成对创建/回收。
- 结构化并发：推荐作用域任务（如 `tokio::task::scope`）避免任务泄漏。

---

## 6. 典型案例

- 高并发 Web：Axum/Tokio 下使用 `async fn` handler，配合中间件与连接池。
- 高性能网络：基于 `AsyncRead/AsyncWrite` 的自定义协议编解码与背压控制。
- 异步多态：以 `impl Trait`/GAT 组合，或 `Pin<Box<dyn Future<...>>>` 封装对象安全接口。

---

## 附：索引锚点与导航

### 异步生命周期 {#异步生命周期}

用于跨文档引用，汇总与异步上下文中生命周期与借用的约束与边界。

### 状态机 {#状态机}

用于跨文档引用，统一指向状态机与生成器降级章节。

### 类型规则 {#类型规则}

用于跨文档引用，统一指向类型/边界规则与 Send/Sync 要求。

### 操作语义 {#操作语义}

用于跨文档引用，统一指向 `poll` 小步语义与 Waker 协议。

### await操作符 {#await操作符}

用于跨文档引用，统一指向 `await` 降级、挂起点与恢复语义。
