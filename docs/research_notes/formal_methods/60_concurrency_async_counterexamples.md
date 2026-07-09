# 并发与异步反例边界 {#并发与异步反例边界}

> **EN**: Concurrency Async Counterexamples
> **Summary**: 并发与异步反例边界 Concurrency Async Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6 (分析/评价)
> **概念族**: 并发安全（Concurrency Safety） / 异步（Async） / Send/Sync / Future / Pin / 反例边界
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [并发与异步反例边界 {#并发与异步反例边界}](#并发与异步反例边界-并发与异步反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. `Rc` 跨线程 {#1-rc-跨线程}](#1-rc-跨线程-1-rc-跨线程)
    - [现象 {#现象-6}](#现象-现象-6)
    - [编译器错误 {#编译器错误-1}](#编译器错误-编译器错误-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. `RefCell` 跨线程 {#2-refcell-跨线程}](#2-refcell-跨线程-2-refcell-跨线程)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [编译器错误 {#编译器错误-1}](#编译器错误-编译器错误-1-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. 死锁：嵌套锁获取顺序 {#3-死锁嵌套锁获取顺序}](#3-死锁嵌套锁获取顺序-3-死锁嵌套锁获取顺序)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [后果 {#后果-2}](#后果-后果-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. 在 async 中持有同步锁跨越 await {#4-在-async-中持有同步锁跨越-await}](#4-在-async-中持有同步锁跨越-await-4-在-async-中持有同步锁跨越-await)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [后果 {#后果-2}](#后果-后果-2-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. `Pin` 契约被破坏 {#5-pin-契约被破坏}](#5-pin-契约被破坏-5-pin-契约被破坏)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [根因 {#根因}](#根因-根因)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. 在 `Drop` 中跨越 await {#6-在-drop-中跨越-await}](#6-在-drop-中跨越-await-6-在-drop-中跨越-await)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. 错误实现 `Future` 的 `poll` {#7-错误实现-future-的-poll}](#7-错误实现-future-的-poll-7-错误实现-future-的-poll)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [后果 {#后果-2}](#后果-后果-2-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)

---

## 1. `Rc` 跨线程 {#1-rc-跨线程}

### 现象 {#现象-6}

```rust
use std::rc::Rc;
use std::thread;

let data = Rc::new(42);
let d = Rc::clone(&data);
thread::spawn(move || {
    println!("{}", d); // ❌ Rc<T> 未实现 Send
});
```

### 编译器错误 {#编译器错误-1}

```text
error[E0277]: `Rc<i32>` cannot be sent between threads safely
```

### 修复方案 {#修复方案-6}

- 使用 `Arc<T>` 替代 `Rc<T>`。

---

## 2. `RefCell` 跨线程 {#2-refcell-跨线程}

### 现象 {#现象-6}

```rust
use std::cell::RefCell;
use std::sync::Arc;
use std::thread;

let data = Arc::new(RefCell::new(0));
for _ in 0..4 {
    let d = Arc::clone(&data);
    thread::spawn(move || {
        *d.borrow_mut() += 1; // ❌ RefCell<T> 未实现 Sync
    });
}
```

### 编译器错误 {#编译器错误-1}

```text
error[E0277]: `RefCell<i32>` cannot be shared between threads safely
```

### 修复方案 {#修复方案-6}

- 使用 `Mutex<T>` 或 `RwLock<T>`：`Arc<Mutex<i32>>`。

---

## 3. 死锁：嵌套锁获取顺序 {#3-死锁嵌套锁获取顺序}

### 现象 {#现象-6}

```rust
use std::sync::{Mutex, Arc};

let a = Arc::new(Mutex::new(0));
let b = Arc::new(Mutex::new(0));

let a1 = Arc::clone(&a);
let b1 = Arc::clone(&b);
thread::spawn(move || {
    let _ga = a1.lock().unwrap();
    let _gb = b1.lock().unwrap(); // 可能死锁
});

let a2 = Arc::clone(&a);
let b2 = Arc::clone(&b);
thread::spawn(move || {
    let _gb = b2.lock().unwrap();
    let _ga = a2.lock().unwrap(); // 与上相反顺序，死锁
});
```

### 后果 {#后果-2}

运行时线程互相等待，程序挂起。

### 修复方案 {#修复方案-6}

- 全局统一的加锁顺序。
- 使用 `std::sync::LockResult` 超时或 try_lock。
- 尽量缩小锁粒度，避免同时持有多把锁。

---

## 4. 在 async 中持有同步锁跨越 await {#4-在-async-中持有同步锁跨越-await}

### 现象 {#现象-6}

```rust
async fn bad(data: &Mutex<i32>) {
    let guard = data.lock().unwrap();
    some_async().await; // ❌ 锁_guard 跨越 await
    drop(guard);
}
```

### 后果 {#后果-2}

- 锁在线程调度期间被持有，阻塞其他任务，降低并发度。
- 若 future 被移动到另一个线程执行，可能引发 `!Send` 问题。

### 修复方案 {#修复方案-6}

- 缩小锁作用域，在 await 前释放。
- 使用异步锁：`tokio::sync::Mutex`。

---

## 5. `Pin` 契约被破坏 {#5-pin-契约被破坏}

### 现象 {#现象-6}

```rust
use std::pin::Pin;

struct SelfRef {
    text: String,
    ptr: *const u8,
}

fn broken(pin: Pin<&mut SelfRef>) {
    let mut_ref = unsafe { pin.get_unchecked_mut() };
    mut_ref.text.push('!'); // ❌ 可能使 ptr 悬垂
}
```

### 根因 {#根因}

自引用类型要求 `Pin` 之后不再移动其指向的内存，且不能进行可能重新分配的操作。

### 修复方案 {#修复方案-6}

- 使用 `pin-project` 等库安全地投影 Pin。
- 避免在 `Pin<&mut Self>` 上调用可能重新分配的方法。

> **相关文档**: [10_pin_self_referential.md](10_pin_self_referential.md)

---

## 6. 在 `Drop` 中跨越 await {#6-在-drop-中跨越-await}

### 现象 {#现象-6}

```rust
struct AsyncDrop;

impl Drop for AsyncDrop {
    fn drop(&mut self) {
        // 无法在这里调用 .await
        cleanup().await; // ❌ Drop::drop 不是 async
    }
}
```

### 修复方案 {#修复方案-6}

- 使用显式异步析构模式：`async fn dispose(self)`。
- 借助 `pin-project-lite` 的 `PinnedDrop`。
- 依赖异步运行时提供的异步清理 API。

---

## 7. 错误实现 `Future` 的 `poll` {#7-错误实现-future-的-poll}

### 现象 {#现象-6}

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct BadFuture;

impl Future for BadFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        // ❌ 永远返回 Pending，不注册 waker
        Poll::Pending
    }
}
```

### 后果 {#后果-2}

任务永远不会被唤醒，future 永远挂起。

### 修复方案 {#修复方案-6}

- 在返回 `Poll::Pending` 前通过 `_cx.waker().wake_by_ref()` 注册唤醒。
- 通常使用 `async/await` 或已有原语（`tokio::sync::oneshot` 等）避免手写 `poll`。

---

## 总结 {#总结}

| 反例 | 涉及概念 | 典型错误/后果 | 修复方向 |
|------|----------|---------------|----------|
| `Rc` 跨线程 | Send | E0277 | `Arc<T>` |
| `RefCell` 共享 | Sync | E0277 | `Mutex<T>` / `RwLock<T>` |
| 死锁 | 锁顺序 | 运行时挂起 | 统一顺序、try_lock |
| 同步锁跨越 await | async 执行模型 | 阻塞/任务迁移问题 | 缩小作用域 / 异步锁 |
| 破坏 Pin 契约 | Pin / 自引用 | UB | pin-project、避免 realloc |
| Drop 中 await | 异步析构 | 编译错误 | 显式 async dispose |
| 错误 poll | Future | 永久挂起 | 注册 waker / 使用 async/await |

> **权威来源**: [Rust Reference – Asynchronous Blocks](https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks) | [Rust Reference – Trait std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html) | [The Rust Programming Language – Ch 16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | [Async Book](https://rust-lang.github.io/async-book/) | [Rustonomicon – Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | [Pinning](https://doc.rust-lang.org/std/pin/index.html)

## 相关概念 {#相关概念}

- [Send/Sync 形式化](10_send_sync_formalization.md)
- [异步状态机](10_async_state_machine.md)
- [Pin 与自引用](10_pin_self_referential.md)
- [所有权与借用反例](60_ownership_counterexamples.md)
- [通用反例汇编](../10_counter_examples_compendium.md)
- [知识图谱索引](../10_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../10_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 2394: async/await](https://rust-lang.github.io/rfcs/2394-async_await.html)
- [RFC 3185: Static async fn in traits](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tokio Docs](https://docs.rs/tokio/)
- [Async Book](https://rust-lang.github.io/async-book/)
