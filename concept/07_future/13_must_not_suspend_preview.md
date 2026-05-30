# `must_not_suspend` Lint Preview
>
> **受众**: [专家]
> **内容分级**: [实验级]

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: F×Eva — 评价跨 await 点的借用安全性
> **前置依赖**: [Async/Await](../03_advanced/02_async.md) · [Interior Mutability](../02_intermediate/08_interior_mutability.md)
> **后置延伸**: [Async Drop](./18_async_drop_preview.md)

> **来源**: [RFC 3014](https://rust-lang.github.io/rfcs/3014-must-not-suspend-lint.html) · [Tracking Issue](https://github.com/rust-lang/rust/issues/83310)

### 10.4 边界测试：`must_not_suspend` 与跨 await 点的借用（运行时错误）

```rust,compile_fail
use std::cell::RefCell;

async fn bad_async() {
    let data = RefCell::new(42);
    let borrow = data.borrow_mut();
    // ❌ 运行时 panic: 若 .await 后其他任务尝试借用 data
    // async 函数可能在 await 点挂起，RefCell 的 borrow 跨越 await
    tokio::task::yield_now().await;
    println!("{}", borrow);
}

fn main() {}
```

> **修正**: **`must_not_suspend`** lint（nightly，`-W must_not_suspend`）警告：某些类型（`RefCell`、`MutexGuard`、`RwLockReadGuard`）在 async 函数中跨越 `.await` 点可能导致**运行时 panic** 或**死锁**。原因：1) `RefCell::borrow_mut()` 获取的引用在 await 点仍然持有；2) 其他任务可能在同一线程尝试 `borrow()`/`borrow_mut()` → panic；3) `MutexGuard` 跨 await 可能导致死锁（若 executor 是单线程）。解决：1) 在 `.await` 前 drop guard；2) 使用 `tokio::sync::Mutex`（`async` 锁，可跨 await）；3) 重新设计数据结构避免跨 await 借用。这与 Go 的 defer + 锁（`defer mu.Unlock()`，goroutine 不挂起当前线程）或 Java 的 `synchronized`（阻塞线程，不挂起任务）不同——Rust 的 async/await 是协作式调度，锁跨越 yield 点危险。[来源: [must_not_suspend lint](https://doc.rust-lang.org/nightly/rustc/lints/listing/allowed-by-default.html#must-not-suspend)] · [来源: [Async Rust](https://rust-lang.github.io/async-book/)]
