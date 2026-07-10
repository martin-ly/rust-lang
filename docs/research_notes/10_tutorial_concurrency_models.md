# 教程：并发模型

**EN**: Tutorial Concurrency Models
**Summary**: Learning entry stub for Rust concurrency models; full explanation lives in the `concept/` authority page.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> 本文件仅保留摘要、速查与链接。

## 速查要点

- Rust 利用所有权与 `Send` / `Sync` trait 在编译期排除数据竞争。
- `Send`：类型可安全跨线程转移所有权；`Sync`：类型可安全跨线程共享引用。
- OS 线程适合 CPU 密集型与真正并行的场景；`std::sync::mpsc` 提供多生产者单消费者通道。
- `Mutex<T>` 与 `RwLock<T>` 用于共享可变状态；`Arc<T>` 提供线程安全的引用计数。
- `async` / `await` 适合高并发 I/O 密集型任务，运行时通常选择 Tokio。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 并发模型 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| 并发模式 | [`concept/03_advanced/00_concurrency/10_concurrency_patterns.md`](../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md) |
| 原子操作与内存序 | [`concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md`](../../concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md) |
| 异步编程 | [`concept/03_advanced/01_async/02_async.md`](../../concept/03_advanced/01_async/02_async.md) |
| 所有权 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| 形式化视角 | [`concept/04_formal/02_separation_logic/04_rustbelt.md`](../../concept/04_formal/02_separation_logic/04_rustbelt.md) |
