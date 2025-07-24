# 并发模型（Concurrency Model）

## 1. 工程原理与定义（Principle & Definition）

并发是指多个任务在同一时间段内交替推进，强调任务切换与资源共享。Rust 通过线程、任务、异步机制等实现高效并发。
Concurrency means multiple tasks make progress within the same time period, focusing on task switching and resource sharing. Rust provides threads, tasks, and async mechanisms for efficient concurrency.

## 2. Rust 1.88 新特性工程化应用

- `std::sync::LazyLock`/`LazyCell`：线程安全的全局/线程本地懒初始化。
- `async fn in traits`：trait原生支持异步方法，简化并发抽象。
- `#[expect]`属性：可控lint，提升并发代码开发体验。
- trait对象向上转型：支持trait对象的安全类型提升，便于并发抽象。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 使用 `std::thread`/`tokio::task` 创建并发任务。
- `Mutex`/`RwLock`/`Arc` 进行安全共享。
- `channel`/`mpsc`/`crossbeam` 进行消息传递。
- `rayon` 实现数据并行。
- `LazyLock`/`LazyCell` 实现惰性并发初始化。

**最佳实践：**

- 优先使用消息传递（channel）解耦线程，减少共享状态。
- 利用类型系统（Send/Sync）静态保证线程安全。
- 使用clippy/loom等工具检测死锁和竞态。
- 结合异步和多线程，提升IO与CPU并发能力。

## 4. 常见问题 FAQ

- Q: Rust 如何避免数据竞争？
  A: 通过所有权、借用和类型系统静态消除绝大多数数据竞争。
- Q: 如何选择线程池和异步任务？
  A: 计算密集型优先线程池，IO密集型优先异步任务。
- Q: 如何检测并发中的死锁？
  A: 使用clippy、loom等工具进行静态和动态分析。

## 5. 参考与扩展阅读

- [Rust 官方并发文档](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Tokio 异步运行时](https://tokio.rs/)
- [Rayon 数据并行库](https://github.com/rayon-rs/rayon)
- [Loom 并发模型测试](https://github.com/tokio-rs/loom)
