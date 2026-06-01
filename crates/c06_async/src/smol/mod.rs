//! Smol 轻量级异步运行时详解
//! Smol async runtime
//!
//! 本模块展示了如何使用 `smol` 轻量级异步运行时。
//! This module demonstrates use `smol` lightweightasyncruntime
//! Smol 是一个简洁、高效的异步运行时，专注于性能和易用性。
//! Smol 、efficient async runtime ，performance and 。
//!
//! ## 核心特性
//! ## Core Features
//!
//! ### 轻量级设计
//! ### lightweight design
//! - **最小化依赖**: 相比其他运行时，依赖更少
//! - **minimum **: its runtime ，
//! - **快速启动**: 启动时间短，适合短期任务
//! - **fast **: time ，short-term task
//! - **低内存占用**: 内存使用量小，适合嵌入式环境
//! - **memory **: memory ，environment
//!
//! ### 高性能
//! ### high performance
//! - **优化的事件循环**: 高效的 I/O 事件处理
//! - **optimization**: efficient I/O processing
//! - **低延迟**: 任务调度延迟低
//! - ****: task
//! - **高吞吐量**: 在 I/O 密集型任务中表现优秀
//! - ****: in I/O task in
//!
//! ### 兼容性
//! ###
//! - **标准异步接口**: 与 tokio、async-std 等运行时兼容
//! - **standard async **: and tokio、async-std etc. runtime
//! - **跨平台支持**: 支持 Windows、Linux、macOS
//! - **嵌入式友好**: 适合资源受限的环境
//! - ****: environment
//!
//! ## 使用场景
//! ## Usage Scenarios
//!
//! 1. **轻量级应用**: 不需要完整运行时功能的应用
//! 1. **lightweightapplication**: needcompleteruntime application
//! 2. **嵌入式系统**: 资源受限的环境
//! 2. **system **: environment
//! 3. **命令行工具**: 简单的异步 CLI 应用
//! 3. ****: singleasync CLI application
//! 4. **测试环境**: 快速测试异步代码
//! 4. **environment **: fast async
//! 5. **微服务**: 轻量级的微服务应用
//! 5. **service**: lightweightservice application
//!
//! ## 与其他运行时的比较
//! ## rather than runtime
//!
//! | 特性 | Smol | Tokio | Async-std |
//! |------|------|-------|-----------|
//! | 启动时间 | 快 | 中等 | 慢 |
//! | time | | in etc. | |
//! | 内存占用 | 低 | 中等 | 高 |
//! | memory | | in etc. | |
//! | 功能丰富度 | 基础 | 丰富 | 丰富 |
//! | functionality | foundation | | |
//! | 学习曲线 | 简单 | 复杂 | 中等 |
//! | learn line | simple | complex | in etc. |
//! | 生态系统 | 小 | 大 | 中等 |
//! | ecosystem system | | | in etc. |
//!
//! ## 基本用法
//! ## this
//!
//! ### 创建运行时
//! ### create runtime
//! ```rust
//! use smol::Task;
//!
//! fn main() {
//!     smol::block_on(async {
//!         // 异步代码
//!         // async
//!     });
//! }
//! ```
//!
//! ### 生成任务
//! ### task
//! ```rust,ignore
//! let task = smol::spawn(async {
//!     // 异步任务
//!     // async task
//! });
//! // 在 async 上下文中 await
//! // in async on under in await
//! ```
//!
//! ## 注意事项
//! ## Notes
//!
//! - Smol 功能相对简单，不适合复杂的异步应用
//! - Smol singleasync application
//! - 对于需要丰富功能的项目，建议使用 Tokio
//! - to functionality project ， Tokio
//! - 适合学习和原型开发
//! - learn and
//!
//! ## 示例
//! ## example
//!
//! ```no_run
//! use c06_async::smol::*;
//!
//! fn main() {
//!     smol::block_on(async {
//!         demo_basic_usage().await;
//!     });
//! }
//! ```

/// 演示 Smol 的基本用法
/// demonstration Smol this
///
/// 这个函数展示了 Smol 运行时的一些基本特性：
/// function Smol runtime this feature ：
/// - 轻量级的任务创建
/// - task
/// - 简单的异步执行
/// - simple async
/// - 基本的并发处理
/// - concurrent processing
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::smol::demo_basic_usage;
///
/// fn main() {
///     smol::block_on(async {
///         demo_basic_usage().await;
///     });
/// }
/// ```
pub async fn demo_basic_usage() {
    use smol::Task;
    use std::time::Duration;

    println!("Smol 轻量级异步运行时演示");

    // 创建多个并发任务
    let tasks: Vec<Task<u64>> = (0..5)
        .map(|i| {
            smol::spawn(async move {
                // 模拟一些异步工作
                smol::Timer::after(Duration::from_millis(100 * (i + 1))).await;
                println!("任务 {} 完成", i);
                i * i
            })
        })
        .collect();

    // 等待所有任务完成并收集结果
    let results = futures::future::join_all(tasks).await;
    println!("所有任务完成，结果: {:?}", results);
}

/// 演示 Smol 的 I/O 操作
/// Smol I/O operation
///
/// 这个函数展示了如何使用 Smol 进行异步 I/O 操作。
/// function Smol async I/O 。
/// 包括计时器、网络请求等常见的异步操作。
/// 、network etc. async 。
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::smol::demo_io_operations;
///
/// fn main() {
///     smol::block_on(async {
///         demo_io_operations().await;
///     });
/// }
/// ```
pub async fn demo_io_operations() {
    use smol::Timer;
    use std::time::Duration;

    println!("Smol I/O 操作演示");

    // 演示计时器
    println!("等待 1 秒...");
    Timer::after(Duration::from_secs(1)).await;
    println!("1 秒已过");

    // 演示并发计时器
    let timer1 = Timer::after(Duration::from_millis(500));
    let timer2 = Timer::after(Duration::from_millis(300));
    let timer3 = Timer::after(Duration::from_millis(800));

    // 等待所有计时器完成
    let _ = futures::join!(timer1, timer2, timer3);
    println!("所有计时器都已完成");
}
