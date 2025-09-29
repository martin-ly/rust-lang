//! Smol 轻量级异步运行时详解
//! 
//! 本模块展示了如何使用 `smol` 轻量级异步运行时。
//! Smol 是一个简洁、高效的异步运行时，专注于性能和易用性。
//! 
//! ## 核心特性
//! 
//! ### 轻量级设计
//! - **最小化依赖**: 相比其他运行时，依赖更少
//! - **快速启动**: 启动时间短，适合短期任务
//! - **低内存占用**: 内存使用量小，适合嵌入式环境
//! 
//! ### 高性能
//! - **优化的事件循环**: 高效的 I/O 事件处理
//! - **低延迟**: 任务调度延迟低
//! - **高吞吐量**: 在 I/O 密集型任务中表现优秀
//! 
//! ### 兼容性
//! - **标准异步接口**: 与 tokio、async-std 等运行时兼容
//! - **跨平台支持**: 支持 Windows、Linux、macOS
//! - **嵌入式友好**: 适合资源受限的环境
//! 
//! ## 使用场景
//! 
//! 1. **轻量级应用**: 不需要完整运行时功能的应用
//! 2. **嵌入式系统**: 资源受限的环境
//! 3. **命令行工具**: 简单的异步 CLI 应用
//! 4. **测试环境**: 快速测试异步代码
//! 5. **微服务**: 轻量级的微服务应用
//! 
//! ## 与其他运行时的比较
//! 
//! | 特性 | Smol | Tokio | Async-std |
//! |------|------|-------|-----------|
//! | 启动时间 | 快 | 中等 | 慢 |
//! | 内存占用 | 低 | 中等 | 高 |
//! | 功能丰富度 | 基础 | 丰富 | 丰富 |
//! | 学习曲线 | 简单 | 复杂 | 中等 |
//! | 生态系统 | 小 | 大 | 中等 |
//! 
//! ## 基本用法
//! 
//! ### 创建运行时
//! ```rust
//! use smol::Task;
//! 
//! fn main() {
//!     smol::run(async {
//!         // 异步代码
//!     });
//! }
//! ```
//! 
//! ### 生成任务
//! ```rust
//! let task = smol::spawn(async {
//!     // 异步任务
//! });
//! task.await;
//! ```
//! 
//! ## 注意事项
//! 
//! - Smol 功能相对简单，不适合复杂的异步应用
//! - 对于需要丰富功能的项目，建议使用 Tokio
//! - 适合学习和原型开发
//! 
//! ## 示例
//! 
//! ```rust
//! use c06_async::smol::*;
//! 
//! fn main() {
//!     smol::run(async {
//!         demo_basic_usage().await;
//!     });
//! }
//! ```

/// 演示 Smol 的基本用法
/// 
/// 这个函数展示了 Smol 运行时的一些基本特性：
/// - 轻量级的任务创建
/// - 简单的异步执行
/// - 基本的并发处理
/// 
/// # 示例
/// ```rust
/// use c06_async::smol::demo_basic_usage;
/// 
/// fn main() {
///     smol::run(async {
///         demo_basic_usage().await;
///     });
/// }
/// ```
pub async fn demo_basic_usage() {
    use smol::Task;
    use std::time::Duration;

    println!("Smol 轻量级异步运行时演示");

    // 创建多个并发任务
    let tasks: Vec<Task<i32>> = (0..5)
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
/// 
/// 这个函数展示了如何使用 Smol 进行异步 I/O 操作。
/// 包括计时器、网络请求等常见的异步操作。
/// 
/// # 示例
/// ```rust
/// use c06_async::smol::demo_io_operations;
/// 
/// fn main() {
///     smol::run(async {
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
