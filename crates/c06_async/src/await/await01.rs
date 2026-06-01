//! async 和 await 关键字详解
//! async and await key
//!
//! 在 Rust 中，`async` 和 `await` 是用于处理异步编程的核心关键字。
//! in Rust in ，`async` and `await` async core key 。
//! 它们允许你编写非阻塞的代码，使得程序在等待某些操作（如 I/O 操作）完成时
//! ，program in etc. （ I/O ）
//! 可以继续执行其他任务，从而显著提高程序的并发性能。
//! can its task ，thereby significant program concurrency performance 。
//!
//! ## 核心概念
//! ## core concept
//!
//! ### async 关键字
//! ### async key
//! - **作用**: 用于定义一个异步函数或异步块
//! - **role **: definition async function or async
//! - **返回值**: 异步函数返回一个实现了 `Future` trait 的值
//! - **return value **: async function `Future` trait
//! - **语义**: 这个值代表一个可能在将来完成的计算
//! - ****: may in future
//!
//! ### await 关键字
//! ### await key
//! - **作用**: 用于等待一个 `Future` 完成
//! - **role **: etc. `Future`
//! - **行为**: 使用 `await` 时，当前的异步任务会被挂起
//! - **as **: `await` ，when before async task is
//! - **恢复**: 直到所等待的 `Future` 完成时，任务才会恢复执行
//! - ****: to etc. `Future` ，task
//!
//! ## 异步编程的优势
//! ## async strength
//!
//! 1. **非阻塞**: 不会阻塞当前线程，允许其他任务执行
//! 1. ****: when before thread ，its task
//! 2. **高效**: 在等待 I/O 时可以进行其他计算
//! 2. **efficient **: in etc. I/O can its
//! 3. **可扩展**: 可以处理大量并发连接
//! 3. ****: can concurrency
//! 4. **资源节约**: 相比传统线程模型，内存和 CPU 开销更小
//! 4. ****: thread ，memory and CPU overhead
//!
//! ## 使用示例
//! ## example
//!
//! ```no_run
//! use c06_async::r#await::async_text01;
//!
//! #[tokio::main]
//! async fn main() {
//!     let result = async_text01().await;
//!     println!("异步任务返回: {}", result);
//! }
//! ```
use std::time::Duration;
use tokio::time::sleep;

/// 演示基本的异步函数用法
/// demonstration this async function
///
/// 这个函数展示了如何使用 `async` 和 `await` 关键字来编写异步代码。
/// function `async` and `await` key async 。
/// 它模拟了一个需要等待的异步操作，然后返回结果。
/// etc. async ，then result 。
///
/// # 异步流程说明
/// # async process explain
/// 1. 函数开始执行，打印开始消息
/// 1. function ，
/// 2. 遇到 `await` 关键字，当前任务被挂起
/// 2. to `await` key ，when before task is
/// 3. 运行时调度其他任务执行
/// 3. runtime its task
/// 4. 等待时间到期后，任务恢复执行
/// 4. etc. time to after ，task
/// 5. 打印完成消息并返回结果
/// 5. and result
///
/// # 返回值
/// # return value
/// 返回一个 `i32` 类型的值（42）
/// `i32` type （42）
///
/// # 示例
/// # example
/// ```no_run
/// use c06_async::r#await::async_text01;
///
/// #[tokio::main]
/// async fn main() {
///     println!("主程序开始");
///     println!("program ");
///     let result = async_text01().await;
///     println!("主程序结束，结果: {}", result);
///     println!("program ，result : {}", result);
/// }
/// ```
///
/// # 注意事项
/// #
/// - 异步函数必须在异步运行时环境中调用（如 tokio）
/// - async function must in async runtime environment in （ tokio）
/// - `await` 只能在 `async` 函数或块中使用
/// - `await` in `async` function or in
/// - 异步函数返回的是 `Future`，需要被等待才能获取结果
/// - async function `Future`，is etc. result
#[allow(unused)]
pub async fn async_text01() -> i32 {
    println!("开始异步任务");

    // 使用 await 等待异步操作完成
    // 这里模拟一个需要 1 秒的异步操作（如网络请求、文件读取等）
    // 在等待期间，当前任务会被挂起，其他任务可以执行
    sleep(Duration::from_secs(1)).await;

    println!("异步任务完成");

    // 返回计算结果
    42
}
