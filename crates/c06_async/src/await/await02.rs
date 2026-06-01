//! 异步并发编程高级示例
//!
//! 本模块展示了如何使用 `futures::join!` 宏来实现并发执行多个异步操作。
//! This module demonstrates use `futures::join!` implementationconcurrentexecutionmultipleasyncoperation
//! 这是异步编程中的一个重要模式，可以显著提高程序的性能。
//! async in important ，can significant program performance 。
//!
//! ## 核心概念
//! ## Core Concepts
//!
//! ### futures::join! 宏
//! - **role **: etc. Future
//! - **并发性**: 所有 Future 会并发执行，而不是顺序执行
//! - **concurrency **: all Future concurrency ，while order
//! - **等待策略**: 等待所有 Future 都完成后才返回
//! - **etc. strategy **: etc. all Future after
//! - **错误处理**: 如果任何一个 Future 失败，join! 会返回错误
//! - **errorhandling**: Future join! error
//!
//! ### 并发 vs 并行
//! ### concurrency vs parallelism
//! - **并发**: 多个任务可以同时进行，但在单线程中交替执行
//! - **concurrency **: task can ，but in thread in alternation
//! - **并行**: 多个任务同时在多个 CPU 核心上执行
//! - **parallelism **: task in CPU core on
//! - **异步并发**: 在等待 I/O 时执行其他任务，提高资源利用率
//! - **async concurrency **: in etc. I/O its task ，
//!
//! ## 使用场景
//! ## Usage Scenarios
//!
//! 1. **网络请求**: 同时发起多个 HTTP 请求
//! 1. **network **: HTTP
//! 2. **数据库查询**: 并发执行多个数据库操作
//! 3. **文件操作**: 同时读取多个文件
//! 3. **file operation **:
//! 4. **API 调用**: 调用多个外部服务
//! 4. **API **: multipleexternal service
//!
//! ## 使用示例
//! ## Usage Examples
//!
//! ```no_run
//! use c06_async::r#await::process;
//!
//! #[tokio::main]
//! async fn main() {
//!     process().await;
//! }
//! ```
use reqwest::{Client, Error};

/// 异步获取数据的辅助函数
///
/// 这个函数封装了 HTTP GET 请求的异步操作，展示了如何将同步的网络操作
/// function HTTP GET asyncoperationdemonstratesynchronous operation
/// 转换为异步操作。
/// conversion as async 。
///
/// # 参数
/// # Parameters
/// - `url`: 要请求的 URL 地址
/// - `url`: URL
/// - `client`: HTTP 客户端实例，包含超时等配置
/// - `client`: HTTP contain configuration
///
/// # 返回值
/// # Return Value
/// - `Ok(String)`: 成功获取的响应体内容
/// - `Ok(String)`: volume inside
/// - `Err(Error)`: 请求失败时的错误信息
/// - `Err(Error)`: error information
///
/// # 异步流程
/// # async flow
/// 1. 发起 HTTP GET 请求（异步）
/// 1. HTTP GET （async ）
/// 2. 等待响应返回（异步）
/// 2. etc. （async ）
/// 3. 将响应体转换为字符串（异步）
/// 3. will volume conversion as （async ）
/// 4. 返回结果
/// 4. result
async fn fetch_data(url: &str, client: &Client) -> Result<String, Error> {
    // 第一步：异步发送 HTTP 请求
    // send() 方法返回一个 Future，await 等待请求完成
    let response = client.get(url).send().await?;

    // 第二步：异步读取响应体
    // text() 方法返回一个 Future，await 等待内容读取完成
    let body = response.text().await?;

    // 返回获取到的内容
    Ok(body)
}

/// 演示异步并发编程的主要函数
///
/// 这个函数展示了如何使用 `futures::join!` 宏来并发执行多个异步操作。
/// function `futures::join!` concurrency async 。
/// 相比顺序执行，并发执行可以显著减少总的执行时间。
/// order ，concurrency can significant time 。
///
/// # 并发策略
/// # concurrent strategy
/// 1. **不同超时**: 为不同的请求设置不同的超时时间
/// 2. **并发执行**: 使用 `join!` 同时等待多个 Future
/// 2. **concurrency **: `join!` etc. Future
/// 3. **错误处理**: 处理部分成功、全部失败等不同情况
/// 3. **error handling **: part 、all etc. situation
///
/// # 性能优势
/// # performance strength
/// - 如果顺序执行，总时间 = 请求1时间 + 请求2时间
/// - sequentialexecutiontime = 1time + 2 time
/// - 如果并发执行，总时间 ≈ max(请求1时间, 请求2时间)
/// - if concurrency ，time ≈ max(1time, 2time )
/// - 在网络 I/O 密集的场景中，性能提升非常显著
/// - in network I/O scenario in ，performance significant
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::r#await::process;
///
/// #[tokio::main]
/// async fn main() {
///     process().await;
/// }
/// ```
pub async fn process() {
    // 创建带有不同超时设置的 HTTP 客户端
    // 客户端1：1秒超时，适合快速响应的服务
    let client = Client::builder()
        .timeout(std::time::Duration::from_secs(1))
        .build()
        .expect("发送 HTTP 请求不应失败");

    // 客户端2：2秒超时，适合响应较慢的服务
    let client2 = Client::builder()
        .timeout(std::time::Duration::from_secs(2))
        .build()
        .expect("发送 HTTP 请求不应失败");

    println!("开始并发获取数据...");

    // 使用 futures::join! 宏并发执行多个异步操作
    // 这两个请求会同时发起，而不是等待第一个完成后再发起第二个
    let results = futures::join!(
        fetch_data("https://example.com/api/1", &client),
        fetch_data("https://example.com/api/2", &client2)
    );

    println!("所有请求完成，处理结果...");

    // 处理并发操作的结果
    // join! 返回一个元组，包含所有 Future 的结果
    match results {
        (Ok(data1), Ok(data2)) => {
            // 两个请求都成功
            println!(
                "✅ 成功获取两个数据源: {} 字节和 {} 字节",
                data1.len(),
                data2.len()
            );
            println!("数据源1长度: {}", data1.len());
            println!("数据源2长度: {}", data2.len());
        }
        (Err(e1), Err(e2)) => {
            // 两个请求都失败
            println!("❌ 两个请求都失败:");
            println!("  请求1错误: {:?}", e1);
            println!("  请求2错误: {:?}", e2);
        }
        (Err(e1), Ok(data2)) => {
            // 第一个请求失败，第二个成功
            println!("⚠️  部分成功:");
            println!("  请求1失败: {:?}", e1);
            println!("  请求2成功，数据长度: {} 字节", data2.len());
        }
        (Ok(data1), Err(e2)) => {
            // 第一个请求成功，第二个失败
            println!("⚠️  部分成功:");
            println!("  请求1成功，数据长度: {} 字节", data1.len());
            println!("  请求2失败: {:?}", e2);
        }
    }

    println!("数据处理完成");
}
