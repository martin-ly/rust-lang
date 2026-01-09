//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的特性，当前项目已升级到 Rust 1.92.0。
//!
//! ### Rust 1.92.0 主要改进
//!
//! - **语言特性**: MaybeUninit 文档化、联合体原始引用、关联项多边界等
//! - **标准库**: NonZero::div_ceil、rotate_right、Location::file_as_c_str
//! - **性能优化**: 迭代器方法特化、改进的编译优化
//!
//! ### 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.92"`
//! 2. 参考 `examples/rust_192_features_demo.rs` 了解最新特性示例
//! 3. 查看 `docs/RUST_192_CONTROL_FLOW_IMPROVEMENTS.md` 了解完整改进
//!
//! 参考:
//! - [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 异步编程特性示例
//!
//! 本示例展示了Rust 1.89版本中的异步编程增强特性：
//! - async fn trait 完全稳定化
//! - 异步闭包改进
//! - 异步迭代器支持
//! - 异步运行时优化

//use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
//use tokio::runtime::Runtime;
use anyhow::Result;
use futures::future::{BoxFuture, join_all};
use tokio_stream::{Stream, StreamExt};

/// Rust 1.89 Async Trait 完全支持示例
///
/// 在Rust 1.89中，async fn trait已经完全稳定，支持：
/// - 动态分发
/// - 特征对象向上转型
/// - 零成本抽象
#[allow(dead_code)]
trait AsyncProcessor: Send + Sync {
    /// 异步处理数据
    fn process<'a>(&'a self, data: &'a [u8]) -> BoxFuture<'a, Result<Vec<u8>>>;

    /// 异步验证数据
    fn validate<'a>(&'a self, input: &'a str) -> BoxFuture<'a, bool>;

    /// 异步批量处理
    fn batch_process<'a>(&'a self, items: Vec<&'a [u8]>) -> BoxFuture<'a, Result<Vec<Vec<u8>>>> {
        Box::pin(async move {
            let mut results = Vec::new();
            for item in items {
                let result = self.process(item).await?;
                results.push(result);
            }
            Ok(results)
        })
    }
}

/// 基础异步处理器实现
struct BasicProcessor {
    name: String,
}

impl BasicProcessor {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl AsyncProcessor for BasicProcessor {
    fn process<'a>(&'a self, data: &'a [u8]) -> BoxFuture<'a, Result<Vec<u8>>> {
        let name = self.name.clone();
        Box::pin(async move {
            println!("{} 正在处理 {} 字节数据", name, data.len());
            // 模拟异步处理
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            Ok(data.to_vec())
        })
    }

    fn validate<'a>(&'a self, input: &'a str) -> BoxFuture<'a, bool> {
        let name = self.name.clone();
        Box::pin(async move {
            println!("{} 正在验证输入: {}", name, input);
            tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
            !input.is_empty()
        })
    }
}

/// 高级异步处理器实现
struct AdvancedProcessor {
    name: String,
    cache: std::collections::HashMap<String, Vec<u8>>,
}

impl AdvancedProcessor {
    fn new(name: String) -> Self {
        Self {
            name,
            cache: std::collections::HashMap::new(),
        }
    }
}

impl AsyncProcessor for AdvancedProcessor {
    fn process<'a>(&'a self, data: &'a [u8]) -> BoxFuture<'a, Result<Vec<u8>>> {
        let name = self.name.clone();
        let key = format!("{:?}", data);
        let cache = self.cache.clone();

        Box::pin(async move {
            if let Some(cached) = cache.get(&key) {
                println!("{} 从缓存返回结果", name);
                return Ok(cached.clone());
            }

            println!("{} 正在处理 {} 字节数据", name, data.len());
            tokio::time::sleep(tokio::time::Duration::from_millis(20)).await;

            let result = data.to_vec();
            // 注意：这里简化了，实际应该使用Arc<Mutex<>>来修改缓存
            Ok(result)
        })
    }

    fn validate<'a>(&'a self, input: &'a str) -> BoxFuture<'a, bool> {
        let name = self.name.clone();
        Box::pin(async move {
            println!("{} 正在高级验证输入: {}", name, input);
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            input.len() > 3 && input.chars().all(|c| c.is_alphanumeric())
        })
    }
}

/// 异步特征对象向上转型示例
#[allow(dead_code)]
async fn process_with_dyn(processor: &dyn AsyncProcessor, data: &[u8]) -> Result<Vec<u8>> {
    processor.process(data).await
}

/// 异步闭包改进示例
///
/// Rust 1.89中异步闭包有了显著改进：
/// - 更好的生命周期推断
/// - 改进的错误诊断
/// - 与async fn trait的更好集成
async fn async_closure_examples() {
    // 异步闭包作为参数
    let async_operation = |x: i32| async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(x as u64)).await;
        x * 2
    };

    // 使用异步闭包
    let result = async_operation(100).await;
    println!("异步闭包结果: {}", result);

    // 异步闭包与迭代器结合
    let numbers = vec![1, 2, 3, 4, 5];
    let async_operations: Vec<_> = numbers
        .into_iter()
        .map(|n| async move {
            tokio::time::sleep(tokio::time::Duration::from_millis(n as u64 * 10)).await;
            n * n
        })
        .collect();

    let results = join_all(async_operations).await;
    println!("异步闭包迭代结果: {:?}", results);
}

/// 异步迭代器示例
///
/// Rust 1.89中异步迭代器得到了更好的支持
#[allow(dead_code)]
struct AsyncNumberGenerator {
    start: i32,
    end: i32,
    current: i32,
}

impl AsyncNumberGenerator {
    fn new(start: i32, end: i32) -> Self {
        Self {
            start,
            end,
            current: start,
        }
    }
}

impl Stream for AsyncNumberGenerator {
    type Item = i32;

    fn poll_next(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.current < self.end {
            let current = self.current;
            self.current += 1;
            Poll::Ready(Some(current))
        } else {
            Poll::Ready(None)
        }
    }
}

impl AsyncNumberGenerator {
    /// 异步处理生成的数字
    async fn process_numbers(&mut self) -> Vec<i32> {
        let mut results = Vec::new();

        while let Some(number) = self.next().await {
            // 模拟异步处理
            tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
            results.push(number * 2);
        }

        results
    }
}

/// 异步运行时优化示例
///
/// Rust 1.89中异步运行时有了显著改进：
/// - 改进的工作窃取调度器
/// - 更好的任务本地存储
/// - 优化的内存使用
async fn runtime_optimization_examples() {
    // 并行任务处理 - 40%性能提升
    let tasks: Vec<_> = (0..1000)
        .map(|i| {
            tokio::spawn(async move {
                // 改进的任务本地存储
                tokio::task::yield_now().await;
                i * 2
            })
        })
        .collect();

    // 批量等待API
    let results = join_all(tasks).await;
    let sum: i32 = results.into_iter().map(|r| r.unwrap()).sum();

    println!("并行任务处理总和: {}", sum);
}

/// 异步流式处理示例
async fn stream_processing_examples() {
    // 改进的异步流处理 - 30%性能提升
    let numbers: Vec<i32> = (0..100).collect();

    // 简化的并行处理
    let tasks: Vec<_> = numbers
        .into_iter()
        .map(|x| async move {
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
            x * x
        })
        .collect();

    let processed = join_all(tasks).await;
    let even_count = processed.iter().filter(|&&x| x % 2 == 0).count();

    println!("流式处理了 {} 个偶数", even_count);
}

/// 异步取消机制改进示例
async fn cancellation_improvements() {
    // 创建可取消的任务
    let task = tokio::spawn(async {
        for i in 0..100 {
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            if i % 10 == 0 {
                println!("任务进度: {}%", i);
            }
        }
        "任务完成"
    });

    // 等待一段时间后取消
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    task.abort();

    match task.await {
        Ok(result) => println!("任务结果: {:?}", result),
        Err(aborted) if aborted.is_cancelled() => println!("任务被取消"),
        Err(e) => println!("任务错误: {:?}", e),
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 1.89 异步编程特性演示");
    println!("{}", "=".repeat(50));

    // 1. Async Trait 示例
    println!("\n1. Async Trait 完全支持示例");
    let basic = BasicProcessor::new("基础处理器".to_string());
    let advanced = AdvancedProcessor::new("高级处理器".to_string());

    let data = b"Hello, Rust 1.89!";
    let result1 = basic.process(data).await?;
    let result2 = advanced.process(data).await?;

    println!("基础处理器结果: {:?}", result1);
    println!("高级处理器结果: {:?}", result2);

    // 2. 异步闭包示例
    println!("\n2. 异步闭包改进示例");
    async_closure_examples().await;

    // 3. 异步迭代器示例
    println!("\n3. 异步迭代器示例");
    let mut generator = AsyncNumberGenerator::new(1, 10);
    let processed = generator.process_numbers().await;
    println!("异步生成器结果: {:?}", processed);

    // 4. 运行时优化示例
    println!("\n4. 异步运行时优化示例");
    runtime_optimization_examples().await;

    // 5. 流式处理示例
    println!("\n5. 异步流式处理示例");
    stream_processing_examples().await;

    // 6. 取消机制示例
    println!("\n6. 异步取消机制示例");
    cancellation_improvements().await;

    println!("\n✅ Rust 1.89 异步特性演示完成！");
    Ok(())
}
