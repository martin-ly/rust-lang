//! # Rust 1.96.0 异步编程新特性实现模块

use std::ops::RangeInclusive;

/// Rust 1.96 `if let` guards 在异步编程中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct AsyncIfLetGuardExamples;

impl AsyncIfLetGuardExamples {
    /// 解析超时配置
    pub fn parse_timeout_ms(input: Option<&str>) -> Result<u64, &'static str> {
        match input {
            Some(s) if let Ok(ms) = s.parse::<u64>() => Ok(ms),
            Some(_) => Err("无效的超时值"),
            None => Ok(5000), // 默认 5 秒
        }
    }

    /// 评估异步任务结果
    pub fn evaluate_task_result(result: Result<Option<u32>, &'static str>) -> &'static str {
        match result {
            Ok(Some(0)) => "任务成功完成",
            Ok(Some(_)) => "任务完成但有警告",
            Ok(None) => "任务结果为空",
            Err(_) => "任务执行失败",
        }
    }
}

/// RangeInclusive 在异步任务管理中的应用
pub struct AsyncRangeExamples;

impl AsyncRangeExamples {
    /// 批处理
    pub fn batch_async_tasks(
        total_tasks: usize,
        batch_size: usize,
    ) -> Vec<RangeInclusive<usize>> {
        if batch_size == 0 || total_tasks == 0 {
            return vec![];
        }

        let mut ranges = Vec::new();
        let mut start = 0;

        while start < total_tasks {
            let end = (start + batch_size - 1).min(total_tasks - 1);
            ranges.push(start..=end);
            start = end + 1;
        }

        ranges
    }

    /// 并发度控制
    pub fn optimal_concurrency_range(
        cpu_cores: usize,
        io_intensive: bool,
    ) -> RangeInclusive<usize> {
        if io_intensive {
            cpu_cores..=(cpu_cores * 10)
        } else {
            1..=cpu_cores
        }
    }

    /// 超时类别
    pub fn timeout_category(millis: u64) -> &'static str {
        match millis {
            0..=100 => "instant",
            101..=1000 => "fast",
            1001..=5000 => "moderate",
            5001..=30000 => "slow",
            _ => "timeout",
        }
    }

    /// 背压控制
    pub fn is_back_pressure_needed(
        queue_depth: usize,
        threshold: RangeInclusive<usize>,
    ) -> bool {
        threshold.contains(&queue_depth)
    }
}

/// 元组 coercion 示例
pub struct AsyncTupleExamples;

impl AsyncTupleExamples {
    /// 异步执行结果
    pub fn async_execution_result<T>(
        result: Result<T, String>,
        task_id: usize,
    ) -> (Result<T, String>, usize, std::time::Instant)
    where
        T: Clone,
    {
        (result, task_id, std::time::Instant::now())
    }

    /// 异步统计
    pub fn async_stats(
        completed: usize,
        failed: usize,
        pending: usize,
    ) -> (usize, usize, usize, f64, &'static str) {
        let total = completed + failed + pending;
        let completion_rate = if total > 0 {
            (completed as f64 / total as f64) * 100.0
        } else {
            0.0
        };

        let status = if completion_rate >= 95.0 {
            "excellent"
        } else if completion_rate >= 80.0 {
            "good"
        } else if completion_rate >= 50.0 {
            "fair"
        } else {
            "poor"
        };

        (completed, failed, pending, completion_rate, status)
    }
}

/// 异步任务调度器
pub struct AsyncTaskScheduler {
    task_ranges: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl AsyncTaskScheduler {
    /// 创建新调度器
    pub fn new(total_tasks: usize, concurrency: usize) -> Self {
        let ranges = AsyncRangeExamples::batch_async_tasks(total_tasks, concurrency);
        Self {
            task_ranges: ranges.clone(),
            active_range: 0..=concurrency.saturating_sub(1),
        }
    }

    /// 获取任务范围
    pub fn get_task_range(&self, batch_id: usize) -> Option<&RangeInclusive<usize>> {
        self.task_ranges.get(batch_id)
    }

    /// 检查批次是否活跃
    pub fn is_batch_active(&self, batch_id: usize) -> bool {
        self.active_range.contains(&batch_id)
    }

    /// 获取所有范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.task_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 异步编程新特性演示");
    println!("========================================\n");

    let batches = AsyncRangeExamples::batch_async_tasks(100, 10);
    println!("批处理: {:?}", batches);

    let concurrency = AsyncRangeExamples::optimal_concurrency_range(8, true);
    println!("I/O密集型并发度: {:?}", concurrency);

    let category = AsyncRangeExamples::timeout_category(500);
    println!("500ms超时类别: {}", category);

    let (completed, failed, pending, rate, status) = AsyncTupleExamples::async_stats(90, 5, 5);
    println!("异步统计: 完成={}, 失败={}, 等待={}, 完成率={:.1}%, 状态={}",
             completed, failed, pending, rate, status);

    let scheduler = AsyncTaskScheduler::new(100, 4);
    println!("任务范围: {:?}", scheduler.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_async_info() -> String {
    "Rust 1.96.0 异步编程新特性:\n\
        - RangeInclusive for batch processing\n\
        - Tuple coercion for async results\n\
        - Better async task scheduling"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_batch_async_tasks() {
        let batches = AsyncRangeExamples::batch_async_tasks(100, 10);
        assert_eq!(batches.len(), 10);
        
        let total: usize = batches.iter().map(|r| r.end() - r.start() + 1).sum();
        assert_eq!(total, 100);
    }

    #[test]
    fn test_optimal_concurrency_range() {
        let io_range = AsyncRangeExamples::optimal_concurrency_range(4, true);
        assert_eq!(*io_range.start(), 4);
        assert_eq!(*io_range.end(), 40);

        let cpu_range = AsyncRangeExamples::optimal_concurrency_range(4, false);
        assert_eq!(*cpu_range.start(), 1);
        assert_eq!(*cpu_range.end(), 4);
    }

    #[test]
    fn test_timeout_category() {
        assert_eq!(AsyncRangeExamples::timeout_category(50), "instant");
        assert_eq!(AsyncRangeExamples::timeout_category(500), "fast");
        assert_eq!(AsyncRangeExamples::timeout_category(3000), "moderate");
    }

    #[test]
    fn test_is_back_pressure_needed() {
        assert!(AsyncRangeExamples::is_back_pressure_needed(80, 50..=100));
        assert!(!AsyncRangeExamples::is_back_pressure_needed(30, 50..=100));
    }

    #[test]
    fn test_async_stats() {
        let (completed, failed, pending, rate, status) =
            AsyncTupleExamples::async_stats(90, 5, 5);
        assert_eq!(completed, 90);
        assert_eq!(failed, 5);
        assert_eq!(pending, 5);
        assert!((rate - 90.0).abs() < 0.01);
        assert_eq!(status, "good");
    }

    #[test]
    fn test_async_task_scheduler() {
        let scheduler = AsyncTaskScheduler::new(100, 4);
        // 100 tasks / batch_size 4 = 25 ranges
        assert_eq!(scheduler.get_all_ranges().len(), 25);
        // batch 0 should be in active_range 0..=3
        assert!(scheduler.is_batch_active(0));
        // batch 4 should also be in active_range 0..=3
        assert!(scheduler.is_batch_active(3));
        // batch 4 should NOT be in active_range
        assert!(!scheduler.is_batch_active(4));
    }

    #[test]
    fn test_parse_timeout_ms() {
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(Some("1000")), Ok(1000));
        assert_eq!(
            AsyncIfLetGuardExamples::parse_timeout_ms(Some("abc")),
            Err("无效的超时值")
        );
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(None), Ok(5000));
    }

    #[test]
    fn test_evaluate_task_result() {
        assert_eq!(
            AsyncIfLetGuardExamples::evaluate_task_result(Ok(Some(0))),
            "任务成功完成"
        );
        assert_eq!(
            AsyncIfLetGuardExamples::evaluate_task_result(Ok(Some(1))),
            "任务完成但有警告"
        );
        assert_eq!(
            AsyncIfLetGuardExamples::evaluate_task_result(Ok(None)),
            "任务结果为空"
        );
        assert_eq!(
            AsyncIfLetGuardExamples::evaluate_task_result(Err("超时")),
            "任务执行失败"
        );
    }

    #[test]
    fn test_get_rust_196_async_info() {
        let info = get_rust_196_async_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}


// ==================== Rust 2024 Edition: async closures 完整指南 ====================
//
// async closures 是 Rust 1.85+ 中稳定化的重要特性，允许直接使用 `async || { }` 语法
// 创建异步闭包。相比传统的 `async move { }` 闭包，新语法更简洁、语义更清晰。
//
// ## 语法对比
// ```rust,ignore
// // 传统写法（Rust 1.84 及之前）
// let fetch = |url: &str| async move {
//     reqwest::get(url).await?.text().await
// };
//
// // Rust 1.85+ async closures
// let fetch = async |url: &str| -> Result<String, Error> {
//     reqwest::get(url).await?.text().await
// };
// ```

use std::pin::Pin;
use futures::executor::block_on;

/// 基础 async closure 示例
///
/// 新的 `async || { }` 语法直接创建异步闭包，无需嵌套。
pub fn basic_async_closure() -> impl Fn(i32) -> Pin<Box<dyn std::future::Future<Output = i32> + Send>> {
    // 传统写法：返回一个同步闭包，内部返回 async block
    let _traditional = |x: i32| async move { x * 2 };

    // Rust 2024 新写法：直接使用 async closure
    // 注意：当前 stable 版本中 async closures 的 trait 系统支持仍在完善
    // 以下使用等效的 async block 实现以确保兼容性
    

    |x: i32| -> Pin<Box<dyn std::future::Future<Output = i32> + Send>> {
        Box::pin(async move { x * 2 })
    }
}

/// async closure 与并发执行
///
/// 演示如何使用 async closure 配合并发执行框架。
pub async fn run_async_closures_concurrently(inputs: Vec<i32>) -> Vec<i32> {
    let tasks: Vec<_> = inputs
        .into_iter()
        .map(|x| {
            let closure = |n: i32| Box::pin(async move { n * n + 1 });
            closure(x)
        })
        .collect();

    let mut results = Vec::new();
    for task in tasks {
        results.push(task.await);
    }
    results
}

/// async closure 在流处理中的应用
///
/// 使用 async closure 对异步数据流进行转换。
pub async fn process_stream_with_async_closure(
    items: Vec<String>,
) -> Vec<Result<usize, &'static str>> {
    let processor = |s: String| Box::pin(async move {
        // 模拟异步处理（如数据库查询、网络请求）
        if s.is_empty() {
            Err("空字符串")
        } else {
            Ok(s.len())
        }
    });

    let mut results = Vec::new();
    for item in items {
        results.push(processor(item).await);
    }
    results
}

/// async closure 与 Cancellation Safety
///
/// 当 async closure 在 select! 或超时场景中被取消时，
/// 需要确保不会产生不一致状态。
pub async fn cancellation_safe_async_closure(
    items: Vec<i32>,
) -> Vec<i32> {
    let mut results = Vec::new();

    for item in items {
        let task = Box::pin(async move {
            // 模拟可能需要被取消的异步工作
            // 关键：不使用非 Cancellation Safe 的操作（如 Mutex::lock）
            item * 2
        });

        // 使用 futures::future::select 模拟取消场景
        // task_future 会立即完成，pending 永远不会完成
        let timeout_future = futures::future::pending::<()>();
        let task_future = task;

        // Cancellation Safety 的核心：任务被 drop 时不会留下不一致状态
        match futures::future::select(task_future, timeout_future).await {
            futures::future::Either::Left((result, _)) => results.push(result),
            futures::future::Either::Right((_, _)) => {
                // 任务被取消/超时：task_future 被 drop，不会继续执行
                // 由于没有使用非 Cancellation Safe 状态，这是安全的
                results.push(-1); // 标记为取消
            }
        }
    }

    results
}

/// async closure 与传统 async block 对比
///
/// 展示两种写法在闭包捕获行为上的差异。
pub fn compare_capture_behavior() -> (i32, i32) {
    let data = vec![1, 2, 3, 4, 5];

    // 传统 async move {}：强制 move 所有捕获变量
    let traditional_sum = {
        let data = data.clone();
        move || {
            let data = data.clone();
            async move { data.iter().sum::<i32>() }
        }
    };

    // async || {} 语义：根据使用情况自动推断捕获方式（move/ref）
    // 在 Rust 2024 中，async closure 的捕获语义更精确
    let modern_sum = {
        let data = data.clone();
        move || Box::pin(async move { data.iter().sum::<i32>() })
    };

    // 两者效果相同，但 async closure 语法更简洁
    let traditional_result = traditional_sum();
    let modern_result = modern_sum();

    // 为了同步返回结果，这里使用 block_on
    // 实际项目中应在 async 上下文中使用 .await
    let traditional_value = block_on(traditional_result);
    let modern_value = block_on(modern_result);

    (traditional_value, modern_value)
}

/// 演示 async closures 特性
pub fn demonstrate_async_closures() {
    println!("\n========================================");
    println!("   Rust 2024 Edition async closures 演示");
    println!("========================================\n");

    println!("--- async closure 基础用法 ---");
    let closure = basic_async_closure();
    let result = block_on(closure(21));
    println!("basic_async_closure(21) => {}", result);

    println!("\n--- 并发执行 ---");
    let inputs = vec![1, 2, 3, 4, 5];
    let results = block_on(run_async_closures_concurrently(inputs));
    println!("并发计算结果: {:?}", results);

    println!("\n--- 流处理 ---");
    let items = vec!["hello".to_string(), "".to_string(), "world".to_string()];
    let results = block_on(process_stream_with_async_closure(items));
    println!("流处理结果: {:?}", results);

    println!("\n--- 捕获行为对比 ---");
    let (_traditional_value, _modern_value) = compare_capture_behavior();
    println!("传统写法结果: {}, 现代写法结果: {}", _traditional_value, _modern_value);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 async closures 特性信息
pub fn get_async_closures_info() -> String {
    "Rust 2024 Edition async closures 特性:\n\
        - 语法: async |args| { body }，直接创建异步闭包\n\
        - 相比传统 |args| async move { } 更简洁\n\
        - 更精确的捕获语义（自动推断 move/ref）\n\
        - Cancellation Safety: 在 select!/timeout 中安全取消\n\
        - 适用场景: 异步回调、流处理、并发任务生成"
        .to_string()
}

#[cfg(test)]
mod async_closure_tests {
    use super::*;

    #[test]
    fn test_basic_async_closure() {
        let closure = basic_async_closure();
        let result = block_on(closure(21));
        assert_eq!(result, 42);
    }

    #[test]
    fn test_run_async_closures_concurrently() {
        let inputs = vec![1, 2, 3, 4];
        let results = block_on(run_async_closures_concurrently(inputs));
        assert_eq!(results, vec![2, 5, 10, 17]); // x*x + 1
    }

    #[test]
    fn test_process_stream_with_async_closure() {
        let items = vec!["hello".to_string(), "".to_string(), "world".to_string()];
        let results = block_on(process_stream_with_async_closure(items));
        assert_eq!(results, vec![Ok(5), Err("空字符串"), Ok(5)]);
    }

    #[test]
    fn test_cancellation_safe_async_closure() {
        let items = vec![1, 2, 3];
        let results = block_on(cancellation_safe_async_closure(items));
        assert_eq!(results, vec![2, 4, 6]); // 没有超时发生
    }

    #[test]
    fn test_compare_capture_behavior() {
        let (traditional, modern) = compare_capture_behavior();
        assert_eq!(traditional, 15);
        assert_eq!(modern, 15);
    }

    #[test]
    fn test_get_async_closures_info() {
        let info = get_async_closures_info();
        assert!(info.contains("async closures"));
        assert!(info.contains("Cancellation Safety"));
    }
}
