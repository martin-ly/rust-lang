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
            Ok(Some(code)) if code == 0 => "任务成功完成",
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
