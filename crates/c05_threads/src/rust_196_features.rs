//! # Rust 1.96.0 稳定特性演示模块
//! **历史稳定 patch**: Rust 1.96.1（基于 Rust 1.96.0 特性集）
//! # Rust 1.96.0/1.96.1 feature demonstration module
//! # Rust 1.96.0/1.96.1 稳定featuredemonstration module
//! # Rust 1.96.0/1.96.1 stablefeaturedemonstration module
//! - `std::assert_matches!` — 模式匹配断言，用于线程 `Result` 测试
//! - `std::assert_matches!` — ，thread `Result`
//! - `std::assert_matches!` — 模式匹配断言，Used forthread `Result` Test for

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::LazyLock;

// ============================================================================
// 1. core::range::Range — Copy 语义，线程池大小范围可复用
// ============================================================================

/// 线程池范围管理器（使用 Rust 1.96.0 `core::range::Range`）
/// thread pool scope （ Rust 1.96.0 `core::range::Range`）
/// `core::range::Range` 实现 `Copy`，因此可以安全地在线程间复制范围值，
/// `core::range::Range` `Copy`，therefore can in thread scope ，
/// 而不需要引用或 `Arc`。
/// while reference or `Arc`。
pub struct ThreadPoolRangeManager {
    worker_ranges: Vec<core::range::Range<usize>>,
    /// 当前活跃的工作线程索引范围
    /// when before worker thread scope
    active_range: core::range::Range<usize>,
}

impl ThreadPoolRangeManager {
    pub fn new(total_tasks: usize, worker_count: usize) -> Self {
        if worker_count == 0 || total_tasks == 0 {
            return Self {
                worker_ranges: vec![],
                active_range: core::range::Range { start: 0, end: 0 },
            };
        }

        let base = total_tasks / worker_count;
        let rem = total_tasks % worker_count;
        let mut ranges = Vec::with_capacity(worker_count);
        let mut start = 0usize;

        for i in 0..worker_count {
            let chunk = base + if i < rem { 1 } else { 0 };
            let end = start + chunk;
            ranges.push(core::range::Range { start, end });
            start = end;
        }

        Self {
            worker_ranges: ranges,
            active_range: core::range::Range {
                start: 0,
                end: worker_count,
            },
        }
    }

    /// Get指定worker threadtaskrange（`Copy`，直接return value）
    pub fn get_worker_range(&self, worker_id: usize) -> Option<core::range::Range<usize>> {
        self.worker_ranges.get(worker_id).copied()
    }

    /// 检查工作线程是否处于活跃范围
    /// Checks工作线程是否处于活跃范围
    /// worker thread scope
    pub fn is_worker_active(&self, worker_id: usize) -> bool {
        // `core::range::Range` 目前没有 `contains`，需手动判断
        worker_id >= self.active_range.start && worker_id < self.active_range.end
    }

    /// 获取所有范围（`Copy` 语义保证可以安全复制）
    /// Gets所有范围（`Copy` 语义保证可以安全复制）
    /// all scope （`Copy` can ）
    pub fn all_ranges(&self) -> &[core::range::Range<usize>] {
        &self.worker_ranges
    }

    /// 计算所有范围覆盖的总任务数（验证无遗漏）
    /// Computes所有范围覆盖的总任务数（验证无遗漏）
    /// all scope task （）
    pub fn total_covered_tasks(&self) -> usize {
        self.worker_ranges.iter().map(|r| r.end - r.start).sum()
    }
}

// ============================================================================
// 2. LazyLock::from(value) — 线程安全的单例/配置（非 const）
// ============================================================================

pub struct ThreadSafeConfig {
    pub max_threads: LazyLock<usize, fn() -> usize>,
    /// 任务队列容量上限
    /// task on
    pub queue_capacity: LazyLock<usize, fn() -> usize>,
}

impl ThreadSafeConfig {
    /// 从运行时确定的值创建配置。
    /// from runtime 。
    pub fn from_values(max_threads: usize, queue_capacity: usize) -> Self {
        Self {
            max_threads: LazyLock::from(max_threads),
            queue_capacity: LazyLock::from(queue_capacity),
        }
    }

    /// 获取当前配置摘要
    /// Gets当前配置摘要
    /// when before summary
    pub fn summary(&self) -> String {
        format!(
            "max_threads={}, queue_capacity={}",
            *self.max_threads, *self.queue_capacity
        )
    }
}

// ============================================================================
// 3. From<T> for AssertUnwindSafe<T> — 线程 panic 捕获
// ============================================================================

pub struct ThreadPanicHandler;

impl ThreadPanicHandler {
    /// 在线程中执行闭包，捕获 panic 并返回 `Result`。
    /// in thread in ， panic and `Result`。
    pub fn run_capturing_panic<F, R>(f: F) -> Result<R, Box<dyn std::any::Any + Send>>
    where
        F: FnOnce() -> R + Send + 'static,
        F: std::panic::UnwindSafe,
    {
        // Rust 1.96: `From<F> for AssertUnwindSafe<F>` 要求 `F: UnwindSafe`
        let wrapped = AssertUnwindSafe::from(f);
        catch_unwind(|| wrapped.0())
    }

    /// 验证：即使闭包 panic，也能被安全捕获。
    /// Validates：即使闭包 panic，也能被安全捕获。
    /// ： panic，is 。
    /// Verify：即使closure panic，也能is安全捕获。
    pub fn demo_panic_capture() -> &'static str {
        let result = Self::run_capturing_panic(|| {
            panic!("模拟线程异常");
        });
        match result {
            Ok(_) => "unexpected_success",
            Err(_) => "panic_captured",
        }
    }
}

// ============================================================================
// 4. assert_matches! — 线程 Result / Option 测试
// ============================================================================

/// 线程任务结果枚举
/// thread task result enum
#[derive(Debug, PartialEq)]
pub enum ThreadTaskResult {
    Success {
        task_id: usize,
        duration_ms: u64,
    },
    Retryable {
        task_id: usize,
        attempt: u8,
    },
    Failed {
        task_id: usize,
        reason: &'static str,
    },
}

/// 使用 `assert_matches!` 验证线程结果模式。
/// `assert_matches!` thread result 。
pub fn verify_thread_results(results: Vec<ThreadTaskResult>) {
    use std::assert_matches;

    for result in &results {
        assert_matches!(
            result,
            ThreadTaskResult::Success { .. }
                | ThreadTaskResult::Retryable { .. }
                | ThreadTaskResult::Failed { .. }
        );
    }
}

// ============================================================================
// 演示函数
// ============================================================================

/// 运行 Rust 1.96 特性演示
/// Run Rust 1.96 feature demonstration
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 线程特性演示");
    println!("========================================\n");

    // core::range::Range 演示
    let manager = ThreadPoolRangeManager::new(100, 4);
    println!("任务分配范围: {:?}", manager.all_ranges());
    println!("覆盖总任务数: {}", manager.total_covered_tasks());

    // LazyLock::from 演示
    let config = ThreadSafeConfig::from_values(8, 1024);
    println!("线程配置: {}", config.summary());

    // AssertUnwindSafe::from 演示
    let status = ThreadPanicHandler::demo_panic_capture();
    println!("Panic 捕获结果: {}", status);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// Gets特性信息
/// feature
pub fn get_rust_196_thread_info() -> String {
    "Rust 1.96.0 线程特性:\n- core::range::Range { start, end } — Copy 语义，可复用的线程池范围\n- \
     LazyLock::from(value) — 从值构造线程安全惰性容器（非 const）\n- From<T> for \
     AssertUnwindSafe<T> — 要求 T: UnwindSafe，安全捕获 panic\n- assert_matches! — 线程 \
     Result/Option 的模式匹配断言"
        .to_string()
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::assert_matches;

    #[test]
    fn test_thread_pool_range_copy_semantics() {
        let manager = ThreadPoolRangeManager::new(100, 4);
        let r0 = manager.get_worker_range(0).unwrap();
        let r0_copy = r0; // `core::range::Range` 是 `Copy`
        assert_eq!(r0.start, r0_copy.start);
        assert_eq!(r0.end, r0_copy.end);
        // 继续使用 r0，证明 Copy 而非 Move
        assert_eq!(r0.end - r0.start, 25);
    }

    #[test]
    fn test_thread_pool_range_distribution() {
        let manager = ThreadPoolRangeManager::new(100, 4);
        assert_eq!(manager.all_ranges().len(), 4);
        assert_eq!(manager.total_covered_tasks(), 100);

        let r0 = manager.get_worker_range(0).unwrap();
        assert_eq!(r0.start, 0);
        assert_eq!(r0.end, 25);
    }

    #[test]
    fn test_thread_pool_active_range() {
        let manager = ThreadPoolRangeManager::new(100, 4);
        assert!(manager.is_worker_active(0));
        assert!(manager.is_worker_active(3));
        assert!(!manager.is_worker_active(4));
    }

    #[test]
    fn test_lazy_lock_from() {
        let config = ThreadSafeConfig::from_values(8, 1024);
        assert_eq!(*config.max_threads, 8);
        assert_eq!(*config.queue_capacity, 1024);
        assert_eq!(config.summary(), "max_threads=8, queue_capacity=1024");
    }

    #[test]
    fn test_assert_unwind_safe_from_unwind_safe_type() {
        // i32 实现 UnwindSafe，转换成功
        let value: i32 = 42;
        let _au: AssertUnwindSafe<i32> = AssertUnwindSafe::from(value);
    }

    #[test]
    fn test_catch_unwind_with_assert_unwind_safe() {
        let result = ThreadPanicHandler::run_capturing_panic(|| {
            42 // 正常返回
        });
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn test_catch_unwind_panic() {
        let result = ThreadPanicHandler::run_capturing_panic(|| {
            panic!("test panic");
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_assert_matches_thread_result() {
        let success = ThreadTaskResult::Success {
            task_id: 1,
            duration_ms: 100,
        };
        assert_matches!(success, ThreadTaskResult::Success { task_id: 1, .. });

        let retry = ThreadTaskResult::Retryable {
            task_id: 2,
            attempt: 3,
        };
        assert_matches!(retry, ThreadTaskResult::Retryable { attempt: 3, .. });

        let failed = ThreadTaskResult::Failed {
            task_id: 3,
            reason: "timeout",
        };
        assert_matches!(
            failed,
            ThreadTaskResult::Failed {
                reason: "timeout",
                ..
            }
        );
    }

    #[test]
    fn test_assert_matches_option_result() {
        let ok_result: Result<i32, &str> = Ok(42);
        assert_matches!(ok_result, Ok(42));

        let some_value: Option<i32> = Some(100);
        assert_matches!(some_value, Some(100));
    }

    #[test]
    fn test_get_rust_196_thread_info() {
        let info = get_rust_196_thread_info();
        assert!(info.contains("core::range::Range"));
        assert!(info.contains("LazyLock::from"));
        assert!(info.contains("AssertUnwindSafe"));
        assert!(info.contains("assert_matches"));
    }

    #[test]
    fn test_core_range_into_iter() {
        let r = core::range::Range { start: 1, end: 5 };
        let collected: Vec<i32> = r.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_range_inclusive_fields() {
        // `core::range::RangeInclusive` 的字段为 `start` 和 `last`
        let ri = core::range::RangeInclusive {
            start: 10,
            last: 20,
        };
        assert_eq!(ri.start, 10);
        assert_eq!(ri.last, 20);
        let collected: Vec<i32> = ri.into_iter().collect();
        assert_eq!(collected, vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]);
    }
}
