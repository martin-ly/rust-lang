//! # Rust 1.96.0 稳定特性演示模块（异步编程）
//! # Rust 1.96.0 feature demonstration module （async ）
//!
//! 本模块展示 Rust 1.96.0 在异步编程中的关键新 API：
//! This module demonstrates Rust 1.96.0 asynckeynew API
//! - `core::range::Range` — `Copy` 语义，适用于异步任务分批范围
//! - `core::range::Range` — `Copy` ，async task scope
//! - `std::assert_matches!` / `debug_assert_matches!` — 异步 Result/Option 模式断言

use std::sync::LazyLock;

// ============================================================================
// 1. core::range::Range — 异步任务分批（Copy 语义）
// ============================================================================

/// 异步任务批次分配器。
/// async task 。
///
/// `core::range::Range` 实现 `Copy`，因此批次范围可以在多个异步任务之间
/// `core::range::Range` `Copy`，therefore scope can in async task 's
/// 自由复制，无需引用或生命周期管理。
pub struct AsyncTaskBatcher;

impl AsyncTaskBatcher {
    /// 将 `total_tasks` 按 `batch_size` 分成多个批次，返回 `core::range::Range` 列表。
    pub fn batch_ranges(total_tasks: usize, batch_size: usize) -> Vec<core::range::Range<usize>> {
        if batch_size == 0 || total_tasks == 0 {
            return vec![];
        }

        let mut ranges = Vec::new();
        let mut start = 0usize;

        while start < total_tasks {
            let end = (start + batch_size).min(total_tasks);
            ranges.push(core::range::Range { start, end });
            start = end;
        }

        ranges
    }

    /// 计算给定批次范围的总任务数。
    pub fn total_in_ranges(ranges: &[core::range::Range<usize>]) -> usize {
        ranges.iter().map(|r| r.end - r.start).sum()
    }

    /// 将范围映射为并发执行的建议优先级（范围越小优先级越高）。
    /// will scope as concurrency （scope ）。
    pub fn priority_for_range(range: core::range::Range<usize>) -> u8 {
        let size = range.end - range.start;
        match size {
            0..=10 => 3,
            11..=50 => 2,
            _ => 1,
        }
    }
}

// ============================================================================
// 2. LazyLock::from(value) — 异步运行时配置
// ============================================================================

/// 异步运行时配置，使用 `LazyLock::from` 包装运行时确定的值。
/// async runtime ， `LazyLock::from` runtime 。
///
/// ⚠️ `LazyLock::from` **不是 `const`**，不能用于 `static`。
/// in async runtime stage to 。
pub struct AsyncRuntimeConfig {
    /// 最大并发任务数
    /// maximum concurrency task
    pub max_concurrency: LazyLock<usize, fn() -> usize>,
    /// 单次批处理大小
    pub batch_size: LazyLock<usize, fn() -> usize>,
    /// 默认超时（毫秒）
    pub default_timeout_ms: LazyLock<u64, fn() -> u64>,
}

impl AsyncRuntimeConfig {
    /// 从运行时值构造配置。
    /// from runtime 。
    pub fn from_values(max_concurrency: usize, batch_size: usize, timeout_ms: u64) -> Self {
        Self {
            max_concurrency: LazyLock::from(max_concurrency),
            batch_size: LazyLock::from(batch_size),
            default_timeout_ms: LazyLock::from(timeout_ms),
        }
    }

    /// 获取配置摘要。
    /// Get configuration
    pub fn summary(&self) -> String {
        format!(
            "max_concurrency={}, batch_size={}, timeout_ms={}",
            *self.max_concurrency, *self.batch_size, *self.default_timeout_ms
        )
    }
}

// ============================================================================
// 3. assert_matches! / debug_assert_matches! — 异步结果测试
// ============================================================================

/// 异步任务结果。
/// async task result 。
#[derive(Debug, PartialEq)]
pub enum AsyncTaskResult {
    Completed { id: usize, output: String },
    TimedOut { id: usize, elapsed_ms: u64 },
    Cancelled { id: usize },
}

/// 使用 `assert_matches!` 验证异步结果集合。
/// `assert_matches!` async result set 。
///
/// 在测试异步系统时，比 `assert!(matches!(...))` 提供更好的诊断信息。
/// in async system ， `assert!(matches!(...))` 。
pub fn verify_async_results(results: &[AsyncTaskResult]) {
    use std::assert_matches;

    for result in results {
        assert_matches!(
            result,
            AsyncTaskResult::Completed { .. }
                | AsyncTaskResult::TimedOut { .. }
                | AsyncTaskResult::Cancelled { .. }
        );
    }
}

/// 异步状态机状态。
/// async state machine state 。
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum AsyncState {
    Idle,
    Polling { attempt: u8 },
    Ready,
    Failed { code: u16 },
}

/// 使用 `debug_assert_matches!` 在运行时检查异步不变式（零成本于 release）。
/// `debug_assert_matches!` in runtime async （cost release）。
///
/// 适用于验证异步状态机的内部状态转换是否符合预期。
/// async state machine inside state conversion 。
pub fn check_async_invariants(state: AsyncState) {
    use std::debug_assert_matches;

    // 零成本抽象：仅在 debug 构建时执行
    debug_assert_matches!(
        state,
        AsyncState::Idle
            | AsyncState::Polling { .. }
            | AsyncState::Ready
            | AsyncState::Failed { .. }
    );
}

// ============================================================================
// 演示函数
// ============================================================================

/// 运行 Rust 1.96 异步特性演示
/// Run Rust 1.96 asyncfeatures
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 异步特性演示");
    println!("========================================\n");

    let batches = AsyncTaskBatcher::batch_ranges(100, 10);
    println!("异步任务批次: {:?}", batches);
    println!("总任务数: {}", AsyncTaskBatcher::total_in_ranges(&batches));

    let config = AsyncRuntimeConfig::from_values(8, 16, 5000);
    println!("运行时配置: {}", config.summary());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// Get featuresinformation
pub fn get_rust_196_async_info() -> String {
    "Rust 1.96.0 异步特性:\n- core::range::Range { start, end } — Copy 语义，异步任务分批\n- \
     LazyLock::from(value) — 异步运行时配置（非 const）\n- assert_matches! / debug_assert_matches! \
     — 异步 Result/Option 断言"
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
    fn test_batch_ranges_copy_semantics() {
        let ranges = AsyncTaskBatcher::batch_ranges(100, 10);
        assert_eq!(ranges.len(), 10);

        // `core::range::Range` 是 `Copy`，可以复制后仍使用原值
        let r0 = ranges[0];
        let r0_copy = r0;
        assert_eq!(r0.start, r0_copy.start);
        assert_eq!(r0.end, r0_copy.end);
        assert_eq!(r0.end - r0.start, 10);
    }

    #[test]
    fn test_batch_ranges_distribution() {
        let ranges = AsyncTaskBatcher::batch_ranges(53, 10);
        assert_eq!(ranges.len(), 6);
        assert_eq!(AsyncTaskBatcher::total_in_ranges(&ranges), 53);

        // 最后一个批次应该包含剩余任务
        let last = ranges.last().unwrap();
        assert_eq!(last.end - last.start, 3);
    }

    #[test]
    fn test_batch_ranges_empty() {
        let ranges = AsyncTaskBatcher::batch_ranges(0, 10);
        assert!(ranges.is_empty());

        let ranges2 = AsyncTaskBatcher::batch_ranges(10, 0);
        assert!(ranges2.is_empty());
    }

    #[test]
    fn test_priority_for_range() {
        let small = core::range::Range { start: 0, end: 5 };
        assert_eq!(AsyncTaskBatcher::priority_for_range(small), 3);

        let medium = core::range::Range { start: 0, end: 30 };
        assert_eq!(AsyncTaskBatcher::priority_for_range(medium), 2);

        let large = core::range::Range { start: 0, end: 100 };
        assert_eq!(AsyncTaskBatcher::priority_for_range(large), 1);
    }

    #[test]
    fn test_lazy_lock_from_runtime_config() {
        let config = AsyncRuntimeConfig::from_values(16, 32, 3000);
        assert_eq!(*config.max_concurrency, 16);
        assert_eq!(*config.batch_size, 32);
        assert_eq!(*config.default_timeout_ms, 3000);
        assert_eq!(
            config.summary(),
            "max_concurrency=16, batch_size=32, timeout_ms=3000"
        );
    }

    #[test]
    fn test_assert_matches_async_result() {
        let completed = AsyncTaskResult::Completed {
            id: 1,
            output: "done".to_string(),
        };
        assert_matches!(completed, AsyncTaskResult::Completed { id: 1, .. });

        let timed_out = AsyncTaskResult::TimedOut {
            id: 2,
            elapsed_ms: 5000,
        };
        assert_matches!(
            timed_out,
            AsyncTaskResult::TimedOut {
                elapsed_ms: 5000,
                ..
            }
        );

        let cancelled = AsyncTaskResult::Cancelled { id: 3 };
        assert_matches!(cancelled, AsyncTaskResult::Cancelled { id: 3 });
    }

    #[test]
    fn test_assert_matches_option_result() {
        let ok: Result<i32, &str> = Ok(100);
        assert_matches!(ok, Ok(100));

        let some: Option<u64> = Some(12345);
        assert_matches!(some, Some(12345));

        let none: Option<u64> = None;
        assert_matches!(none, None);
    }

    #[test]
    fn test_debug_assert_matches_async_state() {
        // debug_assert_matches! 在 debug 构建时生效
        check_async_invariants(AsyncState::Idle);
        check_async_invariants(AsyncState::Polling { attempt: 1 });
        check_async_invariants(AsyncState::Ready);
        check_async_invariants(AsyncState::Failed { code: 500 });
    }

    #[test]
    fn test_verify_async_results() {
        let results = vec![
            AsyncTaskResult::Completed {
                id: 1,
                output: "a".to_string(),
            },
            AsyncTaskResult::TimedOut {
                id: 2,
                elapsed_ms: 100,
            },
            AsyncTaskResult::Cancelled { id: 3 },
        ];
        verify_async_results(&results);
    }

    #[test]
    fn test_core_range_into_iter() {
        let r = core::range::Range { start: 5, end: 10 };
        let collected: Vec<i32> = r.into_iter().collect();
        assert_eq!(collected, vec![5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_range_inclusive_fields() {
        let ri = core::range::RangeInclusive { start: 2, last: 5 };
        assert_eq!(ri.start, 2);
        assert_eq!(ri.last, 5);
        let collected: Vec<i32> = ri.into_iter().collect();
        assert_eq!(collected, vec![2, 3, 4, 5]);
    }

    #[test]
    fn test_get_rust_196_async_info() {
        let info = get_rust_196_async_info();
        assert!(info.contains("core::range::Range"));
        assert!(info.contains("LazyLock::from"));
        assert!(info.contains("assert_matches"));
    }
}
