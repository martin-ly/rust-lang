//! # c08_algorithms - Rust 算法学习库
//!
//! 本 crate 提供 Rust 中常用算法与数据结构的学习实现，涵盖排序、搜索、图算法、
//! 动态规划、贪心、字符串算法、几何、数论、机器学习基础、性能优化与形式化验证示例。
//!
//! ## 特性
//!
//! - **Rust 1.95.0+ 特性对齐**：使用 Edition 2024 与最新标准库 API
//! - **多实现方式**：同步、并行、异步（gen blocks，nightly-only）
//! - **主题化组织**：按算法主题与 LeetCode 分类双维度组织
//! - **形式化验证**：含 Kani 验证示例与循环不变量说明
//! - **完整文档**：算法说明、复杂度分析与可运行示例
//!
//! ## 使用示例

// [来源: Rust Standard Library / The Algorithm Design Manual]
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]
#![allow(clippy::bool_assert_comparison)]
#![allow(clippy::approx_constant)]
// nightly-only 预览模块所需 feature gate，仅在 --cfg nightly 时启用。
// 注：int_format_into / box_as_ptr / nonzero_from_str_radix / exposed_provenance
// 在当前 nightly 已稳定，无需再声明；保留 gen_blocks / yield_expr / portable_simd。
#![cfg_attr(nightly, feature(gen_blocks, yield_expr, portable_simd))]
#![cfg_attr(all(nightly, test), feature(vec_deque_truncate_front))]

//
// ```rust
// use c08_algorithms::topics::sorting::{SortingEngine, SortingAlgorithm};
// use c08_algorithms::topics::searching::{SearchingEngine, SearchingAlgorithm};
//
// // 排序示例
// let data = vec![3, 1, 4, 1, 5, 9, 2, 6];
// let result = SortingEngine::sort_sync(data, SortingAlgorithm::Quick);
// println!("排序结果: {:?}", result.data);
//
// // 搜索示例
// let data = vec![1, 3, 5, 7, 9, 11, 13];
// let result = SearchingEngine::binary_search_sync(&data, &7);
// println!("搜索结果: {:?}", result);
// ```
// ## 形式化验证示例
//
// ```rust
// use c08_algorithms::algorithms::formal_verification_examples::{
//     binary_search_verified,
//     insertion_sort_verified,
// };
//
// // 带完整证明的二分查找
// let arr = vec![1, 3, 5, 7, 9];
// assert_eq!(binary_search_verified(&arr, &5), Some(2));
//
// // 带循环不变量证明的插入排序
// let mut arr = vec![3, 1, 4, 1, 5];
// insertion_sort_verified(&mut arr);
// assert_eq!(arr, vec![1, 1, 3, 4, 5]);
// ```
pub mod error;

// 核心算法模块（Rust 1.95 特性对齐）
pub mod algorithms;

// 主题化算法模块
pub mod topics;

// Kani 形式化验证示例（仅在 cargo kani 时编译）
#[cfg(kani)]
pub mod kani_examples;

// 兼容性：保留原有模块结构
pub mod backtracking;
pub mod data_structure;
pub mod divide_and_conquer;
pub mod dynamic_programming;
pub mod graph;
pub mod greedy;
pub mod searching;
pub mod sorting;

// 高级算法模块
pub mod advanced_algorithms;

// 机器学习模块
pub mod machine_learning;

// SIMD 向量化操作
pub mod simd_operations;

// 性能优化模块
pub mod geometry;
pub mod number_theory;
pub mod performance_examples;
pub mod performance_optimization;
pub mod string_algorithms;

// 示例程序
// pub mod bin; // 暂时注释掉，避免编译错误

pub mod archive;
pub use archive::rust_192_features;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_193_features;
pub mod rust_194_features;
pub mod rust_195_features;

/// Rust 1.95 `gen` block 算法前瞻（nightly-only）。
#[cfg(nightly)]
pub mod rust_195_gen_blocks_preview;

pub mod rust_196_features;

/// Rust 1.96 `gen` block 算法前瞻（nightly-only）。
#[cfg(nightly)]
pub mod rust_196_gen_blocks_preview;

pub mod rust_197_features;

/// Rust 1.98.0 预览特性（需要 nightly）。
#[cfg(nightly)]
pub mod rust_198_features;

pub mod algorithm_decision_trees;

// LeetCode 分类算法模块（结合 Rust 1.95 特性）
pub mod leetcode;

/// 算法库版本号。
pub const VERSION: &str = "0.3.0";

/// 本 crate 目标对齐的 Rust 版本。
pub const RUST_VERSION: &str = "1.95.0";

/// 返回算法库版本号。
///
/// # Examples
///
/// ```
/// use c08_algorithms::get_version;
///
/// let version = get_version();
/// assert!(!version.is_empty());
/// ```
pub fn get_version() -> &'static str {
    VERSION
}

/// 返回本 crate 目标对齐的 Rust 版本号。
///
/// # Examples
///
/// ```
/// use c08_algorithms::get_rust_version;
///
/// let rust_version = get_rust_version();
/// assert!(!rust_version.is_empty());
/// ```
pub fn get_rust_version() -> &'static str {
    RUST_VERSION
}

/// 重新导出主题化模块的主要类型
pub use topics::{
    AlgorithmBenchmark, AlgorithmCategory, AlgorithmInfo, BenchmarkResult, ComplexityAnalyzer,
    ImplementationType, LibraryStats, get_library_stats,
};

// 兼容性函数，使用主题化模块的实现
pub fn get_all_algorithms() -> Vec<AlgorithmInfo> {
    topics::get_all_algorithms()
}

pub fn get_algorithms_by_category(category: AlgorithmCategory) -> Vec<AlgorithmInfo> {
    topics::get_algorithms_by_category(category)
}

pub fn search_algorithms(query: &str) -> Vec<AlgorithmInfo> {
    topics::search_algorithms(query)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_all_algorithms() {
        let algorithms = get_all_algorithms();
        assert!(!algorithms.is_empty());

        // 检查是否包含所有分类
        let categories: std::collections::HashSet<_> =
            algorithms.iter().map(|a| &a.category).collect();

        assert!(categories.contains(&AlgorithmCategory::Sorting));
        assert!(categories.contains(&AlgorithmCategory::Searching));
    }

    #[test]
    fn test_get_algorithms_by_category() {
        let sorting_algorithms = get_algorithms_by_category(AlgorithmCategory::Sorting);
        assert!(!sorting_algorithms.is_empty());

        for algorithm in sorting_algorithms {
            assert_eq!(algorithm.category, AlgorithmCategory::Sorting);
        }
    }

    #[test]
    fn test_search_algorithms() {
        let results = search_algorithms("快速");
        assert!(!results.is_empty());

        let results = search_algorithms("二分");
        assert!(!results.is_empty());

        let results = search_algorithms("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_algorithm_benchmark() {
        let mut benchmark = AlgorithmBenchmark::new();

        benchmark.run_benchmark(
            "测试算法",
            ImplementationType::Synchronous,
            1000,
            100,
            || BenchmarkResult {
                algorithm_name: "测试算法".to_string(),
                implementation_type: ImplementationType::Synchronous,
                input_size: 1000,
                execution_time: std::time::Duration::from_micros(100),
                memory_usage: 1024,
                cpu_usage: 50.0,
                cache_misses: Some(10),
            },
        );

        let avg_time = benchmark.get_average_time("测试算法");
        assert!(avg_time.is_some());
        assert!(avg_time.expect("获取平均时间失败") >= std::time::Duration::from_micros(100));
    }

    #[test]
    fn test_complexity_analyzer() {
        let input_sizes = vec![100, 1000, 10000];
        let results = ComplexityAnalyzer::analyze_time_complexity(
            |size| {
                // 模拟O(n)算法
                std::time::Duration::from_nanos(size as u64)
            },
            &input_sizes,
        );

        assert_eq!(results.len(), 3);

        let complexity = ComplexityAnalyzer::estimate_complexity(&results);
        assert!(!complexity.is_empty());
    }

    #[test]
    fn test_version() {
        assert_eq!(get_version(), "0.3.0");
    }
}

#[cfg(test)]
pub mod miri_tests;
