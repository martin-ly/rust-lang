//! Rust 1.90 高级算法实现库
//!
//! 本库提供了Rust中各种高级算法的完整实现，完全对齐 Rust 1.90 版本特性，
//! 包括排序、搜索、图算法、机器学习算法、密码学算法等。
//!
//! ## 特性
//!
//! - **Rust 1.90 特性对齐**: 完全支持最新语言特性
//! - **主题化组织**: 按算法主题分类组织
//! - **多实现方式**: 同步、并行、异步实现
//! - **形式化验证**: 包含算法正确性证明（循环不变量、霍尔逻辑）
//! - **完整文档**: 详细的算法说明和复杂度分析（主定理、摊还分析）
//! - **异步模式**: Actor/Reactor/CSP三大模式完整实现
//!
//! ## 使用示例
//!
//! ```rust
//! use c08_algorithms::topics::sorting::{SortingEngine, SortingAlgorithm};
//! use c08_algorithms::topics::searching::{SearchingEngine, SearchingAlgorithm};
//!
//! // 排序示例
//! let data = vec![3, 1, 4, 1, 5, 9, 2, 6];
//! let result = SortingEngine::sort_sync(data, SortingAlgorithm::Quick);
//! println!("排序结果: {:?}", result.data);
//!
//! // 搜索示例
//! let data = vec![1, 3, 5, 7, 9, 11, 13];
//! let result = SearchingEngine::binary_search_sync(&data, &7);
//! println!("搜索结果: {:?}", result);
//! ```
//!
//! ## 形式化验证示例
//!
//! ```rust
//! use c08_algorithms::algorithms::formal_verification_examples::{
//!     binary_search_verified,
//!     insertion_sort_verified,
//! };
//!
//! // 带完整证明的二分查找
//! let arr = vec![1, 3, 5, 7, 9];
//! assert_eq!(binary_search_verified(&arr, &5), Some(2));
//!
//! // 带循环不变量证明的插入排序
//! let mut arr = vec![3, 1, 4, 1, 5];
//! insertion_sort_verified(&mut arr);
//! assert_eq!(arr, vec![1, 1, 3, 4, 5]);
//! ```

// 核心算法模块（Rust 1.90 特性对齐）
pub mod algorithms;

// 主题化算法模块
pub mod topics;

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

// 性能优化模块
pub mod geometry;
pub mod number_theory;
pub mod performance_examples;
pub mod performance_optimization;
pub mod string_algorithms;

// 示例程序
// pub mod bin; // 暂时注释掉，避免编译错误

/// 算法库版本信息
pub const VERSION: &str = "0.2.0";
pub const RUST_VERSION: &str = "1.90";

/// 获取库版本信息
pub fn get_version() -> &'static str {
    VERSION
}

/// 获取支持的 Rust 版本
pub fn get_rust_version() -> &'static str {
    RUST_VERSION
}

/// 重新导出主题化模块的主要类型
pub use topics::{
    AlgorithmCategory, AlgorithmInfo, AlgorithmBenchmark, ComplexityAnalyzer,
    ImplementationType, LibraryStats, get_library_stats, BenchmarkResult,
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
        assert!(avg_time.unwrap() >= std::time::Duration::from_micros(100));
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
        assert_eq!(get_version(), "0.2.0");
    }
}
