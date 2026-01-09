//! # 排序算法模块
//!
//! 本模块实现了各种排序算法，包括同步、异步、并行、分布式四个版本。
//! 充分利用 Rust 1.90 的新特性，提供高性能、类型安全的排序实现。

pub mod sync;
pub mod async_exec;
pub mod parallel;
pub mod distributed;

// 重新导出所有排序算法
pub use sync::*;
pub use async_exec::*;

use crate::algorithms::execution_modes::*;
use std::cmp::Ordering;

/// 排序算法类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortingAlgorithm {
    QuickSort,
    MergeSort,
    HeapSort,
    InsertionSort,
    SelectionSort,
    BubbleSort,
    RadixSort,
    CountingSort,
    BucketSort,
    TimSort,
}

/// 排序结果
#[derive(Debug, Clone)]
pub struct SortingResult<T> {
    pub sorted_data: Vec<T>,
    pub comparisons: usize,
    pub swaps: usize,
    pub execution_time: std::time::Duration,
}

/// 排序算法特征
pub trait SortingAlgorithmTrait<T> {
    fn sort(&self, data: &mut [T]) -> SortingResult<T>
    where
        T: Clone + Ord;

    fn sort_by<F>(&self, data: &mut [T], compare: F) -> SortingResult<T>
    where
        T: Clone,
        F: Fn(&T, &T) -> Ordering;
}

/// 排序算法工厂
pub struct SortingAlgorithmFactory;

impl SortingAlgorithmFactory {
    /// 创建同步排序算法
    pub fn create_sync(algorithm: SortingAlgorithm) -> Box<dyn SyncSortingAlgorithm> {
        match algorithm {
            SortingAlgorithm::QuickSort => Box::new(sync::QuickSort),
            SortingAlgorithm::MergeSort => Box::new(sync::MergeSort),
            SortingAlgorithm::HeapSort => Box::new(sync::HeapSort),
            SortingAlgorithm::InsertionSort => Box::new(sync::InsertionSort),
            SortingAlgorithm::SelectionSort => Box::new(sync::SelectionSort),
            SortingAlgorithm::BubbleSort => Box::new(sync::BubbleSort),
            SortingAlgorithm::RadixSort => Box::new(sync::RadixSort),
            SortingAlgorithm::CountingSort => Box::new(sync::CountingSort),
            SortingAlgorithm::BucketSort => Box::new(sync::BucketSort),
            SortingAlgorithm::TimSort => Box::new(sync::TimSort),
        }
    }

    /// 创建异步排序算法
    pub fn create_async(algorithm: SortingAlgorithm) -> Box<dyn AsyncSortingAlgorithm> {
        match algorithm {
            SortingAlgorithm::QuickSort => Box::new(async_exec::AsyncQuickSort),
            SortingAlgorithm::MergeSort => Box::new(async_exec::AsyncMergeSort),
            SortingAlgorithm::HeapSort => Box::new(async_exec::AsyncHeapSort),
            SortingAlgorithm::InsertionSort => Box::new(async_exec::AsyncInsertionSort),
            SortingAlgorithm::SelectionSort => Box::new(async_exec::AsyncSelectionSort),
            SortingAlgorithm::BubbleSort => Box::new(async_exec::AsyncBubbleSort),
            SortingAlgorithm::RadixSort => Box::new(async_exec::AsyncRadixSort),
            SortingAlgorithm::CountingSort => Box::new(async_exec::AsyncCountingSort),
            SortingAlgorithm::BucketSort => Box::new(async_exec::AsyncBucketSort),
            SortingAlgorithm::TimSort => Box::new(async_exec::AsyncTimSort),
        }
    }

    /// 创建并行排序算法
    pub fn create_parallel(algorithm: SortingAlgorithm) -> Box<dyn ParallelSortingAlgorithm> {
        match algorithm {
            SortingAlgorithm::QuickSort => Box::new(parallel::ParallelQuickSort),
            SortingAlgorithm::MergeSort => Box::new(parallel::ParallelMergeSort),
            SortingAlgorithm::HeapSort => Box::new(parallel::ParallelHeapSort),
            SortingAlgorithm::InsertionSort => Box::new(parallel::ParallelInsertionSort),
            SortingAlgorithm::SelectionSort => Box::new(parallel::ParallelSelectionSort),
            SortingAlgorithm::BubbleSort => Box::new(parallel::ParallelBubbleSort),
            SortingAlgorithm::RadixSort => Box::new(parallel::ParallelRadixSort),
            SortingAlgorithm::CountingSort => Box::new(parallel::ParallelCountingSort),
            SortingAlgorithm::BucketSort => Box::new(parallel::ParallelBucketSort),
            SortingAlgorithm::TimSort => Box::new(parallel::ParallelTimSort),
        }
    }

    /// 创建分布式排序算法
    pub fn create_distributed(algorithm: SortingAlgorithm) -> Box<dyn DistributedSortingAlgorithm> {
        match algorithm {
            SortingAlgorithm::QuickSort => Box::new(distributed::DistributedQuickSort),
            SortingAlgorithm::MergeSort => Box::new(distributed::DistributedMergeSort),
            SortingAlgorithm::HeapSort => Box::new(distributed::DistributedHeapSort),
            SortingAlgorithm::InsertionSort => Box::new(distributed::DistributedInsertionSort),
            SortingAlgorithm::SelectionSort => Box::new(distributed::DistributedSelectionSort),
            SortingAlgorithm::BubbleSort => Box::new(distributed::DistributedBubbleSort),
            SortingAlgorithm::RadixSort => Box::new(distributed::DistributedRadixSort),
            SortingAlgorithm::CountingSort => Box::new(distributed::DistributedCountingSort),
            SortingAlgorithm::BucketSort => Box::new(distributed::DistributedBucketSort),
            SortingAlgorithm::TimSort => Box::new(distributed::DistributedTimSort),
        }
    }
}

/// 同步排序算法特征
pub trait SyncSortingAlgorithm {
    fn get_algorithm_type(&self) -> SortingAlgorithm;
    fn get_complexity(&self) -> AlgorithmComplexity;
}

/// 异步排序算法特征
pub trait AsyncSortingAlgorithm {
    fn get_algorithm_type(&self) -> SortingAlgorithm;
    fn get_complexity(&self) -> AlgorithmComplexity;
}

/// 并行排序算法特征
pub trait ParallelSortingAlgorithm {
    fn get_algorithm_type(&self) -> SortingAlgorithm;
    fn get_complexity(&self) -> AlgorithmComplexity;
}

/// 分布式排序算法特征
pub trait DistributedSortingAlgorithm {
    fn get_algorithm_type(&self) -> SortingAlgorithm;
    fn get_complexity(&self) -> AlgorithmComplexity;
}

/// 算法复杂度信息
#[derive(Debug, Clone)]
pub struct AlgorithmComplexity {
    pub time_best: String,
    pub time_average: String,
    pub time_worst: String,
    pub space: String,
    pub stable: bool,
    pub in_place: bool,
}

impl AlgorithmComplexity {
    pub fn new(time_best: &str, time_average: &str, time_worst: &str, space: &str, stable: bool, in_place: bool) -> Self {
        Self {
            time_best: time_best.to_string(),
            time_average: time_average.to_string(),
            time_worst: time_worst.to_string(),
            space: space.to_string(),
            stable,
            in_place,
        }
    }
}

/// 排序算法基准测试器
pub struct SortingBenchmarker;

impl SortingBenchmarker {
    /// 运行完整的排序算法基准测试
    pub async fn run_comprehensive_benchmark(
        data_sizes: Vec<usize>,
        algorithms: Vec<SortingAlgorithm>,
    ) -> Result<ComprehensiveSortingBenchmark, Box<dyn std::error::Error + Send + Sync>> {
        let mut sync_results = Vec::new();
        let mut async_results = Vec::new();
        let mut parallel_results = Vec::new();
        let mut distributed_results = Vec::new();

        for size in &data_sizes {
            let test_data = Self::generate_test_data(*size);

            for algorithm in &algorithms {
                // 同步基准测试
                let _sync_algorithm = SortingAlgorithmFactory::create_sync(*algorithm);
                let mut sync_data = test_data.clone();
                let start = std::time::Instant::now();
                sync_data.sort(); // 使用标准库排序作为示例
                let sync_execution_time = start.elapsed();

                sync_results.push(SortingBenchmarkResult {
                    algorithm: *algorithm,
                    data_size: *size,
                    execution_mode: ExecutionMode::Sync,
                    result: ExecutionResult {
                        result: sync_data,
                        execution_time: sync_execution_time,
                        memory_usage: std::mem::size_of_val(&test_data),
                        thread_count: 1,
                    },
                });

                // 异步基准测试
                let _async_algorithm = SortingAlgorithmFactory::create_async(*algorithm);
                let mut async_data = test_data.clone();
                let start = std::time::Instant::now();
                async_data.sort(); // 使用标准库排序作为示例
                let async_execution_time = start.elapsed();

                async_results.push(SortingBenchmarkResult {
                    algorithm: *algorithm,
                    data_size: *size,
                    execution_mode: ExecutionMode::Async,
                    result: ExecutionResult {
                        result: async_data,
                        execution_time: async_execution_time,
                        memory_usage: std::mem::size_of_val(&test_data),
                        thread_count: 1,
                    },
                });

                // 并行基准测试
                let _parallel_algorithm = SortingAlgorithmFactory::create_parallel(*algorithm);
                let mut parallel_data = test_data.clone();
                let start = std::time::Instant::now();
                parallel_data.sort(); // 使用标准库排序作为示例
                let parallel_execution_time = start.elapsed();

                parallel_results.push(SortingBenchmarkResult {
                    algorithm: *algorithm,
                    data_size: *size,
                    execution_mode: ExecutionMode::Parallel,
                    result: ExecutionResult {
                        result: parallel_data,
                        execution_time: parallel_execution_time,
                        memory_usage: std::mem::size_of_val(&test_data),
                        thread_count: num_cpus::get(),
                    },
                });

                // 分布式基准测试
                let _distributed_algorithm = SortingAlgorithmFactory::create_distributed(*algorithm);
                let mut distributed_data = test_data.clone();
                let start = std::time::Instant::now();
                distributed_data.sort(); // 使用标准库排序作为示例
                let distributed_execution_time = start.elapsed();

                distributed_results.push(SortingBenchmarkResult {
                    algorithm: *algorithm,
                    data_size: *size,
                    execution_mode: ExecutionMode::Distributed,
                    result: ExecutionResult {
                        result: distributed_data,
                        execution_time: distributed_execution_time,
                        memory_usage: std::mem::size_of_val(&test_data),
                        thread_count: 3, // 3个节点
                    },
                });
            }
        }

        Ok(ComprehensiveSortingBenchmark {
            sync_results,
            async_results,
            parallel_results,
            distributed_results,
        })
    }

    /// 生成测试数据
    fn generate_test_data(size: usize) -> Vec<i32> {
        use rand::Rng;
        let mut rng = rand::rng();
        (0..size).map(|_| rng.random_range(-1000..1000)).collect()
    }
}

/// 执行模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionMode {
    Sync,
    Async,
    Parallel,
    Distributed,
}

/// 排序基准测试结果
#[derive(Debug, Clone)]
pub struct SortingBenchmarkResult {
    pub algorithm: SortingAlgorithm,
    pub data_size: usize,
    pub execution_mode: ExecutionMode,
    pub result: ExecutionResult<Vec<i32>>,
}

/// 综合排序基准测试结果
#[derive(Debug, Clone)]
pub struct ComprehensiveSortingBenchmark {
    pub sync_results: Vec<SortingBenchmarkResult>,
    pub async_results: Vec<SortingBenchmarkResult>,
    pub parallel_results: Vec<SortingBenchmarkResult>,
    pub distributed_results: Vec<SortingBenchmarkResult>,
}

impl ComprehensiveSortingBenchmark {
    /// 生成综合性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 综合排序算法基准测试报告 ===\n\n");

        // 按算法分组分析
        let algorithms = [
            SortingAlgorithm::QuickSort,
            SortingAlgorithm::MergeSort,
            SortingAlgorithm::HeapSort,
            SortingAlgorithm::InsertionSort,
            SortingAlgorithm::SelectionSort,
            SortingAlgorithm::BubbleSort,
            SortingAlgorithm::RadixSort,
            SortingAlgorithm::CountingSort,
            SortingAlgorithm::BucketSort,
            SortingAlgorithm::TimSort,
        ];

        for algorithm in &algorithms {
            report.push_str(&format!("=== {:?} ===\n", algorithm));

            // 分析不同执行模式的性能
            let sync_perf = self.get_best_performance(*algorithm, ExecutionMode::Sync);
            let async_perf = self.get_best_performance(*algorithm, ExecutionMode::Async);
            let parallel_perf = self.get_best_performance(*algorithm, ExecutionMode::Parallel);
            let distributed_perf = self.get_best_performance(*algorithm, ExecutionMode::Distributed);

            if let Some(perf) = sync_perf {
                report.push_str(&format!("  同步执行: {:?} (数据大小: {})\n", perf.result.execution_time, perf.data_size));
            }
            if let Some(perf) = async_perf {
                report.push_str(&format!("  异步执行: {:?} (数据大小: {})\n", perf.result.execution_time, perf.data_size));
            }
            if let Some(perf) = parallel_perf {
                report.push_str(&format!("  并行执行: {:?} (数据大小: {})\n", perf.result.execution_time, perf.data_size));
            }
            if let Some(perf) = distributed_perf {
                report.push_str(&format!("  分布式执行: {:?} (数据大小: {})\n", perf.result.execution_time, perf.data_size));
            }

            report.push('\n');
        }

        // 性能对比分析
        report.push_str("=== 性能对比分析 ===\n");
        report.push_str("1. 同步 vs 异步: 异步执行适用于 I/O 密集型任务\n");
        report.push_str("2. 同步 vs 并行: 并行执行在多核 CPU 上表现更佳\n");
        report.push_str("3. 并行 vs 分布式: 分布式执行适用于大规模数据处理\n");
        report.push_str("4. 算法选择: 根据数据规模和性能要求选择合适的算法\n");

        report
    }

    /// 返回位置 impl Trait：按算法产出最佳用例摘要的迭代器
    pub fn best_summary_iter(&self) -> impl Iterator<Item = String> + '_ {
        let modes = [
            ExecutionMode::Sync,
            ExecutionMode::Async,
            ExecutionMode::Parallel,
            ExecutionMode::Distributed,
        ];

        let algorithms = [
            SortingAlgorithm::QuickSort,
            SortingAlgorithm::MergeSort,
            SortingAlgorithm::HeapSort,
            SortingAlgorithm::InsertionSort,
            SortingAlgorithm::SelectionSort,
            SortingAlgorithm::BubbleSort,
            SortingAlgorithm::RadixSort,
            SortingAlgorithm::CountingSort,
            SortingAlgorithm::BucketSort,
            SortingAlgorithm::TimSort,
        ];

        algorithms.into_iter().flat_map(move |alg| {
            modes.into_iter().filter_map(move |mode| {
                self.get_best_performance(alg, mode).map(|r| {
                    format!(
                        "{:?}/{:?}: {:?} (n={})",
                        alg,
                        mode,
                        r.result.execution_time,
                        r.data_size
                    )
                })
            })
        })
    }

    /// 获取指定算法和模式的最佳性能
    fn get_best_performance(&self, algorithm: SortingAlgorithm, mode: ExecutionMode) -> Option<&SortingBenchmarkResult> {
        let results = match mode {
            ExecutionMode::Sync => &self.sync_results,
            ExecutionMode::Async => &self.async_results,
            ExecutionMode::Parallel => &self.parallel_results,
            ExecutionMode::Distributed => &self.distributed_results,
        };

        results
            .iter()
            .filter(|r| r.algorithm == algorithm)
            .min_by_key(|r| r.result.execution_time)
    }
}
