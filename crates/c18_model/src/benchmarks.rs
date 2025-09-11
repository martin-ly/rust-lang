//! 性能基准测试
//! 
//! 本模块提供了各种性能基准测试功能，包括算法性能测试、
//! 内存使用测试、并发性能测试等。使用Rust的类型安全特性确保测试的准确性。

use std::time::{Duration, Instant};
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    /// 测试名称
    pub name: String,
    /// 执行时间
    pub duration: Duration,
    /// 内存使用量（字节）
    pub memory_usage: usize,
    /// 吞吐量（操作/秒）
    pub throughput: f64,
    /// 错误计数
    pub error_count: usize,
    /// 额外指标
    pub metrics: HashMap<String, f64>,
}

/// 基准测试配置
#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    /// 预热迭代次数
    pub warmup_iterations: usize,
    /// 测试迭代次数
    pub test_iterations: usize,
    /// 是否测量内存使用
    pub measure_memory: bool,
    /// 是否测量吞吐量
    pub measure_throughput: bool,
    /// 超时时间
    pub timeout: Option<Duration>,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            warmup_iterations: 10,
            test_iterations: 100,
            measure_memory: true,
            measure_throughput: true,
            timeout: Some(Duration::from_secs(60)),
        }
    }
}

/// 基准测试器
pub struct Benchmarker {
    config: BenchmarkConfig,
    results: Vec<BenchmarkResult>,
}

impl Benchmarker {
    /// 创建新的基准测试器
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            config,
            results: Vec::new(),
        }
    }

    /// 运行基准测试
    pub fn run<F>(&mut self, name: &str, test_fn: F) -> BenchmarkResult
    where
        F: Fn() -> Result<(), String>,
    {
        // 预热
        for _ in 0..self.config.warmup_iterations {
            let _ = test_fn();
        }

        // 测试
        let mut durations = Vec::new();
        let mut error_count = 0;
        let start_memory = self.get_memory_usage();

        for _ in 0..self.config.test_iterations {
            let start = Instant::now();
            match test_fn() {
                Ok(_) => {
                    let duration = start.elapsed();
                    durations.push(duration);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let end_memory = self.get_memory_usage();
        let memory_usage = if end_memory > start_memory {
            end_memory - start_memory
        } else {
            0
        };

        let total_duration: Duration = durations.iter().sum();
        let avg_duration = total_duration / durations.len() as u32;
        let throughput = if avg_duration.as_secs_f64() > 0.0 {
            self.config.test_iterations as f64 / total_duration.as_secs_f64()
        } else {
            0.0
        };

        let result = BenchmarkResult {
            name: name.to_string(),
            duration: avg_duration,
            memory_usage,
            throughput,
            error_count,
            metrics: HashMap::new(),
        };

        self.results.push(result.clone());
        result
    }

    /// 运行并发基准测试
    pub fn run_concurrent<F>(&mut self, name: &str, test_fn: F, num_threads: usize) -> BenchmarkResult
    where
        F: Fn() -> Result<(), String> + Send + Sync + 'static,
    {
        let test_fn = Arc::new(test_fn);
        let mut handles = Vec::new();
        let iterations_per_thread = self.config.test_iterations / num_threads;

        let start = Instant::now();

        for _ in 0..num_threads {
            let test_fn = Arc::clone(&test_fn);
            let handle = thread::spawn(move || {
                let mut local_durations = Vec::new();
                let mut local_errors = 0;

                for _ in 0..iterations_per_thread {
                    let start = Instant::now();
                    match test_fn() {
                        Ok(_) => {
                            local_durations.push(start.elapsed());
                        }
                        Err(_) => {
                            local_errors += 1;
                        }
                    }
                }

                (local_durations, local_errors)
            });
            handles.push(handle);
        }

        let mut all_durations = Vec::new();
        let mut total_errors = 0;

        for handle in handles {
            if let Ok((durations, errors)) = handle.join() {
                all_durations.extend(durations);
                total_errors += errors;
            }
        }

        let total_duration = start.elapsed();
        let avg_duration = if !all_durations.is_empty() {
            all_durations.iter().sum::<Duration>() / all_durations.len() as u32
        } else {
            Duration::from_secs(0)
        };

        let throughput = if total_duration.as_secs_f64() > 0.0 {
            all_durations.len() as f64 / total_duration.as_secs_f64()
        } else {
            0.0
        };

        let result = BenchmarkResult {
            name: format!("{} ({} threads)", name, num_threads),
            duration: avg_duration,
            memory_usage: 0, // 并发测试中难以准确测量内存
            throughput,
            error_count: total_errors,
            metrics: HashMap::new(),
        };

        self.results.push(result.clone());
        result
    }

    /// 获取内存使用量（简化实现）
    fn get_memory_usage(&self) -> usize {
        // 简化实现：返回0
        // 在实际应用中，可以使用更复杂的内存测量方法
        0
    }

    /// 获取所有测试结果
    pub fn get_results(&self) -> &[BenchmarkResult] {
        &self.results
    }

    /// 生成基准测试报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 基准测试报告 ===\n\n");

        for result in &self.results {
            report.push_str(&format!("测试名称: {}\n", result.name));
            report.push_str(&format!("平均执行时间: {:?}\n", result.duration));
            report.push_str(&format!("内存使用量: {} bytes\n", result.memory_usage));
            report.push_str(&format!("吞吐量: {:.2} ops/sec\n", result.throughput));
            report.push_str(&format!("错误次数: {}\n", result.error_count));
            report.push_str("\n");
        }

        // 性能对比
        if self.results.len() > 1 {
            report.push_str("=== 性能对比 ===\n");
            let fastest = self.results.iter()
                .min_by(|a, b| a.duration.cmp(&b.duration))
                .unwrap();
            
            for result in &self.results {
                let speedup = if result.duration.as_nanos() > 0 {
                    result.duration.as_nanos() as f64 / fastest.duration.as_nanos() as f64
                } else {
                    1.0
                };
                report.push_str(&format!(
                    "{}: {:.2}x slower than {}\n",
                    result.name, speedup, fastest.name
                ));
            }
        }

        report
    }

    /// 清空测试结果
    pub fn clear(&mut self) {
        self.results.clear();
    }
}

/// 算法基准测试
pub struct AlgorithmBenchmarker;

impl AlgorithmBenchmarker {
    /// 测试排序算法性能
    pub fn benchmark_sorting<F>(&self, name: &str, sort_fn: F, data_size: usize) -> BenchmarkResult
    where
        F: Fn(&mut [i32]) -> (),
    {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        
        benchmarker.run(name, || {
            let mut data = self.generate_random_data(data_size);
            sort_fn(&mut data);
            
            // 验证排序结果
            if !self.is_sorted(&data) {
                return Err("排序结果不正确".to_string());
            }
            
            Ok(())
        })
    }

    /// 测试搜索算法性能
    pub fn benchmark_search<F>(&self, name: &str, search_fn: F, data_size: usize) -> BenchmarkResult
    where
        F: Fn(&[i32], i32) -> Option<usize>,
    {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let data = self.generate_sorted_data(data_size);
        let target = data[data_size / 2]; // 搜索中间元素
        
        benchmarker.run(name, || {
            match search_fn(&data, target) {
                Some(_) => Ok(()),
                None => Err("搜索失败".to_string()),
            }
        })
    }

    /// 测试数学算法性能
    pub fn benchmark_math<F>(&self, name: &str, math_fn: F, input_size: usize) -> BenchmarkResult
    where
        F: Fn(&[f64]) -> f64,
    {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let data = self.generate_float_data(input_size);
        
        benchmarker.run(name, || {
            let result = math_fn(&data);
            if result.is_nan() || result.is_infinite() {
                return Err("计算结果无效".to_string());
            }
            Ok(())
        })
    }

    /// 生成随机数据
    fn generate_random_data(&self, size: usize) -> Vec<i32> {
        (0..size).map(|_| fastrand::i32(..)).collect()
    }

    /// 生成已排序数据
    fn generate_sorted_data(&self, size: usize) -> Vec<i32> {
        let mut data = self.generate_random_data(size);
        data.sort();
        data
    }

    /// 生成浮点数据
    fn generate_float_data(&self, size: usize) -> Vec<f64> {
        (0..size).map(|_| fastrand::f64()).collect()
    }

    /// 检查数组是否已排序
    fn is_sorted(&self, data: &[i32]) -> bool {
        data.windows(2).all(|w| w[0] <= w[1])
    }
}

/// 内存基准测试
pub struct MemoryBenchmarker;

impl MemoryBenchmarker {
    /// 测试内存分配性能
    pub fn benchmark_allocation(&self, size: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        
        benchmarker.run("内存分配", || {
            let _data = vec![0u8; size];
            Ok(())
        })
    }

    /// 测试内存复制性能
    pub fn benchmark_copy(&self, size: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let data = vec![0u8; size];
        
        benchmarker.run("内存复制", || {
            let _copied = data.clone();
            Ok(())
        })
    }

    /// 测试内存访问模式
    pub fn benchmark_access_pattern(&self, size: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        
        benchmarker.run("顺序访问", move || {
            let mut data = vec![0u8; size];
            for i in 0..size {
                data[i] = i as u8;
            }
            Ok(())
        })
    }
}

/// 并发基准测试
pub struct ConcurrencyBenchmarker;

impl ConcurrencyBenchmarker {
    /// 测试线程创建性能
    pub fn benchmark_thread_creation(&self, num_threads: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        
        benchmarker.run("线程创建", || {
            let mut handles = Vec::new();
            
            for _ in 0..num_threads {
                let handle = thread::spawn(|| {
                    // 简单的计算任务
                    let mut sum = 0;
                    for i in 0..1000 {
                        sum += i;
                    }
                    sum
                });
                handles.push(handle);
            }
            
            for handle in handles {
                let _ = handle.join();
            }
            
            Ok(())
        })
    }

    /// 测试锁性能
    pub fn benchmark_lock_performance(&self, num_threads: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let counter = Arc::new(std::sync::Mutex::new(0));
        
        benchmarker.run_concurrent("锁性能", move || {
            let mut count = counter.lock().unwrap();
            *count += 1;
            Ok(())
        }, num_threads)
    }

    /// 测试无锁性能
    pub fn benchmark_lockfree_performance(&self, num_threads: usize) -> BenchmarkResult {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let counter = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        
        benchmarker.run_concurrent("无锁性能", move || {
            counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Ok(())
        }, num_threads)
    }
}

/// 基准测试套件
pub struct BenchmarkSuite {
    _benchmarker: Benchmarker,
    algorithm_benchmarker: AlgorithmBenchmarker,
    memory_benchmarker: MemoryBenchmarker,
    concurrency_benchmarker: ConcurrencyBenchmarker,
}

impl BenchmarkSuite {
    /// 创建新的基准测试套件
    pub fn new() -> Self {
        Self {
            _benchmarker: Benchmarker::new(BenchmarkConfig::default()),
            algorithm_benchmarker: AlgorithmBenchmarker,
            memory_benchmarker: MemoryBenchmarker,
            concurrency_benchmarker: ConcurrencyBenchmarker,
        }
    }

    /// 运行完整基准测试套件
    pub fn run_full_suite(&mut self) -> String {
        let mut report = String::new();
        report.push_str("=== 完整基准测试套件 ===\n\n");

        // 算法性能测试
        report.push_str("--- 算法性能测试 ---\n");
        let bubble_sort_result = self.algorithm_benchmarker.benchmark_sorting(
            "冒泡排序", 
            |data| {
                for i in 0..data.len() {
                    for j in 0..data.len() - 1 - i {
                        if data[j] > data[j + 1] {
                            data.swap(j, j + 1);
                        }
                    }
                }
            },
            1000
        );
        report.push_str(&format!("冒泡排序: {:?}\n", bubble_sort_result.duration));

        let quick_sort_result = self.algorithm_benchmarker.benchmark_sorting(
            "快速排序",
            |data| {
                data.sort();
            },
            1000
        );
        report.push_str(&format!("快速排序: {:?}\n", quick_sort_result.duration));

        // 内存性能测试
        report.push_str("\n--- 内存性能测试 ---\n");
        let allocation_result = self.memory_benchmarker.benchmark_allocation(1024 * 1024);
        report.push_str(&format!("内存分配: {:?}\n", allocation_result.duration));

        let copy_result = self.memory_benchmarker.benchmark_copy(1024 * 1024);
        report.push_str(&format!("内存复制: {:?}\n", copy_result.duration));

        // 并发性能测试
        report.push_str("\n--- 并发性能测试 ---\n");
        let thread_result = self.concurrency_benchmarker.benchmark_thread_creation(10);
        report.push_str(&format!("线程创建: {:?}\n", thread_result.duration));

        let lock_result = self.concurrency_benchmarker.benchmark_lock_performance(4);
        report.push_str(&format!("锁性能: {:?}\n", lock_result.duration));

        let lockfree_result = self.concurrency_benchmarker.benchmark_lockfree_performance(4);
        report.push_str(&format!("无锁性能: {:?}\n", lockfree_result.duration));

        report
    }
}

impl Default for BenchmarkSuite {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_benchmarker() {
        let mut benchmarker = Benchmarker::new(BenchmarkConfig::default());
        let result = benchmarker.run("测试", || Ok(()));
        
        assert_eq!(result.name, "测试");
        assert_eq!(result.error_count, 0);
    }

    #[test]
    fn test_algorithm_benchmarker() {
        let benchmarker = AlgorithmBenchmarker;
        let result = benchmarker.benchmark_sorting("测试排序", |data| data.sort(), 100);
        
        assert_eq!(result.name, "测试排序");
        assert_eq!(result.error_count, 0);
    }

    #[test]
    fn test_memory_benchmarker() {
        let benchmarker = MemoryBenchmarker;
        let result = benchmarker.benchmark_allocation(1024);
        
        assert_eq!(result.name, "内存分配");
        assert_eq!(result.error_count, 0);
    }

    #[test]
    fn test_concurrency_benchmarker() {
        let benchmarker = ConcurrencyBenchmarker;
        let result = benchmarker.benchmark_thread_creation(2);
        
        assert_eq!(result.name, "线程创建");
        assert_eq!(result.error_count, 0);
    }

    #[test]
    fn test_benchmark_suite() {
        let mut suite = BenchmarkSuite::new();
        let report = suite.run_full_suite();
        
        assert!(report.contains("完整基准测试套件"));
        assert!(report.contains("算法性能测试"));
        assert!(report.contains("内存性能测试"));
        assert!(report.contains("并发性能测试"));
    }
}
