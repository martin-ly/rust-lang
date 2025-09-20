//! 性能基准测试模块
//!
//! 本模块提供了各种设计模式的性能基准测试

use std::sync::Arc;
use std::time::Instant;

/// 单例模式性能测试
pub struct SingletonBenchmark {
    iterations: usize,
}

impl SingletonBenchmark {
    pub fn new(iterations: usize) -> Self {
        Self { iterations }
    }

    /// 测试单例模式的获取性能
    pub fn benchmark_singleton_access(&self) -> f64 {
        use crate::creational::singleton::define::Singleton;

        let singleton = Singleton::new();
        let start = Instant::now();

        for _ in 0..self.iterations {
            let _instance = singleton.get_instance(|| "benchmark instance".to_string());
        }

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }

    /// 测试单例模式的线程安全性能
    pub fn benchmark_singleton_thread_safety(&self) -> f64 {
        use crate::creational::singleton::define::Singleton;
        use std::thread;

        let singleton = Arc::new(Singleton::new());
        let start = Instant::now();

        let mut handles = vec![];
        let threads = 4;
        let iterations_per_thread = self.iterations / threads;

        for _ in 0..threads {
            let singleton_clone = Arc::clone(&singleton);
            let handle = thread::spawn(move || {
                for _ in 0..iterations_per_thread {
                    let _instance =
                        singleton_clone.get_instance(|| "thread safe instance".to_string());
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }
}

/// 享元模式性能测试
pub struct FlyweightBenchmark {
    iterations: usize,
}

impl FlyweightBenchmark {
    pub fn new(iterations: usize) -> Self {
        Self { iterations }
    }

    /// 测试享元模式的创建性能
    pub fn benchmark_flyweight_creation(&self) -> f64 {
        use crate::structural::flyweight::define::OptimizedFlyweightFactory;

        let mut factory = OptimizedFlyweightFactory::new();
        let start = Instant::now();

        for i in 0..self.iterations {
            let _flyweight = factory.get_flyweight(
                &format!("key_{}", i % 10), // 重用前10个键
                format!("state_{}", i),
            );
        }

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }

    /// 测试享元模式的批量创建性能
    pub fn benchmark_flyweight_batch_creation(&self) -> f64 {
        use crate::structural::flyweight::define::OptimizedFlyweightFactory;

        let mut factory = OptimizedFlyweightFactory::new();
        let batch_size = 100;
        let batches = self.iterations / batch_size;

        let start = Instant::now();

        for batch in 0..batches {
            let specs: Vec<(String, String)> = (0..batch_size)
                .map(|i| {
                    let key = format!("batch_{}_key_{}", batch, i % 10);
                    let state = format!("batch_{}_state_{}", batch, i);
                    (key, state)
                })
                .collect();

            let _flyweights = factory.batch_create_flyweights(&specs);
        }

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }
}

/// 代理模式性能测试
pub struct ProxyBenchmark {
    iterations: usize,
}

impl ProxyBenchmark {
    pub fn new(iterations: usize) -> Self {
        Self { iterations }
    }

    /// 测试代理模式的请求处理性能
    pub fn benchmark_proxy_requests(&self) -> f64 {
        use crate::structural::proxy::define::{Proxy, RealSubject, Subject};

        let real_subject = RealSubject::new(1);
        let proxy = Proxy::new(real_subject);
        let start = Instant::now();

        for _ in 0..self.iterations {
            proxy.request();
        }

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }
}

/// 并行模式性能测试
pub struct ParallelBenchmark {
    data_size: usize,
}

impl ParallelBenchmark {
    pub fn new(data_size: usize) -> Self {
        Self { data_size }
    }

    /// 测试并行归约性能
    pub fn benchmark_parallel_reduction(&self) -> f64 {
        use crate::parallel::parallel_reduction::define::parallel_reduction;

        let data: Vec<i32> = (0..self.data_size as i32).collect();
        let start = Instant::now();

        let _result = parallel_reduction(&data, |a, b| a + b);

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }

    /// 测试数据并行处理性能
    pub fn benchmark_data_parallelism(&self) -> f64 {
        use crate::parallel::data_parrallelism::define::parallel_process;

        let mut data: Vec<i32> = (0..self.data_size as i32).collect();
        let start = Instant::now();

        parallel_process(&mut data, |&x| {
            // 简单的处理操作
            let _ = x * 2;
        });

        let duration = start.elapsed();
        duration.as_secs_f64() * 1000.0 // 转换为毫秒
    }
}

/// 综合性能测试套件
pub struct PerformanceTestSuite {
    singleton_benchmark: SingletonBenchmark,
    flyweight_benchmark: FlyweightBenchmark,
    proxy_benchmark: ProxyBenchmark,
    parallel_benchmark: ParallelBenchmark,
}

impl Default for PerformanceTestSuite {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceTestSuite {
    pub fn new() -> Self {
        Self {
            singleton_benchmark: SingletonBenchmark::new(10000),
            flyweight_benchmark: FlyweightBenchmark::new(1000),
            proxy_benchmark: ProxyBenchmark::new(1000),
            parallel_benchmark: ParallelBenchmark::new(100000),
        }
    }

    /// 运行所有性能测试
    pub fn run_all_benchmarks(&self) -> BenchmarkResults {
        println!("开始运行性能基准测试...");

        let singleton_access = self.singleton_benchmark.benchmark_singleton_access();
        println!("单例模式访问性能: {:.2} ms", singleton_access);

        let singleton_thread_safety = self.singleton_benchmark.benchmark_singleton_thread_safety();
        println!("单例模式线程安全性能: {:.2} ms", singleton_thread_safety);

        let flyweight_creation = self.flyweight_benchmark.benchmark_flyweight_creation();
        println!("享元模式创建性能: {:.2} ms", flyweight_creation);

        let flyweight_batch = self
            .flyweight_benchmark
            .benchmark_flyweight_batch_creation();
        println!("享元模式批量创建性能: {:.2} ms", flyweight_batch);

        let proxy_requests = self.proxy_benchmark.benchmark_proxy_requests();
        println!("代理模式请求性能: {:.2} ms", proxy_requests);

        let parallel_reduction = self.parallel_benchmark.benchmark_parallel_reduction();
        println!("并行归约性能: {:.2} ms", parallel_reduction);

        let data_parallelism = self.parallel_benchmark.benchmark_data_parallelism();
        println!("数据并行处理性能: {:.2} ms", data_parallelism);

        BenchmarkResults {
            singleton_access,
            singleton_thread_safety,
            flyweight_creation,
            flyweight_batch,
            proxy_requests,
            parallel_reduction,
            data_parallelism,
        }
    }
}

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResults {
    pub singleton_access: f64,
    pub singleton_thread_safety: f64,
    pub flyweight_creation: f64,
    pub flyweight_batch: f64,
    pub proxy_requests: f64,
    pub parallel_reduction: f64,
    pub data_parallelism: f64,
}

impl BenchmarkResults {
    /// 生成性能报告
    pub fn generate_report(&self) -> String {
        format!(
            "=== 设计模式性能基准测试报告 ===\n\
            单例模式访问性能: {:.2} ms\n\
            单例模式线程安全性能: {:.2} ms\n\
            享元模式创建性能: {:.2} ms\n\
            享元模式批量创建性能: {:.2} ms\n\
            代理模式请求性能: {:.2} ms\n\
            并行归约性能: {:.2} ms\n\
            数据并行处理性能: {:.2} ms\n\
            =================================",
            self.singleton_access,
            self.singleton_thread_safety,
            self.flyweight_creation,
            self.flyweight_batch,
            self.proxy_requests,
            self.parallel_reduction,
            self.data_parallelism
        )
    }

    /// 检查性能是否满足要求
    pub fn check_performance_requirements(&self) -> bool {
        // 性能要求：
        // - 单例模式访问 < 1ms
        // - 享元模式创建 < 10ms
        // - 代理模式请求 < 20ms
        // - 并行归约 < 5ms

        self.singleton_access < 1.0
            && self.flyweight_creation < 10.0
            && self.proxy_requests < 20.0
            && self.parallel_reduction < 5.0
    }
}

/// 运行性能测试的便捷函数
pub fn run_performance_tests() -> BenchmarkResults {
    let test_suite = PerformanceTestSuite::new();
    test_suite.run_all_benchmarks()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton_benchmark() {
        let benchmark = SingletonBenchmark::new(1000);
        let result = benchmark.benchmark_singleton_access();
        assert!(result > 0.0);
    }

    #[test]
    fn test_flyweight_benchmark() {
        let benchmark = FlyweightBenchmark::new(100);
        let result = benchmark.benchmark_flyweight_creation();
        assert!(result > 0.0);
    }

    #[test]
    fn test_proxy_benchmark() {
        let benchmark = ProxyBenchmark::new(100);
        let result = benchmark.benchmark_proxy_requests();
        assert!(result > 0.0);
    }

    #[test]
    fn test_parallel_benchmark() {
        let benchmark = ParallelBenchmark::new(1000);
        let result = benchmark.benchmark_parallel_reduction();
        assert!(result > 0.0);
    }

    #[test]
    fn test_performance_test_suite() {
        let test_suite = PerformanceTestSuite::new();
        let results = test_suite.run_all_benchmarks();

        // 检查所有结果都是正数
        assert!(results.singleton_access > 0.0);
        assert!(results.singleton_thread_safety > 0.0);
        assert!(results.flyweight_creation > 0.0);
        assert!(results.flyweight_batch > 0.0);
        assert!(results.proxy_requests > 0.0);
        assert!(results.parallel_reduction > 0.0);
        assert!(results.data_parallelism > 0.0);
    }

    #[test]
    fn test_benchmark_results_report() {
        let results = BenchmarkResults {
            singleton_access: 0.5,
            singleton_thread_safety: 1.0,
            flyweight_creation: 5.0,
            flyweight_batch: 3.0,
            proxy_requests: 10.0,
            parallel_reduction: 2.0,
            data_parallelism: 1.5,
        };

        let report = results.generate_report();
        assert!(report.contains("设计模式性能基准测试报告"));
        assert!(report.contains("0.50 ms"));
    }

    #[test]
    fn test_performance_requirements() {
        let good_results = BenchmarkResults {
            singleton_access: 0.5,
            singleton_thread_safety: 1.0,
            flyweight_creation: 5.0,
            flyweight_batch: 3.0,
            proxy_requests: 10.0,
            parallel_reduction: 2.0,
            data_parallelism: 1.5,
        };

        assert!(good_results.check_performance_requirements());

        let bad_results = BenchmarkResults {
            singleton_access: 2.0, // 超过要求
            singleton_thread_safety: 1.0,
            flyweight_creation: 5.0,
            flyweight_batch: 3.0,
            proxy_requests: 10.0,
            parallel_reduction: 2.0,
            data_parallelism: 1.5,
        };

        assert!(!bad_results.check_performance_requirements());
    }
}
