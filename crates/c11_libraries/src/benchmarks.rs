//! 性能基准测试模块
//! 
//! 本模块提供了基于 Rust 1.90 特性的性能基准测试功能：
//! - 常量泛型优化的基准测试
//! - 异步性能测试
//! - 内存使用分析
//! - 并发性能测试

// use crate::prelude::*;
use crate::error::Result;
use std::time::{Duration, Instant};
use std::sync::Arc;
#[cfg(feature = "tokio")]
use std::sync::atomic::{AtomicUsize, Ordering};

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub operation_name: String,
    pub total_operations: usize,
    pub total_duration: Duration,
    pub operations_per_second: f64,
    pub average_latency_ms: f64,
    pub min_latency_ms: f64,
    pub max_latency_ms: f64,
    pub p50_latency_ms: f64,
    pub p95_latency_ms: f64,
    pub p99_latency_ms: f64,
}

impl BenchmarkResult {
    pub fn new(operation_name: String) -> Self {
        Self {
            operation_name,
            total_operations: 0,
            total_duration: Duration::ZERO,
            operations_per_second: 0.0,
            average_latency_ms: 0.0,
            min_latency_ms: 0.0,
            max_latency_ms: 0.0,
            p50_latency_ms: 0.0,
            p95_latency_ms: 0.0,
            p99_latency_ms: 0.0,
        }
    }
    
    pub fn calculate_stats(&mut self, latencies: &[f64]) {
        if latencies.is_empty() {
            return;
        }
        
        let mut sorted_latencies = latencies.to_vec();
        sorted_latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        self.total_operations = latencies.len();
        self.average_latency_ms = latencies.iter().sum::<f64>() / latencies.len() as f64;
        self.min_latency_ms = *sorted_latencies.first().unwrap();
        self.max_latency_ms = *sorted_latencies.last().unwrap();
        
        // 计算百分位数
        self.p50_latency_ms = self.calculate_percentile(&sorted_latencies, 50.0);
        self.p95_latency_ms = self.calculate_percentile(&sorted_latencies, 95.0);
        self.p99_latency_ms = self.calculate_percentile(&sorted_latencies, 99.0);
        
        // 计算每秒操作数
        if self.total_duration.as_secs_f64() > 0.0 {
            self.operations_per_second = self.total_operations as f64 / self.total_duration.as_secs_f64();
        }
    }
    
    fn calculate_percentile(&self, sorted_data: &[f64], percentile: f64) -> f64 {
        if sorted_data.is_empty() {
            return 0.0;
        }
        
        let index = (percentile / 100.0) * (sorted_data.len() - 1) as f64;
        let lower = index.floor() as usize;
        let upper = index.ceil() as usize;
        
        if lower == upper {
            sorted_data[lower]
        } else {
            let weight = index - lower as f64;
            sorted_data[lower] * (1.0 - weight) + sorted_data[upper] * weight
        }
    }
    
    pub fn format_report(&self) -> String {
        format!(
            "=== {} 基准测试结果 ===\n\
            总操作数: {}\n\
            总耗时: {:?}\n\
            每秒操作数: {:.2} ops/sec\n\
            平均延迟: {:.2} ms\n\
            最小延迟: {:.2} ms\n\
            最大延迟: {:.2} ms\n\
            P50 延迟: {:.2} ms\n\
            P95 延迟: {:.2} ms\n\
            P99 延迟: {:.2} ms\n",
            self.operation_name,
            self.total_operations,
            self.total_duration,
            self.operations_per_second,
            self.average_latency_ms,
            self.min_latency_ms,
            self.max_latency_ms,
            self.p50_latency_ms,
            self.p95_latency_ms,
            self.p99_latency_ms
        )
    }
}

/// Rust 1.90 特性：使用常量泛型优化的基准测试器
/// 
/// 通过常量泛型参数提供编译时优化的基准测试框架
pub struct OptimizedBenchmarker<const BUFFER_SIZE: usize = 10000> {
    results: Vec<BenchmarkResult>,
    #[allow(dead_code)]
    current_latencies: Vec<f64>,
    #[allow(dead_code)]
    buffer_size: usize,
}

impl<const BUFFER_SIZE: usize> OptimizedBenchmarker<BUFFER_SIZE> {
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
            current_latencies: Vec::with_capacity(BUFFER_SIZE),
            buffer_size: BUFFER_SIZE,
        }
    }
    
    /// 使用常量推断创建指定大小的基准测试器
    pub fn with_buffer_size<const NEW_SIZE: usize>(_size: usize) -> OptimizedBenchmarker<NEW_SIZE> {
        OptimizedBenchmarker::new()
    }
    
    /// 运行基准测试
    pub async fn run_benchmark<F, Fut>(
        &mut self,
        operation_name: String,
        operation: F,
        iterations: usize,
        concurrency: usize,
    ) -> Result<&BenchmarkResult>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: std::future::Future<Output = Result<Vec<u8>>> + Send,
    {
        println!("开始基准测试: {}, 迭代次数: {}, 并发数: {}", operation_name, iterations, concurrency);
        
        let start_time = Instant::now();
        let latencies = self.run_concurrent_benchmark(operation, iterations, concurrency).await?;
        let total_duration = start_time.elapsed();
        
        let mut result = BenchmarkResult::new(operation_name);
        result.total_duration = total_duration;
        result.calculate_stats(&latencies);
        
        self.results.push(result);
        Ok(self.results.last().unwrap())
    }
    
    async fn run_concurrent_benchmark<F, Fut>(
        &mut self,
        operation: F,
        iterations: usize,
        _concurrency: usize,
    ) -> Result<Vec<f64>>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: std::future::Future<Output = Result<Vec<u8>>> + Send,
    {
        let latencies = Arc::new(std::sync::Mutex::new(Vec::with_capacity(iterations)));
        #[cfg(feature = "tokio")]
        let completed = Arc::new(AtomicUsize::new(0));
        
        #[cfg(feature = "tokio")]
        {
            let mut handles = Vec::new();
            
            for _ in 0.._concurrency {
                let operation = operation.clone();
                let latencies = Arc::clone(&latencies);
                let completed = Arc::clone(&completed);
                
                let handle = tokio::spawn(async move {
                    loop {
                        let current = completed.fetch_add(1, Ordering::Relaxed);
                        if current >= iterations {
                            break;
                        }
                        
                        let start = Instant::now();
                        match operation().await {
                            Ok(_) => {
                                let duration = start.elapsed();
                                let latency_ms = duration.as_secs_f64() * 1000.0;
                                
                                if let Ok(mut latencies_vec) = latencies.lock() {
                                    latencies_vec.push(latency_ms);
                                }
                            }
                            Err(_) => {
                                // 记录错误，但不影响基准测试
                                if let Ok(mut latencies_vec) = latencies.lock() {
                                    latencies_vec.push(0.0);
                                }
                            }
                        }
                    }
                });
                
                handles.push(handle);
            }
            
            // 等待所有任务完成
            for handle in handles {
                let _ = handle.await;
            }
        }
        
        #[cfg(not(feature = "tokio"))]
        {
            // 同步版本的基准测试
            for _ in 0..iterations {
                let start = Instant::now();
                match operation().await {
                    Ok(_) => {
                        let duration = start.elapsed();
                        let latency_ms = duration.as_secs_f64() * 1000.0;
                        
                        if let Ok(mut latencies_vec) = latencies.lock() {
                            latencies_vec.push(latency_ms);
                        }
                    }
                    Err(_) => {
                        if let Ok(mut latencies_vec) = latencies.lock() {
                            latencies_vec.push(0.0);
                        }
                    }
                }
            }
        }
        
        let latencies_vec = latencies.lock().unwrap();
        Ok(latencies_vec.clone())
    }
    
    /// 获取所有基准测试结果
    pub fn get_results(&self) -> &[BenchmarkResult] {
        &self.results
    }
    
    /// 生成综合报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 综合基准测试报告 ===\n\n");
        
        for result in &self.results {
            report.push_str(&result.format_report());
            report.push_str("\n");
        }
        
        report
    }
}

/// 内存使用监控器
/// 
/// 使用常量泛型优化内存监控数据结构
pub struct MemoryMonitor<const SAMPLE_COUNT: usize = 1000> {
    samples: [MemorySample; SAMPLE_COUNT],
    current_index: usize,
    total_samples: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct MemorySample {
    pub timestamp: Instant,
    pub allocated_bytes: usize,
    pub used_bytes: usize,
    pub peak_bytes: usize,
}

impl<const SAMPLE_COUNT: usize> MemoryMonitor<SAMPLE_COUNT> {
    pub fn new() -> Self {
        Self {
            samples: [MemorySample {
                timestamp: Instant::now(),
                allocated_bytes: 0,
                used_bytes: 0,
                peak_bytes: 0,
            }; SAMPLE_COUNT],
            current_index: 0,
            total_samples: 0,
        }
    }
    
    /// 使用常量推断创建指定大小的内存监控器
    pub fn with_capacity<const NEW_SIZE: usize>(_size: usize) -> MemoryMonitor<NEW_SIZE> {
        MemoryMonitor::new()
    }
    
    pub fn record_sample(&mut self, allocated_bytes: usize, used_bytes: usize, peak_bytes: usize) {
        self.samples[self.current_index] = MemorySample {
            timestamp: Instant::now(),
            allocated_bytes,
            used_bytes,
            peak_bytes,
        };
        
        self.current_index = (self.current_index + 1) % SAMPLE_COUNT;
        self.total_samples += 1;
    }
    
    pub fn get_memory_stats(&self) -> MemoryStats {
        let samples = &self.samples[..self.total_samples.min(SAMPLE_COUNT)];
        
        if samples.is_empty() {
            return MemoryStats::default();
        }
        
        let avg_allocated = samples.iter().map(|s| s.allocated_bytes).sum::<usize>() as f64 / samples.len() as f64;
        let avg_used = samples.iter().map(|s| s.used_bytes).sum::<usize>() as f64 / samples.len() as f64;
        let max_peak = samples.iter().map(|s| s.peak_bytes).max().unwrap_or(0);
        
        MemoryStats {
            average_allocated_bytes: avg_allocated,
            average_used_bytes: avg_used,
            peak_memory_bytes: max_peak,
            total_samples: self.total_samples,
        }
    }
}

#[derive(Debug, Default)]
pub struct MemoryStats {
    pub average_allocated_bytes: f64,
    pub average_used_bytes: f64,
    pub peak_memory_bytes: usize,
    pub total_samples: usize,
}

/// 并发性能测试器
/// 
/// 测试不同并发级别下的性能表现
pub struct ConcurrencyBenchmarker {
    base_operations: usize,
    concurrency_levels: Vec<usize>,
}

impl ConcurrencyBenchmarker {
    pub fn new(base_operations: usize) -> Self {
        Self {
            base_operations,
            concurrency_levels: vec![1, 2, 4, 8, 16, 32, 64],
        }
    }
    
    pub fn with_concurrency_levels(mut self, levels: Vec<usize>) -> Self {
        self.concurrency_levels = levels;
        self
    }
    
    /// 运行并发基准测试
    pub async fn run_concurrency_benchmark<F, Fut>(
        &self,
        operation_name: String,
        operation: F,
    ) -> Result<Vec<BenchmarkResult>>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: std::future::Future<Output = Result<Vec<u8>>> + Send,
    {
        let mut results = Vec::new();
        
        for &concurrency in &self.concurrency_levels {
            let mut benchmarker = OptimizedBenchmarker::<10000>::new();
            let operation_name = format!("{} (并发: {})", operation_name, concurrency);
            
            let result = benchmarker.run_benchmark(
                operation_name,
                operation.clone(),
                self.base_operations,
                concurrency,
            ).await?;
            
            results.push(result.clone());
        }
        
        Ok(results)
    }
    
    /// 生成并发性能报告
    pub fn generate_concurrency_report(&self, results: &[BenchmarkResult]) -> String {
        let mut report = String::new();
        report.push_str("=== 并发性能测试报告 ===\n");
        report.push_str("并发数\t每秒操作数\t平均延迟(ms)\tP95延迟(ms)\tP99延迟(ms)\n");
        
        for result in results {
            let concurrency = result.operation_name
                .split("并发: ")
                .nth(1)
                .unwrap_or("1")
                .trim_end_matches(')');
            
            report.push_str(&format!(
                "{}\t{:.2}\t\t{:.2}\t\t{:.2}\t\t{:.2}\n",
                concurrency,
                result.operations_per_second,
                result.average_latency_ms,
                result.p95_latency_ms,
                result.p99_latency_ms
            ));
        }
        
        report
    }
}

/// 基准测试套件
/// 
/// 整合所有基准测试功能
pub struct BenchmarkSuite {
    benchmarker: OptimizedBenchmarker<10000>,
    memory_monitor: MemoryMonitor<1000>,
    concurrency_benchmarker: ConcurrencyBenchmarker,
}

impl BenchmarkSuite {
    pub fn new() -> Self {
        Self {
            benchmarker: OptimizedBenchmarker::new(),
            memory_monitor: MemoryMonitor::new(),
            concurrency_benchmarker: ConcurrencyBenchmarker::new(1000),
        }
    }
    
    /// 运行完整的基准测试套件
    pub async fn run_full_suite(&mut self) -> Result<String> {
        let mut report = String::new();
        report.push_str("=== c11_libraries 完整基准测试套件 ===\n\n");
        
        // 1. 基础性能测试
        report.push_str("--- 基础性能测试 ---\n");
        
        // 模拟 Redis 操作
        let redis_result = self.benchmarker.run_benchmark(
            "Redis SET/GET".to_string(),
            || async {
                // 模拟 Redis 操作
                #[cfg(feature = "tokio")]
                tokio::time::sleep(Duration::from_millis(1)).await;
                #[cfg(not(feature = "tokio"))]
                std::thread::sleep(Duration::from_millis(1));
                Ok(b"redis_result".to_vec())
            },
            10000,
            10,
        ).await?;
        
        report.push_str(&redis_result.format_report());
        report.push_str("\n");
        
        // 模拟 PostgreSQL 操作
        let postgres_result = self.benchmarker.run_benchmark(
            "PostgreSQL INSERT/SELECT".to_string(),
            || async {
                // 模拟 PostgreSQL 操作
                #[cfg(feature = "tokio")]
                tokio::time::sleep(Duration::from_millis(5)).await;
                #[cfg(not(feature = "tokio"))]
                std::thread::sleep(Duration::from_millis(5));
                Ok(b"postgres_result".to_vec())
            },
            5000,
            5,
        ).await?;
        
        report.push_str(&postgres_result.format_report());
        report.push_str("\n");
        
        // 2. 并发性能测试
        report.push_str("--- 并发性能测试 ---\n");
        
        let concurrency_results = self.concurrency_benchmarker.run_concurrency_benchmark(
            "Redis 操作".to_string(),
            || async {
                #[cfg(feature = "tokio")]
                tokio::time::sleep(Duration::from_millis(1)).await;
                #[cfg(not(feature = "tokio"))]
                std::thread::sleep(Duration::from_millis(1));
                Ok(b"concurrent_result".to_vec())
            },
        ).await?;
        
        report.push_str(&self.concurrency_benchmarker.generate_concurrency_report(&concurrency_results));
        report.push_str("\n");
        
        // 3. 内存使用分析
        report.push_str("--- 内存使用分析 ---\n");
        
        // 模拟内存使用
        for i in 0..100 {
            let allocated = 1024 * (i + 1);
            let used = allocated * 80 / 100; // 80% 使用率
            let peak = allocated;
            
            self.memory_monitor.record_sample(allocated, used, peak);
        }
        
        let memory_stats = self.memory_monitor.get_memory_stats();
        report.push_str(&format!(
            "平均分配内存: {:.2} KB\n\
            平均使用内存: {:.2} KB\n\
            峰值内存使用: {} KB\n\
            样本数: {}\n",
            memory_stats.average_allocated_bytes / 1024.0,
            memory_stats.average_used_bytes / 1024.0,
            memory_stats.peak_memory_bytes / 1024,
            memory_stats.total_samples
        ));
        
        report.push_str("\n=== 基准测试套件完成 ===\n");
        
        Ok(report)
    }
    
    /// 获取基准测试结果
    pub fn get_benchmark_results(&self) -> &[BenchmarkResult] {
        self.benchmarker.get_results()
    }
    
    /// 获取内存统计
    pub fn get_memory_stats(&self) -> MemoryStats {
        self.memory_monitor.get_memory_stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn test_benchmark_result() {
        let mut result = BenchmarkResult::new("test_operation".to_string());
        let latencies = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        
        result.total_duration = Duration::from_millis(100);
        result.calculate_stats(&latencies);
        
        assert_eq!(result.total_operations, 5);
        assert_eq!(result.average_latency_ms, 3.0);
        assert_eq!(result.min_latency_ms, 1.0);
        assert_eq!(result.max_latency_ms, 5.0);
    }
    
    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn test_optimized_benchmarker() {
        let mut benchmarker = OptimizedBenchmarker::<100>::new();
        
        let result = benchmarker.run_benchmark(
            "test_operation".to_string(),
            || async {
                #[cfg(feature = "tokio")]
                tokio::time::sleep(Duration::from_millis(1)).await;
                #[cfg(not(feature = "tokio"))]
                std::thread::sleep(Duration::from_millis(1));
                Ok(b"test_result".to_vec())
            },
            10,
            2,
        ).await.unwrap();
        
        assert_eq!(result.operation_name, "test_operation");
        assert!(result.total_operations > 0);
    }
    
    #[test]
    fn test_memory_monitor() {
        let mut monitor = MemoryMonitor::<10>::new();
        
        monitor.record_sample(1024, 512, 1024);
        monitor.record_sample(2048, 1024, 2048);
        
        let stats = monitor.get_memory_stats();
        assert_eq!(stats.total_samples, 2);
        assert!(stats.average_allocated_bytes > 0.0);
    }
}
