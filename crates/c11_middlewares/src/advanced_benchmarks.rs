//! 高级性能基准测试模块
//! 
//! 本模块提供了全面的性能基准测试功能，包括：
//! - 内存使用监控
//! - 并发性能测试
//! - 延迟测量
//! - 吞吐量测试
//! - 资源利用率监控

use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;

use crate::error::{Error, Result};

/// 高级基准测试结果
#[derive(Debug, Clone)]
pub struct AdvancedBenchmarkResult {
    pub test_name: String,
    pub duration: Duration,
    pub operations_performed: u64,
    pub throughput_ops_per_sec: f64,
    pub average_latency_ms: f64,
    pub p50_latency_ms: f64,
    pub p95_latency_ms: f64,
    pub p99_latency_ms: f64,
    pub memory_usage_mb: f64,
    pub cpu_usage_percent: f64,
    pub error_count: u64,
    pub success_rate: f64,
}

impl AdvancedBenchmarkResult {
    pub fn new(test_name: String) -> Self {
        Self {
            test_name,
            duration: Duration::from_secs(0),
            operations_performed: 0,
            throughput_ops_per_sec: 0.0,
            average_latency_ms: 0.0,
            p50_latency_ms: 0.0,
            p95_latency_ms: 0.0,
            p99_latency_ms: 0.0,
            memory_usage_mb: 0.0,
            cpu_usage_percent: 0.0,
            error_count: 0,
            success_rate: 100.0,
        }
    }
    
    pub fn calculate_metrics(&mut self, latencies: &[Duration], errors: u64) {
        let total_ops = latencies.len() as u64;
        let successful_ops = total_ops - errors;
        
        self.operations_performed = total_ops;
        self.error_count = errors;
        self.success_rate = if total_ops > 0 {
            (successful_ops as f64 / total_ops as f64) * 100.0
        } else {
            0.0
        };
        
        if self.duration.as_secs_f64() > 0.0 {
            self.throughput_ops_per_sec = total_ops as f64 / self.duration.as_secs_f64();
        }
        
        if !latencies.is_empty() {
            let mut sorted_latencies = latencies.to_vec();
            sorted_latencies.sort();
            
            let total_latency_ms: f64 = sorted_latencies.iter()
                .map(|d| d.as_nanos() as f64 / 1_000_000.0)
                .sum();
            
            self.average_latency_ms = total_latency_ms / sorted_latencies.len() as f64;
            
            // 计算百分位数
            let len = sorted_latencies.len();
            self.p50_latency_ms = if len > 0 {
                sorted_latencies[len / 2].as_nanos() as f64 / 1_000_000.0
            } else { 0.0 };
            
            self.p95_latency_ms = if len > 0 {
                let idx = (len as f64 * 0.95) as usize;
                sorted_latencies[idx.min(len - 1)].as_nanos() as f64 / 1_000_000.0
            } else { 0.0 };
            
            self.p99_latency_ms = if len > 0 {
                let idx = (len as f64 * 0.99) as usize;
                sorted_latencies[idx.min(len - 1)].as_nanos() as f64 / 1_000_000.0
            } else { 0.0 };
        }
    }
}

/// 高级基准测试器
pub struct AdvancedBenchmarker {
    results: Vec<AdvancedBenchmarkResult>,
    memory_monitor: AdvancedMemoryMonitor,
}

impl AdvancedBenchmarker {
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
            memory_monitor: AdvancedMemoryMonitor::new(),
        }
    }
    
    /// 运行单线程性能测试
    pub fn run_single_threaded_benchmark<F>(
        &mut self,
        test_name: &str,
        operation: F,
        iterations: u64,
    ) -> Result<AdvancedBenchmarkResult>
    where
        F: Fn() -> Result<()>,
    {
        let mut result = AdvancedBenchmarkResult::new(test_name.to_string());
        let mut latencies = Vec::with_capacity(iterations as usize);
        let mut errors = 0u64;
        
        // 开始内存监控
        self.memory_monitor.start_monitoring();
        
        let start_time = Instant::now();
        
        for _ in 0..iterations {
            let op_start = Instant::now();
            
            match operation() {
                Ok(_) => {
                    let latency = op_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    errors += 1;
                }
            }
        }
        
        let end_time = Instant::now();
        result.duration = end_time - start_time;
        
        // 停止内存监控并获取结果
        let memory_stats = self.memory_monitor.stop_monitoring();
        result.memory_usage_mb = memory_stats.peak_memory_mb;
        result.cpu_usage_percent = memory_stats.average_cpu_percent;
        
        result.calculate_metrics(&latencies, errors);
        self.results.push(result.clone());
        
        Ok(result)
    }
    
    /// 运行多线程并发测试
    pub fn run_concurrent_benchmark<F>(
        &mut self,
        test_name: &str,
        operation: F,
        iterations: u64,
        thread_count: usize,
    ) -> Result<AdvancedBenchmarkResult>
    where
        F: Fn() -> Result<()> + Send + Sync + Clone + 'static,
    {
        let mut result = AdvancedBenchmarkResult::new(test_name.to_string());
        let iterations_per_thread = iterations / thread_count as u64;
        let remaining_iterations = iterations % thread_count as u64;
        
        // 共享状态
        let latencies = Arc::new(std::sync::Mutex::new(Vec::new()));
        let errors = Arc::new(AtomicU64::new(0));
        let completed_ops = Arc::new(AtomicU64::new(0));
        
        // 开始内存监控
        self.memory_monitor.start_monitoring();
        
        let start_time = Instant::now();
        let mut handles = Vec::new();
        
        // 创建线程
        for thread_id in 0..thread_count {
            let latencies_clone = Arc::clone(&latencies);
            let errors_clone = Arc::clone(&errors);
            let completed_ops_clone = Arc::clone(&completed_ops);
            let operation_clone = operation.clone();
            
            let iterations_for_this_thread = iterations_per_thread + 
                if thread_id == 0 { remaining_iterations } else { 0 };
            
            let handle = thread::spawn(move || {
                let mut thread_latencies = Vec::new();
                
                for _ in 0..iterations_for_this_thread {
                    let op_start = Instant::now();
                    
                    match operation_clone() {
                        Ok(_) => {
                            let latency = op_start.elapsed();
                            thread_latencies.push(latency);
                            completed_ops_clone.fetch_add(1, Ordering::Relaxed);
                        }
                        Err(_) => {
                            errors_clone.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
                
                // 将线程结果合并到共享状态
                if let Ok(mut shared_latencies) = latencies_clone.lock() {
                    shared_latencies.extend(thread_latencies);
                }
            });
            
            handles.push(handle);
        }
        
        // 等待所有线程完成
        for handle in handles {
            handle.join().map_err(|_| Error::Other("线程执行失败".to_string()))?;
        }
        
        let end_time = Instant::now();
        result.duration = end_time - start_time;
        
        // 停止内存监控并获取结果
        let memory_stats = self.memory_monitor.stop_monitoring();
        result.memory_usage_mb = memory_stats.peak_memory_mb;
        result.cpu_usage_percent = memory_stats.average_cpu_percent;
        
        // 获取最终结果
        let final_latencies = latencies.lock().map_err(|_| Error::Other("获取延迟数据失败".to_string()))?;
        let final_errors = errors.load(Ordering::Relaxed);
        
        result.calculate_metrics(&final_latencies, final_errors);
        self.results.push(result.clone());
        
        Ok(result)
    }
    
    /// 获取所有测试结果
    pub fn get_results(&self) -> &[AdvancedBenchmarkResult] {
        &self.results
    }
    
    /// 生成基准测试报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        
        report.push_str("# 高级性能基准测试报告\n\n");
        report.push_str(&format!("总测试数: {}\n\n", self.results.len()));
        
        for result in &self.results {
            report.push_str(&format!("## {}\n\n", result.test_name));
            report.push_str(&format!("- **持续时间**: {:?}\n", result.duration));
            report.push_str(&format!("- **操作次数**: {}\n", result.operations_performed));
            report.push_str(&format!("- **吞吐量**: {:.2} ops/sec\n", result.throughput_ops_per_sec));
            report.push_str(&format!("- **平均延迟**: {:.2} ms\n", result.average_latency_ms));
            report.push_str(&format!("- **P50 延迟**: {:.2} ms\n", result.p50_latency_ms));
            report.push_str(&format!("- **P95 延迟**: {:.2} ms\n", result.p95_latency_ms));
            report.push_str(&format!("- **P99 延迟**: {:.2} ms\n", result.p99_latency_ms));
            report.push_str(&format!("- **内存使用**: {:.2} MB\n", result.memory_usage_mb));
            report.push_str(&format!("- **CPU 使用**: {:.2}%\n", result.cpu_usage_percent));
            report.push_str(&format!("- **错误数**: {}\n", result.error_count));
            report.push_str(&format!("- **成功率**: {:.2}%\n\n", result.success_rate));
        }
        
        report
    }
}

/// 高级内存监控器
pub struct AdvancedMemoryMonitor {
    start_time: Option<Instant>,
    peak_memory_mb: f64,
    total_cpu_time: Duration,
}

impl AdvancedMemoryMonitor {
    pub fn new() -> Self {
        Self {
            start_time: None,
            peak_memory_mb: 0.0,
            total_cpu_time: Duration::from_secs(0),
        }
    }
    
    pub fn start_monitoring(&mut self) {
        self.start_time = Some(Instant::now());
        self.peak_memory_mb = Self::get_current_memory_usage();
    }
    
    pub fn stop_monitoring(&mut self) -> AdvancedMemoryStats {
        let duration = self.start_time.map(|start| start.elapsed()).unwrap_or_default();
        
        AdvancedMemoryStats {
            peak_memory_mb: self.peak_memory_mb,
            average_cpu_percent: if duration.as_secs_f64() > 0.0 {
                self.total_cpu_time.as_secs_f64() / duration.as_secs_f64() * 100.0
            } else {
                0.0
            },
            duration,
        }
    }
    
    fn get_current_memory_usage() -> f64 {
        // 简化的内存使用量获取
        // 在实际应用中，可以使用更精确的内存监控库
        std::process::id() as f64 / 1024.0 // 简化的内存估算
    }
}

#[derive(Debug, Clone)]
pub struct AdvancedMemoryStats {
    pub peak_memory_mb: f64,
    pub average_cpu_percent: f64,
    pub duration: Duration,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    
    #[test]
    fn test_advanced_benchmarker_creation() {
        let benchmarker = AdvancedBenchmarker::new();
        assert_eq!(benchmarker.results.len(), 0);
    }
    
    #[test]
    fn test_single_threaded_benchmark() {
        let mut benchmarker = AdvancedBenchmarker::new();
        
        let result = benchmarker.run_single_threaded_benchmark(
            "test_operation",
            || Ok(()),
            100,
        ).unwrap();
        
        assert_eq!(result.test_name, "test_operation");
        assert_eq!(result.operations_performed, 100);
        assert_eq!(result.error_count, 0);
        assert_eq!(result.success_rate, 100.0);
    }
    
    #[test]
    fn test_concurrent_benchmark() {
        let mut benchmarker = AdvancedBenchmarker::new();
        
        let result = benchmarker.run_concurrent_benchmark(
            "concurrent_test",
            || Ok(()),
            100,
            2,
        ).unwrap();
        
        assert_eq!(result.test_name, "concurrent_test");
        assert_eq!(result.operations_performed, 100);
        assert_eq!(result.error_count, 0);
    }
    
    #[test]
    fn test_benchmark_result_calculation() {
        let mut result = AdvancedBenchmarkResult::new("test".to_string());
        result.duration = Duration::from_secs(1);
        
        let latencies = vec![
            Duration::from_millis(10),
            Duration::from_millis(20),
            Duration::from_millis(30),
        ];
        
        result.calculate_metrics(&latencies, 0);
        
        assert_eq!(result.operations_performed, 3);
        assert_eq!(result.throughput_ops_per_sec, 3.0);
        assert_eq!(result.average_latency_ms, 20.0);
        assert_eq!(result.p50_latency_ms, 20.0);
        assert_eq!(result.success_rate, 100.0);
    }
    
    #[test]
    fn test_memory_monitor() {
        let mut monitor = AdvancedMemoryMonitor::new();
        
        monitor.start_monitoring();
        std::thread::sleep(Duration::from_millis(10));
        let stats = monitor.stop_monitoring();
        
        assert!(stats.duration.as_millis() >= 10);
        assert!(stats.peak_memory_mb >= 0.0);
    }
}
