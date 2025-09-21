//! 性能基准测试模块
//! 
//! 提供全面的性能基准测试、对比分析和性能优化建议

use std::collections::HashMap;
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use thiserror::Error;

/// 基准测试类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BenchmarkType {
    /// 延迟测试
    Latency,
    /// 吞吐量测试
    Throughput,
    /// 内存使用测试
    MemoryUsage,
    /// CPU使用测试
    CpuUsage,
    /// 并发测试
    Concurrency,
    /// 压力测试
    Stress,
    /// 稳定性测试
    Stability,
}

/// 基准测试配置
#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    /// 测试类型
    pub benchmark_type: BenchmarkType,
    /// 测试持续时间
    pub duration: Duration,
    /// 并发数
    pub concurrency: u32,
    /// 测试数据大小
    pub data_size: usize,
    /// 是否启用详细统计
    pub detailed_stats: bool,
    /// 采样间隔
    pub sampling_interval: Duration,
    /// 预热时间
    pub warmup_duration: Duration,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            benchmark_type: BenchmarkType::Latency,
            duration: Duration::from_secs(60),
            concurrency: 1,
            data_size: 1024,
            detailed_stats: true,
            sampling_interval: Duration::from_millis(100),
            warmup_duration: Duration::from_secs(5),
        }
    }
}

/// 基准测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    /// 测试名称
    pub name: String,
    /// 测试类型
    pub benchmark_type: BenchmarkType,
    /// 开始时间
    pub start_time: DateTime<Utc>,
    /// 结束时间
    pub end_time: DateTime<Utc>,
    /// 总执行时间
    pub total_duration: Duration,
    /// 操作总数
    pub total_operations: u64,
    /// 成功操作数
    pub successful_operations: u64,
    /// 失败操作数
    pub failed_operations: u64,
    /// 平均延迟
    pub avg_latency: Duration,
    /// 最小延迟
    pub min_latency: Duration,
    /// 最大延迟
    pub max_latency: Duration,
    /// 95%分位延迟
    pub p95_latency: Duration,
    /// 99%分位延迟
    pub p99_latency: Duration,
    /// 吞吐量 (操作/秒)
    pub throughput: f64,
    /// 平均内存使用 (字节)
    pub avg_memory_usage: u64,
    /// 峰值内存使用 (字节)
    pub peak_memory_usage: u64,
    /// 平均CPU使用率 (%)
    pub avg_cpu_usage: f64,
    /// 峰值CPU使用率 (%)
    pub peak_cpu_usage: f64,
    /// 错误率 (%)
    pub error_rate: f64,
    /// 详细统计信息
    pub detailed_stats: Option<DetailedStats>,
}

/// 详细统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetailedStats {
    /// 延迟分布
    pub latency_distribution: HashMap<String, u64>,
    /// 时间序列数据
    pub time_series: Vec<TimeSeriesPoint>,
    /// 内存使用历史
    pub memory_history: Vec<MemoryPoint>,
    /// CPU使用历史
    pub cpu_history: Vec<CpuPoint>,
    /// 错误历史
    pub error_history: Vec<ErrorPoint>,
}

/// 时间序列数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeSeriesPoint {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 延迟
    pub latency: Duration,
    /// 吞吐量
    pub throughput: f64,
    /// 操作计数
    pub operation_count: u64,
}

/// 内存使用数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryPoint {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 内存使用量 (字节)
    pub memory_usage: u64,
    /// 内存分配次数
    pub allocations: u64,
    /// 内存释放次数
    pub deallocations: u64,
}

/// CPU使用数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpuPoint {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// CPU使用率 (%)
    pub cpu_usage: f64,
    /// 用户态CPU使用率 (%)
    pub user_cpu_usage: f64,
    /// 系统态CPU使用率 (%)
    pub system_cpu_usage: f64,
}

/// 错误数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorPoint {
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 错误类型
    pub error_type: String,
    /// 错误消息
    pub error_message: String,
    /// 错误计数
    pub error_count: u64,
}

/// 基准测试器
pub struct Benchmarker {
    /// 测试结果存储
    results: Arc<RwLock<HashMap<String, BenchmarkResult>>>,
    /// 当前测试状态
    current_test: Arc<RwLock<Option<BenchmarkState>>>,
    /// 统计收集器
    stats_collector: Arc<RwLock<StatsCollector>>,
}

/// 基准测试状态
#[derive(Debug, Clone)]
struct BenchmarkState {
    /// 测试名称
    name: String,
    /// 测试配置
    config: BenchmarkConfig,
    /// 开始时间
    start_time: DateTime<Utc>,
    /// 操作计数
    operation_count: u64,
    /// 成功计数
    success_count: u64,
    /// 失败计数
    failure_count: u64,
    /// 延迟数据
    latencies: Vec<Duration>,
    /// 内存使用数据
    memory_usage: Vec<u64>,
    /// CPU使用数据
    cpu_usage: Vec<f64>,
    /// 错误数据
    errors: Vec<ErrorPoint>,
}

/// 统计收集器
#[derive(Debug, Default)]
struct StatsCollector {
    /// 内存使用历史
    memory_history: Vec<MemoryPoint>,
    /// CPU使用历史
    cpu_history: Vec<CpuPoint>,
    /// 时间序列数据
    time_series: Vec<TimeSeriesPoint>,
}

#[allow(dead_code)]
impl Benchmarker {
    /// 创建新的基准测试器
    pub fn new() -> Self {
        Self {
            results: Arc::new(RwLock::new(HashMap::new())),
            current_test: Arc::new(RwLock::new(None)),
            stats_collector: Arc::new(RwLock::new(StatsCollector::default())),
        }
    }

    /// 开始基准测试
    pub async fn start_benchmark(&self, name: String, config: BenchmarkConfig) -> Result<(), BenchmarkError> {
        let mut current_test = self.current_test.write().await;
        if current_test.is_some() {
            return Err(BenchmarkError::TestAlreadyRunning);
        }

        let state = BenchmarkState {
            name: name.clone(),
            config: config.clone(),
            start_time: Utc::now(),
            operation_count: 0,
            success_count: 0,
            failure_count: 0,
            latencies: Vec::new(),
            memory_usage: Vec::new(),
            cpu_usage: Vec::new(),
            errors: Vec::new(),
        };

        *current_test = Some(state);

        // 启动统计收集
        self.start_stats_collection(config.clone()).await;

        Ok(())
    }

    /// 记录操作结果
    pub async fn record_operation(
        &self,
        latency: Duration,
        success: bool,
        error: Option<String>,
    ) -> Result<(), BenchmarkError> {
        let mut current_test = self.current_test.write().await;
        if let Some(ref mut state) = *current_test {
            state.operation_count += 1;
            state.latencies.push(latency);

            if success {
                state.success_count += 1;
            } else {
                state.failure_count += 1;
                if let Some(error_msg) = error {
                    state.errors.push(ErrorPoint {
                        timestamp: Utc::now(),
                        error_type: "operation_error".to_string(),
                        error_message: error_msg,
                        error_count: 1,
                    });
                }
            }
        }

        Ok(())
    }

    /// 停止基准测试
    pub async fn stop_benchmark(&self) -> Result<BenchmarkResult, BenchmarkError> {
        let mut current_test = self.current_test.write().await;
        let state = current_test.take().ok_or(BenchmarkError::NoTestRunning)?;

        let end_time = Utc::now();
        let total_duration = end_time - state.start_time;

        // 计算统计信息
        let result = self.calculate_benchmark_result(state, end_time, total_duration).await;

        // 存储结果
        {
            let mut results = self.results.write().await;
            results.insert(result.name.clone(), result.clone());
        }

        Ok(result)
    }

    /// 计算基准测试结果
    async fn calculate_benchmark_result(
        &self,
        state: BenchmarkState,
        end_time: DateTime<Utc>,
        total_duration: chrono::Duration,
    ) -> BenchmarkResult {
        let total_operations = state.operation_count;
        let successful_operations = state.success_count;
        let failed_operations = state.failure_count;

        // 计算延迟统计
        let (avg_latency, min_latency, max_latency, p95_latency, p99_latency) = 
            self.calculate_latency_stats(&state.latencies);

        // 计算吞吐量
        let throughput = if total_duration.num_seconds() > 0 {
            total_operations as f64 / total_duration.num_seconds() as f64
        } else {
            0.0
        };

        // 计算内存使用统计
        let (avg_memory_usage, peak_memory_usage) = self.calculate_memory_stats(&state.memory_usage);

        // 计算CPU使用统计
        let (avg_cpu_usage, peak_cpu_usage) = self.calculate_cpu_stats(&state.cpu_usage);

        // 计算错误率
        let error_rate = if total_operations > 0 {
            (failed_operations as f64 / total_operations as f64) * 100.0
        } else {
            0.0
        };

        // 获取详细统计信息
        let detailed_stats = if state.config.detailed_stats {
            Some(self.get_detailed_stats().await)
        } else {
            None
        };

        BenchmarkResult {
            name: state.name,
            benchmark_type: state.config.benchmark_type,
            start_time: state.start_time,
            end_time,
            total_duration: Duration::from_secs(total_duration.num_seconds() as u64),
            total_operations,
            successful_operations,
            failed_operations,
            avg_latency,
            min_latency,
            max_latency,
            p95_latency,
            p99_latency,
            throughput,
            avg_memory_usage,
            peak_memory_usage,
            avg_cpu_usage,
            peak_cpu_usage,
            error_rate,
            detailed_stats,
        }
    }

    /// 计算延迟统计
    fn calculate_latency_stats(&self, latencies: &[Duration]) -> (Duration, Duration, Duration, Duration, Duration) {
        if latencies.is_empty() {
            return (Duration::ZERO, Duration::ZERO, Duration::ZERO, Duration::ZERO, Duration::ZERO);
        }

        let mut sorted_latencies = latencies.to_vec();
        sorted_latencies.sort();

        let avg_latency = Duration::from_nanos(
            latencies.iter().map(|d| d.as_nanos() as u64).sum::<u64>() / latencies.len() as u64
        );

        let min_latency = sorted_latencies[0];
        let max_latency = sorted_latencies[sorted_latencies.len() - 1];

        let p95_index = (sorted_latencies.len() as f64 * 0.95) as usize;
        let p99_index = (sorted_latencies.len() as f64 * 0.99) as usize;

        let p95_latency = sorted_latencies[p95_index.min(sorted_latencies.len() - 1)];
        let p99_latency = sorted_latencies[p99_index.min(sorted_latencies.len() - 1)];

        (avg_latency, min_latency, max_latency, p95_latency, p99_latency)
    }

    /// 计算内存使用统计
    fn calculate_memory_stats(&self, memory_usage: &[u64]) -> (u64, u64) {
        if memory_usage.is_empty() {
            return (0, 0);
        }

        let avg_memory = memory_usage.iter().sum::<u64>() / memory_usage.len() as u64;
        let peak_memory = *memory_usage.iter().max().unwrap_or(&0);

        (avg_memory, peak_memory)
    }

    /// 计算CPU使用统计
    fn calculate_cpu_stats(&self, cpu_usage: &[f64]) -> (f64, f64) {
        if cpu_usage.is_empty() {
            return (0.0, 0.0);
        }

        let avg_cpu = cpu_usage.iter().sum::<f64>() / cpu_usage.len() as f64;
        let peak_cpu = cpu_usage.iter().fold(0.0f64, |a, &b| a.max(b));

        (avg_cpu, peak_cpu)
    }

    /// 获取详细统计信息
    async fn get_detailed_stats(&self) -> DetailedStats {
        let collector = self.stats_collector.read().await;
        
        DetailedStats {
            latency_distribution: HashMap::new(), // 需要实现
            time_series: collector.time_series.clone(),
            memory_history: collector.memory_history.clone(),
            cpu_history: collector.cpu_history.clone(),
            error_history: Vec::new(), // 需要实现
        }
    }

    /// 启动统计收集
    async fn start_stats_collection(&self, config: BenchmarkConfig) {
        let collector = self.stats_collector.clone();
        let sampling_interval = config.sampling_interval;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(sampling_interval);
            loop {
                interval.tick().await;
                
                // 收集内存使用
                let memory_usage = 1024 * 1024; // 模拟1MB
                let memory_point = MemoryPoint {
                    timestamp: Utc::now(),
                    memory_usage,
                    allocations: 0, // 需要实现
                    deallocations: 0, // 需要实现
                };

                // 收集CPU使用
                let cpu_usage = 25.0; // 模拟25%
                let cpu_point = CpuPoint {
                    timestamp: Utc::now(),
                    cpu_usage,
                    user_cpu_usage: 0.0, // 需要实现
                    system_cpu_usage: 0.0, // 需要实现
                };

                // 更新收集器
                {
                    let mut collector = collector.write().await;
                    collector.memory_history.push(memory_point);
                    collector.cpu_history.push(cpu_point);
                }
            }
        });
    }

    /// 获取当前内存使用量
    fn get_current_memory_usage(&self) -> u64 {
        // 这里应该实现实际的内存使用量获取
        // 目前返回一个模拟值
        1024 * 1024 // 1MB
    }

    /// 获取当前CPU使用率
    fn get_current_cpu_usage(&self) -> f64 {
        // 这里应该实现实际的CPU使用率获取
        // 目前返回一个模拟值
        25.0 // 25%
    }

    /// 获取基准测试结果
    pub async fn get_result(&self, name: &str) -> Option<BenchmarkResult> {
        let results = self.results.read().await;
        results.get(name).cloned()
    }

    /// 获取所有基准测试结果
    pub async fn get_all_results(&self) -> Vec<BenchmarkResult> {
        let results = self.results.read().await;
        results.values().cloned().collect()
    }

    /// 比较基准测试结果
    pub async fn compare_results(&self, result1_name: &str, result2_name: &str) -> Result<ComparisonResult, BenchmarkError> {
        let results = self.results.read().await;
        let result1 = results.get(result1_name).ok_or_else(|| BenchmarkError::ResultNotFound(result1_name.to_string()))?;
        let result2 = results.get(result2_name).ok_or_else(|| BenchmarkError::ResultNotFound(result2_name.to_string()))?;

        Ok(ComparisonResult {
            result1: result1.clone(),
            result2: result2.clone(),
            latency_improvement: self.calculate_improvement(result1.avg_latency.as_millis() as f64, result2.avg_latency.as_millis() as f64),
            throughput_improvement: self.calculate_improvement(result1.throughput, result2.throughput),
            memory_improvement: self.calculate_improvement(result1.avg_memory_usage as f64, result2.avg_memory_usage as f64),
            cpu_improvement: self.calculate_improvement(result1.avg_cpu_usage, result2.avg_cpu_usage),
            error_rate_improvement: self.calculate_improvement(result1.error_rate, result2.error_rate),
        })
    }

    /// 计算改进百分比
    fn calculate_improvement(&self, old_value: f64, new_value: f64) -> f64 {
        if old_value == 0.0 {
            return 0.0;
        }
        ((new_value - old_value) / old_value) * 100.0
    }

    /// 生成基准测试报告
    pub async fn generate_report(&self, result_name: &str) -> Result<String, BenchmarkError> {
        let result = self.get_result(result_name).await.ok_or_else(|| BenchmarkError::ResultNotFound(result_name.to_string()))?;

        let mut report = String::new();
        report.push_str("# 基准测试报告\n\n");
        report.push_str(&format!("测试名称: {}\n", result.name));
        report.push_str(&format!("测试类型: {:?}\n", result.benchmark_type));
        report.push_str(&format!("开始时间: {}\n", result.start_time.format("%Y-%m-%d %H:%M:%S UTC")));
        report.push_str(&format!("结束时间: {}\n", result.end_time.format("%Y-%m-%d %H:%M:%S UTC")));
        report.push_str(&format!("总执行时间: {:?}\n\n", result.total_duration));

        // 操作统计
        report.push_str("## 操作统计\n\n");
        report.push_str(&format!("总操作数: {}\n", result.total_operations));
        report.push_str(&format!("成功操作数: {}\n", result.successful_operations));
        report.push_str(&format!("失败操作数: {}\n", result.failed_operations));
        report.push_str(&format!("错误率: {:.2}%\n\n", result.error_rate));

        // 性能统计
        report.push_str("## 性能统计\n\n");
        report.push_str(&format!("平均延迟: {:?}\n", result.avg_latency));
        report.push_str(&format!("最小延迟: {:?}\n", result.min_latency));
        report.push_str(&format!("最大延迟: {:?}\n", result.max_latency));
        report.push_str(&format!("95%分位延迟: {:?}\n", result.p95_latency));
        report.push_str(&format!("99%分位延迟: {:?}\n", result.p99_latency));
        report.push_str(&format!("吞吐量: {:.2} 操作/秒\n\n", result.throughput));

        // 资源使用统计
        report.push_str("## 资源使用统计\n\n");
        report.push_str(&format!("平均内存使用: {} 字节\n", result.avg_memory_usage));
        report.push_str(&format!("峰值内存使用: {} 字节\n", result.peak_memory_usage));
        report.push_str(&format!("平均CPU使用率: {:.2}%\n", result.avg_cpu_usage));
        report.push_str(&format!("峰值CPU使用率: {:.2}%\n", result.peak_cpu_usage));

        Ok(report)
    }
}

/// 比较结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComparisonResult {
    /// 第一个结果
    pub result1: BenchmarkResult,
    /// 第二个结果
    pub result2: BenchmarkResult,
    /// 延迟改进百分比
    pub latency_improvement: f64,
    /// 吞吐量改进百分比
    pub throughput_improvement: f64,
    /// 内存使用改进百分比
    pub memory_improvement: f64,
    /// CPU使用改进百分比
    pub cpu_improvement: f64,
    /// 错误率改进百分比
    pub error_rate_improvement: f64,
}

/// 基准测试错误
#[derive(Debug, Error)]
pub enum BenchmarkError {
    #[error("测试已在运行")]
    TestAlreadyRunning,
    
    #[error("没有正在运行的测试")]
    NoTestRunning,
    
    #[error("结果未找到: {0}")]
    ResultNotFound(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("统计收集错误: {0}")]
    StatsCollectionError(String),
}

/// 基准测试宏
#[macro_export]
macro_rules! benchmark_operation {
    ($benchmarker:expr, $operation:expr) => {{
        let start = std::time::Instant::now();
        let result = $operation;
        let latency = start.elapsed();
        
        let success = result.is_ok();
        let error = if let Err(e) = &result {
            Some(e.to_string())
        } else {
            None
        };
        
        if let Err(e) = $benchmarker.record_operation(latency, success, error).await {
            eprintln!("记录基准测试操作失败: {:?}", e);
        }
        
        result
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_benchmarker_creation() {
        let benchmarker = Benchmarker::new();
        let results = benchmarker.get_all_results().await;
        assert!(results.is_empty());
    }

    #[tokio::test]
    async fn test_benchmark_lifecycle() {
        let benchmarker = Benchmarker::new();
        let config = BenchmarkConfig::default();
        
        // 开始测试
        benchmarker.start_benchmark("test_benchmark".to_string(), config).await.unwrap();
        
        // 记录一些操作
        for _ in 0..10 {
            benchmarker.record_operation(Duration::from_millis(100), true, None).await.unwrap();
        }
        
        // 停止测试
        let result = benchmarker.stop_benchmark().await.unwrap();
        
        assert_eq!(result.name, "test_benchmark");
        assert_eq!(result.total_operations, 10);
        assert_eq!(result.successful_operations, 10);
        assert_eq!(result.failed_operations, 0);
    }

    #[tokio::test]
    async fn test_latency_calculation() {
        let benchmarker = Benchmarker::new();
        let latencies = vec![
            Duration::from_millis(100),
            Duration::from_millis(200),
            Duration::from_millis(150),
            Duration::from_millis(300),
            Duration::from_millis(120),
        ];
        
        let (avg, min, max, p95, p99) = benchmarker.calculate_latency_stats(&latencies);
        
        assert_eq!(min, Duration::from_millis(100));
        assert_eq!(max, Duration::from_millis(300));
        assert!(avg > Duration::ZERO);
        assert!(p95 >= Duration::from_millis(200));
        assert!(p99 >= Duration::from_millis(300));
    }
}
