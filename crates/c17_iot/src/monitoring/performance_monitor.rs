//! 性能监控模块
//! 
//! 提供全面的性能监控功能，包括：
//! - 性能指标收集
//! - 性能分析
//! - 性能报告生成
//! - 性能优化建议

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 性能指标类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PerformanceMetric {
    /// 延迟指标
    Latency {
        operation: String,
        duration: Duration,
        timestamp: DateTime<Utc>,
    },
    /// 吞吐量指标
    Throughput {
        operation: String,
        count: u64,
        duration: Duration,
        timestamp: DateTime<Utc>,
    },
    /// 内存使用指标
    MemoryUsage {
        component: String,
        used_bytes: u64,
        total_bytes: u64,
        timestamp: DateTime<Utc>,
    },
    /// CPU使用指标
    CpuUsage {
        component: String,
        usage_percent: f64,
        timestamp: DateTime<Utc>,
    },
    /// 错误率指标
    ErrorRate {
        operation: String,
        error_count: u64,
        total_count: u64,
        timestamp: DateTime<Utc>,
    },
}

/// 性能统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceStats {
    /// 操作名称
    pub operation: String,
    /// 总执行次数
    pub total_count: u64,
    /// 总执行时间
    pub total_duration: Duration,
    /// 平均执行时间
    pub avg_duration: Duration,
    /// 最小执行时间
    pub min_duration: Duration,
    /// 最大执行时间
    pub max_duration: Duration,
    /// 错误次数
    pub error_count: u64,
    /// 错误率
    pub error_rate: f64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 性能分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceAnalysis {
    /// 分析时间
    pub analysis_time: DateTime<Utc>,
    /// 性能瓶颈
    pub bottlenecks: Vec<PerformanceBottleneck>,
    /// 优化建议
    pub recommendations: Vec<OptimizationRecommendation>,
    /// 整体性能评分
    pub performance_score: f64,
}

/// 性能瓶颈
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceBottleneck {
    /// 瓶颈类型
    pub bottleneck_type: BottleneckType,
    /// 影响的操作
    pub affected_operations: Vec<String>,
    /// 严重程度
    pub severity: Severity,
    /// 描述
    pub description: String,
    /// 建议的解决方案
    pub suggested_solution: String,
}

/// 瓶颈类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BottleneckType {
    /// 高延迟
    HighLatency,
    /// 低吞吐量
    LowThroughput,
    /// 高内存使用
    HighMemoryUsage,
    /// 高CPU使用
    HighCpuUsage,
    /// 高错误率
    HighErrorRate,
    /// 资源竞争
    ResourceContention,
}

/// 严重程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Severity {
    /// 低
    Low,
    /// 中
    Medium,
    /// 高
    High,
    /// 严重
    Critical,
}

/// 优化建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationRecommendation {
    /// 建议类型
    pub recommendation_type: RecommendationType,
    /// 目标操作
    pub target_operation: String,
    /// 建议描述
    pub description: String,
    /// 预期改进
    pub expected_improvement: String,
    /// 实施难度
    pub implementation_difficulty: ImplementationDifficulty,
}

/// 建议类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecommendationType {
    /// 缓存优化
    CacheOptimization,
    /// 并发优化
    ConcurrencyOptimization,
    /// 算法优化
    AlgorithmOptimization,
    /// 资源优化
    ResourceOptimization,
    /// 架构优化
    ArchitectureOptimization,
}

/// 实施难度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ImplementationDifficulty {
    /// 简单
    Easy,
    /// 中等
    Medium,
    /// 困难
    Hard,
    /// 非常困难
    VeryHard,
}

/// 性能监控器
pub struct PerformanceMonitor {
    /// 性能指标存储
    metrics: Arc<RwLock<Vec<PerformanceMetric>>>,
    /// 性能统计信息
    stats: Arc<RwLock<HashMap<String, PerformanceStats>>>,
    /// 配置
    config: PerformanceMonitorConfig,
}

/// 性能监控配置
#[derive(Debug, Clone)]
pub struct PerformanceMonitorConfig {
    /// 最大指标存储数量
    pub max_metrics: usize,
    /// 统计更新间隔
    pub stats_update_interval: Duration,
    /// 是否启用自动分析
    pub auto_analysis_enabled: bool,
    /// 分析间隔
    pub analysis_interval: Duration,
    /// 性能阈值
    pub thresholds: PerformanceThresholds,
}

/// 性能阈值
#[derive(Debug, Clone)]
pub struct PerformanceThresholds {
    /// 高延迟阈值（毫秒）
    pub high_latency_threshold: u64,
    /// 低吞吐量阈值（操作/秒）
    pub low_throughput_threshold: u64,
    /// 高内存使用阈值（百分比）
    pub high_memory_threshold: f64,
    /// 高CPU使用阈值（百分比）
    pub high_cpu_threshold: f64,
    /// 高错误率阈值（百分比）
    pub high_error_rate_threshold: f64,
}

impl Default for PerformanceMonitorConfig {
    fn default() -> Self {
        Self {
            max_metrics: 10000,
            stats_update_interval: Duration::from_secs(60),
            auto_analysis_enabled: true,
            analysis_interval: Duration::from_secs(300),
            thresholds: PerformanceThresholds::default(),
        }
    }
}

impl Default for PerformanceThresholds {
    fn default() -> Self {
        Self {
            high_latency_threshold: 1000, // 1秒
            low_throughput_threshold: 100, // 100操作/秒
            high_memory_threshold: 80.0, // 80%
            high_cpu_threshold: 80.0, // 80%
            high_error_rate_threshold: 5.0, // 5%
        }
    }
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new(config: PerformanceMonitorConfig) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    /// 记录性能指标
    pub async fn record_metric(&self, metric: PerformanceMetric) -> Result<(), PerformanceMonitorError> {
        let mut metrics = self.metrics.write().await;
        
        // 如果超过最大存储数量，移除最旧的指标
        if metrics.len() >= self.config.max_metrics {
            let remove_count = metrics.len() - self.config.max_metrics + 1;
            metrics.drain(0..remove_count);
        }
        
        metrics.push(metric);
        Ok(())
    }

    /// 记录延迟指标
    pub async fn record_latency(&self, operation: String, duration: Duration) -> Result<(), PerformanceMonitorError> {
        let metric = PerformanceMetric::Latency {
            operation,
            duration,
            timestamp: Utc::now(),
        };
        self.record_metric(metric).await
    }

    /// 记录吞吐量指标
    pub async fn record_throughput(&self, operation: String, count: u64, duration: Duration) -> Result<(), PerformanceMonitorError> {
        let metric = PerformanceMetric::Throughput {
            operation,
            count,
            duration,
            timestamp: Utc::now(),
        };
        self.record_metric(metric).await
    }

    /// 记录内存使用指标
    pub async fn record_memory_usage(&self, component: String, used_bytes: u64, total_bytes: u64) -> Result<(), PerformanceMonitorError> {
        let metric = PerformanceMetric::MemoryUsage {
            component,
            used_bytes,
            total_bytes,
            timestamp: Utc::now(),
        };
        self.record_metric(metric).await
    }

    /// 记录CPU使用指标
    pub async fn record_cpu_usage(&self, component: String, usage_percent: f64) -> Result<(), PerformanceMonitorError> {
        let metric = PerformanceMetric::CpuUsage {
            component,
            usage_percent,
            timestamp: Utc::now(),
        };
        self.record_metric(metric).await
    }

    /// 记录错误率指标
    pub async fn record_error_rate(&self, operation: String, error_count: u64, total_count: u64) -> Result<(), PerformanceMonitorError> {
        let metric = PerformanceMetric::ErrorRate {
            operation,
            error_count,
            total_count,
            timestamp: Utc::now(),
        };
        self.record_metric(metric).await
    }

    /// 获取性能统计信息
    pub async fn get_stats(&self) -> Result<HashMap<String, PerformanceStats>, PerformanceMonitorError> {
        let stats = self.stats.read().await;
        Ok(stats.clone())
    }

    /// 获取特定操作的统计信息
    pub async fn get_operation_stats(&self, operation: &str) -> Result<Option<PerformanceStats>, PerformanceMonitorError> {
        let stats = self.stats.read().await;
        Ok(stats.get(operation).cloned())
    }

    /// 更新统计信息
    pub async fn update_stats(&self) -> Result<(), PerformanceMonitorError> {
        let metrics = self.metrics.read().await;
        let mut stats = self.stats.write().await;

        // 按操作分组统计
        let mut operation_stats: HashMap<String, Vec<&PerformanceMetric>> = HashMap::new();
        
        for metric in metrics.iter() {
            let operation = match metric {
                PerformanceMetric::Latency { operation, .. } => operation,
                PerformanceMetric::Throughput { operation, .. } => operation,
                PerformanceMetric::ErrorRate { operation, .. } => operation,
                _ => continue,
            };
            
            operation_stats.entry(operation.clone()).or_insert_with(Vec::new).push(metric);
        }

        // 计算统计信息
        for (operation, metrics) in operation_stats {
            let mut total_count = 0u64;
            let mut total_duration = Duration::ZERO;
            let mut min_duration = Duration::MAX;
            let mut max_duration = Duration::ZERO;
            let mut error_count = 0u64;

            for metric in metrics {
                match metric {
                    PerformanceMetric::Latency { duration, .. } => {
                        total_count += 1;
                        total_duration += *duration;
                        min_duration = min_duration.min(*duration);
                        max_duration = max_duration.max(*duration);
                    },
                    PerformanceMetric::ErrorRate { error_count: errors, total_count: total, .. } => {
                        error_count += errors;
                        total_count += total;
                    },
                    _ => {}
                }
            }

            let avg_duration = if total_count > 0 {
                Duration::from_nanos(total_duration.as_nanos() as u64 / total_count)
            } else {
                Duration::ZERO
            };

            let error_rate = if total_count > 0 {
                (error_count as f64 / total_count as f64) * 100.0
            } else {
                0.0
            };

            let performance_stats = PerformanceStats {
                operation: operation.clone(),
                total_count,
                total_duration,
                avg_duration,
                min_duration: if min_duration == Duration::MAX { Duration::ZERO } else { min_duration },
                max_duration,
                error_count,
                error_rate,
                last_updated: Utc::now(),
            };

            stats.insert(operation, performance_stats);
        }

        Ok(())
    }

    /// 执行性能分析
    pub async fn analyze_performance(&self) -> Result<PerformanceAnalysis, PerformanceMonitorError> {
        let stats = self.stats.read().await;
        let mut bottlenecks = Vec::new();
        let mut recommendations = Vec::new();

        // 分析性能瓶颈
        for (operation, stat) in stats.iter() {
            // 检查高延迟
            if stat.avg_duration.as_millis() > self.config.thresholds.high_latency_threshold as u128 {
                bottlenecks.push(PerformanceBottleneck {
                    bottleneck_type: BottleneckType::HighLatency,
                    affected_operations: vec![operation.clone()],
                    severity: if stat.avg_duration.as_millis() > 5000 { Severity::Critical } else { Severity::High },
                    description: format!("操作 {} 的平均延迟为 {:.2}ms，超过阈值", operation, stat.avg_duration.as_millis()),
                    suggested_solution: "考虑优化算法或增加缓存".to_string(),
                });

                recommendations.push(OptimizationRecommendation {
                    recommendation_type: RecommendationType::AlgorithmOptimization,
                    target_operation: operation.clone(),
                    description: format!("优化 {} 操作的算法实现", operation),
                    expected_improvement: "预期减少50%的延迟".to_string(),
                    implementation_difficulty: ImplementationDifficulty::Medium,
                });
            }

            // 检查高错误率
            if stat.error_rate > self.config.thresholds.high_error_rate_threshold {
                bottlenecks.push(PerformanceBottleneck {
                    bottleneck_type: BottleneckType::HighErrorRate,
                    affected_operations: vec![operation.clone()],
                    severity: if stat.error_rate > 20.0 { Severity::Critical } else { Severity::High },
                    description: format!("操作 {} 的错误率为 {:.2}%，超过阈值", operation, stat.error_rate),
                    suggested_solution: "检查错误处理逻辑和输入验证".to_string(),
                });
            }
        }

        // 计算整体性能评分
        let performance_score = self.calculate_performance_score(&stats).await;

        Ok(PerformanceAnalysis {
            analysis_time: Utc::now(),
            bottlenecks,
            recommendations,
            performance_score,
        })
    }

    /// 计算性能评分
    async fn calculate_performance_score(&self, stats: &HashMap<String, PerformanceStats>) -> f64 {
        if stats.is_empty() {
            return 100.0;
        }

        let mut total_score = 0.0;
        let mut operation_count = 0;

        for stat in stats.values() {
            let mut score: f64 = 100.0;

            // 延迟评分
            if stat.avg_duration.as_millis() > self.config.thresholds.high_latency_threshold as u128 {
                score -= 30.0;
            }

            // 错误率评分
            if stat.error_rate > self.config.thresholds.high_error_rate_threshold {
                score -= 40.0;
            }

            // 吞吐量评分（如果有数据）
            if stat.total_count > 0 {
                let throughput = stat.total_count as f64 / stat.total_duration.as_secs_f64();
                if throughput < self.config.thresholds.low_throughput_threshold as f64 {
                    score -= 20.0;
                }
            }

            total_score += score.max(0.0);
            operation_count += 1;
        }

        if operation_count > 0 {
            total_score / operation_count as f64
        } else {
            100.0
        }
    }

    /// 生成性能报告
    pub async fn generate_report(&self) -> Result<String, PerformanceMonitorError> {
        let analysis = self.analyze_performance().await?;
        let stats = self.get_stats().await?;

        let mut report = String::new();
        report.push_str("# 性能监控报告\n\n");
        report.push_str(&format!("生成时间: {}\n", analysis.analysis_time.format("%Y-%m-%d %H:%M:%S UTC")));
        report.push_str(&format!("整体性能评分: {:.1}/100\n\n", analysis.performance_score));

        // 性能统计
        report.push_str("## 性能统计\n\n");
        for (operation, stat) in stats.iter() {
            report.push_str(&format!("### {}\n", operation));
            report.push_str(&format!("- 总执行次数: {}\n", stat.total_count));
            report.push_str(&format!("- 平均延迟: {:.2}ms\n", stat.avg_duration.as_millis()));
            report.push_str(&format!("- 最小延迟: {:.2}ms\n", stat.min_duration.as_millis()));
            report.push_str(&format!("- 最大延迟: {:.2}ms\n", stat.max_duration.as_millis()));
            report.push_str(&format!("- 错误率: {:.2}%\n", stat.error_rate));
            report.push_str(&format!("- 最后更新: {}\n\n", stat.last_updated.format("%Y-%m-%d %H:%M:%S UTC")));
        }

        // 性能瓶颈
        if !analysis.bottlenecks.is_empty() {
            report.push_str("## 性能瓶颈\n\n");
            for bottleneck in &analysis.bottlenecks {
                report.push_str(&format!("### {:?} - {:?}\n", bottleneck.bottleneck_type, bottleneck.severity));
                report.push_str(&format!("影响操作: {}\n", bottleneck.affected_operations.join(", ")));
                report.push_str(&format!("描述: {}\n", bottleneck.description));
                report.push_str(&format!("建议解决方案: {}\n\n", bottleneck.suggested_solution));
            }
        }

        // 优化建议
        if !analysis.recommendations.is_empty() {
            report.push_str("## 优化建议\n\n");
            for recommendation in &analysis.recommendations {
                report.push_str(&format!("### {:?} - {:?}\n", recommendation.recommendation_type, recommendation.implementation_difficulty));
                report.push_str(&format!("目标操作: {}\n", recommendation.target_operation));
                report.push_str(&format!("描述: {}\n", recommendation.description));
                report.push_str(&format!("预期改进: {}\n\n", recommendation.expected_improvement));
            }
        }

        Ok(report)
    }

    /// 启动自动监控
    pub async fn start_auto_monitoring(&self) -> Result<(), PerformanceMonitorError> {
        let monitor = self.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(monitor.config.stats_update_interval);
            loop {
                interval.tick().await;
                if let Err(e) = monitor.update_stats().await {
                    eprintln!("更新性能统计失败: {:?}", e);
                }
            }
        });

        if self.config.auto_analysis_enabled {
            let monitor = self.clone();
            tokio::spawn(async move {
                let mut interval = tokio::time::interval(monitor.config.analysis_interval);
                loop {
                    interval.tick().await;
                    match monitor.analyze_performance().await {
                        Ok(analysis) => {
                            if analysis.performance_score < 70.0 {
                                println!("⚠️ 性能评分较低: {:.1}/100", analysis.performance_score);
                            }
                        },
                        Err(e) => {
                            eprintln!("性能分析失败: {:?}", e);
                        }
                    }
                }
            });
        }

        Ok(())
    }
}

impl Clone for PerformanceMonitor {
    fn clone(&self) -> Self {
        Self {
            metrics: self.metrics.clone(),
            stats: self.stats.clone(),
            config: self.config.clone(),
        }
    }
}

/// 性能监控错误
#[derive(Debug, thiserror::Error)]
pub enum PerformanceMonitorError {
    #[error("性能监控配置错误: {0}")]
    ConfigError(String),
    
    #[error("性能指标记录失败: {0}")]
    MetricRecordingError(String),
    
    #[error("性能分析失败: {0}")]
    AnalysisError(String),
    
    #[error("报告生成失败: {0}")]
    ReportGenerationError(String),
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
}

/// 性能监控宏
#[macro_export]
macro_rules! measure_performance {
    ($monitor:expr, $operation:expr, $code:block) => {{
        let start = std::time::Instant::now();
        let result = $code;
        let duration = start.elapsed();
        
        if let Err(e) = $monitor.record_latency($operation.to_string(), duration).await {
            eprintln!("记录性能指标失败: {:?}", e);
        }
        
        result
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_performance_monitor_creation() {
        let config = PerformanceMonitorConfig::default();
        let monitor = PerformanceMonitor::new(config);
        
        // 测试基本功能
        monitor.record_latency("test_operation".to_string(), Duration::from_millis(100)).await.unwrap();
        
        let stats = monitor.get_stats().await.unwrap();
        assert!(stats.is_empty()); // 需要先更新统计信息
        
        monitor.update_stats().await.unwrap();
        let stats = monitor.get_stats().await.unwrap();
        assert!(!stats.is_empty());
    }

    #[tokio::test]
    async fn test_performance_analysis() {
        let config = PerformanceMonitorConfig::default();
        let monitor = PerformanceMonitor::new(config);
        
        // 记录一些测试数据
        for i in 0..10 {
            monitor.record_latency("test_operation".to_string(), Duration::from_millis(100 + i * 10)).await.unwrap();
        }
        
        monitor.update_stats().await.unwrap();
        let analysis = monitor.analyze_performance().await.unwrap();
        
        assert!(analysis.performance_score > 0.0);
        assert!(analysis.performance_score <= 100.0);
    }

    #[tokio::test]
    async fn test_performance_report_generation() {
        let config = PerformanceMonitorConfig::default();
        let monitor = PerformanceMonitor::new(config);
        
        // 记录一些测试数据
        monitor.record_latency("test_operation".to_string(), Duration::from_millis(100)).await.unwrap();
        monitor.record_error_rate("test_operation".to_string(), 1, 10).await.unwrap();
        
        monitor.update_stats().await.unwrap();
        let report = monitor.generate_report().await.unwrap();
        
        assert!(report.contains("性能监控报告"));
        assert!(report.contains("test_operation"));
    }
}
