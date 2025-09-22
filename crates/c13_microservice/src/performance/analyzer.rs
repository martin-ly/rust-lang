//! 性能分析器模块
//!
//! 提供性能数据分析和报告生成功能

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use crate::performance::profiler::{ProfilerStats, CategoryStats, TimingStats, MemoryStats};

/// 性能分析器
#[derive(Debug)]
pub struct PerformanceAnalyzer {
    thresholds: AnalysisThresholds,
}

impl PerformanceAnalyzer {
    /// 创建新的性能分析器
    pub fn new() -> Self {
        Self {
            thresholds: AnalysisThresholds::default(),
        }
    }

    /// 分析性能数据
    pub fn analyze(&self, stats: &ProfilerStats) -> PerformanceReport {
        let mut report = PerformanceReport {
            overall_score: 0.0,
            bottlenecks: Vec::new(),
            recommendations: Vec::new(),
            category_analysis: HashMap::new(),
            performance_metrics: PerformanceMetrics::default(),
            summary: String::new(),
        };

        // 分析各个类别
        for (category, category_stats) in &stats.categories {
            let analysis = self.analyze_category(category, category_stats);
            report.category_analysis.insert(category.clone(), analysis);
        }

        // 识别性能瓶颈
        report.bottlenecks = self.identify_bottlenecks(stats);

        // 生成优化建议
        report.recommendations = self.generate_recommendations(stats);

        // 计算整体性能分数
        report.overall_score = self.calculate_overall_score(stats);

        // 生成性能指标
        report.performance_metrics = self.calculate_performance_metrics(stats);

        // 生成总结
        report.summary = self.generate_summary(&report);

        report
    }

    /// 分析单个类别
    fn analyze_category(&self, category: &str, stats: &CategoryStats) -> CategoryAnalysis {
        let mut analysis = CategoryAnalysis {
            category: category.to_string(),
            performance_score: 0.0,
            issues: Vec::new(),
            suggestions: Vec::new(),
        };

        // 分析平均执行时间
        if stats.average_duration > self.thresholds.slow_operation_threshold {
            analysis.issues.push(format!(
                "平均执行时间过长: {:.2}ms (阈值: {:.2}ms)",
                stats.average_duration.as_secs_f64() * 1000.0,
                self.thresholds.slow_operation_threshold.as_secs_f64() * 1000.0
            ));
            analysis.suggestions.push("考虑优化算法或减少I/O操作".to_string());
        }

        // 分析最大执行时间
        if stats.max_duration > self.thresholds.very_slow_operation_threshold {
            analysis.issues.push(format!(
                "最大执行时间过长: {:.2}ms (阈值: {:.2}ms)",
                stats.max_duration.as_secs_f64() * 1000.0,
                self.thresholds.very_slow_operation_threshold.as_secs_f64() * 1000.0
            ));
            analysis.suggestions.push("检查是否存在阻塞操作或死锁".to_string());
        }

        // 分析执行时间差异
        if stats.max_duration > stats.min_duration * 10 {
            analysis.issues.push("执行时间差异过大，可能存在性能不一致的问题".to_string());
            analysis.suggestions.push("优化数据结构和算法，确保性能一致性".to_string());
        }

        // 计算性能分数
        analysis.performance_score = self.calculate_category_score(stats);

        analysis
    }

    /// 识别性能瓶颈
    fn identify_bottlenecks(&self, stats: &ProfilerStats) -> Vec<BottleneckAnalysis> {
        let mut bottlenecks = Vec::new();

        // 分析最慢的类别
        for (category, category_stats) in &stats.categories {
            if category_stats.average_duration > self.thresholds.slow_operation_threshold {
                bottlenecks.push(BottleneckAnalysis {
                    category: category.clone(),
                    severity: BottleneckSeverity::High,
                    description: format!(
                        "{} 类别平均执行时间过长: {:.2}ms",
                        category,
                        category_stats.average_duration.as_secs_f64() * 1000.0
                    ),
                    impact: "可能导致用户体验下降".to_string(),
                    solution: "优化算法或减少I/O操作".to_string(),
                });
            }
        }

        // 分析内存使用
        if stats.memory_stats.max_memory > self.thresholds.high_memory_threshold {
            bottlenecks.push(BottleneckAnalysis {
                category: "memory".to_string(),
                severity: BottleneckSeverity::Medium,
                description: format!(
                    "内存使用过高: {} bytes",
                    stats.memory_stats.max_memory
                ),
                impact: "可能导致内存不足或GC压力".to_string(),
                solution: "优化内存使用，考虑使用对象池或缓存".to_string(),
            });
        }

        // 分析事件频率
        if stats.total_events > self.thresholds.high_event_count_threshold {
            bottlenecks.push(BottleneckAnalysis {
                category: "events".to_string(),
                severity: BottleneckSeverity::Low,
                description: format!(
                    "事件数量过多: {} 个事件",
                    stats.total_events
                ),
                impact: "可能影响性能监控的开销".to_string(),
                solution: "考虑减少事件记录或提高采样率".to_string(),
            });
        }

        bottlenecks
    }

    /// 生成优化建议
    fn generate_recommendations(&self, stats: &ProfilerStats) -> Vec<OptimizationSuggestion> {
        let mut suggestions = Vec::new();

        // 基于时间统计的建议
        if stats.timing_stats.average_duration > Duration::from_millis(100) {
            suggestions.push(OptimizationSuggestion {
                category: "performance".to_string(),
                priority: SuggestionPriority::High,
                title: "优化慢操作".to_string(),
                description: "检测到平均执行时间较长的操作".to_string(),
                action: "使用更高效的算法或数据结构".to_string(),
                expected_improvement: "预计可提升20-50%性能".to_string(),
            });
        }

        // 基于内存统计的建议
        if stats.memory_stats.average_memory > 1024 * 1024 { // 1MB
            suggestions.push(OptimizationSuggestion {
                category: "memory".to_string(),
                priority: SuggestionPriority::Medium,
                title: "优化内存使用".to_string(),
                description: "检测到较高的内存使用量".to_string(),
                action: "使用对象池或减少内存分配".to_string(),
                expected_improvement: "预计可减少30-60%内存使用".to_string(),
            });
        }

        // 基于事件分布的建议
        if stats.categories.len() > 10 {
            suggestions.push(OptimizationSuggestion {
                category: "architecture".to_string(),
                priority: SuggestionPriority::Low,
                title: "简化架构".to_string(),
                description: "检测到过多的性能事件类别".to_string(),
                action: "考虑合并相似的功能模块".to_string(),
                expected_improvement: "预计可提升代码可维护性".to_string(),
            });
        }

        suggestions
    }

    /// 计算整体性能分数
    fn calculate_overall_score(&self, stats: &ProfilerStats) -> f64 {
        let mut total_score = 0.0;
        let mut weight_sum = 0.0;

        // 时间性能权重
        let time_score = self.calculate_time_score(&stats.timing_stats);
        total_score += time_score * 0.4;
        weight_sum += 0.4;

        // 内存性能权重
        let memory_score = self.calculate_memory_score(&stats.memory_stats);
        total_score += memory_score * 0.3;
        weight_sum += 0.3;

        // 事件分布权重
        let event_score = self.calculate_event_score(stats);
        total_score += event_score * 0.3;
        weight_sum += 0.3;

        if weight_sum > 0.0 {
            total_score / weight_sum
        } else {
            0.0
        }
    }

    /// 计算类别性能分数
    fn calculate_category_score(&self, stats: &CategoryStats) -> f64 {
        let mut score = 100.0;

        // 基于平均执行时间扣分
        if stats.average_duration > self.thresholds.slow_operation_threshold {
            let penalty = (stats.average_duration.as_secs_f64() / self.thresholds.slow_operation_threshold.as_secs_f64()) * 10.0;
            score -= penalty.min(50.0);
        }

        // 基于最大执行时间扣分
        if stats.max_duration > self.thresholds.very_slow_operation_threshold {
            let penalty = (stats.max_duration.as_secs_f64() / self.thresholds.very_slow_operation_threshold.as_secs_f64()) * 15.0;
            score -= penalty.min(40.0);
        }

        // 基于执行时间一致性加分
        if stats.max_duration > stats.min_duration {
            let consistency_ratio = stats.min_duration.as_secs_f64() / stats.max_duration.as_secs_f64();
            score += consistency_ratio * 10.0;
        }

        score.max(0.0).min(100.0)
    }

    /// 计算时间性能分数
    fn calculate_time_score(&self, timing_stats: &TimingStats) -> f64 {
        let mut score = 100.0;

        if timing_stats.average_duration > self.thresholds.slow_operation_threshold {
            let penalty = (timing_stats.average_duration.as_secs_f64() / self.thresholds.slow_operation_threshold.as_secs_f64()) * 20.0;
            score -= penalty.min(60.0);
        }

        score.max(0.0).min(100.0)
    }

    /// 计算内存性能分数
    fn calculate_memory_score(&self, memory_stats: &MemoryStats) -> f64 {
        let mut score = 100.0;

        if memory_stats.average_memory > self.thresholds.high_memory_threshold {
            let penalty = (memory_stats.average_memory as f64 / self.thresholds.high_memory_threshold as f64) * 15.0;
            score -= penalty.min(50.0);
        }

        score.max(0.0).min(100.0)
    }

    /// 计算事件分布分数
    fn calculate_event_score(&self, stats: &ProfilerStats) -> f64 {
        let mut score = 100.0;

        // 基于事件数量扣分
        if stats.total_events > self.thresholds.high_event_count_threshold {
            let penalty = (stats.total_events as f64 / self.thresholds.high_event_count_threshold as f64) * 10.0;
            score -= penalty.min(30.0);
        }

        // 基于类别数量加分
        let category_diversity = stats.categories.len() as f64;
        if category_diversity > 5.0 {
            score += (category_diversity - 5.0) * 2.0;
        }

        score.max(0.0).min(100.0)
    }

    /// 计算性能指标
    fn calculate_performance_metrics(&self, stats: &ProfilerStats) -> PerformanceMetrics {
        PerformanceMetrics {
            total_operations: stats.total_events,
            average_response_time: stats.timing_stats.average_duration,
            throughput: if stats.timing_stats.total_duration.as_secs_f64() > 0.0 {
                stats.total_events as f64 / stats.timing_stats.total_duration.as_secs_f64()
            } else {
                0.0
            },
            error_rate: 0.0, // 需要从事件中计算
            cpu_usage: 0.0, // 需要从系统监控中获取
            memory_usage: stats.memory_stats.average_memory,
            cache_hit_rate: 0.0, // 需要从缓存统计中获取
        }
    }

    /// 生成总结
    fn generate_summary(&self, report: &PerformanceReport) -> String {
        let mut summary = String::new();

        summary.push_str(&format!("性能分析总结 (总分: {:.1}/100):\n", report.overall_score));

        if report.overall_score >= 80.0 {
            summary.push_str("✅ 性能表现优秀\n");
        } else if report.overall_score >= 60.0 {
            summary.push_str("⚠️ 性能表现良好，有改进空间\n");
        } else {
            summary.push_str("❌ 性能需要优化\n");
        }

        if !report.bottlenecks.is_empty() {
            summary.push_str(&format!("发现 {} 个性能瓶颈\n", report.bottlenecks.len()));
        }

        if !report.recommendations.is_empty() {
            summary.push_str(&format!("提供 {} 个优化建议\n", report.recommendations.len()));
        }

        summary.push_str(&format!("总操作数: {}\n", report.performance_metrics.total_operations));
        summary.push_str(&format!("平均响应时间: {:.2}ms\n", report.performance_metrics.average_response_time.as_secs_f64() * 1000.0));
        summary.push_str(&format!("吞吐量: {:.2} ops/sec\n", report.performance_metrics.throughput));

        summary
    }
}

impl Default for PerformanceAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// 性能报告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceReport {
    pub overall_score: f64,
    pub bottlenecks: Vec<BottleneckAnalysis>,
    pub recommendations: Vec<OptimizationSuggestion>,
    pub category_analysis: HashMap<String, CategoryAnalysis>,
    pub performance_metrics: PerformanceMetrics,
    pub summary: String,
}

/// 类别分析
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CategoryAnalysis {
    pub category: String,
    pub performance_score: f64,
    pub issues: Vec<String>,
    pub suggestions: Vec<String>,
}

/// 性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub total_operations: usize,
    pub average_response_time: Duration,
    pub throughput: f64,
    pub error_rate: f64,
    pub cpu_usage: f64,
    pub memory_usage: usize,
    pub cache_hit_rate: f64,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            total_operations: 0,
            average_response_time: Duration::ZERO,
            throughput: 0.0,
            error_rate: 0.0,
            cpu_usage: 0.0,
            memory_usage: 0,
            cache_hit_rate: 0.0,
        }
    }
}

/// 瓶颈分析
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BottleneckAnalysis {
    pub category: String,
    pub severity: BottleneckSeverity,
    pub description: String,
    pub impact: String,
    pub solution: String,
}

/// 瓶颈严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BottleneckSeverity {
    Low,
    Medium,
    High,
    Critical,
}

/// 优化建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationSuggestion {
    pub category: String,
    pub priority: SuggestionPriority,
    pub title: String,
    pub description: String,
    pub action: String,
    pub expected_improvement: String,
}

/// 建议优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SuggestionPriority {
    Low,
    Medium,
    High,
    Critical,
}

/// 分析阈值配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnalysisThresholds {
    pub slow_operation_threshold: Duration,
    pub very_slow_operation_threshold: Duration,
    pub high_memory_threshold: usize,
    pub high_event_count_threshold: usize,
}

impl Default for AnalysisThresholds {
    fn default() -> Self {
        Self {
            slow_operation_threshold: Duration::from_millis(100),
            very_slow_operation_threshold: Duration::from_millis(1000),
            high_memory_threshold: 10 * 1024 * 1024, // 10MB
            high_event_count_threshold: 1000,
        }
    }
}
