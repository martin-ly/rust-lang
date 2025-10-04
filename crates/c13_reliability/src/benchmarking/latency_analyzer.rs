/// 延迟分析器
///
/// 用于分析和统计系统延迟数据

use std::collections::HashMap;
use std::time::Duration;

/// 延迟分析器
#[derive(Debug, Clone)]
pub struct LatencyAnalyzer {
    samples: Vec<Duration>,
}

impl LatencyAnalyzer {
    /// 创建新的延迟分析器
    pub fn new() -> Self {
        Self {
            samples: Vec::new(),
        }
    }

    /// 添加延迟样本
    pub fn record(&mut self, latency: Duration) {
        self.samples.push(latency);
    }

    /// 批量添加延迟样本
    pub fn record_batch(&mut self, latencies: Vec<Duration>) {
        self.samples.extend(latencies);
    }

    /// 分析延迟数据
    pub fn analyze(&self) -> LatencyMetrics {
        if self.samples.is_empty() {
            return LatencyMetrics::default();
        }

        let mut sorted = self.samples.clone();
        sorted.sort();

        let count = sorted.len();
        let min = sorted[0];
        let max = sorted[count - 1];

        let sum: Duration = sorted.iter().sum();
        let mean = sum / count as u32;

        let p50 = Self::percentile(&sorted, 50.0);
        let p75 = Self::percentile(&sorted, 75.0);
        let p90 = Self::percentile(&sorted, 90.0);
        let p95 = Self::percentile(&sorted, 95.0);
        let p99 = Self::percentile(&sorted, 99.0);
        let p999 = Self::percentile(&sorted, 99.9);

        // 计算标准差
        let variance: f64 = sorted
            .iter()
            .map(|&x| {
                let diff = x.as_secs_f64() - mean.as_secs_f64();
                diff * diff
            })
            .sum::<f64>()
            / count as f64;
        let std_dev = Duration::from_secs_f64(variance.sqrt());

        LatencyMetrics {
            count,
            min,
            max,
            mean,
            std_dev,
            p50,
            p75,
            p90,
            p95,
            p99,
            p999,
        }
    }

    /// 计算百分位数
    fn percentile(sorted: &[Duration], percentile: f64) -> Duration {
        if sorted.is_empty() {
            return Duration::ZERO;
        }

        let index = (percentile / 100.0 * (sorted.len() - 1) as f64).round() as usize;
        sorted[index.min(sorted.len() - 1)]
    }

    /// 生成延迟分布直方图
    pub fn histogram(&self, bucket_count: usize) -> HashMap<String, usize> {
        if self.samples.is_empty() {
            return HashMap::new();
        }

        let mut sorted = self.samples.clone();
        sorted.sort();

        let min = sorted[0].as_micros();
        let max = sorted[sorted.len() - 1].as_micros();
        let bucket_size = (max - min) / bucket_count as u128 + 1;

        let mut histogram = HashMap::new();

        for sample in &sorted {
            let bucket_idx = ((sample.as_micros() - min) / bucket_size) as usize;
            let bucket_label = format!(
                "{}-{}µs",
                min + bucket_idx as u128 * bucket_size,
                min + (bucket_idx + 1) as u128 * bucket_size
            );
            *histogram.entry(bucket_label).or_insert(0) += 1;
        }

        histogram
    }

    /// 清空所有样本
    pub fn clear(&mut self) {
        self.samples.clear();
    }

    /// 获取样本数量
    pub fn len(&self) -> usize {
        self.samples.len()
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.samples.is_empty()
    }
}

impl Default for LatencyAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// 延迟指标
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LatencyMetrics {
    /// 样本数量
    pub count: usize,
    /// 最小延迟
    pub min: Duration,
    /// 最大延迟
    pub max: Duration,
    /// 平均延迟
    pub mean: Duration,
    /// 标准差
    pub std_dev: Duration,
    /// P50（中位数）
    pub p50: Duration,
    /// P75
    pub p75: Duration,
    /// P90
    pub p90: Duration,
    /// P95
    pub p95: Duration,
    /// P99
    pub p99: Duration,
    /// P99.9
    pub p999: Duration,
}

impl Default for LatencyMetrics {
    fn default() -> Self {
        Self {
            count: 0,
            min: Duration::ZERO,
            max: Duration::ZERO,
            mean: Duration::ZERO,
            std_dev: Duration::ZERO,
            p50: Duration::ZERO,
            p75: Duration::ZERO,
            p90: Duration::ZERO,
            p95: Duration::ZERO,
            p99: Duration::ZERO,
            p999: Duration::ZERO,
        }
    }
}

impl std::fmt::Display for LatencyMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "延迟统计 (样本数: {})", self.count)?;
        writeln!(f, "  最小值: {:?}", self.min)?;
        writeln!(f, "  最大值: {:?}", self.max)?;
        writeln!(f, "  平均值: {:?}", self.mean)?;
        writeln!(f, "  标准差: {:?}", self.std_dev)?;
        writeln!(f, "  P50:    {:?}", self.p50)?;
        writeln!(f, "  P75:    {:?}", self.p75)?;
        writeln!(f, "  P90:    {:?}", self.p90)?;
        writeln!(f, "  P95:    {:?}", self.p95)?;
        writeln!(f, "  P99:    {:?}", self.p99)?;
        writeln!(f, "  P99.9:  {:?}", self.p999)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_latency_analyzer() {
        let mut analyzer = LatencyAnalyzer::new();

        // 添加样本
        for i in 1..=100 {
            analyzer.record(Duration::from_millis(i));
        }

        let metrics = analyzer.analyze();

        assert_eq!(metrics.count, 100);
        assert_eq!(metrics.min, Duration::from_millis(1));
        assert_eq!(metrics.max, Duration::from_millis(100));
        assert_eq!(metrics.p50, Duration::from_millis(50));
        assert_eq!(metrics.p99, Duration::from_millis(99));
    }

    #[test]
    fn test_histogram() {
        let mut analyzer = LatencyAnalyzer::new();

        for i in 1..=100 {
            analyzer.record(Duration::from_micros(i * 100));
        }

        let histogram = analyzer.histogram(10);
        assert!(!histogram.is_empty());
    }

    #[test]
    fn test_empty_analyzer() {
        let analyzer = LatencyAnalyzer::new();
        let metrics = analyzer.analyze();

        assert_eq!(metrics.count, 0);
        assert_eq!(metrics.min, Duration::ZERO);
    }
}

