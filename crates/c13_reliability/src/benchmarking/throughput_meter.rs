/// 吞吐量测量器
///
/// 用于测量系统吞吐量和处理能力

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// 吞吐量测量器
#[derive(Clone)]
pub struct ThroughputMeter {
    state: Arc<RwLock<MeterState>>,
}

#[derive(Debug)]
struct MeterState {
    start_time: Instant,
    request_count: u64,
    byte_count: u64,
    checkpoints: Vec<Checkpoint>,
}

#[derive(Debug, Clone)]
struct Checkpoint {
    timestamp: Instant,
    request_count: u64,
    byte_count: u64,
}

impl ThroughputMeter {
    /// 创建新的吞吐量测量器
    pub fn new() -> Self {
        Self {
            state: Arc::new(RwLock::new(MeterState {
                start_time: Instant::now(),
                request_count: 0,
                byte_count: 0,
                checkpoints: Vec::new(),
            })),
        }
    }

    /// 记录一个请求
    pub async fn record_request(&self) {
        let mut state = self.state.write().await;
        state.request_count += 1;
    }

    /// 记录请求和字节数
    pub async fn record(&self, bytes: u64) {
        let mut state = self.state.write().await;
        state.request_count += 1;
        state.byte_count += bytes;
    }

    /// 批量记录请求
    pub async fn record_batch(&self, count: u64, total_bytes: u64) {
        let mut state = self.state.write().await;
        state.request_count += count;
        state.byte_count += total_bytes;
    }

    /// 创建检查点
    pub async fn checkpoint(&self) {
        let mut state = self.state.write().await;
        let request_count = state.request_count;
        let byte_count = state.byte_count;
        state.checkpoints.push(Checkpoint {
            timestamp: Instant::now(),
            request_count,
            byte_count,
        });
    }

    /// 获取当前指标
    pub async fn metrics(&self) -> ThroughputMetrics {
        let state = self.state.read().await;
        let elapsed = state.start_time.elapsed();

        ThroughputMetrics {
            total_requests: state.request_count,
            total_bytes: state.byte_count,
            elapsed,
            requests_per_second: if elapsed.as_secs_f64() > 0.0 {
                state.request_count as f64 / elapsed.as_secs_f64()
            } else {
                0.0
            },
            bytes_per_second: if elapsed.as_secs_f64() > 0.0 {
                state.byte_count as f64 / elapsed.as_secs_f64()
            } else {
                0.0
            },
        }
    }

    /// 获取时间窗口内的指标
    pub async fn window_metrics(&self, window: Duration) -> ThroughputMetrics {
        let state = self.state.read().await;
        let now = Instant::now();
        let window_start = now - window;

        // 找到窗口开始前的最后一个检查点
        let mut start_requests = 0;
        let mut start_bytes = 0;

        for checkpoint in &state.checkpoints {
            if checkpoint.timestamp <= window_start {
                start_requests = checkpoint.request_count;
                start_bytes = checkpoint.byte_count;
            } else {
                break;
            }
        }

        let requests_in_window = state.request_count - start_requests;
        let bytes_in_window = state.byte_count - start_bytes;

        ThroughputMetrics {
            total_requests: requests_in_window,
            total_bytes: bytes_in_window,
            elapsed: window,
            requests_per_second: if window.as_secs_f64() > 0.0 {
                requests_in_window as f64 / window.as_secs_f64()
            } else {
                0.0
            },
            bytes_per_second: if window.as_secs_f64() > 0.0 {
                bytes_in_window as f64 / window.as_secs_f64()
            } else {
                0.0
            },
        }
    }

    /// 重置计数器
    pub async fn reset(&self) {
        let mut state = self.state.write().await;
        state.start_time = Instant::now();
        state.request_count = 0;
        state.byte_count = 0;
        state.checkpoints.clear();
    }
}

impl Default for ThroughputMeter {
    fn default() -> Self {
        Self::new()
    }
}

/// 吞吐量指标
#[derive(Debug, Clone, PartialEq)]
pub struct ThroughputMetrics {
    /// 总请求数
    pub total_requests: u64,
    /// 总字节数
    pub total_bytes: u64,
    /// 经过时间
    pub elapsed: Duration,
    /// 每秒请求数
    pub requests_per_second: f64,
    /// 每秒字节数
    pub bytes_per_second: f64,
}

impl ThroughputMetrics {
    /// 获取带宽（MB/s）
    pub fn bandwidth_mbps(&self) -> f64 {
        self.bytes_per_second / (1024.0 * 1024.0)
    }

    /// 获取带宽（Mbps）
    pub fn bandwidth_megabits(&self) -> f64 {
        self.bytes_per_second * 8.0 / 1_000_000.0
    }
}

impl std::fmt::Display for ThroughputMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "吞吐量统计 (测量时间: {:?})", self.elapsed)?;
        writeln!(f, "  总请求数:    {}", self.total_requests)?;
        writeln!(f, "  总字节数:    {} bytes", self.total_bytes)?;
        writeln!(f, "  请求/秒:     {:.2}", self.requests_per_second)?;
        writeln!(f, "  字节/秒:     {:.2} bytes/s", self.bytes_per_second)?;
        writeln!(f, "  带宽(MB/s):  {:.2}", self.bandwidth_mbps())?;
        writeln!(f, "  带宽(Mbps):  {:.2}", self.bandwidth_megabits())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_throughput_meter() {
        let meter = ThroughputMeter::new();

        // 记录一些请求
        for _ in 0..100 {
            meter.record(1024).await;
        }

        let metrics = meter.metrics().await;

        assert_eq!(metrics.total_requests, 100);
        assert_eq!(metrics.total_bytes, 102400);
        assert!(metrics.requests_per_second > 0.0);
    }

    #[tokio::test]
    async fn test_checkpoint() {
        let meter = ThroughputMeter::new();

        // 第一批请求
        for _ in 0..50 {
            meter.record_request().await;
        }

        meter.checkpoint().await;
        sleep(Duration::from_millis(10)).await;

        // 第二批请求
        for _ in 0..50 {
            meter.record_request().await;
        }

        let metrics = meter.metrics().await;
        assert_eq!(metrics.total_requests, 100);
    }

    #[tokio::test]
    async fn test_reset() {
        let meter = ThroughputMeter::new();

        meter.record(1000).await;
        meter.reset().await;

        let metrics = meter.metrics().await;
        assert_eq!(metrics.total_requests, 0);
        assert_eq!(metrics.total_bytes, 0);
    }
}

