use anyhow::Result;
use futures::{StreamExt};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, Semaphore};
use tokio::time::{interval, sleep};
use tracing::{info, warn, error, debug};

/// 流处理管道配置
#[derive(Debug, Clone)]
pub struct StreamConfig {
    pub buffer_size: usize,
    pub max_concurrent: usize,
    pub window_size: usize,
    pub window_duration: Duration,
    pub backpressure_threshold: f64,
}

impl Default for StreamConfig {
    fn default() -> Self {
        Self {
            buffer_size: 1000,
            max_concurrent: 10,
            window_size: 100,
            window_duration: Duration::from_secs(1),
            backpressure_threshold: 0.8,
        }
    }
}

/// 数据项
#[derive(Debug, Clone)]
pub struct DataItem {
    pub id: u64,
    pub timestamp: Instant,
    pub value: f64,
    pub category: String,
}

/// 窗口聚合结果
#[derive(Debug)]
pub struct WindowResult {
    pub window_start: Instant,
    pub window_end: Instant,
    pub count: usize,
    pub sum: f64,
    pub avg: f64,
    pub min: f64,
    pub max: f64,
    pub categories: std::collections::HashMap<String, usize>,
}

/// 流处理器
pub struct StreamProcessor {
    config: StreamConfig,
    semaphore: Arc<Semaphore>,
    metrics: ProcessingMetrics,
}

impl Clone for StreamProcessor {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            semaphore: self.semaphore.clone(),
            metrics: ProcessingMetrics {
                items_processed: std::sync::atomic::AtomicU64::new(self.metrics.items_processed.load(std::sync::atomic::Ordering::Relaxed)),
                items_dropped: std::sync::atomic::AtomicU64::new(self.metrics.items_dropped.load(std::sync::atomic::Ordering::Relaxed)),
                processing_errors: std::sync::atomic::AtomicU64::new(self.metrics.processing_errors.load(std::sync::atomic::Ordering::Relaxed)),
                avg_processing_time: std::sync::atomic::AtomicU64::new(self.metrics.avg_processing_time.load(std::sync::atomic::Ordering::Relaxed)),
                backpressure_events: std::sync::atomic::AtomicU64::new(self.metrics.backpressure_events.load(std::sync::atomic::Ordering::Relaxed)),
            },
        }
    }
}

#[derive(Debug, Default)]
struct ProcessingMetrics {
    pub items_processed: std::sync::atomic::AtomicU64,
    pub items_dropped: std::sync::atomic::AtomicU64,
    pub processing_errors: std::sync::atomic::AtomicU64,
    pub avg_processing_time: std::sync::atomic::AtomicU64,
    pub backpressure_events: std::sync::atomic::AtomicU64,
}

impl StreamProcessor {
    pub fn new(config: StreamConfig) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(config.max_concurrent)),
            metrics: ProcessingMetrics::default(),
            config,
        }
    }

    /// 创建数据流（模拟数据源）
    pub fn create_data_stream() -> impl futures::Stream<Item = DataItem> + Unpin {
        let (tx, rx) = mpsc::unbounded_channel();
        
        // 启动数据生成任务
        let tx_clone = tx.clone();
        tokio::spawn(async move {
            let mut counter = 0u64;
            let mut interval = interval(Duration::from_millis(10));
            
            loop {
                interval.tick().await;
                counter += 1;
                
                let item = DataItem {
                    id: counter,
                    timestamp: Instant::now(),
                    value: (counter as f64).sin() * 100.0,
                    category: match counter % 3 {
                        0 => "A".to_string(),
                        1 => "B".to_string(),
                        _ => "C".to_string(),
                    },
                };
                
                if tx_clone.send(item).is_err() {
                    break;
                }
            }
        });
        
        tokio_stream::wrappers::UnboundedReceiverStream::new(rx)
    }

    /// 处理单个数据项
    async fn process_item(&mut self, item: DataItem) -> Result<DataItem> {
        let _permit = self.semaphore.acquire().await?;
        let start = Instant::now();
        
        // 模拟处理时间（有时会失败）
        if item.id % 100 == 0 {
            sleep(Duration::from_millis(50)).await; // 慢处理
        } else if item.id % 200 == 0 {
            return Err(anyhow::anyhow!("Simulated processing error"));
        } else {
            sleep(Duration::from_millis(5)).await; // 正常处理
        }
        
        let processing_time = start.elapsed();
        
        // 更新指标
        self.update_metrics(processing_time, false);
        
        debug!(item_id = item.id, processing_time_ms = processing_time.as_millis(), "Item processed");
        Ok(item)
    }

    /// 窗口聚合处理
    async fn process_window(&self, items: Vec<DataItem>) -> WindowResult {
        let start = items.first().map(|i| i.timestamp).unwrap_or_else(Instant::now);
        let end = items.last().map(|i| i.timestamp).unwrap_or_else(Instant::now);
        
        let count = items.len();
        let sum: f64 = items.iter().map(|i| i.value).sum();
        let avg = if count > 0 { sum / count as f64 } else { 0.0 };
        let min = items.iter().map(|i| i.value).fold(f64::INFINITY, f64::min);
        let max = items.iter().map(|i| i.value).fold(f64::NEG_INFINITY, f64::max);
        
        let mut categories = std::collections::HashMap::new();
        for item in &items {
            *categories.entry(item.category.clone()).or_insert(0) += 1;
        }
        
        WindowResult {
            window_start: start,
            window_end: end,
            count,
            sum,
            avg,
            min,
            max,
            categories,
        }
    }

    /// 更新处理指标
    fn update_metrics(&self, processing_time: Duration, is_error: bool) {
        if is_error {
            self.metrics.processing_errors.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        } else {
            self.metrics.items_processed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            // 简化的平均时间计算
            let current_avg = self.metrics.avg_processing_time.load(std::sync::atomic::Ordering::Relaxed);
            let new_avg = (current_avg + processing_time.as_nanos() as u64) / 2;
            self.metrics.avg_processing_time.store(new_avg, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// 检查背压条件
    #[allow(dead_code)]
    fn check_backpressure(&self, queue_size: usize) -> bool {
        let utilization = queue_size as f64 / self.config.buffer_size as f64;
        if utilization > self.config.backpressure_threshold {
            self.metrics.backpressure_events.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    /// 运行流处理管道
    pub async fn run_pipeline(&self) -> Result<()> {
        let (tx, mut rx) = mpsc::channel::<DataItem>(self.config.buffer_size);
        
        // 数据源任务
        let data_stream = StreamProcessor::create_data_stream();
        let tx_clone = tx.clone();
        let source_task = tokio::spawn(async move {
            let mut stream = data_stream;
            while let Some(item) = stream.next().await {
                if tx_clone.send(item).await.is_err() {
                    break; // 接收端已关闭
                }
            }
        });

        // 处理任务
        let config = self.config.clone();
        let processing_task = tokio::spawn(async move {
            let mut window_buffer = Vec::new();
            let mut last_window_time = Instant::now();
            
            while let Some(item) = rx.recv().await {
                // 检查背压
                let queue_size = rx.len();
                if queue_size > (config.buffer_size as f64 * config.backpressure_threshold) as usize {
                    warn!(queue_size, "Backpressure detected, dropping item {}", item.id);
                    continue;
                }
                
                // 处理项目
                let mut processor = StreamProcessor::new(config.clone());
                match processor.process_item(item.clone()).await {
                    Ok(processed_item) => {
                        window_buffer.push(processed_item);
                        
                        // 检查是否需要输出窗口
                        if window_buffer.len() >= config.window_size 
                            || last_window_time.elapsed() >= config.window_duration {
                            
                            if !window_buffer.is_empty() {
                                let window_result = processor.process_window(window_buffer.clone()).await;
                                info!(
                                    window_count = window_result.count,
                                    window_avg = window_result.avg,
                                    window_min = window_result.min,
                                    window_max = window_result.max,
                                    "Window processed"
                                );
                                
                                window_buffer.clear();
                                last_window_time = Instant::now();
                            }
                        }
                    }
                    Err(e) => {
                        error!(error = %e, item_id = item.id, "Failed to process item");
                        // 注意：这里无法直接更新指标，因为 self 不可变
                    }
                }
            }
        });

        // 指标报告任务
        let metrics_clone = ProcessingMetrics {
            items_processed: std::sync::atomic::AtomicU64::new(self.metrics.items_processed.load(std::sync::atomic::Ordering::Relaxed)),
            items_dropped: std::sync::atomic::AtomicU64::new(self.metrics.items_dropped.load(std::sync::atomic::Ordering::Relaxed)),
            processing_errors: std::sync::atomic::AtomicU64::new(self.metrics.processing_errors.load(std::sync::atomic::Ordering::Relaxed)),
            avg_processing_time: std::sync::atomic::AtomicU64::new(self.metrics.avg_processing_time.load(std::sync::atomic::Ordering::Relaxed)),
            backpressure_events: std::sync::atomic::AtomicU64::new(self.metrics.backpressure_events.load(std::sync::atomic::Ordering::Relaxed)),
        };
        let metrics_task = tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(5));
            loop {
                interval.tick().await;
                info!(
                    processed = metrics_clone.items_processed.load(std::sync::atomic::Ordering::Relaxed),
                    dropped = metrics_clone.items_dropped.load(std::sync::atomic::Ordering::Relaxed),
                    errors = metrics_clone.processing_errors.load(std::sync::atomic::Ordering::Relaxed),
                    avg_time_ms = Duration::from_nanos(metrics_clone.avg_processing_time.load(std::sync::atomic::Ordering::Relaxed)).as_millis() as u64,
                    "Processing metrics"
                );
            }
        });

        // 运行一段时间后停止
        sleep(Duration::from_secs(30)).await;
        
        // 关闭数据源
        drop(tx);
        
        // 等待任务完成
        let _ = tokio::join!(source_task, processing_task, metrics_task);
        
        info!("Stream processing pipeline completed");
        Ok(())
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    let config = StreamConfig {
        buffer_size: 500,
        max_concurrent: 8,
        window_size: 50,
        window_duration: Duration::from_millis(500),
        backpressure_threshold: 0.7,
    };

    let processor = StreamProcessor::new(config);
    processor.run_pipeline().await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_window_aggregation() {
        let processor = StreamProcessor::new(StreamConfig::default());
        
        let items = vec![
            DataItem { id: 1, timestamp: Instant::now(), value: 10.0, category: "A".to_string() },
            DataItem { id: 2, timestamp: Instant::now(), value: 20.0, category: "B".to_string() },
            DataItem { id: 3, timestamp: Instant::now(), value: 30.0, category: "A".to_string() },
        ];
        
        let result = processor.process_window(items).await;
        
        assert_eq!(result.count, 3);
        assert_eq!(result.sum, 60.0);
        assert_eq!(result.avg, 20.0);
        assert_eq!(result.min, 10.0);
        assert_eq!(result.max, 30.0);
        assert_eq!(result.categories.get("A"), Some(&2));
        assert_eq!(result.categories.get("B"), Some(&1));
    }

    #[tokio::test]
    async fn test_backpressure_detection() {
        let processor = StreamProcessor::new(StreamConfig {
            buffer_size: 10,
            backpressure_threshold: 0.5,
            ..Default::default()
        });
        
        assert!(!processor.check_backpressure(4)); // 40% utilization
        assert!(processor.check_backpressure(6));  // 60% utilization
    }
}
