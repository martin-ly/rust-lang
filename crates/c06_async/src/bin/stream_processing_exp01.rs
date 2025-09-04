use futures::stream::{self, Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::time::{Duration, Instant};

/// 数据事件结构
#[derive(Debug, Clone)]
struct DataEvent {
    timestamp: Instant,
    value: f64,
    category: String,
}

impl DataEvent {
    fn new(value: f64, category: String) -> Self {
        Self {
            timestamp: Instant::now(),
            value,
            category,
        }
    }
}

/// 背压控制的流处理器
struct BackpressureStream<S> {
    inner: S,
    buffer_size: usize,
    buffer: Vec<DataEvent>,
}

impl<S> BackpressureStream<S>
where
    S: Stream<Item = DataEvent> + Unpin,
{
    fn new(inner: S, buffer_size: usize) -> Self {
        Self {
            inner,
            buffer_size,
            buffer: Vec::new(),
        }
    }
}

impl<S> Stream for BackpressureStream<S>
where
    S: Stream<Item = DataEvent> + Unpin,
{
    type Item = DataEvent;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 如果缓冲区未满，继续消费上游
        if self.buffer.len() < self.buffer_size {
            match Pin::new(&mut self.inner).poll_next(cx) {
                Poll::Ready(Some(event)) => {
                    self.buffer.push(event);
                    Poll::Ready(Some(self.buffer.remove(0)))
                }
                Poll::Ready(None) => {
                    if let Some(event) = self.buffer.pop() {
                        Poll::Ready(Some(event))
                    } else {
                        Poll::Ready(None)
                    }
                }
                Poll::Pending => Poll::Pending,
            }
        } else {
            // 缓冲区满，应用背压
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

/// 窗口聚合器
struct WindowAggregator {
    window_size: Duration,
    events: Vec<DataEvent>,
}

impl WindowAggregator {
    fn new(window_size: Duration) -> Self {
        Self {
            window_size,
            events: Vec::new(),
        }
    }

    /// 添加事件到窗口
    fn add_event(&mut self, event: DataEvent) {
        let now = Instant::now();
        
        // 移除过期事件
        self.events.retain(|e| now.duration_since(e.timestamp) <= self.window_size);
        
        // 添加新事件
        self.events.push(event);
    }

    /// 获取窗口统计信息
    fn get_stats(&self) -> WindowStats {
        if self.events.is_empty() {
            return WindowStats::default();
        }

        let values: Vec<f64> = self.events.iter().map(|e| e.value).collect();
        let count = values.len() as f64;
        let avg = values.iter().sum::<f64>() / count;
        
        let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        
        let variance = values.iter()
            .map(|v| (v - avg).powi(2))
            .sum::<f64>() / count;

        WindowStats {
            count: self.events.len(),
            avg,
            min,
            max,
            variance: variance.sqrt(), // 标准差
        }
    }
}

#[derive(Debug, Default)]
struct WindowStats {
    count: usize,
    avg: f64,
    min: f64,
    max: f64,
    variance: f64,
}

/// 流式 SQL 查询处理器
struct StreamSQLProcessor {
    aggregators: std::collections::HashMap<String, WindowAggregator>,
    window_size: Duration,
}

impl StreamSQLProcessor {
    fn new(window_size: Duration) -> Self {
        Self {
            aggregators: std::collections::HashMap::new(),
            window_size,
        }
    }

    /// 处理流式查询
    async fn process_query(&mut self, query: &str, events: impl Stream<Item = DataEvent> + Unpin) {
        println!("🔍 执行流式查询: {}", query);
        
        let mut events = events;
        let mut batch_count = 0;
        
        while let Some(event) = events.next().await {
            // 按类别分组聚合
            let aggregator = self.aggregators
                .entry(event.category.clone())
                .or_insert_with(|| WindowAggregator::new(self.window_size));
            
            aggregator.add_event(event);
            
            batch_count += 1;
            
            // 每处理 10 个事件输出一次统计
            if batch_count % 10 == 0 {
                self.print_stats();
            }
        }
        
        // 最终统计
        println!("\n📊 最终统计结果:");
        self.print_stats();
    }

    fn print_stats(&self) {
        for (category, aggregator) in &self.aggregators {
            let stats = aggregator.get_stats();
            if stats.count > 0 {
                println!("  {}: 数量={}, 平均值={:.2}, 范围=[{:.2}, {:.2}], 标准差={:.2}",
                    category, stats.count, stats.avg, stats.min, stats.max, stats.variance);
            }
        }
    }
}

/// 生成模拟数据流
async fn generate_data_stream() -> impl Stream<Item = DataEvent> + Unpin {
    let categories = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    
    Box::pin(stream::unfold((0u64, categories), |(mut id, categories)| async move {
        if id >= 100 {
            None
        } else {
            let category = categories[id as usize % categories.len()].clone();
            let value = (id as f64).sin() * 100.0 + (id as f64).cos() * 50.0;
            let event = DataEvent::new(value, category);
            id += 1;
            Some((event, (id, categories)))
        }
    }))
}

/// 背压测试
async fn test_backpressure() {
    println!("🚀 背压控制测试");
    println!("{}", "=".repeat(40));
    
    let data_stream = generate_data_stream().await;
    let backpressure_stream = BackpressureStream::new(
        data_stream,
        5 // 缓冲区大小
    );
    
    let mut count = 0;
    let start = Instant::now();
    
    tokio::pin!(backpressure_stream);
    
    while let Some(_event) = backpressure_stream.next().await {
        count += 1;
        if count % 20 == 0 {
            println!("  已处理 {} 个事件", count);
        }
        
        // 模拟处理延迟
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    
    let duration = start.elapsed();
    println!("✅ 背压测试完成: 处理 {} 个事件，耗时 {:?}", count, duration);
}

/// 窗口聚合测试
async fn test_window_aggregation() {
    println!("\n🚀 窗口聚合测试");
    println!("{}", "=".repeat(40));
    
    let mut processor = StreamSQLProcessor::new(Duration::from_secs(5));
    let data_stream = generate_data_stream().await;
    
    // 模拟流式 SQL 查询
    let query = "SELECT category, AVG(value), COUNT(*) FROM events GROUP BY category WINDOW 5s";
    processor.process_query(query, data_stream).await;
}

#[tokio::main]
async fn main() {
    println!("🚀 流式处理示例启动");
    println!("{}", "=".repeat(50));
    
    // 测试背压控制
    test_backpressure().await;
    
    // 测试窗口聚合
    test_window_aggregation().await;
    
    println!("\n{}", "=".repeat(50));
    println!("🎯 流式处理示例完成");
}
