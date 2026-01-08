use anyhow::Result;
use prometheus::{
    Counter, CounterVec, Gauge, GaugeVec, Histogram, HistogramOpts,
    Opts, Registry, TextEncoder,
};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::{interval, sleep};
use tracing::{info, error, debug};

/// 应用指标收集器
#[derive(Debug, Clone)]
pub struct MetricsCollector {
    // 计数器
    pub requests_total: Counter,
    pub errors_total: CounterVec,

    // 仪表盘
    pub active_connections: Gauge,
    pub memory_usage_bytes: Gauge,
    pub cpu_usage_percent: Gauge,

    // 直方图
    pub request_duration_seconds: Histogram,
    pub response_size_bytes: Histogram,

    // 自定义指标
    pub custom_metrics: CustomMetrics,

    registry: Registry,
}

#[derive(Debug, Clone)]
pub struct CustomMetrics {
    pub queue_size: GaugeVec,
    pub processing_rate: GaugeVec,
    pub cache_hit_ratio: GaugeVec,
}

impl MetricsCollector {
    pub fn new() -> Result<Self> {
        let registry = Registry::new();

        // 基础计数器
        let requests_total = Counter::new(
            "http_requests_total",
            "Total number of HTTP requests"
        )?;

        let errors_total = CounterVec::new(
            Opts::new("http_errors_total", "Total number of HTTP errors")
                .namespace("app"),
            &["method", "status_code", "endpoint"]
        )?;

        // 仪表盘
        let active_connections = Gauge::new(
            "active_connections",
            "Number of active connections"
        )?;

        let memory_usage_bytes = Gauge::new(
            "memory_usage_bytes",
            "Current memory usage in bytes"
        )?;

        let cpu_usage_percent = Gauge::new(
            "cpu_usage_percent",
            "Current CPU usage percentage"
        )?;

        // 直方图
        let request_duration_seconds = Histogram::with_opts(
            HistogramOpts::new("http_request_duration_seconds", "HTTP request duration")
                .buckets(vec![0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0])
        )?;

        let response_size_bytes = Histogram::with_opts(
            HistogramOpts::new("http_response_size_bytes", "HTTP response size in bytes")
                .buckets(vec![100.0, 1000.0, 10000.0, 100000.0, 1000000.0])
        )?;

        // 自定义指标
        let queue_size = GaugeVec::new(
            Opts::new("queue_size", "Current queue size")
                .namespace("custom"),
            &["queue_name"]
        )?;

        let processing_rate = GaugeVec::new(
            Opts::new("processing_rate", "Items processed per second")
                .namespace("custom"),
            &["processor_type"]
        )?;

        let cache_hit_ratio = GaugeVec::new(
            Opts::new("cache_hit_ratio", "Cache hit ratio")
                .namespace("custom"),
            &["cache_name"]
        )?;

        let custom_metrics = CustomMetrics {
            queue_size,
            processing_rate,
            cache_hit_ratio,
        };

        // 注册所有指标
        registry.register(Box::new(requests_total.clone()))?;
        registry.register(Box::new(errors_total.clone()))?;
        registry.register(Box::new(active_connections.clone()))?;
        registry.register(Box::new(memory_usage_bytes.clone()))?;
        registry.register(Box::new(cpu_usage_percent.clone()))?;
        registry.register(Box::new(request_duration_seconds.clone()))?;
        registry.register(Box::new(response_size_bytes.clone()))?;
        registry.register(Box::new(custom_metrics.queue_size.clone()))?;
        registry.register(Box::new(custom_metrics.processing_rate.clone()))?;
        registry.register(Box::new(custom_metrics.cache_hit_ratio.clone()))?;

        Ok(Self {
            requests_total,
            errors_total,
            active_connections,
            memory_usage_bytes,
            cpu_usage_percent,
            request_duration_seconds,
            response_size_bytes,
            custom_metrics,
            registry,
        })
    }

    /// 记录请求
    pub fn record_request(&self, method: &str, status_code: u16, endpoint: &str, duration: Duration, response_size: usize) {
        self.requests_total.inc();

        if status_code >= 400 {
            self.errors_total.with_label_values(&[method, &status_code.to_string(), endpoint]).inc();
        }

        self.request_duration_seconds.observe(duration.as_secs_f64());
        self.response_size_bytes.observe(response_size as f64);
    }

    /// 更新连接数
    pub fn update_connections(&self, count: i64) {
        self.active_connections.set(count as f64);
    }

    /// 更新内存使用
    pub fn update_memory_usage(&self, bytes: u64) {
        self.memory_usage_bytes.set(bytes as f64);
    }

    /// 更新 CPU 使用率
    pub fn update_cpu_usage(&self, percent: f64) {
        self.cpu_usage_percent.set(percent);
    }

    /// 更新队列大小
    pub fn update_queue_size(&self, queue_name: &str, size: usize) {
        self.custom_metrics.queue_size.with_label_values(&[queue_name]).set(size as f64);
    }

    /// 更新处理速率
    pub fn update_processing_rate(&self, processor_type: &str, rate: f64) {
        self.custom_metrics.processing_rate.with_label_values(&[processor_type]).set(rate);
    }

    /// 更新缓存命中率
    pub fn update_cache_hit_ratio(&self, cache_name: &str, ratio: f64) {
        self.custom_metrics.cache_hit_ratio.with_label_values(&[cache_name]).set(ratio);
    }

    /// 获取指标文本格式
    pub fn gather_metrics(&self) -> Result<String> {
        let metric_families = self.registry.gather();
        let encoder = TextEncoder::new();
        let encoded = encoder.encode_to_string(&metric_families)?;
        Ok(encoded)
    }
}

/// 模拟应用服务
pub struct ApplicationService {
    metrics: MetricsCollector,
    request_count: RwLock<u64>,
    error_count: RwLock<u64>,
}

impl ApplicationService {
    pub fn new() -> Result<Self> {
        Ok(Self {
            metrics: MetricsCollector::new()?,
            request_count: RwLock::new(0),
            error_count: RwLock::new(0),
        })
    }

    /// 模拟处理请求
    pub async fn handle_request(&self, method: &str, endpoint: &str) -> Result<(u16, usize)> {
        let start = Instant::now();

        // 模拟处理时间
        let processing_time = Duration::from_millis(rand::random::<u64>() % 100 + 10);
        sleep(processing_time).await;

        // 模拟响应大小
        let response_size = (rand::random::<u32>() % 10000 + 100) as usize;

        // 模拟错误率（10%）
        let status_code = if rand::random::<f64>() < 0.1 {
            500
        } else {
            200
        };

        // 记录指标
        self.metrics.record_request(
            method,
            status_code,
            endpoint,
            start.elapsed(),
            response_size
        );

        // 更新计数器
        {
            let mut count = self.request_count.write().await;
            *count += 1;
        }

        if status_code >= 400 {
            let mut count = self.error_count.write().await;
            *count += 1;
        }

        Ok((status_code, response_size))
    }

    /// 启动系统指标收集
    pub async fn start_system_metrics_collection(&self) {
        let metrics = self.metrics.clone();

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(5));

            loop {
                interval.tick().await;

                // 模拟系统指标
                let memory_usage = rand::random::<u64>() % 1000000000 + 500000000; // 500MB - 1.5GB
                let cpu_usage = rand::random::<f64>() * 100.0; // 0-100%
                let connections = rand::random::<i64>() % 1000 + 100; // 100-1100

                metrics.update_memory_usage(memory_usage);
                metrics.update_cpu_usage(cpu_usage);
                metrics.update_connections(connections);

                debug!(
                    memory_mb = memory_usage / 1024 / 1024,
                    cpu_percent = cpu_usage,
                    connections = connections,
                    "Updated system metrics"
                );
            }
        });
    }

    /// 启动自定义指标更新
    pub async fn start_custom_metrics_update(&self) {
        let metrics = self.metrics.clone();

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(2));

            loop {
                interval.tick().await;

                // 模拟队列指标
                let queue_sizes = vec![
                    ("input_queue", (rand::random::<u32>() % 1000) as usize),
                    ("processing_queue", (rand::random::<u32>() % 500) as usize),
                    ("output_queue", (rand::random::<u32>() % 200) as usize),
                ];

                for (queue_name, size) in queue_sizes {
                    metrics.update_queue_size(queue_name, size);
                }

                // 模拟处理速率
                let processing_rates = vec![
                    ("data_processor", rand::random::<f64>() * 100.0),
                    ("image_processor", rand::random::<f64>() * 50.0),
                    ("text_processor", rand::random::<f64>() * 200.0),
                ];

                for (processor_type, rate) in processing_rates {
                    metrics.update_processing_rate(processor_type, rate);
                }

                // 模拟缓存命中率
                let cache_ratios = vec![
                    ("redis_cache", rand::random::<f64>() * 0.3 + 0.7), // 70-100%
                    ("memory_cache", rand::random::<f64>() * 0.2 + 0.8), // 80-100%
                ];

                for (cache_name, ratio) in cache_ratios {
                    metrics.update_cache_hit_ratio(cache_name, ratio);
                }
            }
        });
    }

    /// 启动指标导出服务
    pub async fn start_metrics_server(&self, port: u16) -> Result<()> {
        let metrics = self.metrics.clone();

        tokio::spawn(async move {
            use axum::{routing::get, Router, response::Html};

            let app = Router::new()
                .route("/metrics", get(move || async move {
                    match metrics.gather_metrics() {
                        Ok(metrics_text) => Html(metrics_text),
                        Err(e) => {
                            error!(error = %e, "Failed to gather metrics");
                            Html("Error gathering metrics".to_string())
                        }
                    }
                }));

            let addr = format!("0.0.0.0:{}", port);
            let listener = tokio::net::TcpListener::bind(&addr).await.unwrap();

            info!(port = port, "Metrics server started");
            axum::serve(listener, app).await.unwrap();
        });

        Ok(())
    }

    /// 获取当前统计
    pub async fn get_stats(&self) -> (u64, u64) {
        let requests = *self.request_count.read().await;
        let errors = *self.error_count.read().await;
        (requests, errors)
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    // 创建应用服务
    let app = ApplicationService::new()?;

    // 启动指标收集
    app.start_system_metrics_collection().await;
    app.start_custom_metrics_update().await;

    // 启动指标服务器
    app.start_metrics_server(9090).await?;

    info!("Application started. Metrics available at http://localhost:9090/metrics");

    // 模拟请求处理
    let endpoints = vec!["/api/users", "/api/orders", "/api/products", "/api/health"];
    let methods = vec!["GET", "POST", "PUT", "DELETE"];

    for i in 1..=100 {
        let method = methods[i % methods.len()];
        let endpoint = endpoints[i % endpoints.len()];

        match app.handle_request(method, endpoint).await {
            Ok((status, size)) => {
                debug!(
                    request_id = i,
                    method = method,
                    endpoint = endpoint,
                    status = status,
                    response_size = size,
                    "Request processed"
                );
            }
            Err(e) => {
                error!(error = %e, "Failed to process request");
            }
        }

        // 随机延迟
        sleep(Duration::from_millis(rand::random::<u64>() % 100 + 10)).await;
    }

    // 显示最终统计
    let (total_requests, total_errors) = app.get_stats().await;
    info!(
        total_requests = total_requests,
        total_errors = total_errors,
        error_rate = if total_requests > 0 { total_errors as f64 / total_requests as f64 } else { 0.0 },
        "Final statistics"
    );

    // 导出最终指标
    let metrics_text = app.metrics.gather_metrics()?;
    info!("Final metrics:\n{}", metrics_text);

    info!("Metrics collection demo completed");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metrics_collector() {
        let collector = MetricsCollector::new().unwrap();

        // 测试指标记录
        collector.record_request("GET", 200, "/test", Duration::from_millis(100), 1024);
        collector.update_connections(50);
        collector.update_memory_usage(1024 * 1024);
        collector.update_cpu_usage(75.5);

        // 测试指标导出
        let metrics = collector.gather_metrics().unwrap();
        assert!(metrics.contains("http_requests_total"));
        assert!(metrics.contains("active_connections"));
        assert!(metrics.contains("memory_usage_bytes"));
    }

    #[tokio::test]
    async fn test_application_service() {
        let app = ApplicationService::new().unwrap();

        let (status, size) = app.handle_request("GET", "/test").await.unwrap();
        assert!(status >= 200 && status < 600);
        assert!(size > 0);

        let (requests, errors) = app.get_stats().await;
        assert_eq!(requests, 1);
        assert!(errors <= 1);
    }
}
