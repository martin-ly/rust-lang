use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock};
use tokio::time::sleep;
use tracing::{info, debug};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
//use std::sync::atomic::{AtomicUsize, AtomicU64, Ordering};

/// 2025年异步监控和可观测性演示
/// 展示最新的异步监控编程模式和最佳实践

/// 1. 异步指标收集器
#[derive(Debug, Clone)]
pub struct AsyncMetricsCollector {
    metrics: Arc<RwLock<HashMap<String, Metric>>>,
    collectors: Arc<RwLock<Vec<MetricsCollector>>>,
    config: MetricsConfig,
    stats: Arc<RwLock<CollectorStats>>,
}

#[derive(Debug, Clone)]
pub struct Metric {
    pub name: String,
    pub value: f64,
    pub metric_type: MetricType,
    pub labels: HashMap<String, String>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MetricType {
    Counter,
    Gauge,
    Histogram,
    Summary,
}

#[derive(Debug, Clone)]
pub struct MetricsCollector {
    pub id: String,
    pub name: String,
    pub collection_interval: Duration,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub struct MetricsConfig {
    pub collection_interval: Duration,
    pub retention_period: Duration,
    pub max_metrics: usize,
    pub enable_aggregation: bool,
}

impl Default for MetricsConfig {
    fn default() -> Self {
        Self {
            collection_interval: Duration::from_secs(10),
            retention_period: Duration::from_secs(3600),
            max_metrics: 10000,
            enable_aggregation: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CollectorStats {
    pub total_metrics_collected: usize,
    pub active_collectors: usize,
    pub collection_errors: usize,
    pub last_collection_time: Option<Instant>,
}

impl AsyncMetricsCollector {
    pub fn new(config: MetricsConfig) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            collectors: Arc::new(RwLock::new(Vec::new())),
            config,
            stats: Arc::new(RwLock::new(CollectorStats::default())),
        }
    }

    pub async fn record_metric(&self, name: String, value: f64, metric_type: MetricType, labels: HashMap<String, String>) -> Result<()> {
        let metric = Metric {
            name: name.clone(),
            value,
            metric_type,
            labels,
            timestamp: Instant::now(),
        };
        
        let mut metrics = self.metrics.write().await;
        metrics.insert(name.clone(), metric);
        
        let mut stats = self.stats.write().await;
        stats.total_metrics_collected += 1;
        
        debug!("记录指标: {} = {}", name, value);
        Ok(())
    }

    pub async fn add_collector(&self, collector: MetricsCollector) -> Result<()> {
        let mut collectors = self.collectors.write().await;
        collectors.push(collector.clone());
        
        let mut stats = self.stats.write().await;
        stats.active_collectors += 1;
        
        info!("添加指标收集器: {}", collector.name);
        Ok(())
    }

    pub async fn start_collection(&self) -> Result<()> {
        let collectors = self.collectors.read().await;
        let mut tasks = Vec::new();
        
        for collector in collectors.iter() {
            if collector.enabled {
                let collector_clone = self.clone();
                let collector_id = collector.id.clone();
                
                let task = tokio::spawn(async move {
                    collector_clone.collection_loop(&collector_id).await;
                });
                
                tasks.push(task);
            }
        }
        
        info!("启动 {} 个指标收集器", tasks.len());
        Ok(())
    }

    async fn collection_loop(&self, collector_id: &str) {
        let mut interval = tokio::time::interval(self.config.collection_interval);
        
        loop {
            interval.tick().await;
            
            // 模拟指标收集
            let labels = [("collector".to_string(), collector_id.to_string())].iter().cloned().collect();
            let _ = self.record_metric(
                format!("collector_metrics_{}", collector_id),
                rand::random::<f64>() * 100.0,
                MetricType::Gauge,
                labels,
            ).await;
        }
    }

    pub async fn get_metrics(&self) -> HashMap<String, Metric> {
        self.metrics.read().await.clone()
    }

    pub async fn get_stats(&self) -> CollectorStats {
        self.stats.read().await.clone()
    }
}

/// 2. 异步日志聚合器
#[derive(Debug, Clone)]
pub struct AsyncLogAggregator {
    logs: Arc<RwLock<Vec<LogEntry>>>,
    aggregators: Arc<RwLock<Vec<LogAggregator>>>,
    config: LogConfig,
    stats: Arc<RwLock<LogStats>>,
}

#[derive(Debug, Clone)]
pub struct LogEntry {
    pub id: String,
    pub level: LogLevel,
    pub message: String,
    pub timestamp: Instant,
    pub source: String,
    pub fields: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

#[derive(Debug, Clone)]
pub struct LogAggregator {
    pub id: String,
    pub name: String,
    pub filter_level: LogLevel,
    pub aggregation_rules: Vec<AggregationRule>,
}

#[derive(Debug, Clone)]
pub struct AggregationRule {
    pub pattern: String,
    pub aggregation_type: AggregationType,
    pub time_window: Duration,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AggregationType {
    Count,
    Sum,
    Average,
    Max,
    Min,
}

#[derive(Debug, Clone)]
pub struct LogConfig {
    pub max_logs: usize,
    pub retention_period: Duration,
    pub enable_aggregation: bool,
    pub aggregation_interval: Duration,
}

impl Default for LogConfig {
    fn default() -> Self {
        Self {
            max_logs: 100000,
            retention_period: Duration::from_secs(86400),
            enable_aggregation: true,
            aggregation_interval: Duration::from_secs(60),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct LogStats {
    pub total_logs: usize,
    pub aggregated_logs: usize,
    pub active_aggregators: usize,
    pub aggregation_errors: usize,
}

impl AsyncLogAggregator {
    pub fn new(config: LogConfig) -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            aggregators: Arc::new(RwLock::new(Vec::new())),
            config,
            stats: Arc::new(RwLock::new(LogStats::default())),
        }
    }

    pub async fn log(&self, level: LogLevel, message: String, source: String, fields: HashMap<String, String>) -> Result<()> {
        let log_entry = LogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            level,
            message,
            timestamp: Instant::now(),
            source,
            fields,
        };
        
        let mut logs = self.logs.write().await;
        logs.push(log_entry.clone());
        
        let mut stats = self.stats.write().await;
        stats.total_logs += 1;
        
        // 限制日志数量
        if logs.len() > self.config.max_logs {
            let excess = logs.len() - self.config.max_logs;
            logs.drain(0..excess);
        }
        
        debug!("记录日志: {:?} - {}", log_entry.level, log_entry.message);
        Ok(())
    }

    pub async fn add_aggregator(&self, aggregator: LogAggregator) -> Result<()> {
        let mut aggregators = self.aggregators.write().await;
        aggregators.push(aggregator.clone());
        
        let mut stats = self.stats.write().await;
        stats.active_aggregators += 1;
        
        info!("添加日志聚合器: {}", aggregator.name);
        Ok(())
    }

    pub async fn start_aggregation(&self) -> Result<()> {
        if !self.config.enable_aggregation {
            return Ok(());
        }
        
        let mut interval = tokio::time::interval(self.config.aggregation_interval);
        
        loop {
            interval.tick().await;
            self.perform_aggregation().await;
        }
    }

    async fn perform_aggregation(&self) {
        let logs = self.logs.read().await;
        let aggregators = self.aggregators.read().await;
        
        for aggregator in aggregators.iter() {
            for rule in &aggregator.aggregation_rules {
                let matching_logs: Vec<&LogEntry> = logs.iter()
                    .filter(|log| log.message.contains(&rule.pattern))
                    .collect();
                
                if !matching_logs.is_empty() {
                    let mut stats = self.stats.write().await;
                    stats.aggregated_logs += matching_logs.len();
                    
                    info!("聚合日志: 规则 '{}' 匹配 {} 条日志", rule.pattern, matching_logs.len());
                }
            }
        }
    }

    pub async fn get_logs(&self, level: Option<LogLevel>) -> Vec<LogEntry> {
        let logs = self.logs.read().await;
        if let Some(level) = level {
            logs.iter().filter(|log| log.level == level).cloned().collect()
        } else {
            logs.clone()
        }
    }

    pub async fn get_stats(&self) -> LogStats {
        self.stats.read().await.clone()
    }
}

/// 3. 异步分布式追踪
#[derive(Debug, Clone)]
pub struct AsyncDistributedTracing {
    traces: Arc<RwLock<HashMap<String, Trace>>>,
    spans: Arc<RwLock<HashMap<String, Span>>>,
    config: TracingConfig,
    stats: Arc<RwLock<TracingStats>>,
}

#[derive(Debug, Clone)]
pub struct Trace {
    pub id: String,
    pub operation_name: String,
    pub start_time: Instant,
    pub end_time: Option<Instant>,
    pub spans: Vec<String>,
    pub tags: HashMap<String, String>,
    pub status: TraceStatus,
}

#[derive(Debug, Clone)]
pub struct Span {
    pub id: String,
    pub trace_id: String,
    pub parent_id: Option<String>,
    pub operation_name: String,
    pub start_time: Instant,
    pub end_time: Option<Instant>,
    pub tags: HashMap<String, String>,
    pub logs: Vec<SpanLog>,
}

#[derive(Debug, Clone)]
pub struct SpanLog {
    pub timestamp: Instant,
    pub message: String,
    pub fields: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TraceStatus {
    Started,
    Completed,
    Failed,
}

#[derive(Debug, Clone)]
pub struct TracingConfig {
    pub sampling_rate: f64,
    pub max_traces: usize,
    pub trace_retention: Duration,
    pub enable_baggage: bool,
}

impl Default for TracingConfig {
    fn default() -> Self {
        Self {
            sampling_rate: 1.0,
            max_traces: 10000,
            trace_retention: Duration::from_secs(3600),
            enable_baggage: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TracingStats {
    pub total_traces: usize,
    pub completed_traces: usize,
    pub failed_traces: usize,
    pub total_spans: usize,
    pub sampling_decisions: usize,
}

impl AsyncDistributedTracing {
    pub fn new(config: TracingConfig) -> Self {
        Self {
            traces: Arc::new(RwLock::new(HashMap::new())),
            spans: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(TracingStats::default())),
        }
    }

    pub async fn start_trace(&self, operation_name: String, tags: HashMap<String, String>) -> Result<TraceHandle> {
        let trace_id = uuid::Uuid::new_v4().to_string();
        
        // 采样决策
        if rand::random::<f64>() > self.config.sampling_rate {
            return Ok(TraceHandle::NoOp);
        }
        
        let trace = Trace {
            id: trace_id.clone(),
            operation_name: operation_name.clone(),
            start_time: Instant::now(),
            end_time: None,
            spans: Vec::new(),
            tags,
            status: TraceStatus::Started,
        };
        
        let mut traces = self.traces.write().await;
        traces.insert(trace_id.clone(), trace);
        
        let mut stats = self.stats.write().await;
        stats.total_traces += 1;
        stats.sampling_decisions += 1;
        
        info!("开始追踪: {} ({})", operation_name, trace_id);
        Ok(TraceHandle::Active(trace_id))
    }

    pub async fn start_span(&self, trace_id: &str, operation_name: String, parent_id: Option<String>, tags: HashMap<String, String>) -> Result<SpanHandle> {
        let span_id = uuid::Uuid::new_v4().to_string();
        
        let span = Span {
            id: span_id.clone(),
            trace_id: trace_id.to_string(),
            parent_id,
            operation_name,
            start_time: Instant::now(),
            end_time: None,
            tags,
            logs: Vec::new(),
        };
        
        let mut spans = self.spans.write().await;
        spans.insert(span_id.clone(), span);
        
        let mut stats = self.stats.write().await;
        stats.total_spans += 1;
        
        Ok(SpanHandle::Active(span_id))
    }

    pub async fn finish_trace(&self, trace_id: &str, status: TraceStatus) -> Result<()> {
        let mut traces = self.traces.write().await;
        if let Some(trace) = traces.get_mut(trace_id) {
            trace.end_time = Some(Instant::now());
            trace.status = status.clone();
            
            let mut stats = self.stats.write().await;
            match status {
                TraceStatus::Completed => stats.completed_traces += 1,
                TraceStatus::Failed => stats.failed_traces += 1,
                _ => {}
            }
            
            info!("完成追踪: {} ({:?})", trace_id, status);
        }
        
        Ok(())
    }

    pub async fn get_trace(&self, trace_id: &str) -> Option<Trace> {
        let traces = self.traces.read().await;
        traces.get(trace_id).cloned()
    }

    pub async fn get_stats(&self) -> TracingStats {
        self.stats.read().await.clone()
    }
}

#[derive(Debug, Clone)]
pub enum TraceHandle {
    Active(String),
    NoOp,
}

#[derive(Debug, Clone)]
pub enum SpanHandle {
    Active(String),
    NoOp,
}

/// 4. 异步健康检查系统
#[derive(Debug, Clone)]
pub struct AsyncHealthChecker {
    checks: Arc<RwLock<HashMap<String, HealthCheck>>>,
    config: HealthConfig,
    stats: Arc<RwLock<HealthStats>>,
}

#[derive(Debug, Clone)]
pub struct HealthCheck {
    pub id: String,
    pub name: String,
    pub check_type: HealthCheckType,
    pub interval: Duration,
    pub timeout: Duration,
    pub enabled: bool,
    pub last_result: Option<HealthResult>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HealthCheckType {
    Http,
    Database,
    Redis,
    Custom,
}

#[derive(Debug, Clone)]
pub struct HealthResult {
    pub healthy: bool,
    pub response_time: Duration,
    pub error_message: Option<String>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub struct HealthConfig {
    pub check_interval: Duration,
    pub timeout: Duration,
    pub failure_threshold: usize,
    pub success_threshold: usize,
}

impl Default for HealthConfig {
    fn default() -> Self {
        Self {
            check_interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            failure_threshold: 3,
            success_threshold: 2,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct HealthStats {
    pub total_checks: usize,
    pub healthy_checks: usize,
    pub unhealthy_checks: usize,
    pub check_errors: usize,
}

impl AsyncHealthChecker {
    pub fn new(config: HealthConfig) -> Self {
        Self {
            checks: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(HealthStats::default())),
        }
    }

    pub async fn add_check(&self, check: HealthCheck) -> Result<()> {
        let mut checks = self.checks.write().await;
        checks.insert(check.id.clone(), check.clone());
        
        info!("添加健康检查: {}", check.name);
        Ok(())
    }

    pub async fn start_health_checks(&self) -> Result<()> {
        let checks = self.checks.read().await;
        let mut tasks = Vec::new();
        
        for check in checks.values() {
            if check.enabled {
                let checker_clone = self.clone();
                let check_id = check.id.clone();
                
                let task = tokio::spawn(async move {
                    checker_clone.health_check_loop(&check_id).await;
                });
                
                tasks.push(task);
            }
        }
        
        info!("启动 {} 个健康检查", tasks.len());
        Ok(())
    }

    async fn health_check_loop(&self, check_id: &str) {
        let mut interval = tokio::time::interval(self.config.check_interval);
        
        loop {
            interval.tick().await;
            
            let checks = self.checks.read().await;
            if let Some(check) = checks.get(check_id) {
                let result = self.perform_health_check(check).await;
                
                let mut checks_write = self.checks.write().await;
                if let Some(check) = checks_write.get_mut(check_id) {
                    check.last_result = Some(result.clone());
                }
                
                let mut stats = self.stats.write().await;
                stats.total_checks += 1;
                
                if result.healthy {
                    stats.healthy_checks += 1;
                } else {
                    stats.unhealthy_checks += 1;
                    stats.check_errors += 1;
                }
            }
        }
    }

    async fn perform_health_check(&self, check: &HealthCheck) -> HealthResult {
        let start_time = Instant::now();
        
        // 模拟健康检查
        let is_healthy = match check.check_type {
            HealthCheckType::Http => {
                sleep(Duration::from_millis(100)).await;
                rand::random::<f64>() > 0.1
            }
            HealthCheckType::Database => {
                sleep(Duration::from_millis(200)).await;
                rand::random::<f64>() > 0.05
            }
            HealthCheckType::Redis => {
                sleep(Duration::from_millis(50)).await;
                rand::random::<f64>() > 0.15
            }
            HealthCheckType::Custom => {
                sleep(Duration::from_millis(150)).await;
                rand::random::<f64>() > 0.08
            }
        };
        
        let response_time = start_time.elapsed();
        let error_message = if !is_healthy {
            Some("模拟健康检查失败".to_string())
        } else {
            None
        };
        
        HealthResult {
            healthy: is_healthy,
            response_time,
            error_message,
            timestamp: Instant::now(),
        }
    }

    pub async fn get_health_status(&self) -> HashMap<String, HealthResult> {
        let checks = self.checks.read().await;
        let mut status = HashMap::new();
        
        for (id, check) in checks.iter() {
            if let Some(result) = &check.last_result {
                status.insert(id.clone(), result.clone());
            }
        }
        
        status
    }

    pub async fn get_stats(&self) -> HealthStats {
        self.stats.read().await.clone()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    info!("🚀 开始 2025 年异步监控和可观测性演示");

    // 1. 演示异步指标收集器
    info!("📊 演示异步指标收集器");
    let metrics_config = MetricsConfig::default();
    let metrics_collector = AsyncMetricsCollector::new(metrics_config);
    
    // 添加收集器
    let collectors = vec![
        MetricsCollector {
            id: "collector_1".to_string(),
            name: "系统指标收集器".to_string(),
            collection_interval: Duration::from_secs(5),
            enabled: true,
        },
        MetricsCollector {
            id: "collector_2".to_string(),
            name: "应用指标收集器".to_string(),
            collection_interval: Duration::from_secs(10),
            enabled: true,
        },
    ];
    
    for collector in collectors {
        metrics_collector.add_collector(collector).await?;
    }
    
    // 记录一些指标
    for i in 0..10 {
        let labels = [("service".to_string(), "api-gateway".to_string())].iter().cloned().collect();
        metrics_collector.record_metric(
            format!("request_count_{}", i),
            i as f64 * 10.0,
            MetricType::Counter,
            labels,
        ).await?;
    }
    
    let metrics_stats = metrics_collector.get_stats().await;
    info!("指标收集统计: 总指标 {}, 活跃收集器 {}", 
          metrics_stats.total_metrics_collected, metrics_stats.active_collectors);

    // 2. 演示异步日志聚合器
    info!("📝 演示异步日志聚合器");
    let log_config = LogConfig::default();
    let log_aggregator = AsyncLogAggregator::new(log_config);
    
    // 添加聚合器
    let aggregator = LogAggregator {
        id: "aggregator_1".to_string(),
        name: "错误日志聚合器".to_string(),
        filter_level: LogLevel::Error,
        aggregation_rules: vec![
            AggregationRule {
                pattern: "error".to_string(),
                aggregation_type: AggregationType::Count,
                time_window: Duration::from_secs(60),
            }
        ],
    };
    
    log_aggregator.add_aggregator(aggregator).await?;
    
    // 记录一些日志
    for i in 0..20 {
        let level = if i % 5 == 0 { LogLevel::Error } else { LogLevel::Info };
        let fields = [("request_id".to_string(), format!("req_{}", i))].iter().cloned().collect();
        
        log_aggregator.log(
            level,
            format!("处理请求 {}", i),
            "api-gateway".to_string(),
            fields,
        ).await?;
    }
    
    let error_logs = log_aggregator.get_logs(Some(LogLevel::Error)).await;
    let log_stats = log_aggregator.get_stats().await;
    info!("日志统计: 总日志 {}, 错误日志 {}, 聚合日志 {}", 
          log_stats.total_logs, error_logs.len(), log_stats.aggregated_logs);

    // 3. 演示异步分布式追踪
    info!("🔍 演示异步分布式追踪");
    let tracing_config = TracingConfig::default();
    let distributed_tracing = AsyncDistributedTracing::new(tracing_config);
    
    // 开始追踪
    let tags = [("service".to_string(), "api-gateway".to_string())].iter().cloned().collect();
    let trace_handle = distributed_tracing.start_trace("api_request".to_string(), tags).await?;
    
    if let TraceHandle::Active(trace_id) = trace_handle {
        // 开始子span
        let _span_handle = distributed_tracing.start_span(
            &trace_id,
            "database_query".to_string(),
            None,
            HashMap::new(),
        ).await?;
        
        // 模拟一些工作
        sleep(Duration::from_millis(100)).await;
        
        // 完成追踪
        distributed_tracing.finish_trace(&trace_id, TraceStatus::Completed).await?;
        
        info!("完成追踪: {}", trace_id);
    }
    
    let tracing_stats = distributed_tracing.get_stats().await;
    info!("追踪统计: 总追踪 {}, 完成追踪 {}, 总Span {}", 
          tracing_stats.total_traces, tracing_stats.completed_traces, tracing_stats.total_spans);

    // 4. 演示异步健康检查系统
    info!("🏥 演示异步健康检查系统");
    let health_config = HealthConfig::default();
    let health_checker = AsyncHealthChecker::new(health_config);
    
    // 添加健康检查
    let health_checks = vec![
        HealthCheck {
            id: "check_1".to_string(),
            name: "数据库健康检查".to_string(),
            check_type: HealthCheckType::Database,
            interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            enabled: true,
            last_result: None,
        },
        HealthCheck {
            id: "check_2".to_string(),
            name: "Redis健康检查".to_string(),
            check_type: HealthCheckType::Redis,
            interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            enabled: true,
            last_result: None,
        },
    ];
    
    for check in health_checks {
        health_checker.add_check(check).await?;
    }
    
    // 启动健康检查（短时间运行）
    let health_checker_clone = health_checker.clone();
    let health_task = tokio::spawn(async move {
        health_checker_clone.start_health_checks().await
    });
    
    // 让健康检查运行一段时间
    sleep(Duration::from_millis(2000)).await;
    
    health_task.abort();
    
    let health_status = health_checker.get_health_status().await;
    let health_stats = health_checker.get_stats().await;
    
    info!("健康检查统计: 总检查 {}, 健康检查 {}, 不健康检查 {}", 
          health_stats.total_checks, health_stats.healthy_checks, health_stats.unhealthy_checks);
    
    for (check_id, result) in health_status {
        info!("健康检查 {}: {} (响应时间: {:?})", 
              check_id, if result.healthy { "健康" } else { "不健康" }, result.response_time);
    }

    info!("✅ 2025 年异步监控和可观测性演示完成!");
    
    Ok(())
}
