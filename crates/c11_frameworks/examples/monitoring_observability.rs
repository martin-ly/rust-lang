//! 监控和可观测性示例
//!
//! 展示Rust应用的监控和可观测性特性，包括：
//! - 指标收集和导出
//! - 分布式追踪
//! - 日志聚合和分析
//! - 健康检查和监控
//! - 告警和通知
//! - 性能监控
//! - 错误追踪

use axum::{
    Json, Router,
    extract::{Request, State},
    http::{HeaderMap, StatusCode},
    middleware,
    response::{IntoResponse, Response},
    routing::{get, post},
};
use opentelemetry::{
    KeyValue, global,
    trace::{Span, Tracer},
};
use opentelemetry_sdk::{
    export::metrics::aggregation,
    metrics::{Meter, MeterProvider},
    trace::TracerProvider,
};
use opentelemetry_stdout::{ExporterBuilder, SpanExporter};
use prometheus::{
    Counter, Gauge, Histogram, IntCounter, IntGauge, IntHistogram, Registry, TextEncoder, labels,
    opts,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tokio::{
    sync::{RwLock, broadcast, mpsc},
    time::{interval, sleep},
};
use tracing::{Level, debug, error, info, instrument, span, warn};
use uuid::Uuid;

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub metrics: Arc<MetricsCollector>,
    pub tracer: Arc<Tracer>,
    pub health_checker: Arc<HealthChecker>,
    pub alert_manager: Arc<AlertManager>,
    pub log_aggregator: Arc<LogAggregator>,
}

/// 指标收集器
pub struct MetricsCollector {
    pub request_count: Counter,
    pub request_duration: Histogram,
    pub active_connections: Gauge,
    pub error_count: Counter,
    pub memory_usage: Gauge,
    pub cpu_usage: Gauge,
    pub custom_metrics: Arc<RwLock<HashMap<String, CustomMetric>>>,
}

/// 自定义指标
#[derive(Debug, Clone)]
pub struct CustomMetric {
    pub name: String,
    pub value: f64,
    pub labels: HashMap<String, String>,
    pub timestamp: u64,
}

/// 健康检查器
pub struct HealthChecker {
    pub checks: Arc<RwLock<HashMap<String, HealthCheck>>>,
    pub status: Arc<RwLock<HealthStatus>>,
}

/// 健康检查
#[derive(Debug, Clone)]
pub struct HealthCheck {
    pub name: String,
    pub check_fn: String, // 在实际应用中应该是函数
    pub timeout: Duration,
    pub interval: Duration,
    pub last_check: Option<Instant>,
    pub last_result: Option<bool>,
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthStatus {
    pub overall: HealthLevel,
    pub checks: HashMap<String, CheckResult>,
    pub timestamp: u64,
}

/// 健康级别
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum HealthLevel {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    pub status: HealthLevel,
    pub message: String,
    pub duration: Duration,
    pub timestamp: u64,
}

/// 告警管理器
pub struct AlertManager {
    pub rules: Arc<RwLock<Vec<AlertRule>>>,
    pub alerts: Arc<RwLock<Vec<Alert>>>,
    pub notifiers: Arc<RwLock<Vec<Box<dyn Notifier + Send + Sync>>>>,
}

/// 告警规则
#[derive(Debug, Clone)]
pub struct AlertRule {
    pub name: String,
    pub condition: String,
    pub severity: AlertSeverity,
    pub duration: Duration,
    pub enabled: bool,
}

/// 告警
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    pub id: String,
    pub rule_name: String,
    pub severity: AlertSeverity,
    pub message: String,
    pub timestamp: u64,
    pub resolved: bool,
    pub resolved_at: Option<u64>,
}

/// 告警严重程度
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AlertSeverity {
    Critical,
    Warning,
    Info,
}

/// 通知器trait
pub trait Notifier: Send + Sync {
    fn send(&self, alert: &Alert) -> Result<(), String>;
    fn name(&self) -> &str;
}

/// 日志聚合器
pub struct LogAggregator {
    pub logs: Arc<RwLock<Vec<LogEntry>>>,
    pub filters: Arc<RwLock<Vec<LogFilter>>>,
    pub max_logs: usize,
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub id: String,
    pub level: String,
    pub message: String,
    pub timestamp: u64,
    pub source: String,
    pub fields: HashMap<String, String>,
    pub trace_id: Option<String>,
    pub span_id: Option<String>,
}

/// 日志过滤器
#[derive(Debug, Clone)]
pub struct LogFilter {
    pub name: String,
    pub pattern: String,
    pub level: Option<String>,
    pub source: Option<String>,
}

/// 分布式追踪上下文
#[derive(Debug, Clone)]
pub struct TraceContext {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub baggage: HashMap<String, String>,
}

/// 性能监控器
pub struct PerformanceMonitor {
    pub metrics: Arc<RwLock<HashMap<String, PerformanceMetric>>>,
    pub thresholds: Arc<RwLock<HashMap<String, f64>>>,
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetric {
    pub name: String,
    pub value: f64,
    pub unit: String,
    pub timestamp: u64,
}

/// 错误追踪器
pub struct ErrorTracker {
    pub errors: Arc<RwLock<Vec<ErrorEntry>>>,
    pub patterns: Arc<RwLock<Vec<ErrorPattern>>>,
}

/// 错误条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorEntry {
    pub id: String,
    pub error_type: String,
    pub message: String,
    pub stack_trace: String,
    pub timestamp: u64,
    pub context: HashMap<String, String>,
    pub trace_id: Option<String>,
}

/// 错误模式
#[derive(Debug, Clone)]
pub struct ErrorPattern {
    pub pattern: String,
    pub count: AtomicUsize,
    pub first_seen: u64,
    pub last_seen: AtomicU64,
}

/// 监控仪表板数据
#[derive(Debug, Serialize, Deserialize)]
pub struct DashboardData {
    pub metrics: HashMap<String, f64>,
    pub health_status: HealthStatus,
    pub recent_alerts: Vec<Alert>,
    pub error_rate: f64,
    pub response_time: f64,
    pub throughput: f64,
}

impl MetricsCollector {
    pub fn new() -> Self {
        let registry = Registry::new();

        let request_count =
            Counter::new("http_requests_total", "Total number of HTTP requests").unwrap();

        let request_duration = Histogram::new(
            "http_request_duration_seconds",
            "HTTP request duration in seconds",
        )
        .unwrap();

        let active_connections =
            Gauge::new("active_connections", "Number of active connections").unwrap();

        let error_count = Counter::new("http_errors_total", "Total number of HTTP errors").unwrap();

        let memory_usage = Gauge::new("memory_usage_bytes", "Memory usage in bytes").unwrap();

        let cpu_usage = Gauge::new("cpu_usage_percent", "CPU usage percentage").unwrap();

        registry.register(Box::new(request_count.clone())).unwrap();
        registry
            .register(Box::new(request_duration.clone()))
            .unwrap();
        registry
            .register(Box::new(active_connections.clone()))
            .unwrap();
        registry.register(Box::new(error_count.clone())).unwrap();
        registry.register(Box::new(memory_usage.clone())).unwrap();
        registry.register(Box::new(cpu_usage.clone())).unwrap();

        Self {
            request_count,
            request_duration,
            active_connections,
            error_count,
            memory_usage,
            cpu_usage,
            custom_metrics: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 记录请求
    pub fn record_request(&self, method: &str, path: &str, status: u16, duration: Duration) {
        self.request_count.inc();
        self.request_duration.observe(duration.as_secs_f64());

        if status >= 400 {
            self.error_count.inc();
        }
    }

    /// 更新连接数
    pub fn update_connections(&self, count: usize) {
        self.active_connections.set(count as f64);
    }

    /// 更新内存使用
    pub fn update_memory_usage(&self, bytes: usize) {
        self.memory_usage.set(bytes as f64);
    }

    /// 更新CPU使用
    pub fn update_cpu_usage(&self, percent: f64) {
        self.cpu_usage.set(percent);
    }

    /// 添加自定义指标
    pub async fn add_custom_metric(
        &self,
        name: String,
        value: f64,
        labels: HashMap<String, String>,
    ) {
        let metric = CustomMetric {
            name: name.clone(),
            value,
            labels,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };

        let mut metrics = self.custom_metrics.write().await;
        metrics.insert(name, metric);
    }

    /// 获取所有指标
    pub async fn get_all_metrics(&self) -> HashMap<String, f64> {
        let mut metrics = HashMap::new();

        metrics.insert("request_count".to_string(), self.request_count.get());
        metrics.insert("error_count".to_string(), self.error_count.get());
        metrics.insert(
            "active_connections".to_string(),
            self.active_connections.get(),
        );
        metrics.insert("memory_usage".to_string(), self.memory_usage.get());
        metrics.insert("cpu_usage".to_string(), self.cpu_usage.get());

        let custom_metrics = self.custom_metrics.read().await;
        for (name, metric) in custom_metrics.iter() {
            metrics.insert(name.clone(), metric.value);
        }

        metrics
    }
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {
            checks: Arc::new(RwLock::new(HashMap::new())),
            status: Arc::new(RwLock::new(HealthStatus {
                overall: HealthLevel::Healthy,
                checks: HashMap::new(),
                timestamp: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            })),
        }
    }

    /// 添加健康检查
    pub async fn add_check(&self, check: HealthCheck) {
        let mut checks = self.checks.write().await;
        checks.insert(check.name.clone(), check);
    }

    /// 运行健康检查
    pub async fn run_checks(&self) -> HealthStatus {
        let checks = self.checks.read().await;
        let mut results = HashMap::new();
        let mut overall = HealthLevel::Healthy;

        for (name, check) in checks.iter() {
            let start = Instant::now();
            let result = self.run_single_check(check).await;
            let duration = start.elapsed();

            let check_result = CheckResult {
                status: if result {
                    HealthLevel::Healthy
                } else {
                    HealthLevel::Unhealthy
                },
                message: if result {
                    "OK".to_string()
                } else {
                    "Failed".to_string()
                },
                duration,
                timestamp: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            };

            if !result {
                overall = HealthLevel::Unhealthy;
            }

            results.insert(name.clone(), check_result);
        }

        let status = HealthStatus {
            overall,
            checks: results,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };

        let mut current_status = self.status.write().await;
        *current_status = status.clone();

        status
    }

    /// 运行单个健康检查
    async fn run_single_check(&self, check: &HealthCheck) -> bool {
        // 模拟健康检查逻辑
        match check.name.as_str() {
            "database" => {
                // 模拟数据库检查
                sleep(Duration::from_millis(10)).await;
                true
            }
            "redis" => {
                // 模拟Redis检查
                sleep(Duration::from_millis(5)).await;
                true
            }
            "external_api" => {
                // 模拟外部API检查
                sleep(Duration::from_millis(20)).await;
                true
            }
            _ => false,
        }
    }

    /// 获取健康状态
    pub async fn get_status(&self) -> HealthStatus {
        let status = self.status.read().await;
        status.clone()
    }
}

impl AlertManager {
    pub fn new() -> Self {
        Self {
            rules: Arc::new(RwLock::new(Vec::new())),
            alerts: Arc::new(RwLock::new(Vec::new())),
            notifiers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 添加告警规则
    pub async fn add_rule(&self, rule: AlertRule) {
        let mut rules = self.rules.write().await;
        rules.push(rule);
    }

    /// 添加通知器
    pub async fn add_notifier(&self, notifier: Box<dyn Notifier + Send + Sync>) {
        let mut notifiers = self.notifiers.write().await;
        notifiers.push(notifier);
    }

    /// 检查告警规则
    pub async fn check_rules(&self, metrics: &HashMap<String, f64>) {
        let rules = self.rules.read().await;
        let mut alerts = self.alerts.write().await;

        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }

            // 简化的规则检查逻辑
            let should_alert = match rule.condition.as_str() {
                "cpu_usage > 80" => metrics.get("cpu_usage").map_or(false, |&v| v > 80.0),
                "memory_usage > 90" => metrics.get("memory_usage").map_or(false, |&v| v > 90.0),
                "error_rate > 5" => metrics.get("error_rate").map_or(false, |&v| v > 5.0),
                _ => false,
            };

            if should_alert {
                let alert = Alert {
                    id: Uuid::new_v4().to_string(),
                    rule_name: rule.name.clone(),
                    severity: rule.severity.clone(),
                    message: format!("告警规则 {} 触发", rule.name),
                    timestamp: SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                    resolved: false,
                    resolved_at: None,
                };

                alerts.push(alert.clone());

                // 发送通知
                let notifiers = self.notifiers.read().await;
                for notifier in notifiers.iter() {
                    if let Err(e) = notifier.send(&alert) {
                        error!("发送告警通知失败: {}", e);
                    }
                }
            }
        }
    }

    /// 获取活跃告警
    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        let alerts = self.alerts.read().await;
        alerts.iter().filter(|a| !a.resolved).cloned().collect()
    }
}

impl LogAggregator {
    pub fn new(max_logs: usize) -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            filters: Arc::new(RwLock::new(Vec::new())),
            max_logs,
        }
    }

    /// 添加日志条目
    pub async fn add_log(&self, entry: LogEntry) {
        let mut logs = self.logs.write().await;
        logs.push(entry);

        // 限制日志数量
        if logs.len() > self.max_logs {
            logs.drain(0..logs.len() - self.max_logs);
        }
    }

    /// 添加过滤器
    pub async fn add_filter(&self, filter: LogFilter) {
        let mut filters = self.filters.write().await;
        filters.push(filter);
    }

    /// 查询日志
    pub async fn query_logs(&self, level: Option<String>, source: Option<String>) -> Vec<LogEntry> {
        let logs = self.logs.read().await;
        logs.iter()
            .filter(|log| {
                if let Some(ref filter_level) = level {
                    if log.level != *filter_level {
                        return false;
                    }
                }
                if let Some(ref filter_source) = source {
                    if log.source != *filter_source {
                        return false;
                    }
                }
                true
            })
            .cloned()
            .collect()
    }

    /// 获取日志统计
    pub async fn get_log_stats(&self) -> HashMap<String, usize> {
        let logs = self.logs.read().await;
        let mut stats = HashMap::new();

        for log in logs.iter() {
            *stats.entry(log.level.clone()).or_insert(0) += 1;
        }

        stats
    }
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            thresholds: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 记录性能指标
    pub async fn record_metric(&self, name: String, value: f64, unit: String) {
        let metric = PerformanceMetric {
            name: name.clone(),
            value,
            unit,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        };

        let mut metrics = self.metrics.write().await;
        metrics.insert(name, metric);
    }

    /// 设置阈值
    pub async fn set_threshold(&self, name: String, threshold: f64) {
        let mut thresholds = self.thresholds.write().await;
        thresholds.insert(name, threshold);
    }

    /// 检查阈值
    pub async fn check_thresholds(&self) -> Vec<String> {
        let metrics = self.metrics.read().await;
        let thresholds = self.thresholds.read().await;
        let mut violations = Vec::new();

        for (name, metric) in metrics.iter() {
            if let Some(&threshold) = thresholds.get(name) {
                if metric.value > threshold {
                    violations.push(format!(
                        "{} 超过阈值: {} > {}",
                        name, metric.value, threshold
                    ));
                }
            }
        }

        violations
    }
}

impl ErrorTracker {
    pub fn new() -> Self {
        Self {
            errors: Arc::new(RwLock::new(Vec::new())),
            patterns: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 记录错误
    pub async fn record_error(
        &self,
        error_type: String,
        message: String,
        stack_trace: String,
        context: HashMap<String, String>,
    ) {
        let error_entry = ErrorEntry {
            id: Uuid::new_v4().to_string(),
            error_type: error_type.clone(),
            message: message.clone(),
            stack_trace,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            context,
            trace_id: None,
        };

        let mut errors = self.errors.write().await;
        errors.push(error_entry);

        // 更新错误模式
        let mut patterns = self.patterns.write().await;
        if let Some(pattern) = patterns.iter_mut().find(|p| p.pattern == error_type) {
            pattern.count.fetch_add(1, Ordering::Relaxed);
            pattern.last_seen.store(
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                Ordering::Relaxed,
            );
        } else {
            patterns.push(ErrorPattern {
                pattern: error_type,
                count: AtomicUsize::new(1),
                first_seen: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                last_seen: AtomicU64::new(
                    SystemTime::now()
                        .duration_since(UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                ),
            });
        }
    }

    /// 获取错误统计
    pub async fn get_error_stats(&self) -> HashMap<String, usize> {
        let patterns = self.patterns.read().await;
        patterns
            .iter()
            .map(|p| (p.pattern.clone(), p.count.load(Ordering::Relaxed)))
            .collect()
    }
}

/// 控制台通知器
pub struct ConsoleNotifier;

impl Notifier for ConsoleNotifier {
    fn send(&self, alert: &Alert) -> Result<(), String> {
        println!("🚨 告警: {} - {}", alert.severity, alert.message);
        Ok(())
    }

    fn name(&self) -> &str {
        "console"
    }
}

/// 邮件通知器
pub struct EmailNotifier {
    pub email: String,
}

impl Notifier for EmailNotifier {
    fn send(&self, alert: &Alert) -> Result<(), String> {
        // 模拟发送邮件
        info!("发送邮件到 {}: {}", self.email, alert.message);
        Ok(())
    }

    fn name(&self) -> &str {
        "email"
    }
}

/// 监控中间件
pub async fn monitoring_middleware(
    State(state): State<AppState>,
    headers: HeaderMap,
    request: Request,
    next: middleware::Next,
) -> Response {
    let start = Instant::now();
    let method = request.method().to_string();
    let path = request.uri().path().to_string();

    // 创建追踪span
    let span = state.tracer.start("http_request");
    span.set_attribute(KeyValue::new("http.method", method.clone()));
    span.set_attribute(KeyValue::new("http.path", path.clone()));

    let response = next.run(request).await;
    let duration = start.elapsed();
    let status = response.status().as_u16();

    // 记录指标
    state
        .metrics
        .record_request(&method, &path, status, duration);

    // 记录日志
    let log_entry = LogEntry {
        id: Uuid::new_v4().to_string(),
        level: if status >= 400 {
            "ERROR".to_string()
        } else {
            "INFO".to_string()
        },
        message: format!("{} {} - {}", method, path, status),
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        source: "http".to_string(),
        fields: HashMap::new(),
        trace_id: Some(span.span_context().trace_id().to_string()),
        span_id: Some(span.span_context().span_id().to_string()),
    };

    state.log_aggregator.add_log(log_entry).await;

    span.end();
    response
}

/// 健康检查端点
async fn health_check(State(state): State<AppState>) -> Json<HealthStatus> {
    let status = state.health_checker.run_checks().await;
    Json(status)
}

/// 指标端点
async fn metrics(State(state): State<AppState>) -> String {
    let metrics = state.metrics.get_all_metrics().await;
    serde_json::to_string_pretty(&metrics).unwrap()
}

/// 告警端点
async fn alerts(State(state): State<AppState>) -> Json<Vec<Alert>> {
    let alerts = state.alert_manager.get_active_alerts().await;
    Json(alerts)
}

/// 日志端点
async fn logs(
    State(state): State<AppState>,
    Query(params): Query<HashMap<String, String>>,
) -> Json<Vec<LogEntry>> {
    let level = params.get("level").cloned();
    let source = params.get("source").cloned();
    let logs = state.log_aggregator.query_logs(level, source).await;
    Json(logs)
}

/// 仪表板端点
async fn dashboard(State(state): State<AppState>) -> Json<DashboardData> {
    let metrics = state.metrics.get_all_metrics().await;
    let health_status = state.health_checker.get_status().await;
    let recent_alerts = state.alert_manager.get_active_alerts().await;

    let error_rate = metrics.get("error_rate").copied().unwrap_or(0.0);
    let response_time = metrics.get("response_time").copied().unwrap_or(0.0);
    let throughput = metrics.get("throughput").copied().unwrap_or(0.0);

    let dashboard_data = DashboardData {
        metrics,
        health_status,
        recent_alerts,
        error_rate,
        response_time,
        throughput,
    };

    Json(dashboard_data)
}

/// 创建应用路由
fn create_app(state: AppState) -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/metrics", get(metrics))
        .route("/alerts", get(alerts))
        .route("/logs", get(logs))
        .route("/dashboard", get(dashboard))
        .layer(middleware::from_fn_with_state(
            state.clone(),
            monitoring_middleware,
        ))
        .with_state(state)
}

/// 初始化监控系统
async fn init_monitoring() -> AppState {
    // 初始化指标收集器
    let metrics = Arc::new(MetricsCollector::new());

    // 初始化追踪器
    let tracer = Arc::new(global::tracer("monitoring-example"));

    // 初始化健康检查器
    let health_checker = Arc::new(HealthChecker::new());

    // 添加健康检查
    health_checker
        .add_check(HealthCheck {
            name: "database".to_string(),
            check_fn: "check_database".to_string(),
            timeout: Duration::from_secs(5),
            interval: Duration::from_secs(30),
            last_check: None,
            last_result: None,
        })
        .await;

    health_checker
        .add_check(HealthCheck {
            name: "redis".to_string(),
            check_fn: "check_redis".to_string(),
            timeout: Duration::from_secs(3),
            interval: Duration::from_secs(30),
            last_check: None,
            last_result: None,
        })
        .await;

    // 初始化告警管理器
    let alert_manager = Arc::new(AlertManager::new());

    // 添加告警规则
    alert_manager
        .add_rule(AlertRule {
            name: "high_cpu_usage".to_string(),
            condition: "cpu_usage > 80".to_string(),
            severity: AlertSeverity::Warning,
            duration: Duration::from_secs(60),
            enabled: true,
        })
        .await;

    alert_manager
        .add_rule(AlertRule {
            name: "high_memory_usage".to_string(),
            condition: "memory_usage > 90".to_string(),
            severity: AlertSeverity::Critical,
            duration: Duration::from_secs(30),
            enabled: true,
        })
        .await;

    // 添加通知器
    alert_manager.add_notifier(Box::new(ConsoleNotifier)).await;
    alert_manager
        .add_notifier(Box::new(EmailNotifier {
            email: "admin@example.com".to_string(),
        }))
        .await;

    // 初始化日志聚合器
    let log_aggregator = Arc::new(LogAggregator::new(10000));

    AppState {
        metrics,
        tracer,
        health_checker,
        alert_manager,
        log_aggregator,
    }
}

/// 监控任务
async fn monitoring_task(state: AppState) {
    let mut interval = interval(Duration::from_secs(10));

    loop {
        interval.tick().await;

        // 收集系统指标
        let metrics = state.metrics.get_all_metrics().await;

        // 模拟系统指标
        state.metrics.update_memory_usage(1024 * 1024 * 100).await; // 100MB
        state.metrics.update_cpu_usage(45.0).await; // 45%

        // 检查告警规则
        state.alert_manager.check_rules(&metrics).await;

        // 运行健康检查
        state.health_checker.run_checks().await;

        info!("监控任务执行完成");
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    // 初始化监控系统
    let state = init_monitoring().await;

    // 启动监控任务
    let state_clone = state.clone();
    tokio::spawn(monitoring_task(state_clone));

    // 创建应用
    let app = create_app(state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("监控服务器启动在 http://0.0.0.0:3000");

    axum::serve(listener, app).await?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metrics_collector() {
        let collector = MetricsCollector::new();

        collector.record_request("GET", "/test", 200, Duration::from_millis(100));
        collector.update_connections(10);
        collector.update_memory_usage(1024 * 1024);
        collector.update_cpu_usage(50.0);

        let metrics = collector.get_all_metrics().await;
        assert!(metrics.contains_key("request_count"));
        assert!(metrics.contains_key("active_connections"));
        assert!(metrics.contains_key("memory_usage"));
        assert!(metrics.contains_key("cpu_usage"));
    }

    #[tokio::test]
    async fn test_health_checker() {
        let checker = HealthChecker::new();

        checker
            .add_check(HealthCheck {
                name: "test".to_string(),
                check_fn: "test_check".to_string(),
                timeout: Duration::from_secs(5),
                interval: Duration::from_secs(30),
                last_check: None,
                last_result: None,
            })
            .await;

        let status = checker.run_checks().await;
        assert_eq!(status.overall, HealthLevel::Healthy);
        assert!(status.checks.contains_key("test"));
    }

    #[tokio::test]
    async fn test_alert_manager() {
        let manager = AlertManager::new();

        manager
            .add_rule(AlertRule {
                name: "test_rule".to_string(),
                condition: "cpu_usage > 80".to_string(),
                severity: AlertSeverity::Warning,
                duration: Duration::from_secs(60),
                enabled: true,
            })
            .await;

        manager.add_notifier(Box::new(ConsoleNotifier)).await;

        let mut metrics = HashMap::new();
        metrics.insert("cpu_usage".to_string(), 85.0);

        manager.check_rules(&metrics).await;

        let alerts = manager.get_active_alerts().await;
        assert!(!alerts.is_empty());
    }

    #[tokio::test]
    async fn test_log_aggregator() {
        let aggregator = LogAggregator::new(1000);

        let log_entry = LogEntry {
            id: Uuid::new_v4().to_string(),
            level: "INFO".to_string(),
            message: "Test message".to_string(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            source: "test".to_string(),
            fields: HashMap::new(),
            trace_id: None,
            span_id: None,
        };

        aggregator.add_log(log_entry).await;

        let logs = aggregator.query_logs(Some("INFO".to_string()), None).await;
        assert_eq!(logs.len(), 1);

        let stats = aggregator.get_log_stats().await;
        assert_eq!(stats.get("INFO"), Some(&1));
    }

    #[tokio::test]
    async fn test_performance_monitor() {
        let monitor = PerformanceMonitor::new();

        monitor
            .record_metric("response_time".to_string(), 100.0, "ms".to_string())
            .await;
        monitor
            .set_threshold("response_time".to_string(), 200.0)
            .await;

        let violations = monitor.check_thresholds().await;
        assert!(violations.is_empty());
    }

    #[tokio::test]
    async fn test_error_tracker() {
        let tracker = ErrorTracker::new();

        let mut context = HashMap::new();
        context.insert("user_id".to_string(), "123".to_string());

        tracker
            .record_error(
                "ValidationError".to_string(),
                "Invalid input".to_string(),
                "stack trace".to_string(),
                context,
            )
            .await;

        let stats = tracker.get_error_stats().await;
        assert_eq!(stats.get("ValidationError"), Some(&1));
    }
}
