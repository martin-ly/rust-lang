//! OpenTelemetry集成模块
//!
//! 提供分布式追踪、指标收集和结构化日志功能

use anyhow::Result;
use log::info;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

pub mod config;
pub mod local_logging;
pub mod metrics;
pub mod observability;
pub mod otel_logging;
pub mod tracing;

pub use config::*;
pub use metrics::*;
pub use observability::*;
pub use tracing::*;
// 重新导出健康检查相关类型
pub use observability::{
    DatabaseHealthChecker, ErrorSeverity, ErrorStatistics, HealthCheck, HealthChecker,
    HealthStatus, LogStatistics, MetricsSummary, PerformanceSummary, RedisHealthChecker,
    SystemReport, SystemResourceHealthChecker, TracingSummary,
};
// 重新导出日志相关类型，避免命名冲突
pub use otel_logging::{
    AsyncLogWriter, LogAggregator, LogConfig, LogEntry, LogLevel, LogLevelFilter, SlogLogger,
    StructuredLogger, init_logging,
};
// 重新导出本地日志相关类型
pub use local_logging::{
    CompressionStrategy, LocalLogConfig, LocalLogEntry, LocalLogLevel, LocalLogManager, LogFormat,
    LogStats, RotationStrategy,
};

/// OpenTelemetry管理器 - 统一管理追踪、指标、日志和可观测性
pub struct OpenTelemetryManager {
    config: OpenTelemetryConfig,
    tracer: Arc<Tracer>,
    metrics: Arc<MetricsCollector>,
    logger: Arc<StructuredLogger>,
    slog_logger: Arc<SlogLogger>,
    log_aggregator: Arc<LogAggregator>,
    local_log_manager: Option<Arc<LocalLogManager>>,
    performance_monitor: Arc<PerformanceMonitor>,
    error_tracker: Arc<ErrorTracker>,
    system_reporter: Arc<SystemStatusReporter>,
}

impl OpenTelemetryManager {
    /// 创建新的OpenTelemetry管理器
    pub fn new(config: OpenTelemetryConfig) -> Result<Self, Box<dyn std::error::Error>> {
        let tracer = Arc::new(Tracer::new(config.clone()));
        let metrics = Arc::new(MetricsCollector::new());
        let logger = Arc::new(StructuredLogger::new(
            config.service_name.clone(),
            config.service_version.clone(),
        ));

        let mut slog_logger = SlogLogger::new(LogConfig::default());
        slog_logger.init()?;
        let slog_logger = Arc::new(slog_logger);

        // 创建可观测性组件
        let log_aggregator = Arc::new(LogAggregator::new(10000, Duration::from_secs(300)));
        let performance_monitor = Arc::new(PerformanceMonitor::new());
        let error_tracker = Arc::new(ErrorTracker::new());

        let mut system_reporter =
            SystemStatusReporter::new(performance_monitor.clone(), error_tracker.clone());

        // 添加默认健康检查器
        system_reporter.add_health_checker(Box::new(SystemResourceHealthChecker::new(
            "system_resources".to_string(),
            80.0, // 80% CPU阈值
            85.0, // 85% 内存阈值
        )));

        let system_reporter = Arc::new(system_reporter);

        Ok(Self {
            config,
            tracer,
            metrics,
            logger,
            slog_logger,
            log_aggregator,
            local_log_manager: None,
            performance_monitor,
            error_tracker,
            system_reporter,
        })
    }

    /// 初始化所有组件
    pub fn init(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // info!("Initializing OpenTelemetry Manager");

        // 初始化追踪
        if self.config.tracing_enabled {
            init_tracing(self.config.clone())?;
            // info!("Tracing initialized");
        }

        // 初始化日志
        if self.config.logging_enabled {
            let mut logger = StructuredLogger::new(
                self.config.service_name.clone(),
                self.config.service_version.clone(),
            );
            logger.set_slog_logger(self.slog_logger.clone());
            self.logger = Arc::new(logger);
            // info!("Logging initialized");
        }

        // 初始化指标
        if self.config.metrics_enabled {
            // info!("Metrics initialized");
        }

        // info!("OpenTelemetry Manager initialized successfully");
        Ok(())
    }

    /// 获取追踪器
    pub fn tracer(&self) -> Arc<Tracer> {
        self.tracer.clone()
    }

    /// 获取指标收集器
    pub fn metrics(&self) -> Arc<MetricsCollector> {
        self.metrics.clone()
    }

    /// 获取日志记录器
    pub fn logger(&self) -> Arc<StructuredLogger> {
        self.logger.clone()
    }

    /// 获取日志聚合器
    pub fn log_aggregator(&self) -> Arc<LogAggregator> {
        self.log_aggregator.clone()
    }

    /// 获取性能监控器
    pub fn performance_monitor(&self) -> Arc<PerformanceMonitor> {
        self.performance_monitor.clone()
    }

    /// 获取错误追踪器
    pub fn error_tracker(&self) -> Arc<ErrorTracker> {
        self.error_tracker.clone()
    }

    /// 获取系统状态报告器
    pub fn system_reporter(&self) -> Arc<SystemStatusReporter> {
        self.system_reporter.clone()
    }

    /// 启用本地日志管理器
    pub fn enable_local_logging(
        &mut self,
        config: LocalLogConfig,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let local_log_manager = LocalLogManager::new(config)?;
        self.local_log_manager = Some(Arc::new(local_log_manager));
        info!("Local logging enabled");
        Ok(())
    }

    /// 获取本地日志管理器
    pub fn local_log_manager(&self) -> Option<Arc<LocalLogManager>> {
        self.local_log_manager.clone()
    }

    /// 记录本地日志
    pub fn log_local(
        &self,
        level: LocalLogLevel,
        message: &str,
        fields: Option<HashMap<String, String>>,
    ) {
        if let Some(ref manager) = self.local_log_manager {
            manager.log(level, message, fields);
        }
    }

    /// 记录HTTP请求
    pub fn record_http_request(
        &self,
        method: &str,
        path: &str,
        status_code: u16,
        duration: Duration,
    ) {
        let success = status_code < 400;

        // 记录日志
        self.logger
            .log_http_request(method, path, status_code, duration.as_millis() as u64);

        // 记录本地日志
        let mut fields = HashMap::new();
        fields.insert("method".to_string(), method.to_string());
        fields.insert("path".to_string(), path.to_string());
        fields.insert("status_code".to_string(), status_code.to_string());
        fields.insert("duration_ms".to_string(), duration.as_millis().to_string());
        fields.insert("success".to_string(), success.to_string());

        let level = if success {
            LocalLogLevel::Info
        } else {
            LocalLogLevel::Error
        };
        self.log_local(
            level,
            &format!("HTTP {} {} - Status: {}", method, path, status_code),
            Some(fields),
        );

        // 记录指标
        self.metrics
            .increment_counter(metric_names::HTTP_REQUESTS_TOTAL, 1);
        self.metrics
            .record_histogram(metric_names::HTTP_REQUEST_DURATION, duration.as_secs_f64());

        // 记录性能监控
        self.performance_monitor.record_operation(
            &format!("http_{}_{}", method.to_lowercase(), path.replace("/", "_")),
            duration,
            success,
        );

        // 记录错误（如果状态码表示错误）
        if !success {
            let mut context = HashMap::new();
            context.insert("method".to_string(), method.to_string());
            context.insert("path".to_string(), path.to_string());
            context.insert("status_code".to_string(), status_code.to_string());
            context.insert("duration_ms".to_string(), duration.as_millis().to_string());

            let severity = if status_code >= 500 {
                ErrorSeverity::High
            } else {
                ErrorSeverity::Medium
            };

            self.error_tracker.record_error(
                "http_error",
                &format!("HTTP {} {} returned status {}", method, path, status_code),
                context,
                severity,
            );
        }

        // 记录追踪
        if self.config.tracing_enabled
            && let Some(mut span) = self.tracer.start_span(format!("HTTP {} {}", method, path)) {
                span.add_attribute("http.method".to_string(), method.to_string());
                span.add_attribute("http.path".to_string(), path.to_string());
                span.add_attribute("http.status_code".to_string(), status_code.to_string());
                span.add_attribute(
                    "http.duration_ms".to_string(),
                    duration.as_millis().to_string(),
                );

                if !success {
                    span.set_status(SpanStatus::Error(format!("HTTP {}", status_code)));
                }

                self.tracer.finish_span(span);
            }
    }

    /// 记录数据库查询
    pub fn record_database_query(
        &self,
        query: &str,
        duration: Duration,
        rows_affected: Option<u64>,
    ) {
        // 记录日志
        self.logger
            .log_database_query(query, duration.as_millis() as u64, rows_affected);

        // 记录本地日志
        let mut fields = HashMap::new();
        fields.insert("query".to_string(), query.to_string());
        fields.insert("duration_ms".to_string(), duration.as_millis().to_string());
        if let Some(rows) = rows_affected {
            fields.insert("rows_affected".to_string(), rows.to_string());
        }

        self.log_local(LocalLogLevel::Info, "Database query executed", Some(fields));

        // 记录指标
        self.metrics
            .increment_counter(metric_names::DATABASE_QUERIES_TOTAL, 1);
        self.metrics.record_histogram(
            metric_names::DATABASE_QUERY_DURATION,
            duration.as_secs_f64(),
        );

        // 记录追踪
        if self.config.tracing_enabled
            && let Some(mut span) = self.tracer.start_span("database_query".to_string()) {
                span.add_attribute("db.query".to_string(), query.to_string());
                span.add_attribute(
                    "db.duration_ms".to_string(),
                    duration.as_millis().to_string(),
                );
                if let Some(rows) = rows_affected {
                    span.add_attribute("db.rows_affected".to_string(), rows.to_string());
                }
                self.tracer.finish_span(span);
            }
    }

    /// 记录错误
    pub fn record_error(&self, error: &str, context: Option<HashMap<String, String>>) {
        // 记录日志
        self.logger.log_error(error, context.clone());

        // 记录追踪
        if self.config.tracing_enabled
            && let Some(mut span) = self.tracer.start_span("error".to_string()) {
                span.add_attribute("error.message".to_string(), error.to_string());
                if let Some(context) = context {
                    for (key, value) in context {
                        span.add_attribute(format!("error.context.{}", key), value);
                    }
                }
                span.set_status(SpanStatus::Error(error.to_string()));
                self.tracer.finish_span(span);
            }
    }

    /// 记录性能指标
    pub fn record_performance(
        &self,
        operation: &str,
        duration: Duration,
        additional_fields: Option<HashMap<String, String>>,
    ) {
        // 记录日志
        self.logger.log_performance(
            operation,
            duration.as_millis() as u64,
            additional_fields.clone(),
        );

        // 记录指标
        self.metrics.record_timer(operation, duration);

        // 记录追踪
        if self.config.tracing_enabled
            && let Some(mut span) = self.tracer.start_span(operation.to_string()) {
                span.add_attribute(
                    "operation.duration_ms".to_string(),
                    duration.as_millis().to_string(),
                );
                if let Some(fields) = additional_fields {
                    for (key, value) in fields {
                        span.add_attribute(format!("operation.{}", key), value);
                    }
                }
                self.tracer.finish_span(span);
            }
    }

    /// 获取系统状态
    pub fn get_system_status(&self) -> SystemStatus {
        SystemStatus {
            tracing_enabled: self.config.tracing_enabled,
            metrics_enabled: self.config.metrics_enabled,
            logging_enabled: self.config.logging_enabled,
            active_spans: self.tracer.get_active_span_count(),
            total_spans: self.tracer.get_total_span_count(),
            total_counters: self.metrics.get_all_counters().len(),
            total_gauges: self.metrics.get_all_gauges().len(),
            total_histograms: self.metrics.get_histogram_names().len(),
            total_timers: self.metrics.get_timer_names().len(),
        }
    }

    /// 导出所有数据
    pub fn export_all_data(&self) -> Result<ExportedData, Box<dyn std::error::Error>> {
        Ok(ExportedData {
            traces: self.tracer.export_traces()?,
            metrics: self.metrics.export_metrics()?,
            system_status: self.get_system_status(),
        })
    }

    /// 生成完整的系统报告
    pub fn generate_system_report(&self) -> SystemReport {
        self.system_reporter.generate_system_report()
    }

    /// 添加健康检查器
    pub fn add_health_checker(&self, _checker: Box<dyn HealthChecker + Send + Sync>) {
        // 注意：这里需要修改SystemStatusReporter以支持动态添加健康检查器
        // 为了简化，这里只是记录日志
        // info!("Health checker added: {}", checker.name());
    }

    /// 设置性能告警阈值
    pub fn set_performance_alert_threshold(&self, operation: &str, threshold_ms: f64) {
        self.performance_monitor
            .set_alert_threshold(operation, threshold_ms);
    }

    /// 设置错误告警阈值
    pub fn set_error_alert_threshold(&self, error_type: &str, threshold: u64) {
        self.error_tracker
            .set_error_alert_threshold(error_type, threshold);
    }

    /// 获取系统健康状态
    pub fn get_system_health(&self) -> HealthStatus {
        let report = self.generate_system_report();
        report.overall_health
    }
}

impl std::fmt::Debug for OpenTelemetryManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpenTelemetryManager")
            .field("config", &self.config)
            .field("local_log_manager", &self.local_log_manager.is_some())
            .finish()
    }
}

/// 系统状态
#[derive(Clone, Serialize, Deserialize)]
pub struct SystemStatus {
    pub tracing_enabled: bool,
    pub metrics_enabled: bool,
    pub logging_enabled: bool,
    pub active_spans: usize,
    pub total_spans: usize,
    pub total_counters: usize,
    pub total_gauges: usize,
    pub total_histograms: usize,
    pub total_timers: usize,
}

/// 导出的数据
#[derive(Clone, Serialize, Deserialize)]
pub struct ExportedData {
    pub traces: String,
    pub metrics: String,
    pub system_status: SystemStatus,
}
