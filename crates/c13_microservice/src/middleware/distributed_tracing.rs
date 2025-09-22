//! 分布式追踪中间件
//!
//! 提供基于OpenTelemetry的分布式追踪功能，支持跨服务调用追踪

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tracing::{error, info, instrument, warn};
use uuid::Uuid;

use crate::opentelemetry::{
    TraceContext, TraceContextManager, TraceContextPropagator, Tracer, Span, SpanStatus,
    OpenTelemetryManager,
};

/// 分布式追踪中间件配置
#[derive(Debug, Clone)]
pub struct DistributedTracingConfig {
    pub enabled: bool,
    pub service_name: String,
    pub service_version: String,
    pub sample_rate: f64, // 采样率 0.0 - 1.0
    pub max_span_duration: Duration,
    pub enable_baggage: bool,
    pub enable_correlation_id: bool,
    pub log_level: TracingLogLevel,
}

impl Default for DistributedTracingConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            service_name: "microservice".to_string(),
            service_version: "1.0.0".to_string(),
            sample_rate: 1.0, // 100% 采样
            max_span_duration: Duration::from_secs(300), // 5分钟
            enable_baggage: true,
            enable_correlation_id: true,
            log_level: TracingLogLevel::Info,
        }
    }
}

/// 追踪日志级别
#[derive(Debug, Clone)]
pub enum TracingLogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

/// 分布式追踪中间件
#[derive(Clone)]
pub struct DistributedTracingMiddleware {
    pub config: DistributedTracingConfig,
    pub tracer: Arc<Tracer>,
    pub propagator: TraceContextPropagator,
    pub otel_manager: Option<Arc<OpenTelemetryManager>>,
}

impl Default for DistributedTracingMiddleware {
    fn default() -> Self {
        Self::new(DistributedTracingConfig::default())
    }
}

impl DistributedTracingMiddleware {
    pub fn new(config: DistributedTracingConfig) -> Self {
        let tracer = Arc::new(Tracer::new(crate::opentelemetry::OpenTelemetryConfig {
            service_name: config.service_name.clone(),
            service_version: config.service_version.clone(),
            tracing_enabled: config.enabled,
            metrics_enabled: false,
            logging_enabled: false,
            jaeger_endpoint: "http://localhost:14268/api/traces".to_string(),
            sampling_ratio: config.sample_rate,
            resource_attributes: HashMap::new(),
        }));

        Self {
            config,
            tracer,
            propagator: TraceContextPropagator::new(),
            otel_manager: None,
        }
    }

    pub fn with_otel_manager(mut self, manager: Arc<OpenTelemetryManager>) -> Self {
        self.otel_manager = Some(manager);
        self
    }

    /// 创建新的追踪上下文
    pub fn create_trace_context(&self) -> TraceContext {
        TraceContext::new()
    }

    /// 从HTTP头部提取追踪上下文
    pub fn extract_trace_context(&mut self, headers: &HashMap<String, String>) -> Option<TraceContext> {
        if !self.config.enabled {
            return None;
        }

        self.propagator.extract_from_headers(headers)
    }

    /// 将追踪上下文注入到HTTP头部
    pub fn inject_trace_context(&self, context: &TraceContext) -> HashMap<String, String> {
        if !self.config.enabled {
            return HashMap::new();
        }

        self.propagator.inject_to_headers(context)
    }

    /// 开始新的追踪跨度
    #[instrument(skip(self))]
    pub fn start_span(&self, operation_name: &str, context: Option<TraceContext>) -> Option<Span> {
        if !self.config.enabled {
            return None;
        }

        // 设置当前追踪上下文
        if let Some(ctx) = context {
            TraceContextManager::set_current_context(ctx);
        }

        // 创建新的跨度
        let mut span = self.tracer.start_span(operation_name.to_string())?;
        
        // 添加服务信息
        span.add_attribute("service.name".to_string(), self.config.service_name.clone());
        span.add_attribute("service.version".to_string(), self.config.service_version.clone());
        
        // 添加操作开始时间
        span.add_attribute("operation.start_time".to_string(), 
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis()
                .to_string()
        );

        Some(span)
    }

    /// 完成追踪跨度
    #[instrument(skip(self, span))]
    pub fn finish_span(&self, mut span: Span, status: Option<SpanStatus>) {
        if !self.config.enabled {
            return;
        }

        // 设置跨度状态
        if let Some(s) = status {
            span.set_status(s);
        }

        // 添加操作结束时间
        span.add_attribute("operation.end_time".to_string(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis()
                .to_string()
        );

        // 完成跨度
        self.tracer.finish_span(span);
    }

    /// 记录HTTP请求追踪
    #[instrument(skip(self, headers))]
    pub fn trace_http_request(
        &mut self,
        method: &str,
        path: &str,
        headers: &HashMap<String, String>,
    ) -> (Option<TraceContext>, Option<Span>) {
        if !self.config.enabled {
            return (None, None);
        }

        // 提取或创建追踪上下文
        let trace_context = self.extract_trace_context(headers)
            .unwrap_or_else(|| self.create_trace_context());

        // 开始HTTP请求跨度
        let operation_name = format!("HTTP {} {}", method, path);
        let mut span = self.start_span(&operation_name, Some(trace_context.clone()));

        if let Some(ref mut span) = span {
            // 添加HTTP相关属性
            span.add_attribute("http.method".to_string(), method.to_string());
            span.add_attribute("http.path".to_string(), path.to_string());
            span.add_attribute("http.url".to_string(), path.to_string());
            
            // 添加请求ID
            if self.config.enable_correlation_id {
                let request_id = headers.get("x-request-id")
                    .cloned()
                    .unwrap_or_else(|| Uuid::new_v4().to_string());
                span.add_attribute("http.request_id".to_string(), request_id);
            }

            // 添加用户代理
            if let Some(user_agent) = headers.get("user-agent") {
                span.add_attribute("http.user_agent".to_string(), user_agent.clone());
            }

            // 添加客户端IP
            if let Some(client_ip) = headers.get("x-forwarded-for")
                .or_else(|| headers.get("x-real-ip"))
                .or_else(|| headers.get("remote-addr")) {
                span.add_attribute("http.client_ip".to_string(), client_ip.clone());
            }

            // 记录请求开始日志
            self.log_tracing_event(TracingLogLevel::Info, "HTTP请求开始", Some(span));
        }

        (Some(trace_context), span)
    }

    /// 记录HTTP响应追踪
    #[instrument(skip(self, span))]
    pub fn trace_http_response(
        &self,
        span: Option<Span>,
        status_code: u16,
        duration: Duration,
        headers: Option<&HashMap<String, String>>,
    ) {
        if !self.config.enabled {
            return;
        }

        if let Some(mut span) = span {
            // 添加响应相关属性
            span.add_attribute("http.status_code".to_string(), status_code.to_string());
            span.add_attribute("http.duration_ms".to_string(), duration.as_millis().to_string());
            
            // 添加响应头（如果有）
            if let Some(response_headers) = headers {
                if let Some(content_type) = response_headers.get("content-type") {
                    span.add_attribute("http.response.content_type".to_string(), content_type.clone());
                }
                if let Some(content_length) = response_headers.get("content-length") {
                    span.add_attribute("http.response.content_length".to_string(), content_length.clone());
                }
            }

            // 确定跨度状态
            let status = if status_code >= 500 {
                SpanStatus::Error(format!("HTTP服务器错误: {}", status_code))
            } else if status_code >= 400 {
                SpanStatus::Error(format!("HTTP客户端错误: {}", status_code))
            } else {
                SpanStatus::Ok
            };

            // 记录响应日志
            let log_level = if status_code >= 400 {
                TracingLogLevel::Warn
            } else {
                TracingLogLevel::Info
            };
            self.log_tracing_event(log_level, "HTTP请求完成", Some(&span));

            // 完成跨度
            self.finish_span(span, Some(status));
        }
    }

    /// 记录数据库查询追踪
    #[instrument(skip(self, span))]
    pub fn trace_database_query(
        &self,
        span: Option<Span>,
        query: &str,
        duration: Duration,
        rows_affected: Option<u64>,
        error: Option<&str>,
    ) {
        if !self.config.enabled {
            return;
        }

        if let Some(mut span) = span {
            // 添加数据库相关属性
            span.add_attribute("db.operation".to_string(), "query".to_string());
            span.add_attribute("db.statement".to_string(), query.to_string());
            span.add_attribute("db.duration_ms".to_string(), duration.as_millis().to_string());
            
            if let Some(rows) = rows_affected {
                span.add_attribute("db.rows_affected".to_string(), rows.to_string());
            }

            // 确定跨度状态
            let status = if let Some(err) = error {
                span.add_attribute("db.error".to_string(), err.to_string());
                SpanStatus::Error(format!("数据库错误: {}", err))
            } else {
                SpanStatus::Ok
            };

            // 记录查询日志
            let log_level = if error.is_some() {
                TracingLogLevel::Error
            } else {
                TracingLogLevel::Debug
            };
            self.log_tracing_event(log_level, "数据库查询执行", Some(&span));

            // 完成跨度
            self.finish_span(span, Some(status));
        }
    }

    /// 记录外部服务调用追踪
    #[instrument(skip(self, span))]
    pub fn trace_external_service_call(
        &self,
        span: Option<Span>,
        service_name: &str,
        endpoint: &str,
        method: &str,
        duration: Duration,
        status_code: Option<u16>,
        error: Option<&str>,
    ) {
        if !self.config.enabled {
            return;
        }

        if let Some(mut span) = span {
            // 添加外部服务相关属性
            span.add_attribute("external.service.name".to_string(), service_name.to_string());
            span.add_attribute("external.service.endpoint".to_string(), endpoint.to_string());
            span.add_attribute("external.service.method".to_string(), method.to_string());
            span.add_attribute("external.service.duration_ms".to_string(), duration.as_millis().to_string());
            
            if let Some(code) = status_code {
                span.add_attribute("external.service.status_code".to_string(), code.to_string());
            }

            // 确定跨度状态
            let status = if let Some(err) = error {
                span.add_attribute("external.service.error".to_string(), err.to_string());
                SpanStatus::Error(format!("外部服务调用失败: {}", err))
            } else if let Some(code) = status_code {
                if code >= 400 {
                    SpanStatus::Error(format!("外部服务返回错误: {}", code))
                } else {
                    SpanStatus::Ok
                }
            } else {
                SpanStatus::Ok
            };

            // 记录调用日志
            let log_level = if error.is_some() || status_code.map_or(false, |c| c >= 400) {
                TracingLogLevel::Warn
            } else {
                TracingLogLevel::Info
            };
            self.log_tracing_event(log_level, "外部服务调用", Some(&span));

            // 完成跨度
            self.finish_span(span, Some(status));
        }
    }

    /// 记录自定义事件追踪
    #[instrument(skip(self, span, attributes))]
    pub fn trace_custom_event(
        &self,
        span: Option<Span>,
        event_name: &str,
        attributes: Option<HashMap<String, String>>,
        error: Option<&str>,
    ) {
        if !self.config.enabled {
            return;
        }

        if let Some(mut span) = span {
            // 添加自定义事件属性
            span.add_attribute("event.name".to_string(), event_name.to_string());
            
            if let Some(attrs) = attributes {
                for (key, value) in attrs {
                    span.add_attribute(format!("event.{}", key), value);
                }
            }

            // 确定跨度状态
            let status = if let Some(err) = error {
                span.add_attribute("event.error".to_string(), err.to_string());
                SpanStatus::Error(format!("自定义事件失败: {}", err))
            } else {
                SpanStatus::Ok
            };

            // 记录事件日志
            let log_level = if error.is_some() {
                TracingLogLevel::Error
            } else {
                TracingLogLevel::Info
            };
            self.log_tracing_event(log_level, event_name, Some(&span));

            // 完成跨度
            self.finish_span(span, Some(status));
        }
    }

    /// 记录追踪事件日志
    fn log_tracing_event(&self, level: TracingLogLevel, message: &str, span: Option<&Span>) {
        match level {
            TracingLogLevel::Error => {
                error!(
                    message = %message,
                    span_name = span.map(|s| s.name.clone()).unwrap_or_default(),
                    "追踪事件"
                );
            }
            TracingLogLevel::Warn => {
                warn!(
                    message = %message,
                    span_name = span.map(|s| s.name.clone()).unwrap_or_default(),
                    "追踪事件"
                );
            }
            TracingLogLevel::Info => {
                info!(
                    message = %message,
                    span_name = span.map(|s| s.name.clone()).unwrap_or_default(),
                    "追踪事件"
                );
            }
            TracingLogLevel::Debug => {
                tracing::debug!(
                    message = %message,
                    span_name = span.map(|s| s.name.clone()).unwrap_or_default(),
                    "追踪事件"
                );
            }
            TracingLogLevel::Trace => {
                tracing::trace!(
                    message = %message,
                    span_name = span.map(|s| s.name.clone()).unwrap_or_default(),
                    "追踪事件"
                );
            }
        }
    }

    /// 获取当前追踪上下文
    pub fn get_current_context(&self) -> Option<TraceContext> {
        if !self.config.enabled {
            return None;
        }
        TraceContextManager::get_current_context()
    }

    /// 设置当前追踪上下文
    pub fn set_current_context(&self, context: TraceContext) {
        if self.config.enabled {
            TraceContextManager::set_current_context(context);
        }
    }

    /// 清除当前追踪上下文
    pub fn clear_current_context(&self) {
        if self.config.enabled {
            TraceContextManager::clear_current_context();
        }
    }

    /// 获取追踪统计信息
    pub fn get_tracing_stats(&self) -> TracingStats {
        if !self.config.enabled {
            return TracingStats::default();
        }

        TracingStats {
            enabled: true,
            active_spans: self.tracer.get_active_span_count(),
            total_spans: self.tracer.get_total_span_count(),
            service_name: self.config.service_name.clone(),
            service_version: self.config.service_version.clone(),
            sample_rate: self.config.sample_rate,
        }
    }
}

/// 追踪统计信息
#[derive(Debug, Clone, Default)]
pub struct TracingStats {
    pub enabled: bool,
    pub active_spans: usize,
    pub total_spans: usize,
    pub service_name: String,
    pub service_version: String,
    pub sample_rate: f64,
}

/// 追踪上下文构建器
#[derive(Debug, Clone)]
pub struct TraceContextBuilder {
    context: TraceContext,
}

impl TraceContextBuilder {
    pub fn new() -> Self {
        Self {
            context: TraceContext::new(),
        }
    }

    pub fn with_parent(mut self, parent: &TraceContext) -> Self {
        self.context = TraceContext::with_parent(parent);
        self
    }

    pub fn with_baggage(mut self, key: String, value: String) -> Self {
        self.context.baggage.insert(key, value);
        self
    }

    pub fn with_sampled(mut self, sampled: bool) -> Self {
        self.context.sampled = sampled;
        if sampled {
            self.context.flags |= 1;
        } else {
            self.context.flags &= !1;
        }
        self
    }

    pub fn with_debug(mut self, debug: bool) -> Self {
        self.context.debug = debug;
        if debug {
            self.context.flags |= 2;
        } else {
            self.context.flags &= !2;
        }
        self
    }

    pub fn build(self) -> TraceContext {
        self.context
    }
}

impl Default for TraceContextBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_distributed_tracing_config() {
        let config = DistributedTracingConfig::default();
        assert!(config.enabled);
        assert_eq!(config.service_name, "microservice");
        assert_eq!(config.sample_rate, 1.0);
    }

    #[test]
    fn test_trace_context_builder() {
        let context = TraceContextBuilder::new()
            .with_baggage("user_id".to_string(), "123".to_string())
            .with_sampled(true)
            .build();

        assert!(context.sampled);
        assert_eq!(context.baggage.get("user_id"), Some(&"123".to_string()));
    }

    #[tokio::test]
    async fn test_http_request_tracing() {
        let mut middleware = DistributedTracingMiddleware::new(DistributedTracingConfig::default());
        
        let mut headers = HashMap::new();
        headers.insert("user-agent".to_string(), "test-agent".to_string());
        
        let (context, span) = middleware.trace_http_request("GET", "/api/test", &headers);
        
        assert!(context.is_some());
        assert!(span.is_some());
        
        if let Some(span) = span {
            middleware.trace_http_response(Some(span), 200, Duration::from_millis(100), None);
        }
    }
}

impl std::fmt::Debug for DistributedTracingMiddleware {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DistributedTracingMiddleware")
            .field("config", &self.config)
            .field("otel_manager", &self.otel_manager.is_some())
            .finish()
    }
}