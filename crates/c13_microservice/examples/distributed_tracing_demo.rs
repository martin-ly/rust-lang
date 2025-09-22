//! 分布式追踪演示
//!
//! 演示OpenTelemetry分布式追踪功能，包括跨服务调用追踪、上下文传播等
#[allow(unused_imports)]
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, error};
use uuid::Uuid;

use c13_microservice::{
    middleware::{
        DistributedTracingMiddleware, DistributedTracingConfig, TracingLogLevel,
        TraceContextBuilder,
    },
    opentelemetry::{
        OpenTelemetryManager, OpenTelemetryConfig,
    },
    error::Result,
};

/// 分布式追踪演示服务器
#[derive(Debug)]
pub struct DistributedTracingDemo {
    _config: DistributedTracingConfig,
    tracing_middleware: DistributedTracingMiddleware,
    otel_manager: std::sync::Arc<OpenTelemetryManager>,
}

impl DistributedTracingDemo {
    pub fn new() -> std::result::Result<Self, Box<dyn std::error::Error>> {
        // 创建OpenTelemetry配置
        let otel_config = OpenTelemetryConfig {
            service_name: "distributed-tracing-demo".to_string(),
            service_version: "1.0.0".to_string(),
            tracing_enabled: true,
            metrics_enabled: true,
            logging_enabled: true,
            jaeger_endpoint: "http://localhost:14268/api/traces".to_string(),
            sampling_ratio: 1.0,
            resource_attributes: {
                let mut attrs = HashMap::new();
                attrs.insert("deployment.environment".to_string(), "demo".to_string());
                attrs.insert("service.instance.id".to_string(), Uuid::new_v4().to_string());
                attrs
            },
        };

        // 创建OpenTelemetry管理器
        let mut otel_manager = OpenTelemetryManager::new(otel_config)
            .map_err(|e| Box::new(std::io::Error::new(std::io::ErrorKind::Other, format!("{}", e))))?;
        otel_manager.init()
            .map_err(|e| Box::new(std::io::Error::new(std::io::ErrorKind::Other, format!("{}", e))))?;

        // 创建分布式追踪配置
        let tracing_config = DistributedTracingConfig {
            enabled: true,
            service_name: "distributed-tracing-demo".to_string(),
            service_version: "1.0.0".to_string(),
            sample_rate: 1.0,
            max_span_duration: Duration::from_secs(300),
            enable_baggage: true,
            enable_correlation_id: true,
            log_level: TracingLogLevel::Info,
        };

        // 创建分布式追踪中间件
        let otel_manager_arc = std::sync::Arc::new(otel_manager);
        let mut tracing_middleware = DistributedTracingMiddleware::new(tracing_config.clone());
        tracing_middleware = tracing_middleware.with_otel_manager(otel_manager_arc.clone());

        Ok(Self {
            _config: tracing_config,
            tracing_middleware,
            otel_manager: otel_manager_arc,
        })
    }

    /// 启动分布式追踪演示
    pub async fn start(&mut self) -> Result<()> {
        info!("启动分布式追踪演示");

        // 演示基本追踪功能
        self.demonstrate_basic_tracing().await?;

        // 演示HTTP请求追踪
        self.demonstrate_http_tracing().await?;

        // 演示数据库查询追踪
        self.demonstrate_database_tracing().await?;

        // 演示外部服务调用追踪
        self.demonstrate_external_service_tracing().await?;

        // 演示追踪上下文传播
        self.demonstrate_context_propagation().await?;

        // 演示自定义事件追踪
        self.demonstrate_custom_event_tracing().await?;

        // 显示追踪统计信息
        self.show_tracing_stats().await?;

        info!("分布式追踪演示完成");
        Ok(())
    }

    /// 演示基本追踪功能
    async fn demonstrate_basic_tracing(&mut self) -> Result<()> {
        info!("=== 基本追踪功能演示 ===");

        // 创建追踪上下文
        let context = TraceContextBuilder::new()
            .with_baggage("user_id".to_string(), "12345".to_string())
            .with_baggage("session_id".to_string(), Uuid::new_v4().to_string())
            .with_sampled(true)
            .build();

        info!("创建追踪上下文:");
        info!("  Trace ID: {}", context.trace_id);
        info!("  Span ID: {}", context.span_id);
        info!("  Sampled: {}", context.sampled);
        info!("  Baggage: {:?}", context.baggage);

        // 设置当前上下文
        self.tracing_middleware.set_current_context(context);

        // 创建基本跨度
        let span = self.tracing_middleware.start_span("basic_operation", None);
        if let Some(span) = span {
            info!("开始基本操作跨度");
            
            // 模拟一些工作
            sleep(Duration::from_millis(100)).await;
            
            // 完成跨度
            self.tracing_middleware.finish_span(span, None);
            info!("基本操作跨度完成");
        }

        Ok(())
    }

    /// 演示HTTP请求追踪
    async fn demonstrate_http_tracing(&mut self) -> Result<()> {
        info!("=== HTTP请求追踪演示 ===");

        // 模拟HTTP请求头
        let mut headers = HashMap::new();
        headers.insert("user-agent".to_string(), "distributed-tracing-demo/1.0.0".to_string());
        headers.insert("x-request-id".to_string(), Uuid::new_v4().to_string());
        headers.insert("x-forwarded-for".to_string(), "192.168.1.100".to_string());

        // 开始HTTP请求追踪
        let (context, span) = self.tracing_middleware.trace_http_request("GET", "/api/users", &headers);
        
        if let Some(context) = context {
            info!("HTTP请求追踪上下文:");
            info!("  Trace ID: {}", context.trace_id);
            info!("  Span ID: {}", context.span_id);
        }

        // 模拟处理时间
        sleep(Duration::from_millis(50)).await;

        // 模拟响应头
        let mut response_headers = HashMap::new();
        response_headers.insert("content-type".to_string(), "application/json".to_string());
        response_headers.insert("content-length".to_string(), "1024".to_string());

        // 完成HTTP请求追踪
        self.tracing_middleware.trace_http_response(span, 200, Duration::from_millis(50), Some(&response_headers));

        info!("HTTP请求追踪完成");

        // 演示错误响应追踪
        let (_, error_span) = self.tracing_middleware.trace_http_request("POST", "/api/users", &headers);
        sleep(Duration::from_millis(30)).await;
        self.tracing_middleware.trace_http_response(error_span, 500, Duration::from_millis(30), None);

        Ok(())
    }

    /// 演示数据库查询追踪
    async fn demonstrate_database_tracing(&mut self) -> Result<()> {
        info!("=== 数据库查询追踪演示 ===");

        // 获取当前上下文
        let current_context = self.tracing_middleware.get_current_context();

        // 模拟数据库查询
        let queries = vec![
            ("SELECT * FROM users WHERE id = ?", Some(1)),
            ("INSERT INTO users (name, email) VALUES (?, ?)", Some(2)),
            ("UPDATE users SET name = ? WHERE id = ?", Some(1)),
        ];

        for (query, rows_affected) in queries {
            let span = self.tracing_middleware.start_span("database_query", current_context.clone());
            
            // 模拟查询执行时间
            let duration = Duration::from_millis(10 + (rand::random::<u64>() % 50));
            sleep(duration).await;

            // 模拟成功或失败
            let success = rand::random::<bool>();
            if success {
                self.tracing_middleware.trace_database_query(span, query, duration, rows_affected, None);
            } else {
                self.tracing_middleware.trace_database_query(span, query, duration, None, Some("Connection timeout"));
            }
        }

        info!("数据库查询追踪演示完成");
        Ok(())
    }

    /// 演示外部服务调用追踪
    async fn demonstrate_external_service_tracing(&mut self) -> Result<()> {
        info!("=== 外部服务调用追踪演示 ===");

        let services = vec![
            ("payment-service", "/api/process-payment", "POST"),
            ("notification-service", "/api/send-notification", "POST"),
            ("user-service", "/api/get-user-profile", "GET"),
        ];

        for (service_name, endpoint, method) in services {
            let current_context = self.tracing_middleware.get_current_context();
            let span = self.tracing_middleware.start_span("external_service_call", current_context);

            // 模拟外部服务调用时间
            let duration = Duration::from_millis(20 + (rand::random::<u64>() % 100));
            sleep(duration).await;

            // 模拟成功或失败
            let success = rand::random::<bool>();
            if success {
                let status_code = if rand::random::<bool>() { 200 } else { 201 };
                self.tracing_middleware.trace_external_service_call(span, service_name, endpoint, method, duration, Some(status_code), None);
            } else {
                let status_code = if rand::random::<bool>() { 500 } else { 404 };
                self.tracing_middleware.trace_external_service_call(span, service_name, endpoint, method, duration, Some(status_code), Some("Service unavailable"));
            }
        }

        info!("外部服务调用追踪演示完成");
        Ok(())
    }

    /// 演示追踪上下文传播
    async fn demonstrate_context_propagation(&mut self) -> Result<()> {
        info!("=== 追踪上下文传播演示 ===");

        // 创建根上下文
        let root_context = TraceContextBuilder::new()
            .with_baggage("request_id".to_string(), Uuid::new_v4().to_string())
            .with_baggage("user_id".to_string(), "67890".to_string())
            .with_sampled(true)
            .build();

        info!("根上下文:");
        info!("  Trace ID: {}", root_context.trace_id);
        info!("  Span ID: {}", root_context.span_id);
        info!("  Baggage: {:?}", root_context.baggage);

        // 将上下文注入到HTTP头部
        let headers = self.tracing_middleware.inject_trace_context(&root_context);
        info!("注入的HTTP头部: {:?}", headers);

        // 从HTTP头部提取上下文
        let extracted_context = self.tracing_middleware.extract_trace_context(&headers);
        if let Some(context) = extracted_context {
            info!("提取的上下文:");
            info!("  Trace ID: {}", context.trace_id);
            info!("  Span ID: {}", context.span_id);
            info!("  Baggage: {:?}", context.baggage);

            // 创建子跨度
            let child_context = TraceContextBuilder::new()
                .with_parent(&context)
                .build();

            info!("子上下文:");
            info!("  Trace ID: {}", child_context.trace_id);
            info!("  Span ID: {}", child_context.span_id);
            info!("  Parent Span ID: {:?}", child_context.parent_span_id);

            // 使用子上下文创建跨度
            let span = self.tracing_middleware.start_span("child_operation", Some(child_context));
            if let Some(span) = span {
                sleep(Duration::from_millis(25)).await;
                self.tracing_middleware.finish_span(span, None);
            }
        }

        info!("追踪上下文传播演示完成");
        Ok(())
    }

    /// 演示自定义事件追踪
    async fn demonstrate_custom_event_tracing(&mut self) -> Result<()> {
        info!("=== 自定义事件追踪演示 ===");

        let events = vec![
            ("user_login", vec![("user_id".to_string(), "12345".to_string()), ("ip_address".to_string(), "192.168.1.100".to_string())]),
            ("order_created", vec![("order_id".to_string(), "ORD-001".to_string()), ("amount".to_string(), "99.99".to_string())]),
            ("payment_processed", vec![("payment_id".to_string(), "PAY-001".to_string()), ("status".to_string(), "success".to_string())]),
        ];

        for (event_name, attributes) in events {
            let current_context = self.tracing_middleware.get_current_context();
            let span = self.tracing_middleware.start_span("custom_event", current_context);

            let mut attrs_map = HashMap::new();
            for (key, value) in attributes {
                attrs_map.insert(key, value);
            }

            // 模拟事件处理
            sleep(Duration::from_millis(15)).await;

            // 模拟成功或失败
            let success = rand::random::<bool>();
            if success {
                self.tracing_middleware.trace_custom_event(span, event_name, Some(attrs_map), None);
            } else {
                self.tracing_middleware.trace_custom_event(span, event_name, Some(attrs_map), Some("Event processing failed"));
            }
        }

        info!("自定义事件追踪演示完成");
        Ok(())
    }

    /// 显示追踪统计信息
    async fn show_tracing_stats(&self) -> Result<()> {
        info!("=== 追踪统计信息 ===");

        let stats = self.tracing_middleware.get_tracing_stats();
        info!("追踪统计:");
        info!("  启用状态: {}", stats.enabled);
        info!("  活跃跨度数: {}", stats.active_spans);
        info!("  总跨度数: {}", stats.total_spans);
        info!("  服务名称: {}", stats.service_name);
        info!("  服务版本: {}", stats.service_version);
        info!("  采样率: {}", stats.sample_rate);

        // 获取系统状态
        let system_status = self.otel_manager.get_system_status();
        info!("系统状态:");
        info!("  追踪启用: {}", system_status.tracing_enabled);
        info!("  指标启用: {}", system_status.metrics_enabled);
        info!("  日志启用: {}", system_status.logging_enabled);
        info!("  活跃跨度: {}", system_status.active_spans);
        info!("  总跨度: {}", system_status.total_spans);
        info!("  计数器数量: {}", system_status.total_counters);
        info!("  仪表数量: {}", system_status.total_gauges);
        info!("  直方图数量: {}", system_status.total_histograms);
        info!("  计时器数量: {}", system_status.total_timers);

        Ok(())
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("分布式追踪演示开始");

    // 创建并启动演示
    let mut demo = match DistributedTracingDemo::new() {
        Ok(demo) => demo,
        Err(e) => {
            error!("创建分布式追踪演示失败: {}", e);
            return Err(anyhow::anyhow!("创建分布式追踪演示失败: {}", e));
        }
    };

    match demo.start().await {
        Ok(_) => {
            info!("分布式追踪演示成功完成");
        }
        Err(e) => {
            error!("分布式追踪演示失败: {}", e);
            return Err(e.into());
        }
    }

    Ok(())
}
