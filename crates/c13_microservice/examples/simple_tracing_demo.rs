//! 简单分布式追踪演示
//!
//! 演示OpenTelemetry分布式追踪的基本功能

use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, error};

use c13_microservice::{
    middleware::{
        DistributedTracingMiddleware, DistributedTracingConfig, TracingLogLevel,
    },
    opentelemetry::{
        OpenTelemetryConfig,
    },
    error::Result,
};

/// 简单分布式追踪演示
pub struct SimpleTracingDemo {
    tracing_middleware: DistributedTracingMiddleware,
}

impl SimpleTracingDemo {
    pub fn new() -> Result<Self> {
        // 创建OpenTelemetry配置
        let _otel_config = OpenTelemetryConfig {
            service_name: "simple-tracing-demo".to_string(),
            service_version: "1.0.0".to_string(),
            tracing_enabled: true,
            metrics_enabled: false,
            logging_enabled: false,
            jaeger_endpoint: "http://localhost:14268/api/traces".to_string(),
            sampling_ratio: 1.0,
            resource_attributes: HashMap::new(),
        };

        // 创建分布式追踪配置
        let tracing_config = DistributedTracingConfig {
            enabled: true,
            service_name: "simple-tracing-demo".to_string(),
            service_version: "1.0.0".to_string(),
            sample_rate: 1.0,
            max_span_duration: Duration::from_secs(300),
            enable_baggage: true,
            enable_correlation_id: true,
            log_level: TracingLogLevel::Info,
        };

        // 创建分布式追踪中间件
        let tracing_middleware = DistributedTracingMiddleware::new(tracing_config);

        Ok(Self {
            tracing_middleware,
        })
    }

    /// 启动简单分布式追踪演示
    pub async fn start(&mut self) -> Result<()> {
        info!("启动简单分布式追踪演示");

        // 演示基本追踪功能
        self.demonstrate_basic_tracing().await?;

        // 演示HTTP请求追踪
        self.demonstrate_http_tracing().await?;

        // 显示追踪统计信息
        self.show_tracing_stats().await?;

        info!("简单分布式追踪演示完成");
        Ok(())
    }

    /// 演示基本追踪功能
    async fn demonstrate_basic_tracing(&mut self) -> Result<()> {
        info!("=== 基本追踪功能演示 ===");

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
        headers.insert("user-agent".to_string(), "simple-tracing-demo/1.0.0".to_string());

        // 开始HTTP请求追踪
        let (context, span) = self.tracing_middleware.trace_http_request("GET", "/api/users", &headers);
        
        if let Some(context) = context {
            info!("HTTP请求追踪上下文:");
            info!("  Trace ID: {}", context.trace_id);
            info!("  Span ID: {}", context.span_id);
        }

        // 模拟处理时间
        sleep(Duration::from_millis(50)).await;

        // 完成HTTP请求追踪
        self.tracing_middleware.trace_http_response(span, 200, Duration::from_millis(50), None);

        info!("HTTP请求追踪完成");
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

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("简单分布式追踪演示开始");

    // 创建并启动演示
    let mut demo = match SimpleTracingDemo::new() {
        Ok(demo) => demo,
        Err(e) => {
            error!("创建简单分布式追踪演示失败: {}", e);
            return Err(e);
        }
    };

    match demo.start().await {
        Ok(_) => {
            info!("简单分布式追踪演示成功完成");
        }
        Err(e) => {
            error!("简单分布式追踪演示失败: {}", e);
            return Err(e);
        }
    }

    Ok(())
}
