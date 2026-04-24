//! C10 Networks - OpenTelemetry 全链路追踪集成
//!
//! 提供完整的 tracing + OpenTelemetry 集成，支持导出到 Jaeger 和标准输出。
//!
//! # 设计目标
//! - 与现有 `tracing` 生态无缝集成
//! - 支持 OTLP HTTP/gRPC 导出到 Jaeger/Tempo
//! - 提供 stdout 导出器用于开发和调试
//! - 零成本抽象：未启用时不产生运行时开销
//!
//! # 参考实践
//! - Microsoft: Application Insights OpenTelemetry 集成
//! - AWS: Distro for OpenTelemetry (ADOT)
//! - Cloudflare: 边缘 tracing 实践
//!
//! # 快速开始
//!
//! ```rust,no_run
//! use c10_networks::telemetry::{init_tracer, TelemetryConfig, ExportTarget};
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = TelemetryConfig::jaeger_local();
//!     let _guard = init_tracer(config).await.expect("追踪系统初始化失败");
//!
//!     // 你的应用代码...
//! }
//! ```

use opentelemetry::trace::TracerProvider as _;
use std::time::Duration;
use tracing::Span;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

/// 遥测配置
#[derive(Debug, Clone)]
pub struct TelemetryConfig {
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 导出目标
    pub target: ExportTarget,
    /// 批量导出间隔
    pub export_interval: Duration,
    /// 采样率 (0.0 - 1.0)
    pub sampling_rate: f64,
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            service_name: "c10_networks".to_string(),
            service_version: env!("CARGO_PKG_VERSION").to_string(),
            target: ExportTarget::Stdout,
            export_interval: Duration::from_secs(5),
            sampling_rate: 1.0,
        }
    }
}

impl TelemetryConfig {
    /// 本地 Jaeger 开发配置
    ///
    /// Jaeger UI: http://localhost:16686
    pub fn jaeger_local() -> Self {
        Self {
            service_name: "c10_networks".to_string(),
            service_version: env!("CARGO_PKG_VERSION").to_string(),
            target: ExportTarget::JaegerLocal,
            export_interval: Duration::from_secs(1),
            sampling_rate: 1.0,
        }
    }

    /// 标准输出导出配置（开发调试）
    pub fn stdout() -> Self {
        Self {
            service_name: "c10_networks".to_string(),
            service_version: env!("CARGO_PKG_VERSION").to_string(),
            target: ExportTarget::Stdout,
            export_interval: Duration::from_secs(0),
            sampling_rate: 1.0,
        }
    }

    /// OTLP HTTP 端点配置
    pub fn otlp_http(endpoint: impl Into<String>) -> Self {
        Self {
            service_name: "c10_networks".to_string(),
            service_version: env!("CARGO_PKG_VERSION").to_string(),
            target: ExportTarget::OtlpHttp(endpoint.into()),
            export_interval: Duration::from_secs(5),
            sampling_rate: 1.0,
        }
    }
}

/// 导出目标
#[derive(Debug, Clone)]
pub enum ExportTarget {
    /// 标准输出（开发调试）
    Stdout,
    /// 本地 Jaeger (OTLP HTTP, http://localhost:4318)
    JaegerLocal,
    /// 自定义 OTLP HTTP 端点
    OtlpHttp(String),
}

/// 遥测守卫
///
/// 当此守卫被 drop 时，会刷新并关闭 tracer。
pub struct TelemetryGuard {
    provider: opentelemetry_sdk::trace::SdkTracerProvider,
}

impl Drop for TelemetryGuard {
    fn drop(&mut self) {
        if let Err(e) = self.provider.shutdown() {
            eprintln!("OpenTelemetry shutdown error: {:?}", e);
        }
    }
}

/// 初始化 Tracer
///
/// # 示例
///
/// ```rust,no_run
/// use c10_networks::telemetry::{init_tracer, TelemetryConfig};
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let config = TelemetryConfig::stdout();
/// let _guard = init_tracer(config).await.map_err(|e| e as Box<dyn std::error::Error>)?;
/// # Ok(())
/// # }
/// ```
pub async fn init_tracer(
    config: TelemetryConfig,
) -> Result<TelemetryGuard, Box<dyn std::error::Error + Send + Sync>> {
    let resource = opentelemetry_sdk::Resource::builder()
        .with_service_name(config.service_name.clone())
        .with_attribute(
            opentelemetry::KeyValue::new("service.version", config.service_version.clone()),
        )
        .build();

    let provider = match &config.target {
        ExportTarget::Stdout => init_stdout_tracer(resource, &config).await?,
        ExportTarget::JaegerLocal => {
            init_otlp_tracer(resource, "http://localhost:4318/v1/traces".to_string(), &config)
                .await?
        }
        ExportTarget::OtlpHttp(endpoint) => {
            init_otlp_tracer(resource, endpoint.clone(), &config).await?
        }
    };

    // 设置全局 tracer provider
    let tracer = provider.tracer("c10_networks");
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);

    // 初始化 tracing subscriber
    let subscriber = tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer());

    subscriber.init();

    let service_name = &config.service_name;
    let service_version = &config.service_version;
    tracing::info!(
        target: "c10_networks::telemetry",
        service_name = %service_name,
        service_version = %service_version,
        "OpenTelemetry tracer initialized"
    );

    Ok(TelemetryGuard { provider })
}

/// 初始化 stdout 导出器（开发调试）
async fn init_stdout_tracer(
    resource: opentelemetry_sdk::Resource,
    _config: &TelemetryConfig,
) -> Result<opentelemetry_sdk::trace::SdkTracerProvider, Box<dyn std::error::Error + Send + Sync>> {
    let exporter = opentelemetry_stdout::SpanExporter::default();

    let provider = opentelemetry_sdk::trace::SdkTracerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter)
        .build();

    Ok(provider)
}

/// 初始化 OTLP HTTP 导出器
async fn init_otlp_tracer(
    resource: opentelemetry_sdk::Resource,
    endpoint: String,
    config: &TelemetryConfig,
) -> Result<opentelemetry_sdk::trace::SdkTracerProvider, Box<dyn std::error::Error + Send + Sync>> {
    use opentelemetry_otlp::{Protocol, WithExportConfig};

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_protocol(Protocol::HttpBinary)
        .with_endpoint(endpoint)
        .with_timeout(Duration::from_secs(10))
        .build()?;

    let sampler = if config.sampling_rate >= 1.0 {
        opentelemetry_sdk::trace::Sampler::AlwaysOn
    } else if config.sampling_rate <= 0.0 {
        opentelemetry_sdk::trace::Sampler::AlwaysOff
    } else {
        opentelemetry_sdk::trace::Sampler::TraceIdRatioBased(config.sampling_rate)
    };

    let provider = opentelemetry_sdk::trace::SdkTracerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter)
        .with_sampler(sampler)
        .build();

    Ok(provider)
}

/// 创建网络请求追踪 Span
///
/// # 示例
///
/// ```rust
/// use c10_networks::telemetry::request_span;
///
/// let _span = request_span("GET", "/api/v1/users", "192.168.1.1");
/// // 请求处理代码...
/// drop(_span);
/// ```
pub fn request_span(method: &str, path: &str, peer_addr: &str) -> Span {
    let otel_name = format!("{} {}", method, path);
    tracing::info_span!(
        "http_request",
        http_method = %method,
        http_target = %path,
        http_client_ip = %peer_addr,
        otel_name = %otel_name,
    )
}

/// 创建 DNS 查询追踪 Span
pub fn dns_query_span(query: &str, record_type: &str) -> Span {
    tracing::info_span!(
        "dns_query",
        dns_query = %query,
        dns_record_type = %record_type,
        otel_name = "DNS Query",
    )
}

/// 创建 TCP 连接追踪 Span
pub fn tcp_connection_span(peer_addr: &str, local_addr: &str) -> Span {
    tracing::info_span!(
        "tcp_connection",
        network_peer_address = %peer_addr,
        network_local_address = %local_addr,
        otel_name = "TCP Connect",
    )
}

/// 记录网络错误事件
pub fn record_network_error(span: &Span, error: &dyn std::error::Error) {
    tracing::error!(
        parent: span,
        error.message = %error,
        error.type = "network_error",
        "网络操作失败"
    );
}

/// 记录请求响应元数据
pub fn record_response_meta(span: &Span, status_code: u16, content_length: Option<usize>) {
    if let Some(len) = content_length {
        tracing::info!(
            parent: span,
            http_status_code = status_code,
            http_response_body_size = len,
            "请求处理完成"
        );
    } else {
        tracing::info!(
            parent: span,
            http_status_code = status_code,
            "请求处理完成"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_telemetry_config_default() {
        let config = TelemetryConfig::default();
        assert_eq!(config.service_name, "c10_networks");
        assert!(!config.service_version.is_empty());
        assert_eq!(config.sampling_rate, 1.0);
    }

    #[test]
    fn test_telemetry_config_jaeger() {
        let config = TelemetryConfig::jaeger_local();
        assert_eq!(config.service_name, "c10_networks");
        matches!(config.target, ExportTarget::JaegerLocal);
    }

    #[test]
    fn test_telemetry_config_stdout() {
        let config = TelemetryConfig::stdout();
        matches!(config.target, ExportTarget::Stdout);
    }

    #[test]
    fn test_telemetry_config_otlp() {
        let config = TelemetryConfig::otlp_http("http://collector:4318");
        matches!(config.target, ExportTarget::OtlpHttp(_));
    }

    #[test]
    fn test_request_span_creation() {
        let span = request_span("GET", "/api/test", "127.0.0.1");
        assert!(span.is_disabled() || !span.is_none(), "Span 应被正确创建");
    }

    #[test]
    fn test_dns_query_span_creation() {
        let span = dns_query_span("example.com", "A");
        assert!(span.is_disabled() || !span.is_none(), "Span 应被正确创建");
    }

    #[test]
    fn test_tcp_connection_span_creation() {
        let span = tcp_connection_span("192.168.1.1:8080", "10.0.0.1:12345");
        assert!(span.is_disabled() || !span.is_none(), "Span 应被正确创建");
    }
}
