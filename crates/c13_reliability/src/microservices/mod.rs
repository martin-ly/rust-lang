//! # 微服务架构模式模块
//!
//! 本模块提供企业级微服务架构的核心组件，包括：
//!
//! - **服务发现**：动态服务注册、健康检查、负载均衡
//! - **API网关**：统一入口、路由转发、认证授权
//! - **配置中心**：动态配置、版本管理、配置推送
//! - **分布式追踪**：调用链追踪、性能分析
//! - **服务网格**：流量管理、可观测性、安全通信
//!
//! ## 核心特性
//!
//! - ✅ 云原生设计，支持Kubernetes/Docker
//! - ✅ 高可用架构，自动故障转移
//! - ✅ 弹性扩展，动态服务发现
//! - ✅ 可观测性，全链路追踪
//! - ✅ 安全通信，mTLS支持
//!
//! ## 架构设计
//!
//! ```text
//!                    ┌──────────────┐
//!                    │ API Gateway  │
//!                    └──────┬───────┘
//!                           │
//!            ┌──────────────┼──────────────┐
//!            │              │              │
//!       ┌────▼────┐    ┌───▼────┐    ┌───▼────┐
//!       │ Service │    │Service │    │Service │
//!       │    A    │    │   B    │    │   C    │
//!       └────┬────┘    └───┬────┘    └───┬────┘
//!            │             │              │
//!            └─────────────┼──────────────┘
//!                          │
//!                ┌─────────▼──────────┐
//!                │ Service Discovery  │
//!                │   + Config Center  │
//!                └────────────────────┘
//! ```

pub mod service_discovery;
pub mod api_gateway;
pub mod config_center;
pub mod distributed_tracing;
pub mod service_mesh;

// Re-export commonly used types
pub use service_discovery::{
    ServiceDiscovery, ServiceRegistry, ServiceInstance, ServiceMetadata,
    HealthCheck, HealthStatus, LoadBalancer, LoadBalancingStrategy,
};

pub use api_gateway::{
    ApiGateway, Route, RouteConfig, GatewayMiddleware,
    AuthenticationProvider, RateLimitPolicy,
};

pub use config_center::{
    ConfigCenter, ConfigRepository, ConfigItem, ConfigVersion,
    ConfigWatcher, ConfigChangeEvent,
};

pub use distributed_tracing::{
    Span, SpanContext, TraceId, SpanId, SpanKind, SpanStatus,
    Tracer, TracingProvider, TracingConfig,
    Sampler, AlwaysOnSampler, AlwaysOffSampler, RatioSampler,
};

pub use service_mesh::{
    ServiceMesh, Sidecar, TrafficPolicy, CircuitBreakerPolicy as MeshCircuitBreakerPolicy,
    RetryPolicy as MeshRetryPolicy,
};

/// 微服务配置
#[derive(Debug, Clone)]
pub struct MicroserviceConfig {
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 服务实例ID
    pub instance_id: String,
    /// 服务发现配置
    pub discovery_config: service_discovery::DiscoveryConfig,
    /// 网关配置
    pub gateway_config: Option<api_gateway::GatewayConfig>,
    /// 配置中心配置
    pub config_center_config: Option<config_center::ConfigCenterConfig>,
    /// 追踪配置
    pub tracing_config: Option<distributed_tracing::TracingConfig>,
}

impl Default for MicroserviceConfig {
    fn default() -> Self {
        Self {
            service_name: "unknown-service".to_string(),
            service_version: "1.0.0".to_string(),
            instance_id: uuid::Uuid::new_v4().to_string(),
            discovery_config: service_discovery::DiscoveryConfig::default(),
            gateway_config: None,
            config_center_config: None,
            tracing_config: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_microservice_config_default() {
        let config = MicroserviceConfig::default();
        assert_eq!(config.service_name, "unknown-service");
        assert_eq!(config.service_version, "1.0.0");
        assert!(!config.instance_id.is_empty());
    }
}

