//! 服务网格模块
//!
//! 提供服务发现、负载均衡、熔断器和流量管理功能

pub mod service_discovery;
pub mod load_balancer;
pub mod circuit_breaker;
pub mod traffic_management;

pub use service_discovery::{
    ServiceDiscovery, ServiceRegistry, ServiceInstance, ServiceHealth,
    DiscoveryConfig, RegistryConfig, HealthCheck,
};
pub use load_balancer::{
    LoadBalancer, LoadBalancingStrategy, LoadBalancerConfig,
};
pub use circuit_breaker::{
    CircuitBreaker, CircuitBreakerState, CircuitBreakerConfig,
    CircuitBreakerError, CircuitBreakerResult,
};
pub use traffic_management::{
    TrafficManager, TrafficPolicy, TrafficRule, TrafficConfig,
    RetryPolicy, TimeoutPolicy, RateLimitPolicy,
};

use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 服务网格管理器
#[derive(Debug)]
pub struct ServiceMeshManager {
    pub discovery: ServiceDiscovery,
    pub load_balancer: LoadBalancer,
    pub circuit_breakers: HashMap<String, CircuitBreaker>,
    pub traffic_manager: TrafficManager,
    pub config: ServiceMeshConfig,
}

impl ServiceMeshManager {
    /// 创建新的服务网格管理器
    pub fn new(config: ServiceMeshConfig) -> Self {
        let discovery = ServiceDiscovery::new(config.discovery.clone());
        let load_balancer = LoadBalancer::new(config.load_balancer.clone());
        let traffic_manager = TrafficManager::new(config.traffic.clone());

        Self {
            discovery,
            load_balancer,
            circuit_breakers: HashMap::new(),
            traffic_manager,
            config,
        }
    }

    /// 注册服务
    pub async fn register_service(&mut self, service: ServiceInstance) -> Result<(), ServiceMeshError> {
        self.discovery.register_service(service).await
            .map_err(ServiceMeshError::DiscoveryError)
    }

    /// 发现服务实例
    pub async fn discover_services(&mut self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceMeshError> {
        self.discovery.discover_services(service_name).await
            .map_err(ServiceMeshError::DiscoveryError)
    }

    /// 选择服务实例（负载均衡）
    pub async fn select_instance(&mut self, service_name: &str) -> Result<ServiceInstance, ServiceMeshError> {
        let instances = self.discover_services(service_name).await?;
        
        if instances.is_empty() {
            return Err(ServiceMeshError::NoAvailableInstances(service_name.to_string()));
        }

        // 过滤健康的实例
        let healthy_instances: Vec<ServiceInstance> = instances
            .into_iter()
            .filter(|instance| {
                // 检查熔断器状态
                if let Some(circuit_breaker) = self.circuit_breakers.get(&instance.id) {
                    circuit_breaker.can_execute()
                } else {
                    true
                }
            })
            .collect();

        if healthy_instances.is_empty() {
            return Err(ServiceMeshError::NoHealthyInstances(service_name.to_string()));
        }

        // 应用负载均衡策略
        self.load_balancer.select_instance(&healthy_instances)
            .map_err(ServiceMeshError::LoadBalancerError)
    }

    /// 执行服务调用
    pub async fn call_service<F, Fut, T>(&mut self, service_name: &str, operation: F) -> Result<T, ServiceMeshError>
    where
        F: FnOnce(&ServiceInstance) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Result<T, ServiceMeshError>> + Send + 'static,
        T: Send + 'static,
    {
        let instance = self.select_instance(service_name).await?;
        let instance_id = instance.id.clone();

        // 获取或创建熔断器
        let circuit_breaker = self.circuit_breakers
            .entry(instance_id.clone())
            .or_insert_with(|| CircuitBreaker::new(CircuitBreakerConfig::default()));

        // 检查熔断器状态
        if !circuit_breaker.can_execute() {
            return Err(ServiceMeshError::CircuitBreakerOpen(instance_id));
        }

        // 执行操作
        let operation_future = operation(&instance);
        let result = match operation_future.await {
            Ok(value) => {
                circuit_breaker.record_success();
                Ok(value)
            }
            Err(e) => {
                circuit_breaker.record_failure();
                tracing::warn!("服务调用失败: {:?}", e);
                Err(e)
            }
        };

        result
    }

    /// 添加熔断器
    pub fn add_circuit_breaker(&mut self, service_id: String, config: CircuitBreakerConfig) {
        self.circuit_breakers.insert(service_id, CircuitBreaker::new(config));
    }

    /// 获取服务健康状态
    pub async fn get_service_health(&mut self, service_name: &str) -> Result<Vec<ServiceHealth>, ServiceMeshError> {
        self.discovery.get_service_health(service_name).await
            .map_err(ServiceMeshError::DiscoveryError)
    }

    /// 获取服务网格统计信息
    pub fn get_stats(&self) -> ServiceMeshStats {
        ServiceMeshStats {
            registered_services: self.discovery.get_registered_count(),
            active_circuit_breakers: self.circuit_breakers.len(),
            load_balancer_strategy: self.load_balancer.get_strategy(),
            traffic_policies: self.traffic_manager.get_policy_count(),
        }
    }

    /// 清理过期的服务实例
    pub async fn cleanup_expired_services(&mut self) -> Result<usize, ServiceMeshError> {
        self.discovery.cleanup_expired_services().await
            .map_err(ServiceMeshError::DiscoveryError)
    }
}

/// 服务网格配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceMeshConfig {
    pub discovery: DiscoveryConfig,
    pub load_balancer: LoadBalancerConfig,
    pub traffic: TrafficConfig,
    pub circuit_breaker: CircuitBreakerConfig,
}

impl Default for ServiceMeshConfig {
    fn default() -> Self {
        Self {
            discovery: DiscoveryConfig::default(),
            load_balancer: LoadBalancerConfig::default(),
            traffic: TrafficConfig::default(),
            circuit_breaker: CircuitBreakerConfig::default(),
        }
    }
}

/// 服务网格统计信息
#[derive(Debug, Clone)]
pub struct ServiceMeshStats {
    pub registered_services: usize,
    pub active_circuit_breakers: usize,
    pub load_balancer_strategy: String,
    pub traffic_policies: usize,
}

/// 服务网格错误
#[derive(Error, Debug)]
pub enum ServiceMeshError {
    #[error("服务发现错误: {0}")]
    DiscoveryError(#[from] service_discovery::DiscoveryError),
    #[error("负载均衡错误: {0}")]
    LoadBalancerError(#[from] load_balancer::LoadBalancerError),
    #[error("熔断器错误: {0}")]
    CircuitBreakerError(#[from] CircuitBreakerError),
    #[error("流量管理错误: {0}")]
    TrafficError(#[from] traffic_management::TrafficError),
    #[error("没有可用的服务实例: {0}")]
    NoAvailableInstances(String),
    #[error("没有健康的服务实例: {0}")]
    NoHealthyInstances(String),
    #[error("熔断器开启: {0}")]
    CircuitBreakerOpen(String),
    #[error("服务调用超时")]
    ServiceTimeout,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

/// 服务网格结果类型别名
pub type ServiceMeshResult<T> = Result<T, ServiceMeshError>;
