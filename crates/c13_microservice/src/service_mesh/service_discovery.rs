//! 服务发现模块
//!
//! 提供服务注册、发现和健康检查功能

use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 服务发现器
#[derive(Debug)]
pub struct ServiceDiscovery {
    registry: ServiceRegistry,
    _config: DiscoveryConfig,
}

impl ServiceDiscovery {
    /// 创建新的服务发现器
    pub fn new(config: DiscoveryConfig) -> Self {
        Self {
            registry: ServiceRegistry::new(config.registry.clone()),
            _config: config,
        }
    }

    /// 注册服务实例
    pub async fn register_service(&mut self, service: ServiceInstance) -> Result<(), DiscoveryError> {
        self.registry.register_service(service).await
    }

    /// 注销服务实例
    pub async fn unregister_service(&mut self, service_id: &str) -> Result<(), DiscoveryError> {
        self.registry.unregister_service(service_id).await
    }

    /// 发现服务实例
    pub async fn discover_services(&mut self, service_name: &str) -> Result<Vec<ServiceInstance>, DiscoveryError> {
        self.registry.discover_services(service_name).await
    }

    /// 获取服务健康状态
    pub async fn get_service_health(&mut self, service_name: &str) -> Result<Vec<ServiceHealth>, DiscoveryError> {
        self.registry.get_service_health(service_name).await
    }

    /// 获取已注册服务数量
    pub fn get_registered_count(&self) -> usize {
        self.registry.get_registered_count()
    }

    /// 清理过期的服务实例
    pub async fn cleanup_expired_services(&mut self) -> Result<usize, DiscoveryError> {
        self.registry.cleanup_expired_services().await
    }

    /// 更新服务实例
    pub async fn update_service(&mut self, service: ServiceInstance) -> Result<(), DiscoveryError> {
        self.registry.update_service(service).await
    }

    /// 获取所有服务名称
    pub async fn get_all_services(&self) -> Result<Vec<String>, DiscoveryError> {
        self.registry.get_all_services().await
    }
}

/// 服务注册中心
#[derive(Debug)]
pub struct ServiceRegistry {
    services: HashMap<String, Vec<ServiceInstance>>,
    health_checks: HashMap<String, HealthCheck>,
    config: RegistryConfig,
}

impl ServiceRegistry {
    /// 创建新的服务注册中心
    pub fn new(config: RegistryConfig) -> Self {
        Self {
            services: HashMap::new(),
            health_checks: HashMap::new(),
            config,
        }
    }

    /// 注册服务实例
    pub async fn register_service(&mut self, service: ServiceInstance) -> Result<(), DiscoveryError> {
        let service_name = service.name.clone();
        let services = self.services.entry(service_name.clone()).or_insert_with(Vec::new);
        
        // 检查是否已存在相同ID的实例
        if let Some(existing_index) = services.iter().position(|s| s.id == service.id) {
            let service_id = service.id.clone();
            services[existing_index] = service;
            tracing::info!("更新服务实例: {}", service_id);
        } else {
            let service_id = service.id.clone();
            services.push(service);
            tracing::info!("注册新服务实例: {}", service_id);
        }

        Ok(())
    }

    /// 注销服务实例
    pub async fn unregister_service(&mut self, service_id: &str) -> Result<(), DiscoveryError> {
        let mut removed = false;
        
        for (_, services) in self.services.iter_mut() {
            if let Some(index) = services.iter().position(|s| s.id == service_id) {
                services.remove(index);
                removed = true;
                tracing::info!("注销服务实例: {}", service_id);
                break;
            }
        }

        if !removed {
            return Err(DiscoveryError::ServiceNotFound(service_id.to_string()));
        }

        Ok(())
    }

    /// 发现服务实例
    pub async fn discover_services(&self, service_name: &str) -> Result<Vec<ServiceInstance>, DiscoveryError> {
        let services = self.services.get(service_name)
            .cloned()
            .unwrap_or_default();

        if services.is_empty() {
            return Err(DiscoveryError::ServiceNotFound(service_name.to_string()));
        }

        Ok(services)
    }

    /// 获取服务健康状态
    pub async fn get_service_health(&self, service_name: &str) -> Result<Vec<ServiceHealth>, DiscoveryError> {
        let instances = self.discover_services(service_name).await?;
        let mut health_status = Vec::new();

        for instance in instances {
            let service_id = instance.id.clone();
            let health = if let Some(health_check) = self.health_checks.get(&service_id) {
                health_check.check_health(&instance).await
            } else {
                ServiceHealth {
                    service_id: service_id.clone(),
                    healthy: true,
                    last_check: SystemTime::now(),
                    response_time: Duration::from_millis(0),
                    error_message: None,
                }
            };
            health_status.push(health);
        }

        Ok(health_status)
    }

    /// 获取已注册服务数量
    pub fn get_registered_count(&self) -> usize {
        self.services.values().map(|services| services.len()).sum()
    }

    /// 清理过期的服务实例
    pub async fn cleanup_expired_services(&mut self) -> Result<usize, DiscoveryError> {
        let now = SystemTime::now();
        let mut removed_count = 0;

        for (_, services) in self.services.iter_mut() {
            let initial_count = services.len();
            services.retain(|service| {
                if let Ok(age) = now.duration_since(service.registered_at) {
                    age < self.config.service_ttl
                } else {
                    true
                }
            });
            removed_count += initial_count - services.len();
        }

        // 清理空的服务条目
        self.services.retain(|_, services| !services.is_empty());

        Ok(removed_count)
    }

    /// 更新服务实例
    pub async fn update_service(&mut self, service: ServiceInstance) -> Result<(), DiscoveryError> {
        self.register_service(service).await
    }

    /// 获取所有服务名称
    pub async fn get_all_services(&self) -> Result<Vec<String>, DiscoveryError> {
        Ok(self.services.keys().cloned().collect())
    }

    /// 添加健康检查
    pub fn add_health_check(&mut self, service_id: String, health_check: HealthCheck) {
        self.health_checks.insert(service_id, health_check);
    }
}

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub host: String,
    pub port: u16,
    pub protocol: String,
    pub version: String,
    pub tags: Vec<String>,
    pub metadata: HashMap<String, String>,
    pub weight: u32,
    pub registered_at: SystemTime,
    pub last_heartbeat: SystemTime,
}

impl ServiceInstance {
    /// 创建新的服务实例
    pub fn new(
        id: String,
        name: String,
        host: String,
        port: u16,
    ) -> Self {
        let now = SystemTime::now();
        Self {
            id,
            name,
            host,
            port,
            protocol: "http".to_string(),
            version: "1.0.0".to_string(),
            tags: Vec::new(),
            metadata: HashMap::new(),
            weight: 100,
            registered_at: now,
            last_heartbeat: now,
        }
    }

    /// 获取服务地址
    pub fn get_address(&self) -> String {
        format!("{}://{}:{}", self.protocol, self.host, self.port)
    }

    /// 获取服务URL
    pub fn get_url(&self) -> String {
        format!("{}://{}:{}", self.protocol, self.host, self.port)
    }

    /// 添加标签
    pub fn add_tag(&mut self, tag: String) {
        if !self.tags.contains(&tag) {
            self.tags.push(tag);
        }
    }

    /// 添加元数据
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// 更新心跳时间
    pub fn update_heartbeat(&mut self) {
        self.last_heartbeat = SystemTime::now();
    }

    /// 检查服务是否健康
    pub fn is_healthy(&self, max_heartbeat_age: Duration) -> bool {
        if let Ok(age) = SystemTime::now().duration_since(self.last_heartbeat) {
            age < max_heartbeat_age
        } else {
            false
        }
    }
}

/// 服务健康状态
#[derive(Debug, Clone)]
pub struct ServiceHealth {
    pub service_id: String,
    pub healthy: bool,
    pub last_check: SystemTime,
    pub response_time: Duration,
    pub error_message: Option<String>,
}

/// 健康检查
#[derive(Debug)]
pub struct HealthCheck {
    pub check_interval: Duration,
    pub timeout: Duration,
    pub max_failures: u32,
    pub check_path: String,
    pub check_method: String,
}

impl HealthCheck {
    /// 创建新的健康检查
    pub fn new(check_path: String) -> Self {
        Self {
            check_interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            max_failures: 3,
            check_path,
            check_method: "GET".to_string(),
        }
    }

    /// 检查服务健康状态
    pub async fn check_health(&self, instance: &ServiceInstance) -> ServiceHealth {
        let start_time = SystemTime::now();
        
        // 这里简化处理，实际应用中应该发送HTTP请求
        let healthy = true; // 模拟健康检查结果
        let response_time = start_time.elapsed().unwrap_or_default();
        
        ServiceHealth {
            service_id: instance.id.clone(),
            healthy,
            last_check: start_time,
            response_time,
            error_message: if healthy { None } else { Some("Health check failed".to_string()) },
        }
    }
}

/// 服务发现配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiscoveryConfig {
    pub registry: RegistryConfig,
    pub refresh_interval: Duration,
    pub cache_ttl: Duration,
}

impl Default for DiscoveryConfig {
    fn default() -> Self {
        Self {
            registry: RegistryConfig::default(),
            refresh_interval: Duration::from_secs(30),
            cache_ttl: Duration::from_secs(60),
        }
    }
}

/// 注册中心配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    pub service_ttl: Duration,
    pub heartbeat_interval: Duration,
    pub max_instances_per_service: usize,
}

impl Default for RegistryConfig {
    fn default() -> Self {
        Self {
            service_ttl: Duration::from_secs(300), // 5分钟
            heartbeat_interval: Duration::from_secs(30),
            max_instances_per_service: 100,
        }
    }
}

/// 服务发现错误
#[derive(Error, Debug)]
pub enum DiscoveryError {
    #[error("服务未找到: {0}")]
    ServiceNotFound(String),
    #[error("服务注册失败: {0}")]
    RegistrationFailed(String),
    #[error("健康检查失败: {0}")]
    HealthCheckFailed(String),
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("网络错误: {0}")]
    NetworkError(String),
    #[error("超时错误")]
    TimeoutError,
    #[error("序列化错误: {0}")]
    SerializationError(String),
}

/// 服务发现结果类型别名
pub type DiscoveryResult<T> = Result<T, DiscoveryError>;
