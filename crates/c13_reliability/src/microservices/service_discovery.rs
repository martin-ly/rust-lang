//! # 服务发现（Service Discovery）
//!
//! 提供动态服务注册、健康检查和负载均衡功能。
//!
//! ## 核心功能
//!
//! - **服务注册**：动态注册/注销服务实例
//! - **健康检查**：主动和被动健康检查
//! - **服务发现**：根据服务名查找可用实例
//! - **负载均衡**：多种负载均衡策略
//! - **故障转移**：自动剔除不健康实例
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::microservices::service_discovery::*;
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建服务注册中心
//!     let registry = ServiceRegistry::new(DiscoveryConfig::default());
//!     
//!     // 注册服务实例
//!     let instance = ServiceInstance {
//!         service_name: "user-service".to_string(),
//!         instance_id: "user-service-1".to_string(),
//!         host: "127.0.0.1".to_string(),
//!         port: 8080,
//!         metadata: ServiceMetadata::default(),
//!         health_check_url: Some("http://127.0.0.1:8080/health".to_string()),
//!     };
//!     
//!     registry.register(instance).await?;
//!     
//!     // 发现服务
//!     let instances = registry.discover("user-service").await?;
//!     println!("Found {} instances", instances.len());
//!     
//!     Ok(())
//! }
//! ```

use crate::error_handling::prelude::*;
use dashmap::DashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    /// 服务名称
    pub service_name: String,
    /// 实例ID
    pub instance_id: String,
    /// 主机地址
    pub host: String,
    /// 端口
    pub port: u16,
    /// 元数据
    pub metadata: ServiceMetadata,
    /// 健康检查URL
    pub health_check_url: Option<String>,
}

/// 服务元数据
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ServiceMetadata {
    /// 服务版本
    pub version: String,
    /// 权重（用于负载均衡）
    pub weight: u32,
    /// 标签
    pub tags: Vec<String>,
    /// 自定义属性
    pub attributes: std::collections::HashMap<String, String>,
}

/// 健康状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HealthStatus {
    /// 健康
    Healthy,
    /// 不健康
    Unhealthy,
    /// 未知
    Unknown,
}

/// 健康检查结果
#[derive(Debug, Clone)]
pub struct HealthCheckResult {
    /// 实例ID
    pub instance_id: String,
    /// 健康状态
    pub status: HealthStatus,
    /// 检查时间
    pub checked_at: Instant,
    /// 响应时间（毫秒）
    pub response_time_ms: Option<u64>,
    /// 错误信息
    pub error: Option<String>,
}

/// 健康检查器
#[async_trait::async_trait]
pub trait HealthCheck: Send + Sync {
    /// 执行健康检查
    async fn check(&self, instance: &ServiceInstance) -> HealthCheckResult;
}

/// HTTP健康检查器
#[allow(dead_code)]
pub struct HttpHealthCheck {
    timeout: Duration,
    client: reqwest::Client,
}

impl HttpHealthCheck {
    #[allow(dead_code)]
    pub fn new(timeout: Duration) -> Self {
        Self {
            timeout,
            client: reqwest::Client::builder()
                .timeout(timeout)
                .build()
                .unwrap(),
        }
    }
}

#[async_trait::async_trait]
impl HealthCheck for HttpHealthCheck {
    #[allow(dead_code)]
    async fn check(&self, instance: &ServiceInstance) -> HealthCheckResult {
        let start = Instant::now();
        
        let status = if let Some(url) = &instance.health_check_url {
            match self.client.get(url).send().await {
                Ok(response) => {
                    if response.status().is_success() {
                        HealthStatus::Healthy
                    } else {
                        HealthStatus::Unhealthy
                    }
                }
                Err(_) => HealthStatus::Unhealthy,
            }
        } else {
            HealthStatus::Unknown
        };
        
        let response_time = start.elapsed().as_millis() as u64;
        
        HealthCheckResult {
            instance_id: instance.instance_id.clone(),
            status,
            checked_at: Instant::now(),
            response_time_ms: Some(response_time),
            error: None,
        }
    }
}

/// 负载均衡策略
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LoadBalancingStrategy {
    /// 轮询
    RoundRobin,
    /// 随机
    Random,
    /// 加权轮询
    WeightedRoundRobin,
    /// 最少连接
    LeastConnections,
    /// 一致性哈希
    ConsistentHash,
}

/// 负载均衡器
pub struct LoadBalancer {
    strategy: LoadBalancingStrategy,
    round_robin_counter: Arc<RwLock<usize>>,
}

impl LoadBalancer {
    #[allow(dead_code)]
    pub fn new(strategy: LoadBalancingStrategy) -> Self {
        Self {
            strategy,
            round_robin_counter: Arc::new(RwLock::new(0)),
        }
    }
    
    /// 选择一个实例
    pub async fn select(&self, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let mut counter = self.round_robin_counter.write().await;
                let index = *counter % instances.len();
                *counter = (*counter + 1) % instances.len();
                Some(instances[index].clone())
            }
            LoadBalancingStrategy::Random => {
                use rand::Rng;
                let mut rng = rand::rng();
                let index = rng.random_range(0..instances.len());
                Some(instances[index].clone())
            }
            LoadBalancingStrategy::WeightedRoundRobin => {
                // 简化版：根据权重选择
                let total_weight: u32 = instances.iter().map(|i| i.metadata.weight).sum();
                if total_weight == 0 {
                    return Some(instances[0].clone());
                }
                
                use rand::Rng;
                let mut rng = rand::rng();
                let mut random_weight = rng.random_range(0..total_weight);
                
                for instance in instances {
                    if random_weight < instance.metadata.weight {
                        return Some(instance.clone());
                    }
                    random_weight -= instance.metadata.weight;
                }
                
                Some(instances[0].clone())
            }
            LoadBalancingStrategy::LeastConnections => {
                // 简化版：返回第一个
                Some(instances[0].clone())
            }
            LoadBalancingStrategy::ConsistentHash => {
                // 简化版：使用round-robin
                let mut counter = self.round_robin_counter.write().await;
                let index = *counter % instances.len();
                *counter = (*counter + 1) % instances.len();
                Some(instances[index].clone())
            }
        }
    }
}

/// 服务发现配置
#[derive(Debug, Clone)]
pub struct DiscoveryConfig {
    /// 健康检查间隔
    pub health_check_interval: Duration,
    /// 健康检查超时
    pub health_check_timeout: Duration,
    /// 不健康阈值（连续失败次数）
    pub unhealthy_threshold: u32,
    /// 健康阈值（连续成功次数）
    pub healthy_threshold: u32,
    /// 负载均衡策略
    pub load_balancing_strategy: LoadBalancingStrategy,
}

impl Default for DiscoveryConfig {
    fn default() -> Self {
        Self {
            health_check_interval: Duration::from_secs(10),
            health_check_timeout: Duration::from_secs(5),
            unhealthy_threshold: 3,
            healthy_threshold: 2,
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        }
    }
}

/// 实例健康状态
#[derive(Debug)]
struct InstanceHealth {
    instance: ServiceInstance,
    status: HealthStatus,
    consecutive_failures: u32,
    consecutive_successes: u32,
    last_check: Option<Instant>,
}

/// 服务注册中心
pub struct ServiceRegistry {
    config: DiscoveryConfig,
    // service_name -> Vec<InstanceHealth>
    instances: Arc<DashMap<String, Vec<InstanceHealth>>>,
    health_checker: Arc<dyn HealthCheck>,
    load_balancer: Arc<LoadBalancer>,
    health_check_task: Arc<RwLock<Option<tokio::task::JoinHandle<()>>>>,
}

impl ServiceRegistry {
    /// 创建新的服务注册中心
    pub fn new(config: DiscoveryConfig) -> Self {
        let health_checker = Arc::new(HttpHealthCheck::new(config.health_check_timeout));
        let load_balancer = Arc::new(LoadBalancer::new(config.load_balancing_strategy));
        
        Self {
            config,
            instances: Arc::new(DashMap::new()),
            health_checker,
            load_balancer,
            health_check_task: Arc::new(RwLock::new(None)),
        }
    }
    
    /// 注册服务实例
    pub async fn register(&self, instance: ServiceInstance) -> Result<()> {
        let service_name = instance.service_name.clone();
        
        let health = InstanceHealth {
            instance: instance.clone(),
            status: HealthStatus::Healthy,
            consecutive_failures: 0,
            consecutive_successes: 0,
            last_check: None,
        };
        
        self.instances
            .entry(service_name.clone())
            .or_insert_with(Vec::new)
            .push(health);
        
        tracing::info!(
            service_name = %service_name,
            instance_id = %instance.instance_id,
            "Service instance registered"
        );
        
        // 启动健康检查（如果还没启动）
        self.start_health_check().await;
        
        Ok(())
    }
    
    /// 注销服务实例
    pub async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<()> {
        if let Some(mut instances) = self.instances.get_mut(service_name) {
            instances.retain(|h| h.instance.instance_id != instance_id);
            
            tracing::info!(
                service_name = %service_name,
                instance_id = %instance_id,
                "Service instance deregistered"
            );
        }
        
        Ok(())
    }
    
    /// 发现服务实例
    pub async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>> {
        let instances = self.instances
            .get(service_name)
            .map(|entry| {
                entry
                    .iter()
                    .filter(|h| h.status == HealthStatus::Healthy)
                    .map(|h| h.instance.clone())
                    .collect()
            })
            .unwrap_or_default();
        
        Ok(instances)
    }
    
    /// 使用负载均衡选择一个实例
    pub async fn select_instance(&self, service_name: &str) -> Result<Option<ServiceInstance>> {
        let instances = self.discover(service_name).await?;
        Ok(self.load_balancer.select(&instances).await)
    }
    
    /// 启动健康检查任务
    async fn start_health_check(&self) {
        let mut task = self.health_check_task.write().await;
        
        if task.is_none() {
            let instances = Arc::clone(&self.instances);
            let health_checker = Arc::clone(&self.health_checker);
            let interval = self.config.health_check_interval;
            let unhealthy_threshold = self.config.unhealthy_threshold;
            let healthy_threshold = self.config.healthy_threshold;
            
            let handle = tokio::spawn(async move {
                let mut interval_timer = tokio::time::interval(interval);
                
                loop {
                    interval_timer.tick().await;
                    
                    // 对所有实例执行健康检查
                    for mut entry in instances.iter_mut() {
                        let service_name = entry.key().clone();
                        let instances_health = entry.value_mut();
                        
                        for health in instances_health.iter_mut() {
                            let result = health_checker.check(&health.instance).await;
                            
                            match result.status {
                                HealthStatus::Healthy => {
                                    health.consecutive_successes += 1;
                                    health.consecutive_failures = 0;
                                    
                                    if health.consecutive_successes >= healthy_threshold {
                                        health.status = HealthStatus::Healthy;
                                    }
                                }
                                HealthStatus::Unhealthy => {
                                    health.consecutive_failures += 1;
                                    health.consecutive_successes = 0;
                                    
                                    if health.consecutive_failures >= unhealthy_threshold {
                                        health.status = HealthStatus::Unhealthy;
                                        tracing::warn!(
                                            service_name = %service_name,
                                            instance_id = %health.instance.instance_id,
                                            "Instance marked as unhealthy"
                                        );
                                    }
                                }
                                HealthStatus::Unknown => {
                                    health.status = HealthStatus::Unknown;
                                }
                            }
                            
                            health.last_check = Some(result.checked_at);
                        }
                    }
                }
            });
            
            *task = Some(handle);
        }
    }
    
    /// 获取所有服务名称
    pub fn list_services(&self) -> Vec<String> {
        self.instances.iter().map(|entry| entry.key().clone()).collect()
    }
    
    /// 获取服务统计信息
    pub fn get_service_stats(&self, service_name: &str) -> Option<ServiceStats> {
        self.instances.get(service_name).map(|entry| {
            let total = entry.len();
            let healthy = entry.iter().filter(|h| h.status == HealthStatus::Healthy).count();
            let unhealthy = entry.iter().filter(|h| h.status == HealthStatus::Unhealthy).count();
            
            ServiceStats {
                service_name: service_name.to_string(),
                total_instances: total,
                healthy_instances: healthy,
                unhealthy_instances: unhealthy,
            }
        })
    }
}

/// 服务统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceStats {
    pub service_name: String,
    pub total_instances: usize,
    pub healthy_instances: usize,
    pub unhealthy_instances: usize,
}

/// 服务发现接口
#[async_trait::async_trait]
pub trait ServiceDiscovery: Send + Sync {
    /// 注册服务
    async fn register(&self, instance: ServiceInstance) -> Result<()>;
    
    /// 注销服务
    async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<()>;
    
    /// 发现服务
    async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>>;
    
    /// 选择实例
    async fn select_instance(&self, service_name: &str) -> Result<Option<ServiceInstance>>;
}

#[async_trait::async_trait]
impl ServiceDiscovery for ServiceRegistry {
    async fn register(&self, instance: ServiceInstance) -> Result<()> {
        self.register(instance).await
    }
    
    async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<()> {
        self.deregister(service_name, instance_id).await
    }
    
    async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>> {
        self.discover(service_name).await
    }
    
    async fn select_instance(&self, service_name: &str) -> Result<Option<ServiceInstance>> {
        self.select_instance(service_name).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_service_registration() {
        let registry = ServiceRegistry::new(DiscoveryConfig::default());
        
        let instance = ServiceInstance {
            service_name: "test-service".to_string(),
            instance_id: "test-1".to_string(),
            host: "127.0.0.1".to_string(),
            port: 8080,
            metadata: ServiceMetadata::default(),
            health_check_url: None,
        };
        
        registry.register(instance).await.unwrap();
        
        let services = registry.list_services();
        assert!(services.contains(&"test-service".to_string()));
    }
    
    #[tokio::test]
    async fn test_service_discovery() {
        let registry = ServiceRegistry::new(DiscoveryConfig::default());
        
        let instance = ServiceInstance {
            service_name: "test-service".to_string(),
            instance_id: "test-1".to_string(),
            host: "127.0.0.1".to_string(),
            port: 8080,
            metadata: ServiceMetadata {
                version: "1.0.0".to_string(),
                weight: 1,
                tags: vec!["test".to_string()],
                attributes: std::collections::HashMap::new(),
            },
            health_check_url: None,
        };
        
        registry.register(instance.clone()).await.unwrap();
        
        let instances = registry.discover("test-service").await.unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].instance_id, "test-1");
    }
    
    #[tokio::test]
    async fn test_load_balancer_round_robin() {
        let lb = LoadBalancer::new(LoadBalancingStrategy::RoundRobin);
        
        let instances = vec![
            ServiceInstance {
                service_name: "test".to_string(),
                instance_id: "1".to_string(),
                host: "127.0.0.1".to_string(),
                port: 8081,
                metadata: ServiceMetadata::default(),
                health_check_url: None,
            },
            ServiceInstance {
                service_name: "test".to_string(),
                instance_id: "2".to_string(),
                host: "127.0.0.1".to_string(),
                port: 8082,
                metadata: ServiceMetadata::default(),
                health_check_url: None,
            },
        ];
        
        let selected1 = lb.select(&instances).await.unwrap();
        let selected2 = lb.select(&instances).await.unwrap();
        
        assert_ne!(selected1.instance_id, selected2.instance_id);
    }
}

