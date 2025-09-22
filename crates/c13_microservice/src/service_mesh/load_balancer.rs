//! 负载均衡模块
//!
//! 提供多种负载均衡策略

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::service_discovery::ServiceInstance;

/// 负载均衡器
#[derive(Debug)]
pub struct LoadBalancer {
    strategy: LoadBalancingStrategy,
    _config: LoadBalancerConfig,
    round_robin_index: Arc<AtomicUsize>,
    connection_counts: Arc<std::sync::RwLock<HashMap<String, usize>>>,
}

impl LoadBalancer {
    /// 创建新的负载均衡器
    pub fn new(config: LoadBalancerConfig) -> Self {
        Self {
            strategy: config.strategy.clone(),
            _config: config,
            round_robin_index: Arc::new(AtomicUsize::new(0)),
            connection_counts: Arc::new(std::sync::RwLock::new(HashMap::new())),
        }
    }

    /// 选择服务实例
    pub fn select_instance(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        if instances.is_empty() {
            return Err(LoadBalancerError::NoAvailableInstances);
        }

        if instances.len() == 1 {
            return Ok(instances[0].clone());
        }

        match &self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                self.select_round_robin(instances)
            }
            LoadBalancingStrategy::WeightedRoundRobin => {
                self.select_weighted_round_robin(instances)
            }
            LoadBalancingStrategy::LeastConnections => {
                self.select_least_connections(instances)
            }
            LoadBalancingStrategy::Random => {
                self.select_random(instances)
            }
            LoadBalancingStrategy::WeightedRandom => {
                self.select_weighted_random(instances)
            }
        }
    }

    /// 轮询选择
    fn select_round_robin(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        let index = self.round_robin_index.fetch_add(1, Ordering::Relaxed) % instances.len();
        Ok(instances[index].clone())
    }

    /// 加权轮询选择
    fn select_weighted_round_robin(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        let total_weight: u32 = instances.iter().map(|i| i.weight).sum();
        if total_weight == 0 {
            return self.select_round_robin(instances);
        }

        let mut current_weight = 0;
        let mut selected_instance = None;
        let mut max_weight = 0;

        for instance in instances {
            current_weight += instance.weight;
            if current_weight > max_weight {
                max_weight = current_weight;
                selected_instance = Some(instance);
            }
        }

        selected_instance
            .map(|instance| instance.clone())
            .ok_or_else(|| LoadBalancerError::SelectionFailed)
    }

    /// 最少连接数选择
    fn select_least_connections(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        let connection_counts = self.connection_counts.read().unwrap();
        
        let mut min_connections = usize::MAX;
        let mut selected_instance = None;

        for instance in instances {
            let connections = connection_counts.get(&instance.id).copied().unwrap_or(0);
            if connections < min_connections {
                min_connections = connections;
                selected_instance = Some(instance);
            }
        }

        selected_instance
            .map(|instance| instance.clone())
            .ok_or_else(|| LoadBalancerError::SelectionFailed)
    }

    /// 随机选择
    fn select_random(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
            .hash(&mut hasher);
        
        let index = (hasher.finish() as usize) % instances.len();
        Ok(instances[index].clone())
    }

    /// 加权随机选择
    fn select_weighted_random(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, LoadBalancerError> {
        let total_weight: u32 = instances.iter().map(|i| i.weight).sum();
        if total_weight == 0 {
            return self.select_random(instances);
        }

        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
            .hash(&mut hasher);
        
        let random_weight = (hasher.finish() as u32) % total_weight;
        let mut current_weight = 0;

        for instance in instances {
            current_weight += instance.weight;
            if current_weight >= random_weight {
                return Ok(instance.clone());
            }
        }

        // 回退到第一个实例
        Ok(instances[0].clone())
    }

    /// 增加连接数
    pub fn increment_connections(&self, service_id: &str) {
        let mut connection_counts = self.connection_counts.write().unwrap();
        *connection_counts.entry(service_id.to_string()).or_insert(0) += 1;
    }

    /// 减少连接数
    pub fn decrement_connections(&self, service_id: &str) {
        let mut connection_counts = self.connection_counts.write().unwrap();
        if let Some(count) = connection_counts.get_mut(service_id) {
            if *count > 0 {
                *count -= 1;
            }
        }
    }

    /// 获取负载均衡策略
    pub fn get_strategy(&self) -> String {
        match &self.strategy {
            LoadBalancingStrategy::RoundRobin => "round_robin".to_string(),
            LoadBalancingStrategy::WeightedRoundRobin => "weighted_round_robin".to_string(),
            LoadBalancingStrategy::LeastConnections => "least_connections".to_string(),
            LoadBalancingStrategy::Random => "random".to_string(),
            LoadBalancingStrategy::WeightedRandom => "weighted_random".to_string(),
        }
    }

    /// 获取连接统计信息
    pub fn get_connection_stats(&self) -> HashMap<String, usize> {
        self.connection_counts.read().unwrap().clone()
    }
}

/// 负载均衡策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
    WeightedRandom,
}

impl Default for LoadBalancingStrategy {
    fn default() -> Self {
        Self::RoundRobin
    }
}

/// 负载均衡配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadBalancerConfig {
    pub strategy: LoadBalancingStrategy,
    pub health_check_interval: std::time::Duration,
    pub max_retries: u32,
    pub retry_delay: std::time::Duration,
}

impl Default for LoadBalancerConfig {
    fn default() -> Self {
        Self {
            strategy: LoadBalancingStrategy::default(),
            health_check_interval: std::time::Duration::from_secs(30),
            max_retries: 3,
            retry_delay: std::time::Duration::from_millis(100),
        }
    }
}

/// 负载均衡错误
#[derive(Error, Debug)]
pub enum LoadBalancerError {
    #[error("没有可用的实例")]
    NoAvailableInstances,
    #[error("选择实例失败")]
    SelectionFailed,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("健康检查失败: {0}")]
    HealthCheckFailed(String),
}

/// 负载均衡结果类型别名
pub type LoadBalancerResult<T> = Result<T, LoadBalancerError>;
