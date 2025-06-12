# 4.1.4 服务发现与注册 (Service Discovery and Registration)

## 目录

1. [4.1.4.1 服务发现模型](#4141-服务发现模型)
2. [4.1.4.2 注册中心](#4142-注册中心)
3. [4.1.4.3 负载均衡](#4143-负载均衡)
4. [4.1.4.4 健康检查](#4144-健康检查)
5. [4.1.4.5 故障转移](#4145-故障转移)

## 4.1.4.1 服务发现模型

### 定义 4.1.4.1 (服务发现)

服务发现是动态定位和连接微服务的机制：
$$ServiceDiscovery = \{(S, R, L) | S \in Services, R \in Registry, L \in LoadBalancer\}$$

### 定义 4.1.4.2 (服务注册)

服务注册是将服务信息存储到注册中心的过程：
$$ServiceRegistration = \{Register(S, M) | S \in Services, M \in Metadata\}$$

### 定义 4.1.4.3 (服务发现模式)

服务发现有两种主要模式：

- **客户端发现**: $ClientDiscovery = \{Client \rightarrow Registry \rightarrow Service\}$
- **服务端发现**: $ServerDiscovery = \{Client \rightarrow LoadBalancer \rightarrow Service\}$

## 4.1.4.2 注册中心

### 定义 4.1.4.4 (注册中心)

注册中心是存储服务元数据的中央存储：
$$Registry = \{(S_i, M_i, T_i) | S_i \in Services, M_i \in Metadata, T_i \in Timestamp\}$$

**Rust实现**：

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    id: String,
    service_name: String,
    host: String,
    port: u16,
    metadata: HashMap<String, String>,
    health_status: HealthStatus,
    last_heartbeat: DateTime<Utc>,
    version: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    ttl: std::time::Duration,
}

impl ServiceRegistry {
    pub fn new(ttl: std::time::Duration) -> Self {
        ServiceRegistry {
            services: Arc::new(RwLock::new(HashMap::new())),
            ttl,
        }
    }
    
    pub async fn register(&self, instance: ServiceInstance) -> Result<(), RegistryError> {
        let mut services = self.services.write().unwrap();
        let service_instances = services
            .entry(instance.service_name.clone())
            .or_insert_with(Vec::new);
            
        // 检查是否已存在相同实例
        if let Some(existing_index) = service_instances
            .iter()
            .position(|i| i.id == instance.id) {
            service_instances[existing_index] = instance;
        } else {
            service_instances.push(instance);
        }
        
        Ok(())
    }
    
    pub async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<(), RegistryError> {
        let mut services = self.services.write().unwrap();
        if let Some(service_instances) = services.get_mut(service_name) {
            service_instances.retain(|instance| instance.id != instance_id);
        }
        Ok(())
    }
    
    pub async fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, RegistryError> {
        let services = self.services.read().unwrap();
        let instances = services
            .get(service_name)
            .cloned()
            .unwrap_or_default();
            
        // 过滤掉不健康的实例
        let healthy_instances: Vec<ServiceInstance> = instances
            .into_iter()
            .filter(|instance| {
                instance.health_status == HealthStatus::Healthy &&
                Utc::now().signed_duration_since(instance.last_heartbeat).num_seconds() < self.ttl.as_secs() as i64
            })
            .collect();
            
        Ok(healthy_instances)
    }
    
    pub async fn update_heartbeat(&self, service_name: &str, instance_id: &str) -> Result<(), RegistryError> {
        let mut services = self.services.write().unwrap();
        if let Some(service_instances) = services.get_mut(service_name) {
            if let Some(instance) = service_instances
                .iter_mut()
                .find(|i| i.id == instance_id) {
                instance.last_heartbeat = Utc::now();
            }
        }
        Ok(())
    }
    
    pub async fn cleanup_expired(&self) {
        let mut services = self.services.write().unwrap();
        for service_instances in services.values_mut() {
            service_instances.retain(|instance| {
                Utc::now().signed_duration_since(instance.last_heartbeat).num_seconds() < self.ttl.as_secs() as i64
            });
        }
    }
}

#[derive(Debug)]
pub enum RegistryError {
    ServiceNotFound,
    InstanceNotFound,
    RegistrationFailed,
    DeregistrationFailed,
}

// 服务注册客户端
pub struct ServiceRegistryClient {
    registry_url: String,
    client: reqwest::Client,
}

impl ServiceRegistryClient {
    pub fn new(registry_url: String) -> Self {
        ServiceRegistryClient {
            registry_url,
            client: reqwest::Client::new(),
        }
    }
    
    pub async fn register(&self, instance: &ServiceInstance) -> Result<(), RegistryError> {
        let response = self.client
            .post(&format!("{}/register", self.registry_url))
            .json(instance)
            .send()
            .await
            .map_err(|_| RegistryError::RegistrationFailed)?;
            
        if response.status().is_success() {
            Ok(())
        } else {
            Err(RegistryError::RegistrationFailed)
        }
    }
    
    pub async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<(), RegistryError> {
        let response = self.client
            .delete(&format!("{}/services/{}/instances/{}", self.registry_url, service_name, instance_id))
            .send()
            .await
            .map_err(|_| RegistryError::DeregistrationFailed)?;
            
        if response.status().is_success() {
            Ok(())
        } else {
            Err(RegistryError::DeregistrationFailed)
        }
    }
    
    pub async fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, RegistryError> {
        let response = self.client
            .get(&format!("{}/services/{}", self.registry_url, service_name))
            .send()
            .await
            .map_err(|_| RegistryError::ServiceNotFound)?;
            
        if response.status().is_success() {
            let instances: Vec<ServiceInstance> = response.json().await
                .map_err(|_| RegistryError::ServiceNotFound)?;
            Ok(instances)
        } else {
            Err(RegistryError::ServiceNotFound)
        }
    }
    
    pub async fn heartbeat(&self, service_name: &str, instance_id: &str) -> Result<(), RegistryError> {
        let response = self.client
            .put(&format!("{}/services/{}/instances/{}/heartbeat", self.registry_url, service_name, instance_id))
            .send()
            .await
            .map_err(|_| RegistryError::RegistrationFailed)?;
            
        if response.status().is_success() {
            Ok(())
        } else {
            Err(RegistryError::RegistrationFailed)
        }
    }
}
```

## 4.1.4.3 负载均衡

### 定义 4.1.4.5 (负载均衡)

负载均衡是将请求分发到多个服务实例的机制：
$$LoadBalancer = \{Distribute(Request, Instances) \rightarrow Instance\}$$

### 定义 4.1.4.6 (负载均衡算法)

常见的负载均衡算法：

- **轮询**: $RoundRobin(i) = i \bmod n$
- **加权轮询**: $WeightedRoundRobin(i, w) = \arg\max_j \frac{w_j}{\sum_{k=1}^n w_k}$
- **最少连接**: $LeastConnections = \arg\min_i Connections(i)$
- **一致性哈希**: $ConsistentHash(key) = \arg\min_i Hash(key) \bmod Hash(instance_i)$

**Rust实现**：

```rust
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

pub trait LoadBalancer {
    type Instance;
    
    fn select_instance(&self, instances: &[Self::Instance]) -> Option<&Self::Instance>;
}

pub struct RoundRobinLoadBalancer {
    counter: AtomicUsize,
}

impl RoundRobinLoadBalancer {
    pub fn new() -> Self {
        RoundRobinLoadBalancer {
            counter: AtomicUsize::new(0),
        }
    }
}

impl LoadBalancer for RoundRobinLoadBalancer {
    type Instance = ServiceInstance;
    
    fn select_instance(&self, instances: &[Self::Instance]) -> Option<&Self::Instance> {
        if instances.is_empty() {
            return None;
        }
        
        let index = self.counter.fetch_add(1, Ordering::Relaxed) % instances.len();
        instances.get(index)
    }
}

pub struct WeightedRoundRobinLoadBalancer {
    counter: AtomicUsize,
    weights: Vec<u32>,
}

impl WeightedRoundRobinLoadBalancer {
    pub fn new(weights: Vec<u32>) -> Self {
        WeightedRoundRobinLoadBalancer {
            counter: AtomicUsize::new(0),
            weights,
        }
    }
    
    fn get_weighted_index(&self, instances: &[ServiceInstance]) -> usize {
        let total_weight: u32 = self.weights.iter().sum();
        let current = self.counter.fetch_add(1, Ordering::Relaxed) as u32;
        let normalized = current % total_weight;
        
        let mut cumulative_weight = 0;
        for (i, &weight) in self.weights.iter().enumerate() {
            cumulative_weight += weight;
            if normalized < cumulative_weight {
                return i;
            }
        }
        
        0 // fallback
    }
}

impl LoadBalancer for WeightedRoundRobinLoadBalancer {
    type Instance = ServiceInstance;
    
    fn select_instance(&self, instances: &[Self::Instance]) -> Option<&Self::Instance> {
        if instances.is_empty() {
            return None;
        }
        
        let index = self.get_weighted_index(instances);
        instances.get(index)
    }
}

pub struct LeastConnectionsLoadBalancer {
    connection_counts: Arc<RwLock<HashMap<String, usize>>>,
}

impl LeastConnectionsLoadBalancer {
    pub fn new() -> Self {
        LeastConnectionsLoadBalancer {
            connection_counts: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn increment_connections(&self, instance_id: &str) {
        let mut counts = self.connection_counts.write().unwrap();
        *counts.entry(instance_id.to_string()).or_insert(0) += 1;
    }
    
    pub fn decrement_connections(&self, instance_id: &str) {
        let mut counts = self.connection_counts.write().unwrap();
        if let Some(count) = counts.get_mut(instance_id) {
            if *count > 0 {
                *count -= 1;
            }
        }
    }
}

impl LoadBalancer for LeastConnectionsLoadBalancer {
    type Instance = ServiceInstance;
    
    fn select_instance(&self, instances: &[Self::Instance]) -> Option<&Self::Instance> {
        if instances.is_empty() {
            return None;
        }
        
        let counts = self.connection_counts.read().unwrap();
        let selected = instances
            .iter()
            .min_by_key(|instance| counts.get(&instance.id).unwrap_or(&0))?;
            
        Some(selected)
    }
}

pub struct ConsistentHashLoadBalancer {
    ring: Vec<(u64, String)>,
    virtual_nodes: usize,
}

impl ConsistentHashLoadBalancer {
    pub fn new(virtual_nodes: usize) -> Self {
        ConsistentHashLoadBalancer {
            ring: Vec::new(),
            virtual_nodes,
        }
    }
    
    pub fn add_instances(&mut self, instances: &[ServiceInstance]) {
        self.ring.clear();
        
        for instance in instances {
            for i in 0..self.virtual_nodes {
                let virtual_key = format!("{}:{}", instance.id, i);
                let hash = self.hash(&virtual_key);
                self.ring.push((hash, instance.id.clone()));
            }
        }
        
        self.ring.sort_by_key(|(hash, _)| *hash);
    }
    
    pub fn hash(&self, key: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

impl LoadBalancer for ConsistentHashLoadBalancer {
    type Instance = ServiceInstance;
    
    fn select_instance(&self, instances: &[Self::Instance]) -> Option<&Self::Instance> {
        if instances.is_empty() || self.ring.is_empty() {
            return None;
        }
        
        // 简化的实现，实际应该基于请求的key进行哈希
        let request_hash = self.hash("request_key");
        
        // 找到第一个大于等于请求哈希的节点
        let index = self.ring
            .binary_search_by(|(hash, _)| hash.cmp(&request_hash))
            .unwrap_or_else(|i| i % self.ring.len());
            
        let instance_id = &self.ring[index].1;
        instances.iter().find(|instance| instance.id == *instance_id)
    }
}
```

## 4.1.4.4 健康检查

### 定义 4.1.4.7 (健康检查)

健康检查是验证服务实例可用性的机制：
$$HealthCheck = \{Check(Instance) \rightarrow \{Healthy, Unhealthy, Unknown\}\}$$

**Rust实现**：

```rust
use std::time::Duration;
use tokio::time::timeout;

pub trait HealthChecker {
    type Instance;
    
    async fn check_health(&self, instance: &Self::Instance) -> HealthStatus;
}

pub struct HttpHealthChecker {
    timeout: Duration,
}

impl HttpHealthChecker {
    pub fn new(timeout: Duration) -> Self {
        HttpHealthChecker { timeout }
    }
}

impl HealthChecker for HttpHealthChecker {
    type Instance = ServiceInstance;
    
    async fn check_health(&self, instance: &Self::Instance) -> HealthStatus {
        let health_url = format!("http://{}:{}/health", instance.host, instance.port);
        
        match timeout(self.timeout, reqwest::get(&health_url)).await {
            Ok(Ok(response)) => {
                if response.status().is_success() {
                    HealthStatus::Healthy
                } else {
                    HealthStatus::Unhealthy
                }
            }
            _ => HealthStatus::Unhealthy,
        }
    }
}

pub struct TcpHealthChecker {
    timeout: Duration,
}

impl TcpHealthChecker {
    pub fn new(timeout: Duration) -> Self {
        TcpHealthChecker { timeout }
    }
}

impl HealthChecker for TcpHealthChecker {
    type Instance = ServiceInstance;
    
    async fn check_health(&self, instance: &Self::Instance) -> HealthStatus {
        use tokio::net::TcpStream;
        
        let address = format!("{}:{}", instance.host, instance.port);
        
        match timeout(self.timeout, TcpStream::connect(&address)).await {
            Ok(Ok(_)) => HealthStatus::Healthy,
            _ => HealthStatus::Unhealthy,
        }
    }
}

pub struct HealthCheckScheduler {
    registry: Arc<ServiceRegistry>,
    health_checker: Box<dyn HealthChecker<Instance = ServiceInstance>>,
    interval: Duration,
}

impl HealthCheckScheduler {
    pub fn new(
        registry: Arc<ServiceRegistry>,
        health_checker: Box<dyn HealthChecker<Instance = ServiceInstance>>,
        interval: Duration,
    ) -> Self {
        HealthCheckScheduler {
            registry,
            health_checker,
            interval,
        }
    }
    
    pub async fn start(&self) {
        let registry = self.registry.clone();
        let health_checker = self.health_checker.clone();
        let interval = self.interval;
        
        tokio::spawn(async move {
            let mut interval_timer = tokio::time::interval(interval);
            
            loop {
                interval_timer.tick().await;
                
                // 获取所有服务实例
                let services = registry.services.read().unwrap();
                for (service_name, instances) in services.iter() {
                    for instance in instances {
                        let health_status = health_checker.check_health(instance).await;
                        
                        // 更新健康状态
                        if health_status != instance.health_status {
                            // 这里需要更新注册中心中的健康状态
                            // 简化实现，实际应该调用registry的更新方法
                        }
                    }
                }
            }
        });
    }
}
```

## 4.1.4.5 故障转移

### 定义 4.1.4.8 (故障转移)

故障转移是在服务实例失败时自动切换到备用实例的机制：
$$Failover = \{Detect(Instance) \land \neg Healthy(Instance) \rightarrow Switch(BackupInstance)\}$$

**Rust实现**：

```rust
pub struct FailoverManager {
    registry: Arc<ServiceRegistry>,
    load_balancer: Box<dyn LoadBalancer<Instance = ServiceInstance>>,
    health_checker: Box<dyn HealthChecker<Instance = ServiceInstance>>,
    retry_policy: RetryPolicy,
}

#[derive(Debug, Clone)]
pub struct RetryPolicy {
    max_retries: usize,
    retry_delay: Duration,
    backoff_multiplier: f64,
}

impl RetryPolicy {
    pub fn new(max_retries: usize, retry_delay: Duration, backoff_multiplier: f64) -> Self {
        RetryPolicy {
            max_retries,
            retry_delay,
            backoff_multiplier,
        }
    }
}

impl FailoverManager {
    pub fn new(
        registry: Arc<ServiceRegistry>,
        load_balancer: Box<dyn LoadBalancer<Instance = ServiceInstance>>,
        health_checker: Box<dyn HealthChecker<Instance = ServiceInstance>>,
        retry_policy: RetryPolicy,
    ) -> Self {
        FailoverManager {
            registry,
            load_balancer,
            health_checker,
            retry_policy,
        }
    }
    
    pub async fn execute_with_failover<F, T, E>(
        &self,
        service_name: &str,
        operation: F,
    ) -> Result<T, E>
    where
        F: Fn(&ServiceInstance) -> Result<T, E>,
        E: std::fmt::Debug,
    {
        let mut retry_count = 0;
        let mut current_delay = self.retry_policy.retry_delay;
        
        loop {
            // 获取可用的服务实例
            let instances = self.registry.get_instances(service_name).await
                .map_err(|_| {
                    // 这里需要适当的错误类型转换
                    std::io::Error::new(std::io::ErrorKind::Other, "Service not found")
                })?;
                
            if instances.is_empty() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "No available instances",
                ));
            }
            
            // 选择实例
            let selected_instance = self.load_balancer.select_instance(&instances)
                .ok_or_else(|| {
                    std::io::Error::new(std::io::ErrorKind::Other, "No instance selected")
                })?;
            
            // 检查实例健康状态
            let health_status = self.health_checker.check_health(selected_instance).await;
            
            match health_status {
                HealthStatus::Healthy => {
                    // 执行操作
                    match operation(selected_instance) {
                        Ok(result) => return Ok(result),
                        Err(error) => {
                            // 操作失败，检查是否需要重试
                            if retry_count >= self.retry_policy.max_retries {
                                return Err(error);
                            }
                            
                            retry_count += 1;
                            tokio::time::sleep(current_delay).await;
                            current_delay = Duration::from_secs_f64(
                                current_delay.as_secs_f64() * self.retry_policy.backoff_multiplier
                            );
                            continue;
                        }
                    }
                }
                HealthStatus::Unhealthy | HealthStatus::Unknown => {
                    // 实例不健康，尝试下一个实例
                    if retry_count >= self.retry_policy.max_retries {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::Other,
                            "All instances unhealthy",
                        ));
                    }
                    
                    retry_count += 1;
                    tokio::time::sleep(current_delay).await;
                    current_delay = Duration::from_secs_f64(
                        current_delay.as_secs_f64() * self.retry_policy.backoff_multiplier
                    );
                }
            }
        }
    }
}

// 服务发现客户端
pub struct ServiceDiscoveryClient {
    registry_client: ServiceRegistryClient,
    load_balancer: Box<dyn LoadBalancer<Instance = ServiceInstance>>,
    failover_manager: FailoverManager,
}

impl ServiceDiscoveryClient {
    pub fn new(
        registry_url: String,
        load_balancer: Box<dyn LoadBalancer<Instance = ServiceInstance>>,
        health_checker: Box<dyn HealthChecker<Instance = ServiceInstance>>,
    ) -> Self {
        let registry_client = ServiceRegistryClient::new(registry_url);
        let registry = Arc::new(ServiceRegistry::new(Duration::from_secs(30)));
        let retry_policy = RetryPolicy::new(3, Duration::from_millis(100), 2.0);
        let failover_manager = FailoverManager::new(
            registry,
            load_balancer.clone(),
            health_checker,
            retry_policy,
        );
        
        ServiceDiscoveryClient {
            registry_client,
            load_balancer,
            failover_manager,
        }
    }
    
    pub async fn call_service<T>(
        &self,
        service_name: &str,
        operation: impl Fn(&ServiceInstance) -> Result<T, std::io::Error>,
    ) -> Result<T, std::io::Error> {
        self.failover_manager.execute_with_failover(service_name, operation).await
    }
}
```

## 持续上下文管理

### 进度跟踪

- [x] 服务发现模型定义
- [x] 注册中心实现
- [x] 负载均衡算法
- [x] 健康检查机制
- [x] 故障转移策略

### 下一步计划

1. 完成容错与弹性设计
2. 开始事件驱动架构
3. 建立响应式架构

### 中断恢复点

当前状态：服务发现与注册内容已完成，准备开始容错与弹性设计的内容编写。
