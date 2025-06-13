# 服务发现模式 (Service Discovery Pattern) - 形式化重构

## 1. 形式化定义 (Formal Definition)

### 1.1 服务发现模式五元组

设服务发现模式为五元组 $S = (R, L, H, U, T)$，其中：

- $R$ 是服务注册表集合
- $L$ 是负载均衡器集合
- $H$ 是健康检查器集合
- $U$ 是服务更新器集合
- $T$ 是时间戳集合

### 1.2 服务定义

**定义1.2.1 (服务)**
服务 $s \in S$ 定义为：
$$s = (id, endpoint, metadata, status, timestamp)$$
其中：

- $id \in I$ 是服务唯一标识符
- $endpoint \in E$ 是服务端点
- $metadata \in M$ 是服务元数据
- $status \in \{Healthy, Unhealthy, Unknown\}$ 是服务状态
- $timestamp \in T$ 是最后更新时间

**定义1.2.2 (服务注册表)**
服务注册表 $r \in R$ 定义为：
$$r = (services, index, consistency, version)$$
其中：

- $services \subseteq S$ 是服务集合
- $index: I \rightarrow S$ 是服务索引函数
- $consistency \in \{Strong, Eventual\}$ 是一致性级别
- $version \in \mathbb{N}$ 是版本号

### 1.3 负载均衡定义

**定义1.3.1 (负载均衡器)**
负载均衡器 $l \in L$ 定义为：
$$l = (strategy, weights, health, metrics)$$
其中：

- $strategy \in \{RoundRobin, Weighted, LeastConnections, ConsistentHash\}$ 是负载均衡策略
- $weights: S \rightarrow \mathbb{R}^+$ 是权重函数
- $health: S \rightarrow \{0, 1\}$ 是健康状态函数
- $metrics: S \rightarrow \mathbb{R}^+$ 是性能指标函数

## 2. 数学理论 (Mathematical Theory)

### 2.1 服务注册理论

**公理2.1.1 (服务注册唯一性)**
每个服务在注册表中只能有一个条目：
$$\forall s_1, s_2 \in S: s_1.id = s_2.id \implies s_1 = s_2$$

**公理2.1.2 (服务注册原子性)**
服务注册操作是原子的：
$$\text{atomic}(\text{register}(s)) \land \text{atomic}(\text{deregister}(s))$$

**公理2.1.3 (服务注册一致性)**
注册表状态最终一致：
$$\forall r \in R: \text{eventually\_consistent}(r)$$

### 2.2 负载均衡理论

**定义2.2.1 (负载均衡公平性)**
负载均衡是公平的，当且仅当：
$$\forall s_1, s_2 \in S: \frac{\text{load}(s_1)}{\text{capacity}(s_1)} = \frac{\text{load}(s_2)}{\text{capacity}(s_2)}$$

**定义2.2.2 (负载均衡效率)**
负载均衡效率定义为：
$$\text{efficiency}(l) = \frac{\text{min\_load}(l)}{\text{max\_load}(l)}$$

**公理2.2.1 (负载均衡最优性)**
最优负载均衡策略最小化最大负载：
$$\text{optimal}(l) = \arg\min_{l'} \max_{s \in S} \text{load}(s)$$

### 2.3 健康检查理论

**定义2.3.1 (健康检查)**
健康检查函数定义为：
$$\text{health\_check}: S \times T \rightarrow \{Healthy, Unhealthy, Unknown\}$$

**公理2.3.1 (健康检查及时性)**
健康检查结果及时更新：
$$\forall s \in S: |t - s.timestamp| \leq \text{check\_interval}$$

**公理2.3.2 (健康检查准确性)**
健康检查结果准确反映服务状态：
$$\text{health\_check}(s, t) = s.status$$

### 2.4 一致性理论

**定义2.4.1 (强一致性)**
强一致性定义为：
$$\forall r_1, r_2 \in R: \text{read}(r_1) = \text{read}(r_2)$$

**定义2.4.2 (最终一致性)**
最终一致性定义为：
$$\forall r_1, r_2 \in R: \text{eventually}(\text{read}(r_1) = \text{read}(r_2))$$

## 3. 核心定理 (Core Theorems)

### 3.1 服务发现正确性定理

**定理3.1.1 (服务发现正确性)**
服务发现模式保证服务正确发现。

**证明：**
根据公理2.1.1，每个服务在注册表中唯一存在。根据公理2.1.2，注册操作是原子的，确保数据一致性。

**定理3.1.2 (服务发现完整性)**
服务发现模式保证所有健康服务都能被发现。

**证明：**
根据公理2.3.1和公理2.3.2，健康检查及时且准确，确保只有健康服务被包含在发现结果中。

### 3.2 负载均衡定理

**定理3.2.1 (负载均衡最优性)**
最优负载均衡策略存在且唯一。

**证明：**
根据公理2.2.1，最优策略最小化最大负载。由于负载函数是连续的，最优解存在且唯一。

**定理3.2.2 (负载均衡收敛性)**
负载均衡算法最终收敛到最优状态。

**证明：**
负载均衡算法是单调递减的，且有下界，因此必然收敛。

### 3.3 一致性定理

**定理3.3.1 (强一致性保证)**
在强一致性模式下，所有读取操作返回相同结果。

**证明：**
根据定义2.4.1，强一致性确保所有注册表副本状态相同。

**定理3.3.2 (最终一致性保证)**
在最终一致性模式下，系统最终达到一致状态。

**证明：**
根据定义2.4.2，最终一致性确保在有限时间内达到一致。

### 3.4 复杂度定理

**定理3.4.1 (服务发现时间复杂度)**
服务发现的时间复杂度为 $O(\log n)$。

**证明：**
使用索引结构，服务发现可以在对数时间内完成。

**定理3.4.2 (负载均衡时间复杂度)**
负载均衡的时间复杂度为 $O(1)$。

**证明：**
负载均衡策略可以在常数时间内选择服务。

## 4. Rust实现 (Rust Implementation)

### 4.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use uuid::Uuid;

/// 服务状态枚举
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ServiceStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 服务定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Service {
    pub id: String,
    pub endpoint: String,
    pub metadata: HashMap<String, String>,
    pub status: ServiceStatus,
    pub timestamp: Instant,
    pub weight: f64,
    pub connections: usize,
}

/// 负载均衡策略枚举
#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    Weighted,
    LeastConnections,
    ConsistentHash,
}

/// 服务注册表
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Service>>>,
    version: Arc<Mutex<u64>>,
    consistency: ConsistencyLevel,
}

#[derive(Debug, Clone)]
pub enum ConsistencyLevel {
    Strong,
    Eventual,
}

impl ServiceRegistry {
    pub fn new(consistency: ConsistencyLevel) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            version: Arc::new(Mutex::new(0)),
            consistency,
        }
    }

    /// 注册服务
    pub async fn register(&self, service: Service) -> Result<(), Box<dyn std::error::Error>> {
        let mut services = self.services.write().await;
        services.insert(service.id.clone(), service);
        
        let mut version = self.version.lock().unwrap();
        *version += 1;
        
        Ok(())
    }

    /// 注销服务
    pub async fn deregister(&self, service_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut services = self.services.write().await;
        services.remove(service_id);
        
        let mut version = self.version.lock().unwrap();
        *version += 1;
        
        Ok(())
    }

    /// 发现服务
    pub async fn discover(&self, service_id: &str) -> Option<Service> {
        let services = self.services.read().await;
        services.get(service_id).cloned()
    }

    /// 获取所有健康服务
    pub async fn get_healthy_services(&self) -> Vec<Service> {
        let services = self.services.read().await;
        services
            .values()
            .filter(|s| s.status == ServiceStatus::Healthy)
            .cloned()
            .collect()
    }

    /// 获取版本号
    pub fn get_version(&self) -> u64 {
        *self.version.lock().unwrap()
    }
}

/// 负载均衡器
pub struct LoadBalancer {
    strategy: LoadBalancingStrategy,
    current_index: Arc<Mutex<usize>>,
}

impl LoadBalancer {
    pub fn new(strategy: LoadBalancingStrategy) -> Self {
        Self {
            strategy,
            current_index: Arc::new(Mutex::new(0)),
        }
    }

    /// 选择服务
    pub async fn select_service(&self, services: &[Service]) -> Option<Service> {
        if services.is_empty() {
            return None;
        }

        match self.strategy {
            LoadBalancingStrategy::RoundRobin => self.round_robin(services).await,
            LoadBalancingStrategy::Weighted => self.weighted(services).await,
            LoadBalancingStrategy::LeastConnections => self.least_connections(services).await,
            LoadBalancingStrategy::ConsistentHash => self.consistent_hash(services).await,
        }
    }

    /// 轮询策略
    async fn round_robin(&self, services: &[Service]) -> Option<Service> {
        let mut index = self.current_index.lock().unwrap();
        let service = services[*index % services.len()].clone();
        *index += 1;
        Some(service)
    }

    /// 权重策略
    async fn weighted(&self, services: &[Service]) -> Option<Service> {
        let total_weight: f64 = services.iter().map(|s| s.weight).sum();
        let mut random = rand::random::<f64>() * total_weight;
        
        for service in services {
            random -= service.weight;
            if random <= 0.0 {
                return Some(service.clone());
            }
        }
        
        services.last().cloned()
    }

    /// 最少连接策略
    async fn least_connections(&self, services: &[Service]) -> Option<Service> {
        services
            .iter()
            .min_by_key(|s| s.connections)
            .cloned()
    }

    /// 一致性哈希策略
    async fn consistent_hash(&self, services: &[Service]) -> Option<Service> {
        // 简化的一致性哈希实现
        let hash = services.len();
        Some(services[hash % services.len()].clone())
    }
}

/// 健康检查器
pub struct HealthChecker {
    check_interval: Duration,
    timeout: Duration,
}

impl HealthChecker {
    pub fn new(check_interval: Duration, timeout: Duration) -> Self {
        Self {
            check_interval,
            timeout,
        }
    }

    /// 检查服务健康状态
    pub async fn check_health(&self, service: &Service) -> ServiceStatus {
        // 简化的健康检查实现
        // 实际实现中应该发送HTTP请求或其他协议请求
        if service.timestamp.elapsed() < self.check_interval {
            ServiceStatus::Healthy
        } else {
            ServiceStatus::Unknown
        }
    }

    /// 批量健康检查
    pub async fn check_all_services(&self, registry: &ServiceRegistry) {
        let healthy_services = registry.get_healthy_services().await;
        
        for service in healthy_services {
            let status = self.check_health(&service).await;
            if status != service.status {
                // 更新服务状态
                let mut updated_service = service.clone();
                updated_service.status = status;
                updated_service.timestamp = Instant::now();
                
                if let Err(e) = registry.register(updated_service).await {
                    eprintln!("Failed to update service status: {}", e);
                }
            }
        }
    }
}
```

### 4.2 泛型实现

```rust
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 泛型服务注册表
pub struct GenericServiceRegistry<K, V> {
    services: Arc<RwLock<HashMap<K, V>>>,
    version: Arc<Mutex<u64>>,
}

impl<K, V> GenericServiceRegistry<K, V>
where
    K: Clone + Eq + Hash + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            version: Arc::new(Mutex::new(0)),
        }
    }

    /// 注册服务
    pub async fn register(&self, key: K, value: V) -> Result<(), Box<dyn std::error::Error>> {
        let mut services = self.services.write().await;
        services.insert(key, value);
        
        let mut version = self.version.lock().unwrap();
        *version += 1;
        
        Ok(())
    }

    /// 注销服务
    pub async fn deregister(&self, key: &K) -> Result<(), Box<dyn std::error::Error>> {
        let mut services = self.services.write().await;
        services.remove(key);
        
        let mut version = self.version.lock().unwrap();
        *version += 1;
        
        Ok(())
    }

    /// 发现服务
    pub async fn discover(&self, key: &K) -> Option<V> {
        let services = self.services.read().await;
        services.get(key).cloned()
    }

    /// 获取所有服务
    pub async fn get_all_services(&self) -> Vec<V> {
        let services = self.services.read().await;
        services.values().cloned().collect()
    }
}

/// 泛型负载均衡器
pub struct GenericLoadBalancer<T, F> {
    strategy: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, F> GenericLoadBalancer<T, F>
where
    T: Clone + Send + Sync + 'static,
    F: Fn(&[T]) -> Option<T> + Send + Sync + 'static,
{
    pub fn new(strategy: F) -> Self {
        Self {
            strategy,
            _phantom: std::marker::PhantomData,
        }
    }

    /// 选择服务
    pub async fn select_service(&self, services: &[T]) -> Option<T> {
        (self.strategy)(services)
    }
}
```

### 4.3 异步实现

```rust
use tokio::sync::mpsc;
use tokio::time::{interval, timeout};
use std::collections::HashMap;

/// 异步服务发现客户端
pub struct AsyncServiceDiscovery {
    registry: Arc<ServiceRegistry>,
    load_balancer: Arc<LoadBalancer>,
    health_checker: Arc<HealthChecker>,
    update_tx: mpsc::Sender<ServiceUpdate>,
}

#[derive(Debug, Clone)]
pub enum ServiceUpdate {
    Register(Service),
    Deregister(String),
    UpdateStatus(String, ServiceStatus),
}

impl AsyncServiceDiscovery {
    pub fn new(
        registry: Arc<ServiceRegistry>,
        load_balancer: Arc<LoadBalancer>,
        health_checker: Arc<HealthChecker>,
    ) -> Self {
        let (update_tx, _) = mpsc::channel(100);
        Self {
            registry,
            load_balancer,
            health_checker,
            update_tx,
        }
    }

    /// 异步服务发现
    pub async fn discover_service(&self, service_id: &str) -> Option<Service> {
        self.registry.discover(service_id).await
    }

    /// 异步负载均衡选择
    pub async fn select_service(&self) -> Option<Service> {
        let services = self.registry.get_healthy_services().await;
        self.load_balancer.select_service(&services).await
    }

    /// 启动健康检查循环
    pub async fn start_health_check_loop(&self) {
        let registry = self.registry.clone();
        let health_checker = self.health_checker.clone();
        
        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(30));
            
            loop {
                interval.tick().await;
                health_checker.check_all_services(&registry).await;
            }
        });
    }

    /// 注册服务
    pub async fn register_service(&self, service: Service) -> Result<(), Box<dyn std::error::Error>> {
        self.registry.register(service).await
    }

    /// 注销服务
    pub async fn deregister_service(&self, service_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.registry.deregister(service_id).await
    }
}

/// 分布式服务注册表
pub struct DistributedServiceRegistry {
    local_registry: Arc<ServiceRegistry>,
    peers: Arc<RwLock<Vec<String>>>,
    replication_factor: usize,
}

impl DistributedServiceRegistry {
    pub fn new(replication_factor: usize) -> Self {
        Self {
            local_registry: Arc::new(ServiceRegistry::new(ConsistencyLevel::Eventual)),
            peers: Arc::new(RwLock::new(Vec::new())),
            replication_factor,
        }
    }

    /// 添加对等节点
    pub async fn add_peer(&self, peer: String) {
        let mut peers = self.peers.write().await;
        peers.push(peer);
    }

    /// 在指定数据中心注册服务
    pub async fn register_service_in_datacenter(
        &self,
        datacenter: &str,
        service: Service,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let datacenters = self.peers.read().await;
        if let Some(peer) = datacenters.iter().find(|&&x| x == datacenter) {
            // 这里应该实现实际的网络复制逻辑
            println!("Replicating service {} to peer {}", service.id, peer);
            self.local_registry.register(service).await
        } else {
            Err(anyhow::anyhow!("Datacenter not found").into())
        }
    }

    /// 跨数据中心服务发现
    pub async fn discover_service_global(&self, service_id: &str) -> Vec<Service> {
        let datacenters = self.peers.read().await;
        let mut all_services = Vec::new();
        
        for peer in datacenters.iter() {
            if let Some(service) = self.local_registry.discover(service_id).await {
                let mut service_with_dc = service.clone();
                service_with_dc.metadata.insert("datacenter".to_string(), peer.clone());
                all_services.push(service_with_dc);
            }
        }
        
        all_services
    }

    /// 全局负载均衡
    pub async fn select_service_global(&self, service_id: &str) -> Option<Service> {
        let services = self.discover_service_global(service_id).await;
        self.load_balancer.select_service(&services).await
    }
}
```

### 4.4 一致性哈希实现

```rust
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::collections::BTreeMap;

/// 一致性哈希环
pub struct ConsistentHashRing {
    ring: BTreeMap<u64, String>,
    virtual_nodes: usize,
}

impl ConsistentHashRing {
    pub fn new(virtual_nodes: usize) -> Self {
        Self {
            ring: BTreeMap::new(),
            virtual_nodes,
        }
    }

    /// 添加节点
    pub fn add_node(&mut self, node: String) {
        for i in 0..self.virtual_nodes {
            let virtual_node = format!("{}#{}", node, i);
            let hash = self.hash(&virtual_node);
            self.ring.insert(hash, node.clone());
        }
    }

    /// 移除节点
    pub fn remove_node(&mut self, node: &str) {
        let mut to_remove = Vec::new();
        
        for (hash, ring_node) in &self.ring {
            if ring_node == node {
                to_remove.push(*hash);
            }
        }
        
        for hash in to_remove {
            self.ring.remove(&hash);
        }
    }

    /// 获取负责节点
    pub fn get_node(&self, key: &str) -> Option<&String> {
        if self.ring.is_empty() {
            return None;
        }
        
        let hash = self.hash(key);
        
        // 查找大于等于hash的第一个节点
        let mut iter = self.ring.range(hash..);
        if let Some((_, node)) = iter.next() {
            return Some(node);
        }
        
        // 如果没找到，返回第一个节点（环的起点）
        self.ring.values().next()
    }

    /// 哈希函数
    fn hash(&self, key: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    /// 获取所有节点
    pub fn get_all_nodes(&self) -> Vec<&String> {
        self.ring.values().collect()
    }
}

/// 一致性哈希负载均衡器
pub struct ConsistentHashLoadBalancer {
    ring: Arc<Mutex<ConsistentHashRing>>,
}

impl ConsistentHashLoadBalancer {
    pub fn new(virtual_nodes: usize) -> Self {
        Self {
            ring: Arc::new(Mutex::new(ConsistentHashRing::new(virtual_nodes))),
        }
    }

    /// 添加服务节点
    pub async fn add_service(&self, service_id: String) {
        let mut ring = self.ring.lock().unwrap();
        ring.add_node(service_id);
    }

    /// 移除服务节点
    pub async fn remove_service(&self, service_id: &str) {
        let mut ring = self.ring.lock().unwrap();
        ring.remove_node(service_id);
    }

    /// 选择服务
    pub async fn select_service(&self, key: &str) -> Option<String> {
        let ring = self.ring.lock().unwrap();
        ring.get_node(key).cloned()
    }
}
```

## 5. 应用场景 (Application Scenarios)

### 5.1 微服务架构

```rust
use std::collections::HashMap;

/// 微服务注册中心
pub struct MicroserviceRegistry {
    registry: Arc<ServiceRegistry>,
    load_balancer: Arc<LoadBalancer>,
    health_checker: Arc<HealthChecker>,
}

impl MicroserviceRegistry {
    pub fn new() -> Self {
        let registry = Arc::new(ServiceRegistry::new(ConsistencyLevel::Eventual));
        let load_balancer = Arc::new(LoadBalancer::new(LoadBalancingStrategy::RoundRobin));
        let health_checker = Arc::new(HealthChecker::new(
            Duration::from_secs(30),
            Duration::from_secs(5),
        ));
        
        Self {
            registry,
            load_balancer,
            health_checker,
        }
    }

    /// 注册微服务
    pub async fn register_microservice(
        &self,
        name: String,
        endpoint: String,
        metadata: HashMap<String, String>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let service = Service {
            id: name,
            endpoint,
            metadata,
            status: ServiceStatus::Healthy,
            timestamp: Instant::now(),
            weight: 1.0,
            connections: 0,
        };
        
        self.registry.register(service).await
    }

    /// 发现微服务
    pub async fn discover_microservice(&self, name: &str) -> Option<Service> {
        self.registry.discover(name).await
    }

    /// 负载均衡调用
    pub async fn call_service(&self, service_name: &str) -> Option<String> {
        let services = self.registry.get_healthy_services().await;
        let filtered_services: Vec<Service> = services
            .into_iter()
            .filter(|s| s.metadata.get("name") == Some(&service_name.to_string()))
            .collect();
        
        if let Some(service) = self.load_balancer.select_service(&filtered_services).await {
            Some(service.endpoint)
        } else {
            None
        }
    }
}
```

### 5.2 容器编排

```rust
/// Kubernetes风格的服务发现
pub struct KubernetesServiceDiscovery {
    registry: Arc<ServiceRegistry>,
    namespace: String,
    labels: HashMap<String, String>,
}

impl KubernetesServiceDiscovery {
    pub fn new(namespace: String) -> Self {
        Self {
            registry: Arc::new(ServiceRegistry::new(ConsistencyLevel::Strong)),
            namespace,
            labels: HashMap::new(),
        }
    }

    /// 添加标签选择器
    pub fn add_label(&mut self, key: String, value: String) {
        self.labels.insert(key, value);
    }

    /// 注册Pod
    pub async fn register_pod(
        &self,
        pod_name: String,
        endpoint: String,
        labels: HashMap<String, String>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut metadata = HashMap::new();
        metadata.insert("namespace".to_string(), self.namespace.clone());
        metadata.insert("pod_name".to_string(), pod_name);
        
        for (key, value) in labels {
            metadata.insert(key, value);
        }
        
        let service = Service {
            id: format!("{}/{}", self.namespace, pod_name),
            endpoint,
            metadata,
            status: ServiceStatus::Healthy,
            timestamp: Instant::now(),
            weight: 1.0,
            connections: 0,
        };
        
        self.registry.register(service).await
    }

    /// 通过标签发现服务
    pub async fn discover_by_labels(&self, labels: &HashMap<String, String>) -> Vec<Service> {
        let all_services = self.registry.get_healthy_services().await;
        
        all_services
            .into_iter()
            .filter(|service| {
                for (key, value) in labels {
                    if service.metadata.get(key) != Some(value) {
                        return false;
                    }
                }
                true
            })
            .collect()
    }
}
```

### 5.3 云原生应用

```rust
/// 云原生服务网格
pub struct ServiceMesh {
    registry: Arc<DistributedServiceRegistry>,
    load_balancer: Arc<ConsistentHashLoadBalancer>,
    circuit_breaker: Arc<CircuitBreaker>,
}

/// 熔断器
pub struct CircuitBreaker {
    failure_threshold: usize,
    recovery_timeout: Duration,
    state: Arc<Mutex<CircuitBreakerState>>,
}

#[derive(Debug, Clone)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: usize, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            state: Arc::new(Mutex::new(CircuitBreakerState::Closed)),
        }
    }

    /// 执行操作
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E> + Send + 'static,
        T: Send + 'static,
        E: Send + 'static,
    {
        let state = self.state.lock().unwrap();
        
        match *state {
            CircuitBreakerState::Open => {
                return Err(anyhow::anyhow!("Circuit breaker is open").into());
            }
            CircuitBreakerState::HalfOpen | CircuitBreakerState::Closed => {
                // 执行操作
                let result = operation();
                
                // 根据结果更新状态
                match result {
                    Ok(_) => {
                        let mut state = self.state.lock().unwrap();
                        *state = CircuitBreakerState::Closed;
                    }
                    Err(_) => {
                        let mut state = self.state.lock().unwrap();
                        *state = CircuitBreakerState::Open;
                    }
                }
                
                result
            }
        }
    }
}

impl ServiceMesh {
    pub fn new() -> Self {
        let registry = Arc::new(DistributedServiceRegistry::new(3));
        let load_balancer = Arc::new(ConsistentHashLoadBalancer::new(150));
        let circuit_breaker = Arc::new(CircuitBreaker::new(
            5,
            Duration::from_secs(60),
        ));
        
        Self {
            registry,
            load_balancer,
            circuit_breaker,
        }
    }

    /// 服务间调用
    pub async fn call_service(&self, service_name: &str, request: &str) -> Result<String, Box<dyn std::error::Error>> {
        // 服务发现
        let service = self.registry.local_registry.discover(service_name).await
            .ok_or_else(|| anyhow::anyhow!("Service not found"))?;
        
        // 负载均衡
        let endpoint = self.load_balancer.select_service(request).await
            .unwrap_or_else(|| service.endpoint.clone());
        
        // 熔断器保护
        self.circuit_breaker.execute(|| async {
            // 实际的HTTP调用
            Ok(format!("Response from {}", endpoint))
        }).await
    }
}
```

## 6. 变体模式 (Variant Patterns)

### 6.1 权重负载均衡

```rust
/// 权重负载均衡器
pub struct WeightedLoadBalancer {
    services: Arc<RwLock<Vec<Service>>>,
}

impl WeightedLoadBalancer {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 添加服务
    pub async fn add_service(&self, service: Service) {
        let mut services = self.services.write().await;
        services.push(service);
    }

    /// 选择服务（权重轮询）
    pub async fn select_service(&self) -> Option<Service> {
        let services = self.services.read().await;
        if services.is_empty() {
            return None;
        }
        
        // 计算总权重
        let total_weight: f64 = services.iter().map(|s| s.weight).sum();
        
        // 生成随机数
        let mut random = rand::random::<f64>() * total_weight;
        
        // 选择服务
        for service in services.iter() {
            random -= service.weight;
            if random <= 0.0 {
                return Some(service.clone());
            }
        }
        
        services.last().cloned()
    }
}
```

### 6.2 健康检查变体

```rust
/// 高级健康检查器
pub struct AdvancedHealthChecker {
    check_interval: Duration,
    timeout: Duration,
    success_threshold: usize,
    failure_threshold: usize,
    health_history: Arc<RwLock<HashMap<String, Vec<bool>>>>,
}

impl AdvancedHealthChecker {
    pub fn new(
        check_interval: Duration,
        timeout: Duration,
        success_threshold: usize,
        failure_threshold: usize,
    ) -> Self {
        Self {
            check_interval,
            timeout,
            success_threshold,
            failure_threshold,
            health_history: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 检查服务健康状态
    pub async fn check_health(&self, service: &Service) -> ServiceStatus {
        let health_result = self.perform_health_check(service).await;
        
        // 更新健康历史
        let mut history = self.health_history.write().await;
        let service_history = history.entry(service.id.clone()).or_insert_with(Vec::new);
        service_history.push(health_result);
        
        // 保持历史记录在合理范围内
        if service_history.len() > 10 {
            service_history.remove(0);
        }
        
        // 根据历史记录判断状态
        if service_history.len() >= self.failure_threshold {
            let recent_failures = service_history
                .iter()
                .rev()
                .take(self.failure_threshold)
                .filter(|&&x| !x)
                .count();
            
            if recent_failures >= self.failure_threshold {
                return ServiceStatus::Unhealthy;
            }
        }
        
        if service_history.len() >= self.success_threshold {
            let recent_successes = service_history
                .iter()
                .rev()
                .take(self.success_threshold)
                .filter(|&&x| x)
                .count();
            
            if recent_successes >= self.success_threshold {
                return ServiceStatus::Healthy;
            }
        }
        
        ServiceStatus::Unknown
    }

    /// 执行实际的健康检查
    async fn perform_health_check(&self, service: &Service) -> bool {
        // 这里应该实现实际的健康检查逻辑
        // 例如：HTTP GET请求、TCP连接测试等
        service.timestamp.elapsed() < self.check_interval
    }
}
```

### 6.3 多数据中心支持

```rust
/// 多数据中心服务发现
pub struct MultiDatacenterServiceDiscovery {
    datacenters: Arc<RwLock<HashMap<String, Arc<ServiceRegistry>>>>,
    global_load_balancer: Arc<LoadBalancer>,
}

impl MultiDatacenterServiceDiscovery {
    pub fn new() -> Self {
        Self {
            datacenters: Arc::new(RwLock::new(HashMap::new())),
            global_load_balancer: Arc::new(LoadBalancer::new(LoadBalancingStrategy::Weighted)),
        }
    }

    /// 添加数据中心
    pub async fn add_datacenter(&self, name: String) {
        let mut datacenters = self.datacenters.write().await;
        datacenters.insert(name, Arc::new(ServiceRegistry::new(ConsistencyLevel::Eventual)));
    }

    /// 在指定数据中心注册服务
    pub async fn register_service_in_datacenter(
        &self,
        datacenter: &str,
        service: Service,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let datacenters = self.datacenters.read().await;
        if let Some(registry) = datacenters.get(datacenter) {
            registry.register(service).await
        } else {
            Err(anyhow::anyhow!("Datacenter not found").into())
        }
    }

    /// 跨数据中心服务发现
    pub async fn discover_service_global(&self, service_id: &str) -> Vec<Service> {
        let datacenters = self.datacenters.read().await;
        let mut all_services = Vec::new();
        
        for (datacenter_name, registry) in datacenters.iter() {
            if let Some(service) = registry.discover(service_id).await {
                let mut service_with_dc = service.clone();
                service_with_dc.metadata.insert("datacenter".to_string(), datacenter_name.clone());
                all_services.push(service_with_dc);
            }
        }
        
        all_services
    }

    /// 全局负载均衡
    pub async fn select_service_global(&self, service_id: &str) -> Option<Service> {
        let services = self.discover_service_global(service_id).await;
        self.global_load_balancer.select_service(&services).await
    }
}
```

## 7. 性能分析 (Performance Analysis)

### 7.1 理论性能

**定理7.1.1 (服务发现性能)**
服务发现的性能为：
$$\text{DiscoveryPerformance} = O(\log n)$$
其中 $n$ 是服务数量。

**定理7.1.2 (负载均衡性能)**
负载均衡的性能为：
$$\text{LoadBalancingPerformance} = O(1)$$

### 7.2 实际性能测试

```rust
use std::time::Instant;

/// 性能测试
async fn performance_test() {
    let registry = ServiceRegistry::new(ConsistencyLevel::Eventual);
    let load_balancer = LoadBalancer::new(LoadBalancingStrategy::RoundRobin);
    
    let start = Instant::now();
    
    // 注册大量服务
    for i in 0..1000 {
        let service = Service {
            id: format!("service_{}", i),
            endpoint: format!("http://service_{}:8080", i),
            metadata: HashMap::new(),
            status: ServiceStatus::Healthy,
            timestamp: Instant::now(),
            weight: 1.0,
            connections: 0,
        };
        
        registry.register(service).await.unwrap();
    }
    
    let registration_time = start.elapsed();
    println!("Registration time: {:?}", registration_time);
    
    // 服务发现性能测试
    let start = Instant::now();
    for i in 0..10000 {
        let _service = registry.discover(&format!("service_{}", i % 1000)).await;
    }
    
    let discovery_time = start.elapsed();
    println!("Discovery time: {:?}", discovery_time);
    println!("Average discovery time: {:?}", discovery_time / 10000);
    
    // 负载均衡性能测试
    let start = Instant::now();
    for _ in 0..10000 {
        let services = registry.get_healthy_services().await;
        let _selected = load_balancer.select_service(&services).await;
    }
    
    let load_balancing_time = start.elapsed();
    println!("Load balancing time: {:?}", load_balancing_time);
    println!("Average load balancing time: {:?}", load_balancing_time / 10000);
}

#[tokio::main]
async fn main() {
    performance_test().await;
}
```

## 8. 总结 (Summary)

服务发现模式通过以下特性提供了强大的分布式服务管理能力：

1. **服务注册**: 支持服务的动态注册和注销
2. **服务发现**: 提供高效的服务查找机制
3. **负载均衡**: 支持多种负载均衡策略
4. **健康检查**: 确保服务可用性
5. **一致性保证**: 支持强一致性和最终一致性
6. **可扩展性**: 支持水平扩展和分布式部署

该模式是现代分布式系统的核心组件，广泛应用于微服务架构、容器编排和云原生应用中。
