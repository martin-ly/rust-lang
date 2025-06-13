# 服务发现模式 (Service Discovery Pattern)

## 1. 概述

### 1.1 模式定义

服务发现模式是一种分布式系统设计模式，用于在动态环境中自动发现和注册服务实例，实现服务间的动态连接和负载均衡。

### 1.2 核心概念

- **服务注册 (Service Registration)**: 服务实例向注册中心注册自己的信息
- **服务发现 (Service Discovery)**: 客户端从注册中心获取服务实例信息
- **健康检查 (Health Check)**: 定期检查服务实例的健康状态
- **负载均衡 (Load Balancing)**: 在多个服务实例间分配请求

## 2. 形式化定义

### 2.1 服务发现模式五元组

**定义2.1 (服务发现模式五元组)**
设 $SD = (S, R, C, H, L)$ 为服务发现模式，其中：

- $S = \{s_1, s_2, ..., s_n\}$ 是服务实例集合
- $R = \{r_1, r_2, ..., r_m\}$ 是注册中心集合
- $C = \{c_1, c_2, ..., c_k\}$ 是客户端集合
- $H = \{h_1, h_2, ..., h_p\}$ 是健康检查函数集合
- $L = \{l_1, l_2, ..., l_q\}$ 是负载均衡策略集合

### 2.2 服务实例定义

**定义2.2 (服务实例)**
服务实例 $s_i = (id_i, addr_i, port_i, meta_i, status_i)$，其中：

- $id_i$ 是服务实例唯一标识符
- $addr_i$ 是服务实例地址
- $port_i$ 是服务实例端口
- $meta_i$ 是服务实例元数据
- $status_i \in \{healthy, unhealthy, unknown\}$ 是服务实例状态

### 2.3 注册中心定义

**定义2.4 (注册中心)**
注册中心 $r_j = (registry_j, heartbeat_j, ttl_j, consistency_j)$，其中：

- $registry_j \subseteq S$ 是注册的服务实例集合
- $heartbeat_j: S \rightarrow \mathbb{R}^+$ 是心跳间隔函数
- $ttl_j: S \rightarrow \mathbb{R}^+$ 是生存时间函数
- $consistency_j \in \{strong, eventual\}$ 是一致性级别

## 3. 数学理论

### 3.1 服务发现理论

**定义3.1 (服务发现函数)**
服务发现函数 $discover: C \times R \times S \rightarrow 2^S$ 定义为：

$$discover(c, r, service\_type) = \{s \in r.registry | s.meta.type = service\_type \land s.status = healthy\}$$

**定理3.1.1 (服务发现完整性)**
对于任意客户端 $c$ 和注册中心 $r$，如果存在健康服务实例，则服务发现函数返回非空集合。

**证明**：
设 $S_{healthy} = \{s \in r.registry | s.status = healthy\}$，则：
1. 如果 $S_{healthy} \neq \emptyset$，则 $discover(c, r, service\_type) \subseteq S_{healthy}$
2. 由于 $discover$ 函数过滤条件为 $s.status = healthy$，所以返回的集合只包含健康实例
3. 因此，如果存在健康服务实例，函数返回非空集合。

### 3.2 服务注册理论

**定义3.2 (服务注册函数)**
服务注册函数 $register: S \times R \rightarrow \mathbb{B}$ 定义为：

$$register(s, r) = \begin{cases}
true & \text{if } s \notin r.registry \land s.status = healthy \\
false & \text{otherwise}
\end{cases}$$

**定理3.2.1 (服务注册唯一性)**
服务注册函数保证同一服务实例不会重复注册。

**证明**：
1. 函数条件包含 $s \notin r.registry$
2. 如果服务实例已在注册中心，函数返回 $false$
3. 因此，同一服务实例不会重复注册。

### 3.3 健康检查理论

**定义3.3 (健康检查函数)**
健康检查函数 $health\_check: S \times H \rightarrow \mathbb{B}$ 定义为：

$$health\_check(s, h) = \begin{cases}
true & \text{if } h(s) \text{ returns success within timeout} \\
false & \text{otherwise}
\end{cases}$$

**定理3.3.1 (健康检查一致性)**
健康检查函数在给定时间内对同一服务实例的结果是一致的。

**证明**：
1. 健康检查函数是确定性的
2. 在给定超时时间内，函数结果只依赖于服务实例的实际状态
3. 因此，对同一服务实例的多次检查结果一致。

### 3.4 负载均衡理论

**定义3.4 (负载均衡函数)**
负载均衡函数 $load\_balance: 2^S \times L \rightarrow S$ 定义为：

$$load\_balance(instances, strategy) = strategy.select(instances)$$

**定理3.4.1 (负载均衡公平性)**
负载均衡函数在多个健康服务实例间公平分配请求。

**证明**：
1. 负载均衡策略 $strategy$ 实现公平分配算法
2. 函数只从健康实例集合中选择
3. 因此，请求在健康实例间公平分配。

## 4. 核心定理

### 4.1 服务发现正确性定理

**定理4.1 (服务发现正确性)**
服务发现模式 $SD$ 是正确的，当且仅当：

1. **服务注册完整性**: $\forall s \in S, \exists r \in R: s \in r.registry$
2. **服务发现可达性**: $\forall c \in C, \forall r \in R, \forall service\_type: discover(c, r, service\_type) \neq \emptyset \Rightarrow \exists s \in S: s.meta.type = service\_type \land s.status = healthy$
3. **健康检查准确性**: $\forall s \in S, \forall h \in H: health\_check(s, h) = true \Rightarrow s.status = healthy$
4. **负载均衡有效性**: $\forall instances \subseteq S, \forall l \in L: load\_balance(instances, l) \in instances$

**证明**：
1. **服务注册完整性**: 确保所有服务实例都被注册到某个注册中心
2. **服务发现可达性**: 确保客户端能够发现所有可用的服务实例
3. **健康检查准确性**: 确保健康检查结果准确反映服务实例状态
4. **负载均衡有效性**: 确保负载均衡选择的服务实例在可用实例集合中

### 4.2 服务发现一致性定理

**定理4.2 (服务发现一致性)**
在最终一致性模型下，服务发现模式满足：

$$\forall c_1, c_2 \in C, \forall r \in R, \forall service\_type: \lim_{t \to \infty} discover(c_1, r, service\_type) = discover(c_2, r, service\_type)$$

**证明**：
1. 在最终一致性模型下，所有客户端最终看到相同的注册中心状态
2. 服务发现函数是确定性的
3. 因此，所有客户端最终获得相同的服务实例列表

### 4.3 服务发现性能定理

**定理4.3 (服务发现性能)**
服务发现模式的性能复杂度为：

- **注册复杂度**: $O(\log|S|)$ 时间复杂度
- **发现复杂度**: $O(|S|)$ 时间复杂度
- **健康检查复杂度**: $O(1)$ 单次检查时间复杂度
- **负载均衡复杂度**: $O(|instances|)$ 时间复杂度

**证明**：
1. **注册复杂度**: 使用哈希表或树结构存储，查找复杂度为 $O(\log|S|)$
2. **发现复杂度**: 需要遍历所有服务实例进行过滤，复杂度为 $O(|S|)$
3. **健康检查复杂度**: 单次健康检查是常数时间操作
4. **负载均衡复杂度**: 需要遍历可用实例集合进行选择

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::time::interval;
use serde::{Deserialize, Serialize};

/// 服务实例状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ServiceStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub metadata: HashMap<String, String>,
    pub status: ServiceStatus,
    pub last_heartbeat: Instant,
}

/// 注册中心
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, ServiceInstance>>>,
    heartbeat_interval: Duration,
    ttl: Duration,
}

impl ServiceRegistry {
    pub fn new(heartbeat_interval: Duration, ttl: Duration) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_interval,
            ttl,
        }
    }

    /// 服务注册
    pub fn register(&self, instance: ServiceInstance) -> bool {
        let mut services = self.services.write().unwrap();
        if services.contains_key(&instance.id) {
            false
        } else {
            services.insert(instance.id.clone(), instance);
            true
        }
    }

    /// 服务发现
    pub fn discover(&self, service_type: &str) -> Vec<ServiceInstance> {
        let services = self.services.read().unwrap();
        services
            .values()
            .filter(|instance| {
                instance.metadata.get("type") == Some(&service_type.to_string())
                    && instance.status == ServiceStatus::Healthy
            })
            .cloned()
            .collect()
    }

    /// 健康检查
    pub async fn health_check(&self, instance_id: &str) -> bool {
        // 模拟健康检查
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }

    /// 心跳更新
    pub fn heartbeat(&self, instance_id: &str) -> bool {
        let mut services = self.services.write().unwrap();
        if let Some(instance) = services.get_mut(instance_id) {
            instance.last_heartbeat = Instant::now();
            true
        } else {
            false
        }
    }

    /// 清理过期服务
    pub fn cleanup_expired(&self) {
        let mut services = self.services.write().unwrap();
        let now = Instant::now();
        services.retain(|_, instance| {
            now.duration_since(instance.last_heartbeat) < self.ttl
        });
    }
}

/// 负载均衡器
pub trait LoadBalancer {
    fn select(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance>;
}

/// 轮询负载均衡器
pub struct RoundRobinBalancer {
    current: std::sync::atomic::AtomicUsize,
}

impl RoundRobinBalancer {
    pub fn new() -> Self {
        Self {
            current: std::sync::atomic::AtomicUsize::new(0),
        }
    }
}

impl LoadBalancer for RoundRobinBalancer {
    fn select(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let current = self.current.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let index = current % instances.len();
        instances.get(index)
    }
}

/// 服务发现客户端
pub struct ServiceDiscoveryClient {
    registry: Arc<ServiceRegistry>,
    load_balancer: Box<dyn LoadBalancer + Send + Sync>,
}

impl ServiceDiscoveryClient {
    pub fn new(registry: Arc<ServiceRegistry>, load_balancer: Box<dyn LoadBalancer + Send + Sync>) -> Self {
        Self {
            registry,
            load_balancer,
        }
    }

    /// 发现服务实例
    pub fn discover_service(&self, service_type: &str) -> Option<ServiceInstance> {
        let instances = self.registry.discover(service_type);
        self.load_balancer.select(&instances).cloned()
    }
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};

/// 泛型服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenericServiceInstance<T> {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub metadata: T,
    pub status: ServiceStatus,
    pub last_heartbeat: Instant,
}

/// 泛型注册中心
pub struct GenericServiceRegistry<T> {
    services: Arc<RwLock<HashMap<String, GenericServiceInstance<T>>>>,
    heartbeat_interval: Duration,
    ttl: Duration,
}

impl<T: Clone + Send + Sync + 'static> GenericServiceRegistry<T> {
    pub fn new(heartbeat_interval: Duration, ttl: Duration) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_interval,
            ttl,
        }
    }

    /// 泛型服务注册
    pub fn register(&self, instance: GenericServiceInstance<T>) -> bool {
        let mut services = self.services.write().unwrap();
        if services.contains_key(&instance.id) {
            false
        } else {
            services.insert(instance.id.clone(), instance);
            true
        }
    }

    /// 泛型服务发现
    pub fn discover<F>(&self, predicate: F) -> Vec<GenericServiceInstance<T>>
    where
        F: Fn(&GenericServiceInstance<T>) -> bool,
    {
        let services = self.services.read().unwrap();
        services
            .values()
            .filter(|instance| {
                instance.status == ServiceStatus::Healthy && predicate(instance)
            })
            .cloned()
            .collect()
    }
}

/// 泛型负载均衡器
pub trait GenericLoadBalancer<T> {
    fn select(&self, instances: &[GenericServiceInstance<T>]) -> Option<&GenericServiceInstance<T>>;
}

/// 泛型服务发现客户端
pub struct GenericServiceDiscoveryClient<T, L>
where
    L: GenericLoadBalancer<T> + Send + Sync,
{
    registry: Arc<GenericServiceRegistry<T>>,
    load_balancer: L,
}

impl<T, L> GenericServiceDiscoveryClient<T, L>
where
    T: Clone + Send + Sync + 'static,
    L: GenericLoadBalancer<T> + Send + Sync,
{
    pub fn new(registry: Arc<GenericServiceRegistry<T>>, load_balancer: L) -> Self {
        Self {
            registry,
            load_balancer,
        }
    }

    /// 泛型服务发现
    pub fn discover_service<F>(&self, predicate: F) -> Option<GenericServiceInstance<T>>
    where
        F: Fn(&GenericServiceInstance<T>) -> bool,
    {
        let instances = self.registry.discover(predicate);
        self.load_balancer.select(&instances).cloned()
    }
}
```

### 5.3 异步实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::sync::RwLock as TokioRwLock;
use serde::{Deserialize, Serialize};

/// 异步服务注册中心
pub struct AsyncServiceRegistry {
    services: Arc<TokioRwLock<HashMap<String, ServiceInstance>>>,
    heartbeat_interval: Duration,
    ttl: Duration,
}

impl AsyncServiceRegistry {
    pub fn new(heartbeat_interval: Duration, ttl: Duration) -> Self {
        Self {
            services: Arc::new(TokioRwLock::new(HashMap::new())),
            heartbeat_interval,
            ttl,
        }
    }

    /// 异步服务注册
    pub async fn register(&self, instance: ServiceInstance) -> bool {
        let mut services = self.services.write().await;
        if services.contains_key(&instance.id) {
            false
        } else {
            services.insert(instance.id.clone(), instance);
            true
        }
    }

    /// 异步服务发现
    pub async fn discover(&self, service_type: &str) -> Vec<ServiceInstance> {
        let services = self.services.read().await;
        services
            .values()
            .filter(|instance| {
                instance.metadata.get("type") == Some(&service_type.to_string())
                    && instance.status == ServiceStatus::Healthy
            })
            .cloned()
            .collect()
    }

    /// 异步健康检查
    pub async fn health_check(&self, instance_id: &str) -> bool {
        // 异步健康检查实现
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }

    /// 异步心跳更新
    pub async fn heartbeat(&self, instance_id: &str) -> bool {
        let mut services = self.services.write().await;
        if let Some(instance) = services.get_mut(instance_id) {
            instance.last_heartbeat = Instant::now();
            true
        } else {
            false
        }
    }

    /// 异步清理过期服务
    pub async fn cleanup_expired(&self) {
        let mut services = self.services.write().await;
        let now = Instant::now();
        services.retain(|_, instance| {
            now.duration_since(instance.last_heartbeat) < self.ttl
        });
    }
}

/// 异步负载均衡器
#[async_trait::async_trait]
pub trait AsyncLoadBalancer: Send + Sync {
    async fn select(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance>;
}

/// 异步轮询负载均衡器
pub struct AsyncRoundRobinBalancer {
    current: std::sync::atomic::AtomicUsize,
}

impl AsyncRoundRobinBalancer {
    pub fn new() -> Self {
        Self {
            current: std::sync::atomic::AtomicUsize::new(0),
        }
    }
}

#[async_trait::async_trait]
impl AsyncLoadBalancer for AsyncRoundRobinBalancer {
    async fn select(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let current = self.current.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let index = current % instances.len();
        instances.get(index)
    }
}

/// 异步服务发现客户端
pub struct AsyncServiceDiscoveryClient {
    registry: Arc<AsyncServiceRegistry>,
    load_balancer: Box<dyn AsyncLoadBalancer>,
}

impl AsyncServiceDiscoveryClient {
    pub fn new(registry: Arc<AsyncServiceRegistry>, load_balancer: Box<dyn AsyncLoadBalancer>) -> Self {
        Self {
            registry,
            load_balancer,
        }
    }

    /// 异步服务发现
    pub async fn discover_service(&self, service_type: &str) -> Option<ServiceInstance> {
        let instances = self.registry.discover(service_type).await;
        self.load_balancer.select(&instances).await.cloned()
    }
}
```

## 6. 应用场景

### 6.1 微服务架构

```rust
use std::sync::Arc;

/// 微服务应用
pub struct MicroserviceApp {
    service_discovery: Arc<ServiceDiscoveryClient>,
}

impl MicroserviceApp {
    pub fn new(service_discovery: Arc<ServiceDiscoveryClient>) -> Self {
        Self { service_discovery }
    }

    /// 调用用户服务
    pub async fn call_user_service(&self, user_id: &str) -> Result<String, Box<dyn std::error::Error>> {
        if let Some(instance) = self.service_discovery.discover_service("user-service") {
            // 调用用户服务
            let url = format!("http://{}:{}/users/{}", instance.address, instance.port, user_id);
            let response = reqwest::get(&url).await?;
            let result = response.text().await?;
            Ok(result)
        } else {
            Err("User service not available".into())
        }
    }

    /// 调用订单服务
    pub async fn call_order_service(&self, order_id: &str) -> Result<String, Box<dyn std::error::Error>> {
        if let Some(instance) = self.service_discovery.discover_service("order-service") {
            // 调用订单服务
            let url = format!("http://{}:{}/orders/{}", instance.address, instance.port, order_id);
            let response = reqwest::get(&url).await?;
            let result = response.text().await?;
            Ok(result)
        } else {
            Err("Order service not available".into())
        }
    }
}
```

### 6.2 容器编排

```rust
use std::sync::Arc;

/// 容器编排系统
pub struct ContainerOrchestrator {
    service_discovery: Arc<ServiceDiscoveryClient>,
}

impl ContainerOrchestrator {
    pub fn new(service_discovery: Arc<ServiceDiscoveryClient>) -> Self {
        Self { service_discovery }
    }

    /// 部署服务
    pub async fn deploy_service(&self, service_name: &str, image: &str, replicas: u32) -> Result<(), Box<dyn std::error::Error>> {
        // 部署服务实例
        for i in 0..replicas {
            let instance = ServiceInstance {
                id: format!("{}-{}", service_name, i),
                address: format!("{}-{}.service", service_name, i),
                port: 8080,
                metadata: {
                    let mut meta = HashMap::new();
                    meta.insert("type".to_string(), service_name.to_string());
                    meta.insert("image".to_string(), image.to_string());
                    meta
                },
                status: ServiceStatus::Healthy,
                last_heartbeat: Instant::now(),
            };
            
            // 注册服务实例
            // 这里应该调用实际的容器编排API
            println!("Deployed service instance: {}", instance.id);
        }
        
        Ok(())
    }

    /// 扩缩容服务
    pub async fn scale_service(&self, service_name: &str, target_replicas: u32) -> Result<(), Box<dyn std::error::Error>> {
        // 获取当前服务实例
        let current_instances = self.service_discovery.registry.discover(service_name);
        let current_count = current_instances.len() as u32;
        
        if target_replicas > current_count {
            // 扩容
            let additional = target_replicas - current_count;
            self.deploy_service(service_name, "latest", additional).await?;
        } else if target_replicas < current_count {
            // 缩容
            let to_remove = current_count - target_replicas;
            // 这里应该调用实际的容器编排API来删除实例
            println!("Scaling down service {} by {} instances", service_name, to_remove);
        }
        
        Ok(())
    }
}
```

### 6.3 云原生应用

```rust
use std::sync::Arc;

/// 云原生应用
pub struct CloudNativeApp {
    service_discovery: Arc<ServiceDiscoveryClient>,
}

impl CloudNativeApp {
    pub fn new(service_discovery: Arc<ServiceDiscoveryClient>) -> Self {
        Self { service_discovery }
    }

    /// 服务网格集成
    pub async fn integrate_service_mesh(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 集成服务网格
        let services = vec!["auth-service", "payment-service", "notification-service"];
        
        for service_name in services {
            if let Some(instance) = self.service_discovery.discover_service(service_name) {
                // 配置服务网格代理
                println!("Configuring service mesh proxy for: {}", instance.id);
                
                // 设置路由规则
                // 设置重试策略
                // 设置熔断器
                // 设置监控
            }
        }
        
        Ok(())
    }

    /// 多集群服务发现
    pub async fn multi_cluster_discovery(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 多集群服务发现
        let clusters = vec!["cluster-1", "cluster-2", "cluster-3"];
        
        for cluster in clusters {
            // 从不同集群发现服务
            if let Some(instance) = self.service_discovery.discover_service("global-service") {
                println!("Found service in cluster {}: {}", cluster, instance.id);
            }
        }
        
        Ok(())
    }
}
```

## 7. 变体模式

### 7.1 客户端发现模式

```rust
/// 客户端发现模式
pub struct ClientSideDiscovery {
    registry: Arc<ServiceRegistry>,
}

impl ClientSideDiscovery {
    pub fn new(registry: Arc<ServiceRegistry>) -> Self {
        Self { registry }
    }

    /// 客户端直接发现服务
    pub fn discover_service(&self, service_type: &str) -> Option<ServiceInstance> {
        let instances = self.registry.discover(service_type);
        if instances.is_empty() {
            None
        } else {
            // 客户端实现负载均衡
            Some(instances[0].clone())
        }
    }
}
```

### 7.2 服务端发现模式

```rust
/// 服务端发现模式
pub struct ServerSideDiscovery {
    load_balancer: Arc<dyn LoadBalancer + Send + Sync>,
}

impl ServerSideDiscovery {
    pub fn new(load_balancer: Arc<dyn LoadBalancer + Send + Sync>) -> Self {
        Self { load_balancer }
    }

    /// 服务端负载均衡
    pub fn route_request(&self, service_type: &str, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        self.load_balancer.select(instances)
    }
}
```

### 7.3 第三方注册模式

```rust
/// 第三方注册模式
pub struct ThirdPartyRegistration {
    registrar: Arc<ServiceRegistry>,
}

impl ThirdPartyRegistration {
    pub fn new(registrar: Arc<ServiceRegistry>) -> Self {
        Self { registrar }
    }

    /// 第三方注册服务
    pub async fn register_service(&self, service_config: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 解析服务配置
        let config: serde_json::Value = serde_json::from_str(service_config)?;
        
        // 创建服务实例
        let instance = ServiceInstance {
            id: config["id"].as_str().unwrap().to_string(),
            address: config["address"].as_str().unwrap().to_string(),
            port: config["port"].as_u64().unwrap() as u16,
            metadata: {
                let mut meta = HashMap::new();
                meta.insert("type".to_string(), config["type"].as_str().unwrap().to_string());
                meta
            },
            status: ServiceStatus::Healthy,
            last_heartbeat: Instant::now(),
        };
        
        // 注册服务
        self.registrar.register(instance);
        
        Ok(())
    }
}
```

## 8. 性能优化

### 8.1 缓存优化

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

/// 缓存服务发现客户端
pub struct CachedServiceDiscoveryClient {
    registry: Arc<ServiceRegistry>,
    load_balancer: Box<dyn LoadBalancer + Send + Sync>,
    cache: Arc<RwLock<HashMap<String, (Vec<ServiceInstance>, Instant)>>>,
    cache_ttl: Duration,
}

impl CachedServiceDiscoveryClient {
    pub fn new(
        registry: Arc<ServiceRegistry>,
        load_balancer: Box<dyn LoadBalancer + Send + Sync>,
        cache_ttl: Duration,
    ) -> Self {
        Self {
            registry,
            load_balancer,
            cache: Arc::new(RwLock::new(HashMap::new())),
            cache_ttl,
        }
    }

    /// 带缓存的服务发现
    pub fn discover_service(&self, service_type: &str) -> Option<ServiceInstance> {
        // 检查缓存
        {
            let cache = self.cache.read().unwrap();
            if let Some((instances, timestamp)) = cache.get(service_type) {
                if Instant::now().duration_since(*timestamp) < self.cache_ttl {
                    return self.load_balancer.select(instances).cloned();
                }
            }
        }
        
        // 从注册中心获取
        let instances = self.registry.discover(service_type);
        
        // 更新缓存
        {
            let mut cache = self.cache.write().unwrap();
            cache.insert(service_type.to_string(), (instances.clone(), Instant::now()));
        }
        
        self.load_balancer.select(&instances).cloned()
    }

    /// 清理过期缓存
    pub fn cleanup_cache(&self) {
        let mut cache = self.cache.write().unwrap();
        let now = Instant::now();
        cache.retain(|_, (_, timestamp)| {
            now.duration_since(*timestamp) < self.cache_ttl
        });
    }
}
```

### 8.2 异步优化

```rust
use tokio::sync::RwLock as TokioRwLock;

/// 异步缓存服务发现客户端
pub struct AsyncCachedServiceDiscoveryClient {
    registry: Arc<AsyncServiceRegistry>,
    load_balancer: Box<dyn AsyncLoadBalancer>,
    cache: Arc<TokioRwLock<HashMap<String, (Vec<ServiceInstance>, Instant)>>>,
    cache_ttl: Duration,
}

impl AsyncCachedServiceDiscoveryClient {
    pub fn new(
        registry: Arc<AsyncServiceRegistry>,
        load_balancer: Box<dyn AsyncLoadBalancer>,
        cache_ttl: Duration,
    ) -> Self {
        Self {
            registry,
            load_balancer,
            cache: Arc::new(TokioRwLock::new(HashMap::new())),
            cache_ttl,
        }
    }

    /// 异步带缓存的服务发现
    pub async fn discover_service(&self, service_type: &str) -> Option<ServiceInstance> {
        // 检查缓存
        {
            let cache = self.cache.read().await;
            if let Some((instances, timestamp)) = cache.get(service_type) {
                if Instant::now().duration_since(*timestamp) < self.cache_ttl {
                    return self.load_balancer.select(instances).await.cloned();
                }
            }
        }
        
        // 从注册中心获取
        let instances = self.registry.discover(service_type).await;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            cache.insert(service_type.to_string(), (instances.clone(), Instant::now()));
        }
        
        self.load_balancer.select(&instances).await.cloned()
    }

    /// 异步清理过期缓存
    pub async fn cleanup_cache(&self) {
        let mut cache = self.cache.write().await;
        let now = Instant::now();
        cache.retain(|_, (_, timestamp)| {
            now.duration_since(*timestamp) < self.cache_ttl
        });
    }
}
```

## 9. 总结

服务发现模式是分布式系统中的核心模式，通过形式化的数学理论和Rust实现，我们建立了完整的服务发现框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于微服务、容器编排、云原生等场景
5. **性能优化**: 通过缓存和异步机制提供高性能实现

该模式为分布式系统的服务发现提供了理论基础和实践指导，是构建可扩展、高可用分布式系统的重要组件。 