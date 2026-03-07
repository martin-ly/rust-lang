# 服务发现语义 (Service Discovery Semantics)

## 目录

- [服务发现语义 (Service Discovery Semantics)](#服务发现语义-service-discovery-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 服务发现基础模型](#2-服务发现基础模型)
    - [2.1 核心概念](#21-核心概念)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 注册语义](#3-注册语义)
    - [3.1 服务注册模式](#31-服务注册模式)
    - [3.2 自注册 vs 第三方注册](#32-自注册-vs-第三方注册)
  - [4. 发现语义](#4-发现语义)
    - [4.1 客户端发现](#41-客户端发现)
    - [4.2 服务端发现](#42-服务端发现)
  - [5. 一致性语义](#5-一致性语义)
    - [5.1 CAP 权衡](#51-cap-权衡)
    - [5.2 一致性级别](#52-一致性级别)
  - [6. 健康检查语义](#6-健康检查语义)
    - [6.1 健康检查策略](#61-健康检查策略)
    - [6.2 故障转移](#62-故障转移)
  - [7. 形式化保证](#7-形式化保证)
    - [7.1 服务发现不变量](#71-服务发现不变量)
    - [7.2 活性保证](#72-活性保证)
  - [8. Rust 实现示例](#8-rust-实现示例)
    - [8.1 基于 etcd 的服务发现](#81-基于-etcd-的服务发现)
  - [9. 总结](#9-总结)

## 1. 引言

服务发现是分布式系统的核心基础设施，允许动态定位网络服务。本文档分析服务发现的形式化语义、一致性模型和 Rust 实现。

---

## 2. 服务发现基础模型

### 2.1 核心概念

```
服务发现架构:

┌──────────────────────────────────────────────────────────────┐
│                     服务发现系统                              │
│                                                               │
│   ┌──────────┐         ┌──────────────┐         ┌──────────┐ │
│   │ Service  │──注册──→│   Registry   │←───────│ Client   │ │
│   │ Provider │  (Register)│  (注册表)   │  发现   │          │ │
│   │          │         │              │ (Discover)│         │ │
│   │ 心跳保活 │──心跳──→│              │         └──────────┘ │
│   │          │  (Keepalive)            │                     │ │
│   └──────────┘         └──────────────┘                      │ │
│                              ↑                               │ │
│                              │ 健康检查                       │ │
│                         ┌────┴────┐                          │ │
│                         │ Health  │                          │ │
│                         │ Checker │                          │ │
│                         └─────────┘                          │ │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
服务发现系统 = (S, R, C, O, H)

S: 服务集合 {s₁, s₂, ...}
R: 注册中心 (Registry)
C: 客户端集合
O: 操作集合 {Register, Deregister, Discover, Update}
H: 健康检查协议

服务记录: ServiceRecord = (id, name, endpoints, metadata, ttl)
```

**服务状态机:**

$$
\text{ServiceState} = \{ \text{Unknown}, \text{Healthy}, \text{Unhealthy}, \text{Registering} \}
$$

$$
\text{Healthy} \xrightarrow{\text{health\_check\_fail}} \text{Unhealthy}
$$

$$
\text{Unhealthy} \xrightarrow{\text{health\_check\_pass}} \text{Healthy}
$$

$$
\text{Healthy} \xrightarrow{\text{ttl\_expire}} \text{Unknown}
$$

---

## 3. 注册语义

### 3.1 服务注册模式

```rust
// 服务注册 trait
trait ServiceRegistry {
    // 注册服务实例
    async fn register(&self, instance: ServiceInstance) -> Result<Registration, RegistryError>;

    // 注销服务实例
    async fn deregister(&self, id: InstanceId) -> Result<(), RegistryError>;

    // 发现服务
    async fn discover(&self, name: ServiceName) -> Result<Vec<ServiceInstance>, RegistryError>;

    // 监听变更
    fn watch(&self, name: ServiceName) -> impl Stream<Item = ServiceChange>;
}

#[derive(Clone)]
struct ServiceInstance {
    id: InstanceId,
    name: ServiceName,
    address: SocketAddr,
    metadata: HashMap<String, String>,
    ttl: Duration,  // 生存时间
}

enum ServiceChange {
    Registered(ServiceInstance),
    Deregistered(InstanceId),
    HealthChanged(InstanceId, HealthStatus),
}
```

### 3.2 自注册 vs 第三方注册

```rust
// 自注册模式 (Self-Registration)
struct SelfRegistration<R: ServiceRegistry> {
    registry: R,
    instance: ServiceInstance,
    heartbeat_interval: Duration,
}

impl<R: ServiceRegistry> SelfRegistration<R> {
    async fn start(&self) {
        // 初始注册
        let reg = self.registry.register(self.instance.clone()).await.unwrap();

        // 心跳保活
        loop {
            sleep(self.heartbeat_interval).await;

            if let Err(e) = self.registry.heartbeat(reg.id()).await {
                tracing::error!("Heartbeat failed: {:?}", e);
                // 重新注册
                let _ = self.registry.register(self.instance.clone()).await;
            }
        }
    }
}

// 第三方注册 (Sidecar 模式)
struct SidecarRegistration<R: ServiceRegistry> {
    registry: R,
    service_addr: SocketAddr,
    check_endpoint: String,
}

impl<R: ServiceRegistry> SidecarRegistration<R> {
    async fn monitor(&self) {
        loop {
            // 主动健康检查
            let healthy = self.check_health().await;

            match healthy {
                true => self.ensure_registered().await,
                false => self.ensure_deregistered().await,
            }

            sleep(Duration::from_secs(5)).await;
        }
    }
}
```

---

## 4. 发现语义

### 4.1 客户端发现

```rust
// 客户端负载均衡
trait LoadBalancer {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance>;
}

struct RoundRobin {
    counter: AtomicUsize,
}

impl LoadBalancer for RoundRobin {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        let idx = self.counter.fetch_add(1, Ordering::SeqCst) % instances.len();
        Some(&instances[idx])
    }
}

struct RandomLB;

impl LoadBalancer for RandomLB {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance> {
        use rand::seq::SliceRandom;
        instances.choose(&mut rand::thread_rng())
    }
}

// 客户端发现
struct ClientSideDiscovery<R, L> {
    registry: R,
    load_balancer: L,
    cache: RwLock<HashMap<ServiceName, Vec<ServiceInstance>>>,
}

impl<R: ServiceRegistry, L: LoadBalancer> ClientSideDiscovery<R, L> {
    async fn invoke<F, T>(&self, service: ServiceName, f: F) -> Result<T, DiscoveryError>
    where
        F: Fn(&ServiceInstance) -> T,
    {
        // 1. 从缓存或注册中心获取实例
        let instances = self.get_instances(service).await?;

        // 2. 负载均衡选择
        let instance = self.load_balancer.select(&instances)
            .ok_or(DiscoveryError::NoAvailableInstance)?;

        // 3. 调用
        Ok(f(instance))
    }
}
```

### 4.2 服务端发现

```rust
// 服务端发现（代理模式）
struct ServerSideDiscovery {
    proxy: ReverseProxy,
    registry: Arc<dyn ServiceRegistry>,
    routes: RwLock<HashMap<ServiceName, Vec<Backend>>>,
}

impl ServerSideDiscovery {
    async fn route(&self, request: Request) -> Result<Response, ProxyError> {
        let service = extract_service_name(&request);

        // 获取健康后端
        let backends = self.get_healthy_backends(&service).await?;

        // 负载均衡选择
        let backend = self.select_backend(&backends)?;

        // 代理请求
        self.proxy.forward(request, backend).await
    }
}
```

---

## 5. 一致性语义

### 5.1 CAP 权衡

```
服务发现的 CAP 选择:

┌─────────────────────────────────────────────────────────────┐
│                      AP 优先 (如 Consul, Eureka)             │
│  • 最终一致性                                                │
│  • 分区下可用                                                │
│  • 可能返回过期数据                                          │
├─────────────────────────────────────────────────────────────┤
│                      CP 优先 (如 etcd, ZooKeeper)            │
│  • 强一致性                                                  │
│  • 分区下牺牲可用性                                          │
│  • 总是返回最新数据                                          │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 一致性级别

```rust
enum ConsistencyLevel {
    Strong,      // 强一致性：读取最新
    Bounded,     // 有界陈旧：读取不超过 N 秒前的数据
    Eventual,    // 最终一致：可能读取旧数据
    Cached,      // 纯缓存：可能读取很旧的数据
}

struct DiscoveryOptions {
    consistency: ConsistencyLevel,
    max_staleness: Option<Duration>,
    prefer_local: bool,  // 优先同可用区
}

impl ServiceRegistry for ConsistentRegistry {
    async fn discover_with_options(
        &self,
        name: ServiceName,
        options: DiscoveryOptions,
    ) -> Result<Vec<ServiceInstance>, RegistryError> {
        match options.consistency {
            ConsistencyLevel::Strong => {
                // 从 Leader 读取
                self.read_from_leader(name).await
            }
            ConsistencyLevel::Bounded => {
                // 检查缓存新鲜度
                if self.cache_fresh_enough(&name, options.max_staleness) {
                    self.read_from_cache(name)
                } else {
                    self.read_from_follower(name).await
                }
            }
            _ => self.read_from_cache(name),
        }
    }
}
```

---

## 6. 健康检查语义

### 6.1 健康检查策略

```rust
enum HealthCheckStrategy {
    // 推送模式：服务主动报告健康
    Push { interval: Duration },

    // 拉取模式：注册中心主动检查
    Pull {
        endpoint: String,
        interval: Duration,
        timeout: Duration,
    },

    // TTL 模式：过期即认为不健康
    Ttl { ttl: Duration },
}

struct HealthChecker {
    strategy: HealthCheckStrategy,
    failure_threshold: u32,
    success_threshold: u32,
}

impl HealthChecker {
    async fn check(&self, instance: &ServiceInstance) -> HealthStatus {
        match &self.strategy {
            HealthCheckStrategy::Pull { endpoint, timeout, .. } => {
                match timeout(*timeout, self.probe(instance, endpoint)).await {
                    Ok(true) => HealthStatus::Healthy,
                    _ => HealthStatus::Unhealthy,
                }
            }
            // ...
        }
    }
}
```

### 6.2 故障转移

```rust
struct FailoverDiscovery<R> {
    primary: R,
    secondaries: Vec<R>,
    circuit_breakers: HashMap<InstanceId, CircuitBreaker>,
}

impl<R: ServiceRegistry> FailoverDiscovery<R> {
    async fn discover_resilient(&self, name: ServiceName) -> Result<Vec<ServiceInstance>, Error> {
        // 尝试主注册中心
        match self.primary.discover(name.clone()).await {
            Ok(instances) => return Ok(instances),
            Err(e) => tracing::warn!("Primary discovery failed: {:?}", e),
        }

        // 故障转移到备用
        for (idx, secondary) in self.secondaries.iter().enumerate() {
            match secondary.discover(name.clone()).await {
                Ok(instances) => {
                    tracing::info!("Failover to secondary {} succeeded", idx);
                    return Ok(instances);
                }
                Err(e) => tracing::warn!("Secondary {} failed: {:?}", idx, e),
            }
        }

        Err(Error::AllBackendsFailed)
    }
}
```

---

## 7. 形式化保证

### 7.1 服务发现不变量

```
基本不变量:

1. 注册持久性:
   register(s) ∧ healthy(s) → ◇ discover(s) = s

2. TTL 过期:
   last_heartbeat(s) + ttl < now → ¬healthy(s)

3. 健康传播:
   health_check(s) = unhealthy → ◇ discover() 不包含 s

4. 最终一致性 (AP):
   □◇ (register(s) → ◇ discover() 包含 s)
```

### 7.2 活性保证

```
活性 (Liveness):

  如果服务 s 健康且已注册
  那么最终客户端能够发现 s

  □ (healthy(s) ∧ registered(s) → ◇ discoverable(s))
```

---

## 8. Rust 实现示例

### 8.1 基于 etcd 的服务发现

```rust
use etcd_client::{Client, GetOptions, WatchOptions};

struct EtcdServiceRegistry {
    client: Client,
    prefix: String,
}

impl ServiceRegistry for EtcdServiceRegistry {
    async fn register(&self, instance: ServiceInstance) -> Result<Registration, RegistryError> {
        let key = format!("{}/{}/{}", self.prefix, instance.name, instance.id);
        let value = serde_json::to_string(&instance)?;

        // 带 TTL 的租约
        let lease = self.client.lease_grant(instance.ttl.as_secs() as i64, None).await?;

        self.client
            .put(key, value, Some(PutOptions::new().with_lease(lease.id())))
            .await?;

        Ok(Registration::new(lease.id()))
    }

    async fn discover(&self, name: ServiceName) -> Result<Vec<ServiceInstance>, RegistryError> {
        let prefix = format!("{}/{}/", self.prefix, name);

        let response = self.client
            .get(prefix, Some(GetOptions::new().with_prefix()))
            .await?;

        let instances = response.kvs()
            .iter()
            .filter_map(|kv| serde_json::from_slice(kv.value()).ok())
            .collect();

        Ok(instances)
    }

    fn watch(&self, name: ServiceName) -> impl Stream<Item = ServiceChange> {
        let prefix = format!("{}/{}/", self.prefix, name);

        self.client.watch(prefix, Some(WatchOptions::new().with_prefix()))
            .filter_map(|event| async move {
                match event {
                    Ok(event) => parse_service_change(event),
                    Err(_) => None,
                }
            })
    }
}
```

---

## 9. 总结

| 维度 | 关键选择 | 形式化 |
|------|----------|--------|
| 发现模式 | Client-side / Server-side | 代理模式 |
| 一致性 | AP (可用优先) / CP (一致优先) | CAP 定理 |
| 健康检查 | Push / Pull / TTL | 状态机 |
| 负载均衡 | RoundRobin / Random / Weighted | 选择函数 |

$$
\text{ServiceDiscovery} = \text{Registry} \times \text{HealthCheck} \times \text{LoadBalance} \times \text{Consistency}
$$
