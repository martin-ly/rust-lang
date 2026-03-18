# 负载均衡语义 (Load Balancing Semantics)

## 目录

- [负载均衡语义 (Load Balancing Semantics)](#负载均衡语义-load-balancing-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 负载均衡算法分类](#2-负载均衡算法分类)
    - [2.1 算法类型谱系](#21-算法类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 算法数学模型](#3-算法数学模型)
    - [3.1 轮询算法](#31-轮询算法)
    - [3.2 一致性哈希](#32-一致性哈希)
    - [3.3 最少连接算法](#33-最少连接算法)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心负载均衡器框架](#41-核心负载均衡器框架)
    - [4.2 自适应负载均衡](#42-自适应负载均衡)
    - [4.3 健康检查集成](#43-健康检查集成)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 轮询公平性证明](#51-轮询公平性证明)
    - [5.2 一致性哈希性质](#52-一致性哈希性质)
  - [6. 性能分析](#6-性能分析)
  - [7. 总结](#7-总结)

## 1. 引言

负载均衡是分布式系统中分配请求到多个后端实例的核心机制。
本文档深入分析各种负载均衡算法的数学原理、语义保证及其在 Rust 中的高效实现。

---

## 2. 负载均衡算法分类

### 2.1 算法类型谱系

```
负载均衡算法分类:

┌──────────────────────────────────────────────────────────────────┐
│                      负载均衡算法                                 │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌───────────────────┐  ┌───────────────────┐                   │
│  │   静态算法        │  │   动态算法        │                   │
│  │   (Stateless)     │  │   (Stateful)      │                   │
│  ├───────────────────┤  ├───────────────────┤                   │
│  │ • 轮询 (RR)       │  │ • 最少连接 (LC)   │                   │
│  │ • 随机 (Random)   │  │ • 最少响应时间    │                   │
│  │ • 加权轮询 (WRR)  │  │ • 自适应算法      │                   │
│  │ • 哈希 (Hash)     │  │ • 机器学习调度    │                   │
│  │ • 一致性哈希 (CH) │  │ • 预测性调度      │                   │
│  └───────────────────┘  └───────────────────┘                   │
│                                                                  │
│  ┌───────────────────┐  ┌───────────────────┐                   │
│  │   局部感知        │  │   全局感知        │                   │
│  │   (Locality)      │  │   (Global)        │                   │
│  ├───────────────────┤  ├───────────────────┤                   │
│  │ • 区域优先        │  │ • 集中式调度器    │                   │
│  │ • 机架感知        │  │ • 分布式一致性    │                   │
│  │ • 数据中心感知    │  │ • 全局优化        │                   │
│  └───────────────────┘  └───────────────────┘                   │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
负载均衡形式化语义:

后端池:
  BackendPool = {b₁, b₂, ..., bₙ}

后端状态:
  State(b) = (healthy, weight, connections, latency, load)

选择函数:
  Select: BackendPool × Request × Context → Backend

负载均衡器正确性:
  1. 健康性: Select(pool, ...) ∈ {b ∈ pool | healthy(b) = true}
  2. 完备性: healthy(b) = true → P(Select = b) > 0
  3. 公平性: |E[count(bᵢ)] - E[count(bⱼ)]| ≤ ε

性能目标:
  Minimize: Σ latency(b) × requests(b)
  Subject to: ∀b. load(b) ≤ capacity(b)
```

---

## 3. 算法数学模型

### 3.1 轮询算法

```
简单轮询:
  counter_{t+1} = (counter_t + 1) mod n
  Select_t = pool[counter_t]

加权轮询 (平滑算法):
  初始化: current_weight[i] = 0 for all i

  每步:
    current_weight[i] += effective_weight[i]
    selected = argmax(current_weight)
    current_weight[selected] -= total_weight

  其中:
    effective_weight[i] = weight[i] if healthy(bᵢ) else 0
    total_weight = Σ effective_weight[i]

平滑性保证:
  在 total_weight 次选择内，后端 bᵢ 被选择 exactly weight[i] 次
```

### 3.2 一致性哈希

```
一致性哈希:

哈希环:
  Ring = [0, 2³²-1] 或 [0, 2¹⁶⁰-1] (SHA-1)

节点映射:
  MapNode: Backend × replica_id → HashValue

  virtual_nodes(b) = {hash(b.id + ":" + i) | i ∈ [0, replicas)}

键映射:
  MapKey: Key → HashValue

节点选择:
  Select(key) = min_{v ∈ virtual_nodes} {v ≥ MapKey(key)}
              (顺时针方向最近的虚拟节点)

边界处理:
  如果 MapKey(key) > max(virtual_nodes):
    Select(key) = min(virtual_nodes)

节点增删影响:
  |AffectedKeys| / |TotalKeys| ≈ 1/n
  (仅约 1/n 的键需要重新映射)

虚拟节点数量:
  replicas = 150 通常提供良好的分布
  std_dev / mean ≈ 1/√replicas
```

### 3.3 最少连接算法

```
最少连接:

选择函数:
  Select(pool) = argmin_{b ∈ pool} connections(b)

加权最少连接:
  score(b) = connections(b) / weight(b)
  Select(pool) = argmin_{b ∈ pool} score(b)

动态调整:
  connections(b) = active_connections + pending_connections × α

  α: 待定连接权重因子 (通常 0.5-0.8)

最短响应时间变体:
  score(b) = connections(b) × avg_response_time(b) / weight(b)
```

---

## 4. Rust 实现

### 4.1 核心负载均衡器框架

```rust
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::sync::RwLock;
use async_trait::async_trait;
use std::time::{Duration, Instant};

/// 后端实例
#[derive(Debug, Clone)]
pub struct Backend {
    pub id: String,
    pub address: String,
    pub weight: u32,
    pub healthy: Arc<RwLock<bool>>,
    pub connections: Arc<AtomicUsize>,
    pub response_time_ms: Arc<RwLock<f64>>,
}

impl Backend {
    pub fn new(id: String, address: String, weight: u32) -> Self {
        Self {
            id,
            address,
            weight,
            healthy: Arc::new(RwLock::new(true)),
            connections: Arc::new(AtomicUsize::new(0)),
            response_time_ms: Arc::new(RwLock::new(0.0)),
        }
    }

    pub async fn is_healthy(&self) -> bool {
        *self.healthy.read().await
    }

    pub fn increment_connections(&self) {
        self.connections.fetch_add(1, Ordering::Relaxed);
    }

    pub fn decrement_connections(&self) {
        self.connections.fetch_sub(1, Ordering::Relaxed);
    }

    pub fn active_connections(&self) -> usize {
        self.connections.load(Ordering::Relaxed)
    }
}

/// 负载均衡器 trait
#[async_trait]
pub trait LoadBalancer: Send + Sync {
    /// 选择一个后端
    async fn select(&self, key: Option<&str>) -> Option<Backend>;

    /// 添加后端
    async fn add_backend(&self, backend: Backend);

    /// 移除后端
    async fn remove_backend(&self, id: &str);

    /// 更新后端健康状态
    async fn set_healthy(&self, id: &str, healthy: bool);

    /// 获取所有健康后端
    async fn healthy_backends(&self) -> Vec<Backend>;
}

/// 轮询负载均衡器
pub struct RoundRobinBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    counter: AtomicUsize,
}

impl RoundRobinBalancer {
    pub fn new() -> Self {
        Self {
            backends: Arc::new(RwLock::new(Vec::new())),
            counter: AtomicUsize::new(0),
        }
    }
}

#[async_trait]
impl LoadBalancer for RoundRobinBalancer {
    async fn select(&self, _key: Option<&str>) -> Option<Backend> {
        let backends = self.backends.read().await;
        let healthy: Vec<_> = backends
            .iter()
            .filter(|b| b.is_healthy())
            .cloned()
            .collect();

        if healthy.is_empty() {
            return None;
        }

        let idx = self.counter.fetch_add(1, Ordering::Relaxed) % healthy.len();
        healthy.get(idx).cloned()
    }

    async fn add_backend(&self, backend: Backend) {
        self.backends.write().await.push(backend);
    }

    async fn remove_backend(&self, id: &str) {
        let mut backends = self.backends.write().await;
        backends.retain(|b| b.id != id);
    }

    async fn set_healthy(&self, id: &str, healthy: bool) {
        let backends = self.backends.read().await;
        if let Some(backend) = backends.iter().find(|b| b.id == id) {
            *backend.healthy.write().await = healthy;
        }
    }

    async fn healthy_backends(&self) -> Vec<Backend> {
        let backends = self.backends.read().await;
        futures::future::join_all(
            backends.iter().map(|b| async move {
                if b.is_healthy().await {
                    Some(b.clone())
                } else {
                    None
                }
            })
        )
        .await
        .into_iter()
        .flatten()
        .collect()
    }
}

/// 加权轮询负载均衡器（平滑算法）
pub struct WeightedRoundRobinBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    current_weights: Arc<RwLock<Vec<i32>>>,
}

impl WeightedRoundRobinBalancer {
    pub fn new() -> Self {
        Self {
            backends: Arc::new(RwLock::new(Vec::new())),
            current_weights: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl LoadBalancer for WeightedRoundRobinBalancer {
    async fn select(&self, _key: Option<&str>) -> Option<Backend> {
        let backends = self.backends.read().await;
        let mut weights = self.current_weights.write().await;

        // 过滤健康后端
        let healthy_indices: Vec<usize> = backends
            .iter()
            .enumerate()
            .filter(|(_, b)| *b.healthy.blocking_read())
            .map(|(i, _)| i)
            .collect();

        if healthy_indices.is_empty() {
            return None;
        }

        // 计算总权重
        let total_weight: i32 = healthy_indices
            .iter()
            .map(|&i| backends[i].weight as i32)
            .sum();

        if total_weight == 0 {
            return None;
        }

        // 平滑加权轮询
        let mut max_idx = 0;
        let mut max_weight = -1;

        for &i in &healthy_indices {
            weights[i] += backends[i].weight as i32;
            if weights[i] > max_weight {
                max_weight = weights[i];
                max_idx = i;
            }
        }

        weights[max_idx] -= total_weight;

        backends.get(max_idx).cloned()
    }

    async fn add_backend(&self, backend: Backend) {
        let mut backends = self.backends.write().await;
        let mut weights = self.current_weights.write().await;
        backends.push(backend);
        weights.push(0);
    }

    async fn remove_backend(&self, id: &str) {
        let mut backends = self.backends.write().await;
        let mut weights = self.current_weights.write().await;

        if let Some(idx) = backends.iter().position(|b| b.id == id) {
            backends.remove(idx);
            weights.remove(idx);
        }
    }

    async fn set_healthy(&self, id: &str, healthy: bool) {
        let backends = self.backends.read().await;
        if let Some(backend) = backends.iter().find(|b| b.id == id) {
            *backend.healthy.write().await = healthy;
        }
    }

    async fn healthy_backends(&self) -> Vec<Backend> {
        let backends = self.backends.read().await;
        let mut result = Vec::new();
        for backend in backends.iter() {
            if *backend.healthy.read().await {
                result.push(backend.clone());
            }
        }
        result
    }
}

/// 一致性哈希负载均衡器
pub struct ConsistentHashBalancer {
    /// 虚拟节点到后端的映射
    ring: Arc<RwLock<BTreeMap<u64, Backend>>>,
    /// 每个后端的虚拟节点数
    replicas: usize,
    /// 哈希函数
    hasher: Box<dyn Fn(&str) -> u64 + Send + Sync>,
}

impl ConsistentHashBalancer {
    pub fn new(replicas: usize) -> Self {
        Self {
            ring: Arc::new(RwLock::new(BTreeMap::new())),
            replicas,
            hasher: Box::new(Self::default_hash),
        }
    }

    /// 默认哈希函数 (FNV-1a)
    fn default_hash(key: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    /// 计算虚拟节点哈希
    fn virtual_node_hash(&self, backend_id: &str, replica: usize) -> u64 {
        (self.hasher)(&format!("{}:{}", backend_id, replica))
    }
}

#[async_trait]
impl LoadBalancer for ConsistentHashBalancer {
    async fn select(&self, key: Option<&str>) -> Option<Backend> {
        let ring = self.ring.read().await;

        if ring.is_empty() {
            return None;
        }

        let hash = key.map(|k| (self.hasher)(k))
            .unwrap_or_else(|| rand::random());

        // 找到顺时针方向第一个节点
        let selected = ring
            .range(hash..)
            .next()
            .or_else(|| ring.iter().next())
            .map(|(_, backend)| backend.clone());

        selected
    }

    async fn add_backend(&self, backend: Backend) {
        let mut ring = self.ring.write().await;

        // 添加虚拟节点
        for i in 0..self.replicas {
            let hash = self.virtual_node_hash(&backend.id, i);
            ring.insert(hash, backend.clone());
        }
    }

    async fn remove_backend(&self, id: &str) {
        let mut ring = self.ring.write().await;

        // 移除该后端的所有虚拟节点
        let hashes_to_remove: Vec<u64> = ring
            .iter()
            .filter(|(_, b)| b.id == id)
            .map(|(h, _)| *h)
            .collect();

        for hash in hashes_to_remove {
            ring.remove(&hash);
        }
    }

    async fn set_healthy(&self, id: &str, healthy: bool) {
        // 一致性哈希通常不直接处理健康检查
        // 而是在选择后由调用方处理
        let ring = self.ring.read().await;
        for (_, backend) in ring.iter() {
            if backend.id == id {
                *backend.healthy.write().await = healthy;
            }
        }
    }

    async fn healthy_backends(&self) -> Vec<Backend> {
        let ring = self.ring.read().await;
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();

        for (_, backend) in ring.iter() {
            if seen.insert(backend.id.clone()) && *backend.healthy.read().await {
                result.push(backend.clone());
            }
        }

        result
    }
}

/// 最少连接负载均衡器
pub struct LeastConnectionsBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
}

impl LeastConnectionsBalancer {
    pub fn new() -> Self {
        Self {
            backends: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl LoadBalancer for LeastConnectionsBalancer {
    async fn select(&self, _key: Option<&str>) -> Option<Backend> {
        let backends = self.backends.read().await;

        let healthy: Vec<_> = backends
            .iter()
            .filter(|b| *b.healthy.blocking_read())
            .collect();

        if healthy.is_empty() {
            return None;
        }

        // 找到连接数最少的后端
        healthy
            .into_iter()
            .min_by_key(|b| b.active_connections())
            .cloned()
    }

    async fn add_backend(&self, backend: Backend) {
        self.backends.write().await.push(backend);
    }

    async fn remove_backend(&self, id: &str) {
        let mut backends = self.backends.write().await;
        backends.retain(|b| b.id != id);
    }

    async fn set_healthy(&self, id: &str, healthy: bool) {
        let backends = self.backends.read().await;
        if let Some(backend) = backends.iter().find(|b| b.id == id) {
            *backend.healthy.write().await = healthy;
        }
    }

    async fn healthy_backends(&self) -> Vec<Backend> {
        let backends = self.backends.read().await;
        let mut result = Vec::new();
        for backend in backends.iter() {
            if *backend.healthy.read().await {
                result.push(backend.clone());
            }
        }
        result
    }
}
```

### 4.2 自适应负载均衡

```rust
/// 自适应负载均衡器（基于响应时间）
pub struct AdaptiveLoadBalancer {
    backends: Arc<RwLock<Vec<Backend>>>,
    /// 响应时间估计（指数加权移动平均）
    ewma_response_times: Arc<RwLock<HashMap<String, f64>>>,
    /// EWMA 平滑因子
    alpha: f64,
}

impl AdaptiveLoadBalancer {
    pub fn new(alpha: f64) -> Self {
        Self {
            backends: Arc::new(RwLock::new(Vec::new())),
            ewma_response_times: Arc::new(RwLock::new(HashMap::new())),
            alpha,
        }
    }

    /// 记录请求完成
    pub async fn record_response(&self, backend_id: &str, response_time_ms: f64) {
        let mut times = self.ewma_response_times.write().await;

        let new_ewma = times
            .get(backend_id)
            .map(|old| self.alpha * response_time_ms + (1.0 - self.alpha) * old)
            .unwrap_or(response_time_ms);

        times.insert(backend_id.to_string(), new_ewma);
    }

    /// 计算后端得分（越低越好）
    async fn calculate_score(&self, backend: &Backend) -> f64 {
        let connections = backend.active_connections() as f64;
        let times = self.ewma_response_times.read().await;
        let response_time = times.get(&backend.id).copied().unwrap_or(100.0);

        // 得分 = 连接数 × 响应时间 / 权重
        connections * response_time / backend.weight as f64
    }
}

#[async_trait]
impl LoadBalancer for AdaptiveLoadBalancer {
    async fn select(&self, _key: Option<&str>) -> Option<Backend> {
        let backends = self.backends.read().await;

        let mut healthy_with_scores: Vec<_> = Vec::new();

        for backend in backends.iter() {
            if *backend.healthy.read().await {
                let score = self.calculate_score(backend).await;
                healthy_with_scores.push((backend.clone(), score));
            }
        }

        if healthy_with_scores.is_empty() {
            return None;
        }

        // 选择得分最低的后端
        healthy_with_scores
            .into_iter()
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|(backend, _)| backend)
    }

    async fn add_backend(&self, backend: Backend) {
        self.backends.write().await.push(backend);
    }

    async fn remove_backend(&self, id: &str) {
        let mut backends = self.backends.write().await;
        backends.retain(|b| b.id != id);

        let mut times = self.ewma_response_times.write().await;
        times.remove(id);
    }

    async fn set_healthy(&self, id: &str, healthy: bool) {
        let backends = self.backends.read().await;
        if let Some(backend) = backends.iter().find(|b| b.id == id) {
            *backend.healthy.write().await = healthy;
        }
    }

    async fn healthy_backends(&self) -> Vec<Backend> {
        let backends = self.backends.read().await;
        let mut result = Vec::new();
        for backend in backends.iter() {
            if *backend.healthy.read().await {
                result.push(backend.clone());
            }
        }
        result
    }
}
```

### 4.3 健康检查集成

```rust
use tokio::time::{interval, Duration};

/// 健康检查配置
#[derive(Debug, Clone)]
pub struct HealthCheckConfig {
    pub interval: Duration,
    pub timeout: Duration,
    pub unhealthy_threshold: u32,
    pub healthy_threshold: u32,
    pub path: String,
}

/// 健康检查器
pub struct HealthChecker {
    config: HealthCheckConfig,
    balancer: Arc<dyn LoadBalancer>,
    client: reqwest::Client,
}

impl HealthChecker {
    pub fn new(config: HealthCheckConfig, balancer: Arc<dyn LoadBalancer>) -> Self {
        Self {
            config,
            balancer,
            client: reqwest::Client::new(),
        }
    }

    /// 启动健康检查循环
    pub async fn start(self: Arc<Self>) {
        let mut ticker = interval(self.config.interval);

        loop {
            ticker.tick().await;
            self.check_all().await;
        }
    }

    async fn check_all(&self) {
        let backends = self.balancer.healthy_backends().await;

        for backend in backends {
            let checker = Arc::clone(&self);
            let backend_id = backend.id.clone();

            tokio::spawn(async move {
                let healthy = checker.check_backend(&backend).await;
                checker.balancer.set_healthy(&backend_id, healthy).await;
            });
        }
    }

    async fn check_backend(&self, backend: &Backend) -> bool {
        let url = format!("http://{}{}", backend.address, self.config.path);

        match tokio::time::timeout(
            self.config.timeout,
            self.client.get(&url).send()
        ).await {
            Ok(Ok(response)) => response.status().is_success(),
            _ => false,
        }
    }
}
```

---

## 5. 形式化验证

### 5.1 轮询公平性证明

```
轮询公平性定理:

定理: 在 N 次选择中，每个健康后端被选择的次数差不超过 1。

证明:
  设轮询计数器初始值为 k

  在 N 次选择后:
    后端 bᵢ 被选择的次数 = ⌈(N + (n - i - k mod n)) / n⌉ 或 ⌊...⌋

  最大差值:
    max(count) - min(count) ≤ 1

  这是因为:
    counter_t = (k + t) mod n
    在任意连续的 n 次选择中，每个后端恰好被选择一次。

平滑加权轮询定理:

定理: 在 total_weight 次选择中，后端 bᵢ 被选择恰好 weight[i] 次。

证明概要:
  1. 初始: current_weight[i] = 0
  2. 每步: current_weight[i] += effective_weight[i]
  3. 选择 max(current_weight) 后，该值减去 total_weight

  不变式: Σ current_weight[i] = 0 (每步结束时)

  因此，在 total_weight 步中，每个 bᵢ 被选中的次数正比于其权重。
```

### 5.2 一致性哈希性质

```
一致性哈希定理:

单调性 (Monotonicity):
  添加或删除节点时，只有与该节点相关的键被重新映射。

  |AffectedKeys| ≤ |Keys| / n × (1 + ε)

  其中 ε 是虚拟节点引入的偏差

平衡性 (Balance):
  每个后端处理的键数期望相等:

  E[|Keys(bᵢ)|] = |Keys| / n

  方差:
  Var[|Keys(bᵢ)|] ≈ |Keys| / (n × replicas)

分散性 (Spread):
  同一键在不同视图中映射到不同节点的概率:

  P(different) ≤ 1 - (1 - 1/n)^{view_diff}
```

---

## 6. 性能分析

```
负载均衡算法复杂度:

| 算法           | 选择复杂度 | 添加后端 | 移除后端 | 状态需求 |
|----------------|------------|----------|----------|----------|
| 轮询           | O(1)       | O(1)     | O(n)     | 计数器   |
| 加权轮询       | O(n)       | O(1)     | O(n)     | 权重数组 |
| 随机           | O(1)       | O(1)     | O(n)     | 无       |
| 最少连接       | O(n)       | O(1)     | O(n)     | 连接计数 |
| 一致性哈希     | O(log VN)  | O(R)     | O(R)     | 哈希环   |
| 自适应         | O(n)       | O(1)     | O(n)     | 历史数据 |

其中:
  n = 后端数量
  R = 每个后端的虚拟节点数
  VN = 总虚拟节点数 = n × R
```

---

## 7. 总结

| 场景 | 推荐算法 | 理由 |
|------|----------|------|
| 均匀负载 | 加权轮询 | 简单、公平 |
| 会话保持 | 一致性哈希 | 相同键路由到相同后端 |
| 长连接 | 最少连接 | 防止后端过载 |
| 异构后端 | 自适应 | 根据性能动态调整 |
| 缓存友好 | 一致性哈希 | 提高缓存命中率 |

核心公式:

$$
\text{Select}_{RR}(i) = b_{(i \mod n)}
$$

$$
\text{Select}_{CH}(key) = \min_{v \in \text{ring}} \{v \geq \text{hash}(key)\}
$$

$$
\text{Select}_{LC} = \arg\min_{b \in \text{healthy}} \text{connections}(b)
$$

$$
\text{Score}_{adaptive}(b) = \frac{\text{connections}(b) \times \text{latency}(b)}{\text{weight}(b)}
$$
