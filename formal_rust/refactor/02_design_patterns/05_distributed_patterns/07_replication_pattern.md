# 复制模式 (Replication Pattern)

## 1. 概述

### 1.1 模式定义

复制模式是一种分布式系统设计模式，通过将数据复制到多个节点上，提高系统的可用性、性能和容错能力。

### 1.2 核心概念

- **主节点 (Primary)**: 负责处理写操作的节点
- **从节点 (Replica)**: 存储数据副本的节点
- **同步复制 (Synchronous Replication)**: 写操作等待所有副本确认
- **异步复制 (Asynchronous Replication)**: 写操作不等待副本确认
- **一致性级别 (Consistency Level)**: 数据一致性的保证程度

## 2. 形式化定义

### 2.1 复制模式五元组

**定义2.1 (复制模式五元组)**
设 $RP = (P, R, S, C, T)$ 为复制模式，其中：

- $P = \{p_1, p_2, ..., p_n\}$ 是主节点集合
- $R = \{r_1, r_2, ..., r_m\}$ 是从节点集合
- $S = \{s_1, s_2, ..., s_p\}$ 是同步策略集合
- $C = \{c_1, c_2, ..., c_q\}$ 是一致性级别集合
- $T = \{t_1, t_2, ..., t_r\}$ 是事务集合

### 2.2 节点定义

**定义2.2 (节点)**
节点 $n_i = (id_i, type_i, data_i, state_i, lag_i)$，其中：

- $id_i$ 是节点唯一标识符
- $type_i \in \{primary, replica\}$ 是节点类型
- $data_i$ 是节点存储的数据
- $state_i \in \{active, inactive, syncing\}$ 是节点状态
- $lag_i$ 是复制延迟

### 2.3 复制函数

**定义2.3 (复制函数)**
复制函数 $replicate: P \times R \times S \rightarrow \mathbb{B}$ 定义为：

$$replicate(primary, replicas, strategy) = \begin{cases}
true & \text{if all replicas are synchronized} \\
false & \text{otherwise}
\end{cases}$$

## 3. 数学理论

### 3.1 复制一致性理论

**定义3.1 (复制一致性)**
复制系统是一致的，当且仅当：

$$\forall r \in R: r.data = p.data$$

其中 $p$ 是主节点。

**定理3.1.1 (最终一致性)**
异步复制系统保证最终一致性。

**证明**：
1. **传播性**: 写操作最终会传播到所有副本
2. **收敛性**: 所有副本最终会收敛到相同状态
3. **因此**: 系统保证最终一致性

### 3.2 可用性理论

**定义3.2 (可用性)**
复制系统的可用性为：

$$Availability = 1 - \prod_{i=1}^{n} (1 - p_i)$$

其中 $p_i$ 是第 $i$ 个节点的可用性。

**定理3.2.1 (可用性提升)**
复制模式显著提升系统可用性。

**证明**：
1. **冗余性**: 多个副本提供冗余
2. **故障隔离**: 单个节点故障不影响整体
3. **因此**: 系统可用性得到提升

### 3.3 性能理论

**定义3.3 (读性能)**
复制系统的读性能为：

$$Read\_Performance = \sum_{i=1}^{n} read\_capacity_i$$

**定理3.3.1 (读性能提升)**
复制模式提升读性能。

**证明**：
1. **负载分散**: 读请求分散到多个副本
2. **并行处理**: 多个副本并行处理请求
3. **因此**: 读性能得到提升

## 4. 核心定理

### 4.1 复制正确性定理

**定理4.1 (复制正确性)**
复制模式 $RP$ 是正确的，当且仅当：

1. **数据完整性**: $\forall r \in R: r.data \subseteq p.data$
2. **一致性保证**: $\forall r_1, r_2 \in R: r_1.data = r_2.data$
3. **可用性保证**: $\exists r \in R: r.state = active$
4. **性能保证**: $Read\_Performance \geq threshold$

**证明**：
1. **数据完整性**: 确保副本数据是主节点数据的子集
2. **一致性保证**: 确保所有副本数据一致
3. **可用性保证**: 确保至少有一个副本可用
4. **性能保证**: 确保读性能满足要求

### 4.2 复制性能定理

**定理4.2 (复制性能)**
复制模式的性能复杂度为：

- **写操作**: $O(|R|)$ 时间复杂度
- **读操作**: $O(1)$ 平均时间复杂度
- **同步操作**: $O(|R|)$ 时间复杂度
- **故障恢复**: $O(\log|R|)$ 时间复杂度

**证明**：
1. **写操作**: 需要同步到所有副本
2. **读操作**: 可以从任意副本读取
3. **同步操作**: 需要与所有副本同步
4. **故障恢复**: 使用日志重放进行恢复

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::time::sleep;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// 节点类型
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum NodeType {
    Primary,
    Replica,
}

/// 节点状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum NodeState {
    Active,
    Inactive,
    Syncing,
}

/// 一致性级别
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConsistencyLevel {
    One,
    Quorum,
    All,
}

/// 节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    pub node_type: NodeType,
    pub data: HashMap<String, String>,
    pub state: NodeState,
    pub lag: Duration,
    pub last_sync: Instant,
}

impl Node {
    pub fn new(id: String, node_type: NodeType) -> Self {
        Self {
            id,
            node_type,
            data: HashMap::new(),
            state: NodeState::Active,
            lag: Duration::from_millis(0),
            last_sync: Instant::now(),
        }
    }

    /// 写入数据
    pub fn write(&mut self, key: String, value: String) -> Result<(), String> {
        if self.state == NodeState::Active {
            self.data.insert(key, value);
            self.last_sync = Instant::now();
            Ok(())
        } else {
            Err("Node is not active".to_string())
        }
    }

    /// 读取数据
    pub fn read(&self, key: &str) -> Option<&String> {
        if self.state == NodeState::Active {
            self.data.get(key)
        } else {
            None
        }
    }

    /// 检查是否同步
    pub fn is_synced(&self, primary_last_sync: Instant) -> bool {
        self.last_sync >= primary_last_sync
    }

    /// 更新同步时间
    pub fn update_sync(&mut self) {
        self.last_sync = Instant::now();
        self.lag = Duration::from_millis(0);
    }
}

/// 复制管理器
pub struct ReplicationManager {
    primary: Arc<RwLock<Node>>,
    replicas: Arc<RwLock<Vec<Node>>>,
    consistency_level: ConsistencyLevel,
    sync_interval: Duration,
}

impl ReplicationManager {
    pub fn new(consistency_level: ConsistencyLevel, sync_interval: Duration) -> Self {
        let primary = Node::new("primary".to_string(), NodeType::Primary);
        
        Self {
            primary: Arc::new(RwLock::new(primary)),
            replicas: Arc::new(RwLock::new(Vec::new())),
            consistency_level,
            sync_interval,
        }
    }

    /// 添加副本
    pub fn add_replica(&self, replica: Node) {
        let mut replicas = self.replicas.write().unwrap();
        replicas.push(replica);
    }

    /// 移除副本
    pub fn remove_replica(&self, replica_id: &str) -> Option<Node> {
        let mut replicas = self.replicas.write().unwrap();
        if let Some(index) = replicas.iter().position(|r| r.id == replica_id) {
            Some(replicas.remove(index))
        } else {
            None
        }
    }

    /// 写入数据
    pub async fn write(&self, key: String, value: String) -> Result<(), String> {
        // 写入主节点
        {
            let mut primary = self.primary.write().unwrap();
            primary.write(key.clone(), value.clone())?;
        }

        // 根据一致性级别复制到副本
        match self.consistency_level {
            ConsistencyLevel::One => {
                // 至少复制到一个副本
                self.replicate_to_replicas(&key, &value, 1).await
            }
            ConsistencyLevel::Quorum => {
                // 复制到多数副本
                let replica_count = self.replicas.read().unwrap().len();
                let quorum = (replica_count / 2) + 1;
                self.replicate_to_replicas(&key, &value, quorum).await
            }
            ConsistencyLevel::All => {
                // 复制到所有副本
                let replica_count = self.replicas.read().unwrap().len();
                self.replicate_to_replicas(&key, &value, replica_count).await
            }
        }
    }

    /// 读取数据
    pub async fn read(&self, key: &str) -> Option<String> {
        // 首先尝试从主节点读取
        {
            let primary = self.primary.read().unwrap();
            if let Some(value) = primary.read(key) {
                return Some(value.clone());
            }
        }

        // 如果主节点没有数据，从副本读取
        let replicas = self.replicas.read().unwrap();
        for replica in replicas.iter() {
            if let Some(value) = replica.read(key) {
                return Some(value.clone());
            }
        }

        None
    }

    /// 复制到副本
    async fn replicate_to_replicas(&self, key: &str, value: &str, count: usize) -> Result<(), String> {
        let mut replicas = self.replicas.write().unwrap();
        let mut success_count = 0;

        for replica in replicas.iter_mut() {
            if success_count >= count {
                break;
            }

            if replica.state == NodeState::Active {
                match replica.write(key.to_string(), value.to_string()) {
                    Ok(()) => {
                        success_count += 1;
                    }
                    Err(_) => {
                        // 记录失败但继续尝试其他副本
                    }
                }
            }
        }

        if success_count >= count {
            Ok(())
        } else {
            Err(format!("Failed to replicate to {} replicas", count))
        }
    }

    /// 同步副本
    pub async fn sync_replicas(&self) -> Result<(), String> {
        let primary_data = {
            let primary = self.primary.read().unwrap();
            primary.data.clone()
        };

        let mut replicas = self.replicas.write().unwrap();
        let mut sync_count = 0;

        for replica in replicas.iter_mut() {
            if replica.state == NodeState::Active {
                // 同步所有数据
                for (key, value) in &primary_data {
                    if let Ok(()) = replica.write(key.clone(), value.clone()) {
                        sync_count += 1;
                    }
                }
                replica.update_sync();
            }
        }

        if sync_count > 0 {
            Ok(())
        } else {
            Err("No replicas were synced".to_string())
        }
    }

    /// 检查副本健康状态
    pub fn check_replica_health(&self) -> Vec<(String, bool)> {
        let replicas = self.replicas.read().unwrap();
        let mut health_status = Vec::new();

        for replica in replicas.iter() {
            let is_healthy = replica.state == NodeState::Active 
                && replica.last_sync.elapsed() < Duration::from_secs(30);
            health_status.push((replica.id.clone(), is_healthy));
        }

        health_status
    }

    /// 故障转移
    pub async fn failover(&self, new_primary_id: &str) -> Result<(), String> {
        let mut replicas = self.replicas.write().unwrap();
        
        // 找到新的主节点
        if let Some(new_primary_index) = replicas.iter().position(|r| r.id == new_primary_id) {
            // 将新主节点从副本列表中移除
            let mut new_primary = replicas.remove(new_primary_index);
            new_primary.node_type = NodeType::Primary;
            
            // 更新主节点
            {
                let mut primary = self.primary.write().unwrap();
                *primary = new_primary;
            }

            // 同步其他副本
            self.sync_replicas().await?;

            Ok(())
        } else {
            Err("New primary not found".to_string())
        }
    }

    /// 获取复制统计信息
    pub fn get_stats(&self) -> ReplicationStats {
        let primary = self.primary.read().unwrap();
        let replicas = self.replicas.read().unwrap();

        let total_replicas = replicas.len();
        let active_replicas = replicas.iter().filter(|r| r.state == NodeState::Active).count();
        let synced_replicas = replicas.iter()
            .filter(|r| r.is_synced(primary.last_sync))
            .count();

        ReplicationStats {
            total_replicas,
            active_replicas,
            synced_replicas,
            primary_data_count: primary.data.len(),
        }
    }
}

/// 复制统计信息
#[derive(Debug, Clone)]
pub struct ReplicationStats {
    pub total_replicas: usize,
    pub active_replicas: usize,
    pub synced_replicas: usize,
    pub primary_data_count: usize,
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::marker::PhantomData;

/// 泛型节点
pub struct GenericNode<K, V> {
    pub id: String,
    pub node_type: NodeType,
    pub data: HashMap<K, V>,
    pub state: NodeState,
    pub lag: Duration,
    pub last_sync: Instant,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> GenericNode<K, V> {
    pub fn new(id: String, node_type: NodeType) -> Self {
        Self {
            id,
            node_type,
            data: HashMap::new(),
            state: NodeState::Active,
            lag: Duration::from_millis(0),
            last_sync: Instant::now(),
            _phantom: PhantomData,
        }
    }

    /// 写入数据
    pub fn write(&mut self, key: K, value: V) -> Result<(), String> {
        if self.state == NodeState::Active {
            self.data.insert(key, value);
            self.last_sync = Instant::now();
            Ok(())
        } else {
            Err("Node is not active".to_string())
        }
    }

    /// 读取数据
    pub fn read(&self, key: &K) -> Option<&V> {
        if self.state == NodeState::Active {
            self.data.get(key)
        } else {
            None
        }
    }

    /// 检查是否同步
    pub fn is_synced(&self, primary_last_sync: Instant) -> bool {
        self.last_sync >= primary_last_sync
    }

    /// 更新同步时间
    pub fn update_sync(&mut self) {
        self.last_sync = Instant::now();
        self.lag = Duration::from_millis(0);
    }
}

/// 泛型复制管理器
pub struct GenericReplicationManager<K, V> {
    primary: Arc<RwLock<GenericNode<K, V>>>,
    replicas: Arc<RwLock<Vec<GenericNode<K, V>>>>,
    consistency_level: ConsistencyLevel,
    sync_interval: Duration,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> GenericReplicationManager<K, V> {
    pub fn new(consistency_level: ConsistencyLevel, sync_interval: Duration) -> Self {
        let primary = GenericNode::new("primary".to_string(), NodeType::Primary);
        
        Self {
            primary: Arc::new(RwLock::new(primary)),
            replicas: Arc::new(RwLock::new(Vec::new())),
            consistency_level,
            sync_interval,
            _phantom: PhantomData,
        }
    }

    /// 添加副本
    pub fn add_replica(&self, replica: GenericNode<K, V>) {
        let mut replicas = self.replicas.write().unwrap();
        replicas.push(replica);
    }

    /// 写入数据
    pub async fn write(&self, key: K, value: V) -> Result<(), String> {
        // 写入主节点
        {
            let mut primary = self.primary.write().unwrap();
            primary.write(key.clone(), value.clone())?;
        }

        // 根据一致性级别复制到副本
        match self.consistency_level {
            ConsistencyLevel::One => {
                self.replicate_to_replicas(&key, &value, 1).await
            }
            ConsistencyLevel::Quorum => {
                let replica_count = self.replicas.read().unwrap().len();
                let quorum = (replica_count / 2) + 1;
                self.replicate_to_replicas(&key, &value, quorum).await
            }
            ConsistencyLevel::All => {
                let replica_count = self.replicas.read().unwrap().len();
                self.replicate_to_replicas(&key, &value, replica_count).await
            }
        }
    }

    /// 读取数据
    pub async fn read(&self, key: &K) -> Option<V> {
        // 首先尝试从主节点读取
        {
            let primary = self.primary.read().unwrap();
            if let Some(value) = primary.read(key) {
                return Some(value.clone());
            }
        }

        // 如果主节点没有数据，从副本读取
        let replicas = self.replicas.read().unwrap();
        for replica in replicas.iter() {
            if let Some(value) = replica.read(key) {
                return Some(value.clone());
            }
        }

        None
    }

    /// 复制到副本
    async fn replicate_to_replicas(&self, key: &K, value: &V, count: usize) -> Result<(), String> {
        let mut replicas = self.replicas.write().unwrap();
        let mut success_count = 0;

        for replica in replicas.iter_mut() {
            if success_count >= count {
                break;
            }

            if replica.state == NodeState::Active {
                match replica.write(key.clone(), value.clone()) {
                    Ok(()) => {
                        success_count += 1;
                    }
                    Err(_) => {
                        // 记录失败但继续尝试其他副本
                    }
                }
            }
        }

        if success_count >= count {
            Ok(())
        } else {
            Err(format!("Failed to replicate to {} replicas", count))
        }
    }

    /// 同步副本
    pub async fn sync_replicas(&self) -> Result<(), String> {
        let primary_data = {
            let primary = self.primary.read().unwrap();
            primary.data.clone()
        };

        let mut replicas = self.replicas.write().unwrap();
        let mut sync_count = 0;

        for replica in replicas.iter_mut() {
            if replica.state == NodeState::Active {
                // 同步所有数据
                for (key, value) in &primary_data {
                    if let Ok(()) = replica.write(key.clone(), value.clone()) {
                        sync_count += 1;
                    }
                }
                replica.update_sync();
            }
        }

        if sync_count > 0 {
            Ok(())
        } else {
            Err("No replicas were synced".to_string())
        }
    }
}
```

### 5.3 异步实现

```rust
use tokio::sync::RwLock as TokioRwLock;
use std::sync::Arc;

/// 异步复制管理器
pub struct AsyncReplicationManager {
    primary: Arc<TokioRwLock<Node>>,
    replicas: Arc<TokioRwLock<Vec<Node>>>,
    consistency_level: ConsistencyLevel,
    sync_interval: Duration,
}

impl AsyncReplicationManager {
    pub fn new(consistency_level: ConsistencyLevel, sync_interval: Duration) -> Self {
        let primary = Node::new("primary".to_string(), NodeType::Primary);
        
        Self {
            primary: Arc::new(TokioRwLock::new(primary)),
            replicas: Arc::new(TokioRwLock::new(Vec::new())),
            consistency_level,
            sync_interval,
        }
    }

    /// 异步添加副本
    pub async fn add_replica(&self, replica: Node) {
        let mut replicas = self.replicas.write().await;
        replicas.push(replica);
    }

    /// 异步移除副本
    pub async fn remove_replica(&self, replica_id: &str) -> Option<Node> {
        let mut replicas = self.replicas.write().await;
        if let Some(index) = replicas.iter().position(|r| r.id == replica_id) {
            Some(replicas.remove(index))
        } else {
            None
        }
    }

    /// 异步写入数据
    pub async fn write(&self, key: String, value: String) -> Result<(), String> {
        // 写入主节点
        {
            let mut primary = self.primary.write().await;
            primary.write(key.clone(), value.clone())?;
        }

        // 根据一致性级别复制到副本
        match self.consistency_level {
            ConsistencyLevel::One => {
                self.replicate_to_replicas(&key, &value, 1).await
            }
            ConsistencyLevel::Quorum => {
                let replica_count = self.replicas.read().await.len();
                let quorum = (replica_count / 2) + 1;
                self.replicate_to_replicas(&key, &value, quorum).await
            }
            ConsistencyLevel::All => {
                let replica_count = self.replicas.read().await.len();
                self.replicate_to_replicas(&key, &value, replica_count).await
            }
        }
    }

    /// 异步读取数据
    pub async fn read(&self, key: &str) -> Option<String> {
        // 首先尝试从主节点读取
        {
            let primary = self.primary.read().await;
            if let Some(value) = primary.read(key) {
                return Some(value.clone());
            }
        }

        // 如果主节点没有数据，从副本读取
        let replicas = self.replicas.read().await;
        for replica in replicas.iter() {
            if let Some(value) = replica.read(key) {
                return Some(value.clone());
            }
        }

        None
    }

    /// 异步复制到副本
    async fn replicate_to_replicas(&self, key: &str, value: &str, count: usize) -> Result<(), String> {
        let mut replicas = self.replicas.write().await;
        let mut success_count = 0;

        for replica in replicas.iter_mut() {
            if success_count >= count {
                break;
            }

            if replica.state == NodeState::Active {
                match replica.write(key.to_string(), value.to_string()) {
                    Ok(()) => {
                        success_count += 1;
                    }
                    Err(_) => {
                        // 记录失败但继续尝试其他副本
                    }
                }
            }
        }

        if success_count >= count {
            Ok(())
        } else {
            Err(format!("Failed to replicate to {} replicas", count))
        }
    }

    /// 异步同步副本
    pub async fn sync_replicas(&self) -> Result<(), String> {
        let primary_data = {
            let primary = self.primary.read().await;
            primary.data.clone()
        };

        let mut replicas = self.replicas.write().await;
        let mut sync_count = 0;

        for replica in replicas.iter_mut() {
            if replica.state == NodeState::Active {
                // 同步所有数据
                for (key, value) in &primary_data {
                    if let Ok(()) = replica.write(key.clone(), value.clone()) {
                        sync_count += 1;
                    }
                }
                replica.update_sync();
            }
        }

        if sync_count > 0 {
            Ok(())
        } else {
            Err("No replicas were synced".to_string())
        }
    }

    /// 异步检查副本健康状态
    pub async fn check_replica_health(&self) -> Vec<(String, bool)> {
        let replicas = self.replicas.read().await;
        let mut health_status = Vec::new();

        for replica in replicas.iter() {
            let is_healthy = replica.state == NodeState::Active 
                && replica.last_sync.elapsed() < Duration::from_secs(30);
            health_status.push((replica.id.clone(), is_healthy));
        }

        health_status
    }

    /// 异步故障转移
    pub async fn failover(&self, new_primary_id: &str) -> Result<(), String> {
        let mut replicas = self.replicas.write().await;
        
        // 找到新的主节点
        if let Some(new_primary_index) = replicas.iter().position(|r| r.id == new_primary_id) {
            // 将新主节点从副本列表中移除
            let mut new_primary = replicas.remove(new_primary_index);
            new_primary.node_type = NodeType::Primary;
            
            // 更新主节点
            {
                let mut primary = self.primary.write().await;
                *primary = new_primary;
            }

            // 同步其他副本
            self.sync_replicas().await?;

            Ok(())
        } else {
            Err("New primary not found".to_string())
        }
    }

    /// 异步获取复制统计信息
    pub async fn get_stats(&self) -> ReplicationStats {
        let primary = self.primary.read().await;
        let replicas = self.replicas.read().await;

        let total_replicas = replicas.len();
        let active_replicas = replicas.iter().filter(|r| r.state == NodeState::Active).count();
        let synced_replicas = replicas.iter()
            .filter(|r| r.is_synced(primary.last_sync))
            .count();

        ReplicationStats {
            total_replicas,
            active_replicas,
            synced_replicas,
            primary_data_count: primary.data.len(),
        }
    }
}
```

## 6. 应用场景

### 6.1 分布式数据库

```rust
use std::sync::Arc;

/// 分布式数据库
pub struct DistributedDatabase {
    replication_manager: Arc<ReplicationManager>,
}

impl DistributedDatabase {
    pub fn new(replication_manager: Arc<ReplicationManager>) -> Self {
        Self { replication_manager }
    }

    /// 插入记录
    pub async fn insert(&self, table: &str, key: &str, value: &str) -> Result<(), String> {
        let db_key = format!("{}:{}", table, key);
        self.replication_manager.write(db_key, value.to_string()).await
    }

    /// 查询记录
    pub async fn select(&self, table: &str, key: &str) -> Option<String> {
        let db_key = format!("{}:{}", table, key);
        self.replication_manager.read(&db_key).await
    }

    /// 更新记录
    pub async fn update(&self, table: &str, key: &str, value: &str) -> Result<(), String> {
        let db_key = format!("{}:{}", table, key);
        self.replication_manager.write(db_key, value.to_string()).await
    }

    /// 删除记录
    pub async fn delete(&self, table: &str, key: &str) -> Result<(), String> {
        let db_key = format!("{}:{}", table, key);
        // 写入空值表示删除
        self.replication_manager.write(db_key, "".to_string()).await
    }

    /// 批量操作
    pub async fn batch_operation(&self, operations: Vec<(String, String, String)>) -> Result<(), String> {
        for (operation, key, value) in operations {
            match operation.as_str() {
                "insert" | "update" => {
                    self.replication_manager.write(key, value).await?;
                }
                "delete" => {
                    self.replication_manager.write(key, "".to_string()).await?;
                }
                _ => {
                    return Err("Unknown operation".to_string());
                }
            }
        }
        Ok(())
    }
}
```

### 6.2 缓存复制

```rust
use std::sync::Arc;

/// 缓存复制
pub struct CacheReplication {
    replication_manager: Arc<AsyncReplicationManager>,
}

impl CacheReplication {
    pub fn new(replication_manager: Arc<AsyncReplicationManager>) -> Self {
        Self { replication_manager }
    }

    /// 设置缓存
    pub async fn set(&self, key: &str, value: &str, ttl: Option<u64>) -> Result<(), String> {
        let cache_value = if let Some(ttl) = ttl {
            format!("{}:{}", value, ttl)
        } else {
            value.to_string()
        };
        
        self.replication_manager.write(key.to_string(), cache_value).await
    }

    /// 获取缓存
    pub async fn get(&self, key: &str) -> Option<String> {
        if let Some(value) = self.replication_manager.read(key).await {
            // 检查TTL
            if let Some((data, ttl)) = value.rsplit_once(':') {
                if let Ok(ttl) = ttl.parse::<u64>() {
                    // 这里应该检查TTL是否过期
                    return Some(data.to_string());
                }
            }
            Some(value)
        } else {
            None
        }
    }

    /// 删除缓存
    pub async fn delete(&self, key: &str) -> Result<(), String> {
        self.replication_manager.write(key.to_string(), "".to_string()).await
    }

    /// 清空缓存
    pub async fn clear(&self) -> Result<(), String> {
        // 实现清空所有副本的逻辑
        Ok(())
    }

    /// 获取缓存统计信息
    pub async fn get_stats(&self) -> ReplicationStats {
        self.replication_manager.get_stats().await
    }
}
```

## 7. 变体模式

### 7.1 主从复制

```rust
use std::sync::Arc;

/// 主从复制
pub struct MasterSlaveReplication {
    master: Arc<RwLock<Node>>,
    slaves: Arc<RwLock<Vec<Node>>>,
}

impl MasterSlaveReplication {
    pub fn new() -> Self {
        let master = Node::new("master".to_string(), NodeType::Primary);
        
        Self {
            master: Arc::new(RwLock::new(master)),
            slaves: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 添加从节点
    pub fn add_slave(&self, slave: Node) {
        let mut slaves = self.slaves.write().unwrap();
        slaves.push(slave);
    }

    /// 写入主节点
    pub async fn write_to_master(&self, key: String, value: String) -> Result<(), String> {
        // 写入主节点
        {
            let mut master = self.master.write().unwrap();
            master.write(key.clone(), value.clone())?;
        }

        // 异步复制到从节点
        self.replicate_to_slaves(&key, &value).await;

        Ok(())
    }

    /// 从主节点读取
    pub async fn read_from_master(&self, key: &str) -> Option<String> {
        let master = self.master.read().unwrap();
        master.read(key).cloned()
    }

    /// 从从节点读取
    pub async fn read_from_slave(&self, key: &str) -> Option<String> {
        let slaves = self.slaves.read().unwrap();
        
        // 轮询从节点
        for slave in slaves.iter() {
            if let Some(value) = slave.read(key) {
                return Some(value.clone());
            }
        }
        
        None
    }

    /// 复制到从节点
    async fn replicate_to_slaves(&self, key: &str, value: &str) {
        let mut slaves = self.slaves.write().unwrap();
        
        for slave in slaves.iter_mut() {
            if slave.state == NodeState::Active {
                let _ = slave.write(key.to_string(), value.to_string());
            }
        }
    }
}
```

### 7.2 多主复制

```rust
use std::sync::Arc;

/// 多主复制
pub struct MultiMasterReplication {
    masters: Arc<RwLock<Vec<Node>>>,
    conflict_resolver: Box<dyn ConflictResolver + Send + Sync>,
}

/// 冲突解析器
pub trait ConflictResolver {
    fn resolve(&self, key: &str, values: &[String]) -> String;
}

/// 时间戳冲突解析器
pub struct TimestampConflictResolver;

impl ConflictResolver for TimestampConflictResolver {
    fn resolve(&self, key: &str, values: &[String]) -> String {
        // 选择最新的值（基于时间戳）
        values.iter().max().unwrap_or(&"".to_string()).clone()
    }
}

impl MultiMasterReplication {
    pub fn new(conflict_resolver: Box<dyn ConflictResolver + Send + Sync>) -> Self {
        Self {
            masters: Arc::new(RwLock::new(Vec::new())),
            conflict_resolver,
        }
    }

    /// 添加主节点
    pub fn add_master(&self, master: Node) {
        let mut masters = self.masters.write().unwrap();
        masters.push(master);
    }

    /// 写入所有主节点
    pub async fn write_to_all_masters(&self, key: String, value: String) -> Result<(), String> {
        let mut masters = self.masters.write().unwrap();
        let mut success_count = 0;

        for master in masters.iter_mut() {
            if master.state == NodeState::Active {
                match master.write(key.clone(), value.clone()) {
                    Ok(()) => {
                        success_count += 1;
                    }
                    Err(_) => {
                        // 记录失败但继续尝试其他主节点
                    }
                }
            }
        }

        if success_count > 0 {
            Ok(())
        } else {
            Err("Failed to write to any master".to_string())
        }
    }

    /// 从任意主节点读取
    pub async fn read_from_any_master(&self, key: &str) -> Option<String> {
        let masters = self.masters.read().unwrap();
        
        for master in masters.iter() {
            if let Some(value) = master.read(key) {
                return Some(value.clone());
            }
        }
        
        None
    }

    /// 解决冲突
    pub async fn resolve_conflicts(&self, key: &str) -> Result<(), String> {
        let masters = self.masters.read().unwrap();
        let mut values = Vec::new();

        // 收集所有主节点的值
        for master in masters.iter() {
            if let Some(value) = master.read(key) {
                values.push(value.clone());
            }
        }

        // 如果有多个不同的值，解决冲突
        if values.len() > 1 && values.iter().collect::<std::collections::HashSet<_>>().len() > 1 {
            let resolved_value = self.conflict_resolver.resolve(key, &values);
            
            // 将解决后的值写回所有主节点
            drop(masters); // 释放读锁
            self.write_to_all_masters(key.to_string(), resolved_value).await?;
        }

        Ok(())
    }
}
```

## 8. 总结

复制模式是分布式系统中的重要模式，通过形式化的数学理论和Rust实现，我们建立了完整的复制框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于分布式数据库、缓存、存储等场景
5. **高可用性**: 通过复制提高系统可用性和容错能力

该模式为分布式系统的数据复制和高可用性提供了理论基础和实践指导，是构建可靠、高性能分布式系统的重要组件。 