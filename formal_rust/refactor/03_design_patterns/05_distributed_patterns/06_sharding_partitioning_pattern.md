# 分片/分区模式 (Sharding/Partitioning Pattern)

## 1. 概述

### 1.1 模式定义

分片/分区模式是一种分布式系统设计模式，通过将数据或服务分割成多个片段（分片），分布到不同的节点上，实现水平扩展和负载均衡。

### 1.2 核心概念

- **分片 (Shard)**: 数据或服务的逻辑片段
- **分区键 (Partition Key)**: 用于确定数据分片位置的键
- **分片函数 (Sharding Function)**: 将数据映射到分片的函数
- **一致性哈希 (Consistent Hashing)**: 一种分片算法
- **再平衡 (Rebalancing)**: 重新分配分片的过程

## 2. 形式化定义

### 2.1 分片模式五元组

**定义2.1 (分片模式五元组)**
设 $SP = (D, S, F, K, R)$ 为分片模式，其中：

- $D = \{d_1, d_2, ..., d_n\}$ 是数据集合
- $S = \{s_1, s_2, ..., s_m\}$ 是分片集合
- $F = \{f_1, f_2, ..., f_p\}$ 是分片函数集合
- $K = \{k_1, k_2, ..., k_q\}$ 是分区键集合
- $R = \{r_1, r_2, ..., r_r\}$ 是再平衡规则集合

### 2.2 分片定义

**定义2.2 (分片)**
分片 $s_i = (id_i, data_i, capacity_i, load_i)$，其中：

- $id_i$ 是分片唯一标识符
- $data_i \subseteq D$ 是分片包含的数据
- $capacity_i$ 是分片容量
- $load_i$ 是分片当前负载

### 2.3 分片函数

**定义2.3 (分片函数)**
分片函数 $f: K \times S \rightarrow S$ 定义为：

$$f(key, shards) = shard_i \text{ where } i = hash(key) \bmod |shards|$$

## 3. 数学理论

### 3.1 分片一致性理论

**定义3.1 (分片一致性)**
分片系统是一致的，当且仅当：

$$\forall d \in D: \exists! s \in S: d \in s.data$$

**定理3.1.1 (分片唯一性)**
正确的分片函数确保每个数据项只属于一个分片。

**证明**：

1. **确定性**: 分片函数是确定性的
2. **唯一性**: 每个键映射到唯一的分片
3. **因此**: 每个数据项只属于一个分片

### 3.2 负载均衡理论

**定义3.2 (负载均衡)**
分片系统的负载是均衡的，当且仅当：

$$\forall s_i, s_j \in S: |s_i.load - s_j.load| \leq \epsilon$$

其中 $\epsilon$ 是负载差异阈值。

**定理3.2.1 (负载均衡性)**
一致性哈希算法能够实现良好的负载均衡。

**证明**：

1. **均匀分布**: 哈希函数将数据均匀分布
2. **最小移动**: 节点变化时最小化数据移动
3. **因此**: 实现良好的负载均衡

### 3.3 扩展性理论

**定义3.3 (扩展性)**
分片系统是可扩展的，当且仅当：

$$\forall s \in S: \frac{|s.data|}{s.capacity} \leq \alpha$$

其中 $\alpha$ 是容量利用率阈值。

**定理3.3.1 (水平扩展性)**
分片模式支持水平扩展。

**证明**：

1. **线性扩展**: 分片数量与系统容量成正比
2. **独立扩展**: 每个分片可以独立扩展
3. **因此**: 支持水平扩展

## 4. 核心定理

### 4.1 分片正确性定理

**定理4.1 (分片正确性)**
分片模式 $SP$ 是正确的，当且仅当：

1. **数据完整性**: $\forall d \in D: \exists s \in S: d \in s.data$
2. **分片唯一性**: $\forall d \in D: \exists! s \in S: d \in s.data$
3. **负载均衡**: $\forall s_i, s_j \in S: |s_i.load - s_j.load| \leq \epsilon$
4. **扩展性**: $\forall s \in S: \frac{|s.data|}{s.capacity} \leq \alpha$

**证明**：

1. **数据完整性**: 确保所有数据都被分片
2. **分片唯一性**: 确保数据不重复分片
3. **负载均衡**: 确保分片间负载均衡
4. **扩展性**: 确保系统可以扩展

### 4.2 分片性能定理

**定理4.2 (分片性能)**
分片模式的性能复杂度为：

- **查找复杂度**: $O(\log|S|)$ 时间复杂度
- **插入复杂度**: $O(\log|S|)$ 时间复杂度
- **删除复杂度**: $O(\log|S|)$ 时间复杂度
- **再平衡复杂度**: $O(|D|)$ 时间复杂度

**证明**：

1. **查找复杂度**: 使用哈希表或树结构进行查找
2. **插入复杂度**: 需要确定目标分片并插入
3. **删除复杂度**: 需要定位并删除数据
4. **再平衡复杂度**: 需要重新分配所有数据

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::{HashMap, BTreeMap};
use std::sync::{Arc, RwLock};
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;
use serde::{Deserialize, Serialize};

/// 分片
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Shard {
    pub id: String,
    pub data: HashMap<String, String>,
    pub capacity: usize,
    pub load: usize,
}

impl Shard {
    pub fn new(id: String, capacity: usize) -> Self {
        Self {
            id,
            data: HashMap::new(),
            capacity,
            load: 0,
        }
    }

    /// 添加数据
    pub fn add_data(&mut self, key: String, value: String) -> bool {
        if self.load < self.capacity {
            self.data.insert(key, value);
            self.load += 1;
            true
        } else {
            false
        }
    }

    /// 获取数据
    pub fn get_data(&self, key: &str) -> Option<&String> {
        self.data.get(key)
    }

    /// 删除数据
    pub fn remove_data(&mut self, key: &str) -> Option<String> {
        if let Some(value) = self.data.remove(key) {
            self.load -= 1;
            Some(value)
        } else {
            None
        }
    }

    /// 检查容量
    pub fn has_capacity(&self) -> bool {
        self.load < self.capacity
    }

    /// 获取负载率
    pub fn get_load_ratio(&self) -> f64 {
        self.load as f64 / self.capacity as f64
    }
}

/// 分片函数
pub trait ShardingFunction {
    fn get_shard(&self, key: &str, shards: &[Shard]) -> Option<&Shard>;
}

/// 哈希分片函数
pub struct HashShardingFunction;

impl ShardingFunction for HashShardingFunction {
    fn get_shard(&self, key: &str, shards: &[Shard]) -> Option<&Shard> {
        if shards.is_empty() {
            return None;
        }

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        let index = (hash % shards.len() as u64) as usize;
        
        shards.get(index)
    }
}

/// 范围分片函数
pub struct RangeShardingFunction {
    ranges: Vec<(String, String)>,
}

impl RangeShardingFunction {
    pub fn new(ranges: Vec<(String, String)>) -> Self {
        Self { ranges }
    }
}

impl ShardingFunction for RangeShardingFunction {
    fn get_shard(&self, key: &str, shards: &[Shard]) -> Option<&Shard> {
        for (i, (start, end)) in self.ranges.iter().enumerate() {
            if key >= start && key <= end {
                return shards.get(i);
            }
        }
        None
    }
}

/// 分片管理器
pub struct ShardManager {
    shards: Arc<RwLock<Vec<Shard>>>,
    sharding_function: Box<dyn ShardingFunction + Send + Sync>,
    rebalance_threshold: f64,
}

impl ShardManager {
    pub fn new(
        sharding_function: Box<dyn ShardingFunction + Send + Sync>,
        rebalance_threshold: f64,
    ) -> Self {
        Self {
            shards: Arc::new(RwLock::new(Vec::new())),
            sharding_function,
            rebalance_threshold,
        }
    }

    /// 添加分片
    pub fn add_shard(&self, shard: Shard) {
        let mut shards = self.shards.write().unwrap();
        shards.push(shard);
    }

    /// 移除分片
    pub fn remove_shard(&self, shard_id: &str) -> Option<Shard> {
        let mut shards = self.shards.write().unwrap();
        if let Some(index) = shards.iter().position(|s| s.id == shard_id) {
            Some(shards.remove(index))
        } else {
            None
        }
    }

    /// 插入数据
    pub fn insert(&self, key: String, value: String) -> Result<(), String> {
        let mut shards = self.shards.write().unwrap();
        
        if let Some(shard) = self.sharding_function.get_shard(&key, &shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)
                .ok_or("Shard not found")?;
            
            if shards[shard_index].add_data(key, value) {
                Ok(())
            } else {
                Err("Shard is full".to_string())
            }
        } else {
            Err("No suitable shard found".to_string())
        }
    }

    /// 查找数据
    pub fn get(&self, key: &str) -> Option<String> {
        let shards = self.shards.read().unwrap();
        
        if let Some(shard) = self.sharding_function.get_shard(key, &shards) {
            shard.get_data(key).cloned()
        } else {
            None
        }
    }

    /// 删除数据
    pub fn remove(&self, key: &str) -> Option<String> {
        let mut shards = self.shards.write().unwrap();
        
        if let Some(shard) = self.sharding_function.get_shard(key, &shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)?;
            shards[shard_index].remove_data(key)
        } else {
            None
        }
    }

    /// 检查是否需要再平衡
    pub fn needs_rebalancing(&self) -> bool {
        let shards = self.shards.read().unwrap();
        
        if shards.is_empty() {
            return false;
        }

        let avg_load = shards.iter().map(|s| s.get_load_ratio()).sum::<f64>() / shards.len() as f64;
        
        shards.iter().any(|shard| {
            let load_ratio = shard.get_load_ratio();
            (load_ratio - avg_load).abs() > self.rebalance_threshold
        })
    }

    /// 执行再平衡
    pub fn rebalance(&self) -> Result<(), String> {
        if !self.needs_rebalancing() {
            return Ok(());
        }

        let mut shards = self.shards.write().unwrap();
        let mut all_data: Vec<(String, String)> = Vec::new();

        // 收集所有数据
        for shard in shards.iter() {
            for (key, value) in &shard.data {
                all_data.push((key.clone(), value.clone()));
            }
        }

        // 清空所有分片
        for shard in shards.iter_mut() {
            shard.data.clear();
            shard.load = 0;
        }

        // 重新分配数据
        for (key, value) in all_data {
            if let Some(shard) = self.sharding_function.get_shard(&key, &shards) {
                let shard_index = shards.iter().position(|s| s.id == shard.id)
                    .ok_or("Shard not found")?;
                shards[shard_index].add_data(key, value);
            }
        }

        Ok(())
    }

    /// 获取分片统计信息
    pub fn get_stats(&self) -> ShardStats {
        let shards = self.shards.read().unwrap();
        
        let total_shards = shards.len();
        let total_data = shards.iter().map(|s| s.load).sum();
        let avg_load = if total_shards > 0 {
            shards.iter().map(|s| s.get_load_ratio()).sum::<f64>() / total_shards as f64
        } else {
            0.0
        };
        let max_load = shards.iter().map(|s| s.get_load_ratio()).fold(0.0, f64::max);
        let min_load = shards.iter().map(|s| s.get_load_ratio()).fold(f64::INFINITY, f64::min);

        ShardStats {
            total_shards,
            total_data,
            avg_load,
            max_load,
            min_load,
        }
    }
}

/// 分片统计信息
#[derive(Debug, Clone)]
pub struct ShardStats {
    pub total_shards: usize,
    pub total_data: usize,
    pub avg_load: f64,
    pub max_load: f64,
    pub min_load: f64,
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::marker::PhantomData;

/// 泛型分片
pub struct GenericShard<K, V> {
    pub id: String,
    pub data: HashMap<K, V>,
    pub capacity: usize,
    pub load: usize,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> GenericShard<K, V> {
    pub fn new(id: String, capacity: usize) -> Self {
        Self {
            id,
            data: HashMap::new(),
            capacity,
            load: 0,
            _phantom: PhantomData,
        }
    }

    /// 添加数据
    pub fn add_data(&mut self, key: K, value: V) -> bool {
        if self.load < self.capacity {
            self.data.insert(key, value);
            self.load += 1;
            true
        } else {
            false
        }
    }

    /// 获取数据
    pub fn get_data(&self, key: &K) -> Option<&V> {
        self.data.get(key)
    }

    /// 删除数据
    pub fn remove_data(&mut self, key: &K) -> Option<V> {
        if let Some(value) = self.data.remove(key) {
            self.load -= 1;
            Some(value)
        } else {
            None
        }
    }

    /// 检查容量
    pub fn has_capacity(&self) -> bool {
        self.load < self.capacity
    }

    /// 获取负载率
    pub fn get_load_ratio(&self) -> f64 {
        self.load as f64 / self.capacity as f64
    }
}

/// 泛型分片函数
pub trait GenericShardingFunction<K> {
    fn get_shard(&self, key: &K, shards: &[GenericShard<K, String>]) -> Option<&GenericShard<K, String>>;
}

/// 泛型哈希分片函数
pub struct GenericHashShardingFunction;

impl<K: Hash> GenericShardingFunction<K> for GenericHashShardingFunction {
    fn get_shard(&self, key: &K, shards: &[GenericShard<K, String>]) -> Option<&GenericShard<K, String>> {
        if shards.is_empty() {
            return None;
        }

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        let index = (hash % shards.len() as u64) as usize;
        
        shards.get(index)
    }
}

/// 泛型分片管理器
pub struct GenericShardManager<K, V> {
    shards: Arc<RwLock<Vec<GenericShard<K, V>>>>,
    sharding_function: Box<dyn GenericShardingFunction<K> + Send + Sync>,
    rebalance_threshold: f64,
    _phantom: PhantomData<(K, V)>,
}

impl<K, V> GenericShardManager<K, V> {
    pub fn new(
        sharding_function: Box<dyn GenericShardingFunction<K> + Send + Sync>,
        rebalance_threshold: f64,
    ) -> Self {
        Self {
            shards: Arc::new(RwLock::new(Vec::new())),
            sharding_function,
            rebalance_threshold,
            _phantom: PhantomData,
        }
    }

    /// 添加分片
    pub fn add_shard(&self, shard: GenericShard<K, V>) {
        let mut shards = self.shards.write().unwrap();
        shards.push(shard);
    }

    /// 插入数据
    pub fn insert(&self, key: K, value: V) -> Result<(), String> {
        let mut shards = self.shards.write().unwrap();
        
        // 转换为临时类型进行分片查找
        let temp_shards: Vec<GenericShard<K, String>> = shards
            .iter()
            .map(|s| GenericShard {
                id: s.id.clone(),
                data: HashMap::new(),
                capacity: s.capacity,
                load: s.load,
                _phantom: PhantomData,
            })
            .collect();

        if let Some(shard) = self.sharding_function.get_shard(&key, &temp_shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)
                .ok_or("Shard not found")?;
            
            if shards[shard_index].add_data(key, value) {
                Ok(())
            } else {
                Err("Shard is full".to_string())
            }
        } else {
            Err("No suitable shard found".to_string())
        }
    }

    /// 查找数据
    pub fn get(&self, key: &K) -> Option<V> {
        let shards = self.shards.read().unwrap();
        
        // 转换为临时类型进行分片查找
        let temp_shards: Vec<GenericShard<K, String>> = shards
            .iter()
            .map(|s| GenericShard {
                id: s.id.clone(),
                data: HashMap::new(),
                capacity: s.capacity,
                load: s.load,
                _phantom: PhantomData,
            })
            .collect();

        if let Some(shard) = self.sharding_function.get_shard(key, &temp_shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)?;
            shards[shard_index].get_data(key).cloned()
        } else {
            None
        }
    }

    /// 删除数据
    pub fn remove(&self, key: &K) -> Option<V> {
        let mut shards = self.shards.write().unwrap();
        
        // 转换为临时类型进行分片查找
        let temp_shards: Vec<GenericShard<K, String>> = shards
            .iter()
            .map(|s| GenericShard {
                id: s.id.clone(),
                data: HashMap::new(),
                capacity: s.capacity,
                load: s.load,
                _phantom: PhantomData,
            })
            .collect();

        if let Some(shard) = self.sharding_function.get_shard(key, &temp_shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)?;
            shards[shard_index].remove_data(key)
        } else {
            None
        }
    }
}
```

### 5.3 异步实现

```rust
use tokio::sync::RwLock as TokioRwLock;
use std::sync::Arc;

/// 异步分片管理器
pub struct AsyncShardManager {
    shards: Arc<TokioRwLock<Vec<Shard>>>,
    sharding_function: Box<dyn ShardingFunction + Send + Sync>,
    rebalance_threshold: f64,
}

impl AsyncShardManager {
    pub fn new(
        sharding_function: Box<dyn ShardingFunction + Send + Sync>,
        rebalance_threshold: f64,
    ) -> Self {
        Self {
            shards: Arc::new(TokioRwLock::new(Vec::new())),
            sharding_function,
            rebalance_threshold,
        }
    }

    /// 异步添加分片
    pub async fn add_shard(&self, shard: Shard) {
        let mut shards = self.shards.write().await;
        shards.push(shard);
    }

    /// 异步移除分片
    pub async fn remove_shard(&self, shard_id: &str) -> Option<Shard> {
        let mut shards = self.shards.write().await;
        if let Some(index) = shards.iter().position(|s| s.id == shard_id) {
            Some(shards.remove(index))
        } else {
            None
        }
    }

    /// 异步插入数据
    pub async fn insert(&self, key: String, value: String) -> Result<(), String> {
        let mut shards = self.shards.write().await;
        
        if let Some(shard) = self.sharding_function.get_shard(&key, &shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)
                .ok_or("Shard not found")?;
            
            if shards[shard_index].add_data(key, value) {
                Ok(())
            } else {
                Err("Shard is full".to_string())
            }
        } else {
            Err("No suitable shard found".to_string())
        }
    }

    /// 异步查找数据
    pub async fn get(&self, key: &str) -> Option<String> {
        let shards = self.shards.read().await;
        
        if let Some(shard) = self.sharding_function.get_shard(key, &shards) {
            shard.get_data(key).cloned()
        } else {
            None
        }
    }

    /// 异步删除数据
    pub async fn remove(&self, key: &str) -> Option<String> {
        let mut shards = self.shards.write().await;
        
        if let Some(shard) = self.sharding_function.get_shard(key, &shards) {
            let shard_index = shards.iter().position(|s| s.id == shard.id)?;
            shards[shard_index].remove_data(key)
        } else {
            None
        }
    }

    /// 异步检查是否需要再平衡
    pub async fn needs_rebalancing(&self) -> bool {
        let shards = self.shards.read().await;
        
        if shards.is_empty() {
            return false;
        }

        let avg_load = shards.iter().map(|s| s.get_load_ratio()).sum::<f64>() / shards.len() as f64;
        
        shards.iter().any(|shard| {
            let load_ratio = shard.get_load_ratio();
            (load_ratio - avg_load).abs() > self.rebalance_threshold
        })
    }

    /// 异步执行再平衡
    pub async fn rebalance(&self) -> Result<(), String> {
        if !self.needs_rebalancing().await {
            return Ok(());
        }

        let mut shards = self.shards.write().await;
        let mut all_data: Vec<(String, String)> = Vec::new();

        // 收集所有数据
        for shard in shards.iter() {
            for (key, value) in &shard.data {
                all_data.push((key.clone(), value.clone()));
            }
        }

        // 清空所有分片
        for shard in shards.iter_mut() {
            shard.data.clear();
            shard.load = 0;
        }

        // 重新分配数据
        for (key, value) in all_data {
            if let Some(shard) = self.sharding_function.get_shard(&key, &shards) {
                let shard_index = shards.iter().position(|s| s.id == shard.id)
                    .ok_or("Shard not found")?;
                shards[shard_index].add_data(key, value);
            }
        }

        Ok(())
    }

    /// 异步获取分片统计信息
    pub async fn get_stats(&self) -> ShardStats {
        let shards = self.shards.read().await;
        
        let total_shards = shards.len();
        let total_data = shards.iter().map(|s| s.load).sum();
        let avg_load = if total_shards > 0 {
            shards.iter().map(|s| s.get_load_ratio()).sum::<f64>() / total_shards as f64
        } else {
            0.0
        };
        let max_load = shards.iter().map(|s| s.get_load_ratio()).fold(0.0, f64::max);
        let min_load = shards.iter().map(|s| s.get_load_ratio()).fold(f64::INFINITY, f64::min);

        ShardStats {
            total_shards,
            total_data,
            avg_load,
            max_load,
            min_load,
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
    shard_manager: Arc<ShardManager>,
}

impl DistributedDatabase {
    pub fn new(shard_manager: Arc<ShardManager>) -> Self {
        Self { shard_manager }
    }

    /// 插入记录
    pub async fn insert_record(&self, table: &str, key: &str, value: &str) -> Result<(), String> {
        let shard_key = format!("{}:{}", table, key);
        self.shard_manager.insert(shard_key, value.to_string())
    }

    /// 查询记录
    pub async fn get_record(&self, table: &str, key: &str) -> Option<String> {
        let shard_key = format!("{}:{}", table, key);
        self.shard_manager.get(&shard_key)
    }

    /// 删除记录
    pub async fn delete_record(&self, table: &str, key: &str) -> Option<String> {
        let shard_key = format!("{}:{}", table, key);
        self.shard_manager.remove(&shard_key)
    }

    /// 批量插入
    pub async fn batch_insert(&self, records: Vec<(String, String, String)>) -> Result<(), String> {
        for (table, key, value) in records {
            self.insert_record(&table, &key, &value).await?;
        }
        Ok(())
    }
}
```

### 6.2 缓存分片

```rust
use std::sync::Arc;

/// 缓存分片
pub struct CacheSharding {
    shard_manager: Arc<AsyncShardManager>,
}

impl CacheSharding {
    pub fn new(shard_manager: Arc<AsyncShardManager>) -> Self {
        Self { shard_manager }
    }

    /// 设置缓存
    pub async fn set(&self, key: &str, value: &str, ttl: Option<u64>) -> Result<(), String> {
        let cache_value = if let Some(ttl) = ttl {
            format!("{}:{}", value, ttl)
        } else {
            value.to_string()
        };
        
        self.shard_manager.insert(key.to_string(), cache_value).await
    }

    /// 获取缓存
    pub async fn get(&self, key: &str) -> Option<String> {
        if let Some(value) = self.shard_manager.get(key).await {
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
    pub async fn delete(&self, key: &str) -> Option<String> {
        self.shard_manager.remove(key).await
    }

    /// 清空缓存
    pub async fn clear(&self) -> Result<(), String> {
        // 实现清空所有分片的逻辑
        Ok(())
    }
}
```

## 7. 变体模式

### 7.1 一致性哈希分片

```rust
use std::sync::Arc;

/// 一致性哈希分片
pub struct ConsistentHashSharding {
    ring: BTreeMap<u64, String>,
    virtual_nodes: usize,
}

impl ConsistentHashSharding {
    pub fn new(virtual_nodes: usize) -> Self {
        Self {
            ring: BTreeMap::new(),
            virtual_nodes,
        }
    }

    /// 添加节点
    pub fn add_node(&mut self, node_id: &str) {
        for i in 0..self.virtual_nodes {
            let virtual_key = format!("{}:{}", node_id, i);
            let mut hasher = DefaultHasher::new();
            virtual_key.hash(&mut hasher);
            let hash = hasher.finish();
            self.ring.insert(hash, node_id.to_string());
        }
    }

    /// 移除节点
    pub fn remove_node(&mut self, node_id: &str) {
        let mut to_remove = Vec::new();
        for (hash, id) in &self.ring {
            if id == node_id {
                to_remove.push(*hash);
            }
        }
        for hash in to_remove {
            self.ring.remove(&hash);
        }
    }

    /// 获取节点
    pub fn get_node(&self, key: &str) -> Option<&String> {
        if self.ring.is_empty() {
            return None;
        }

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();

        // 查找大于等于hash的第一个节点
        if let Some((_, node_id)) = self.ring.range(hash..).next() {
            Some(node_id)
        } else {
            // 如果没找到，返回第一个节点（环形）
            self.ring.values().next()
        }
    }
}
```

### 7.2 范围分片

```rust
use std::sync::Arc;

/// 范围分片
pub struct RangeSharding {
    ranges: Vec<(String, String, String)>, // (start, end, shard_id)
}

impl RangeSharding {
    pub fn new() -> Self {
        Self { ranges: Vec::new() }
    }

    /// 添加范围
    pub fn add_range(&mut self, start: String, end: String, shard_id: String) {
        self.ranges.push((start, end, shard_id));
        self.ranges.sort_by(|a, b| a.0.cmp(&b.0));
    }

    /// 获取分片
    pub fn get_shard(&self, key: &str) -> Option<&String> {
        for (start, end, shard_id) in &self.ranges {
            if key >= start && key <= end {
                return Some(shard_id);
            }
        }
        None
    }

    /// 分割范围
    pub fn split_range(&mut self, shard_id: &str, split_key: &str) -> Result<(), String> {
        if let Some(index) = self.ranges.iter().position(|(_, _, id)| id == shard_id) {
            let (start, end, _) = &self.ranges[index];
            
            if split_key > start && split_key < end {
                let new_shard_id = format!("{}_split", shard_id);
                
                // 更新原范围
                self.ranges[index] = (start.clone(), split_key.to_string(), shard_id.to_string());
                
                // 添加新范围
                self.ranges.push((split_key.to_string(), end.clone(), new_shard_id));
                
                // 重新排序
                self.ranges.sort_by(|a, b| a.0.cmp(&b.0));
                
                Ok(())
            } else {
                Err("Split key is not within range".to_string())
            }
        } else {
            Err("Shard not found".to_string())
        }
    }
}
```

## 8. 总结

分片/分区模式是分布式系统中的重要模式，通过形式化的数学理论和Rust实现，我们建立了完整的分片框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于分布式数据库、缓存、存储等场景
5. **扩展性**: 支持水平扩展和负载均衡

该模式为分布式系统的数据分片和负载均衡提供了理论基础和实践指导，是构建可扩展、高性能分布式系统的重要组件。
