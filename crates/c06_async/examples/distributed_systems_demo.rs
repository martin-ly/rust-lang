//! 分布式系统异步演示
//! 
//! 本示例展示了分布式系统中的异步编程模式：
//! - 分布式锁
//! - 一致性哈希
//! - 分布式缓存
//! - 分布式消息队列
//! - 分布式事务
//! - 分布式配置管理
//! - 分布式日志
//! - 分布式监控
//! 
//! 运行方式：
//! ```bash
//! cargo run --example distributed_systems_demo
//! ```

use std::collections::{HashMap, BTreeMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::{interval};
use anyhow::Result;
use uuid::Uuid;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

/// 分布式锁
#[allow(dead_code)]
pub struct DistributedLock {
    lock_name: String,
    lock_holder: Arc<Mutex<Option<String>>>,
    lock_expiry: Arc<Mutex<Option<Instant>>>,
    lock_timeout: Duration,
    heartbeat_interval: Duration,
}

impl DistributedLock {
    pub fn new(lock_name: String, lock_timeout: Duration) -> Self {
        Self {
            lock_name,
            lock_holder: Arc::new(Mutex::new(None)),
            lock_expiry: Arc::new(Mutex::new(None)),
            lock_timeout,
            heartbeat_interval: Duration::from_secs(10),
        }
    }

    pub async fn acquire(&self, client_id: String) -> Result<bool> {
        let mut holder = self.lock_holder.lock().await;
        let mut expiry = self.lock_expiry.lock().await;

        // 检查锁是否已过期
        if let Some(expiry_time) = *expiry {
            if Instant::now() > expiry_time {
                *holder = None;
                *expiry = None;
            }
        }

        // 尝试获取锁
        if holder.is_none() {
            *holder = Some(client_id.clone());
            *expiry = Some(Instant::now() + self.lock_timeout);
            
            // 启动心跳
            self.start_heartbeat(client_id.clone()).await;
            
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub async fn release(&self, client_id: String) -> Result<()> {
        let mut holder = self.lock_holder.lock().await;
        let mut expiry = self.lock_expiry.lock().await;

        if holder.as_ref() == Some(&client_id) {
            *holder = None;
            *expiry = None;
        }

        Ok(())
    }

    async fn start_heartbeat(&self, client_id: String) {
        let holder = Arc::clone(&self.lock_holder);
        let expiry = Arc::clone(&self.lock_expiry);
        let timeout = self.lock_timeout;

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(5));

            loop {
                interval.tick().await;

                let current_holder = holder.lock().await;
                if current_holder.as_ref() != Some(&client_id) {
                    break;
                }

                let mut expiry_guard = expiry.lock().await;
                *expiry_guard = Some(Instant::now() + timeout);
            }
        });
    }
}

/// 一致性哈希环
#[allow(dead_code)]
pub struct ConsistentHashRing<T> {
    ring: Arc<RwLock<BTreeMap<u64, T>>>,
    virtual_nodes: u32,
}

impl<T: Clone + Send + Sync + std::fmt::Debug> ConsistentHashRing<T> {
    pub fn new(virtual_nodes: u32) -> Self {
        Self {
            ring: Arc::new(RwLock::new(BTreeMap::new())),
            virtual_nodes,
        }
    }

    pub async fn add_node(&self, node: T) -> Result<()>
    where
        T: Hash,
    {
        let mut ring = self.ring.write().await;
        
        for i in 0..self.virtual_nodes {
            let mut hasher = DefaultHasher::new();
            format!("{:?}:{}", node, i).hash(&mut hasher);
            let hash = hasher.finish();
            ring.insert(hash, node.clone());
        }

        Ok(())
    }

    pub async fn remove_node(&self, node: &T) -> Result<()>
    where
        T: Hash + PartialEq,
    {
        let mut ring = self.ring.write().await;
        let keys_to_remove: Vec<u64> = ring
            .iter()
            .filter(|(_, n)| n == &node)
            .map(|(k, _)| *k)
            .collect();

        for key in keys_to_remove {
            ring.remove(&key);
        }

        Ok(())
    }

    pub async fn get_node(&self, key: &str) -> Option<T> {
        let ring = self.ring.read().await;
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();

        // 查找第一个大于等于 hash 的节点
        if let Some((_, node)) = ring.range(hash..).next() {
            Some(node.clone())
        } else {
            // 如果没有找到，返回第一个节点（环的起点）
            ring.values().next().cloned()
        }
    }
}

/// 分布式缓存
#[allow(dead_code)]
pub struct DistributedCache {
    nodes: Arc<ConsistentHashRing<String>>,
    caches: Arc<RwLock<HashMap<String, CacheNode>>>,
}

#[derive(Debug, Clone)]
pub struct CacheNode {
    pub id: String,
    pub data: HashMap<String, CacheEntry>,
    pub last_accessed: Instant,
}

#[derive(Debug, Clone)]
pub struct CacheEntry {
    pub value: String,
    pub expiry: Option<Instant>,
    pub created_at: Instant,
}

impl DistributedCache {
    pub fn new() -> Self {
        Self {
            nodes: Arc::new(ConsistentHashRing::new(150)),
            caches: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn add_node(&self, node_id: String) -> Result<()> {
        self.nodes.add_node(node_id.clone()).await?;
        
        let mut caches = self.caches.write().await;
        caches.insert(node_id.clone(), CacheNode {
            id: node_id,
            data: HashMap::new(),
            last_accessed: Instant::now(),
        });

        Ok(())
    }

    pub async fn get(&self, key: &str) -> Option<String> {
        let node_id = self.nodes.get_node(key).await?;
        
        let mut caches = self.caches.write().await;
        if let Some(node) = caches.get_mut(&node_id) {
            node.last_accessed = Instant::now();
            
            if let Some(entry) = node.data.get(key) {
                // 检查是否过期
                if let Some(expiry) = entry.expiry {
                    if Instant::now() > expiry {
                        node.data.remove(key);
                        return None;
                    }
                }
                return Some(entry.value.clone());
            }
        }

        None
    }

    pub async fn set(&self, key: String, value: String, ttl: Option<Duration>) -> Result<()> {
        let node_id = self.nodes.get_node(&key).await
            .ok_or_else(|| anyhow::anyhow!("没有可用的缓存节点"))?;

        let mut caches = self.caches.write().await;
        if let Some(node) = caches.get_mut(&node_id) {
            node.last_accessed = Instant::now();
            
            let expiry = ttl.map(|duration| Instant::now() + duration);
            let entry = CacheEntry {
                value,
                expiry,
                created_at: Instant::now(),
            };
            
            node.data.insert(key, entry);
        }

        Ok(())
    }

    pub async fn get_stats(&self) -> CacheStats {
        let caches = self.caches.read().await;
        let mut total_entries = 0;
        let mut total_size = 0;

        for node in caches.values() {
            total_entries += node.data.len();
            total_size += node.data.values().map(|e| e.value.len()).sum::<usize>();
        }

        CacheStats {
            total_nodes: caches.len(),
            total_entries,
            total_size,
        }
    }
}

#[derive(Debug)]
pub struct CacheStats {
    pub total_nodes: usize,
    pub total_entries: usize,
    pub total_size: usize,
}

/// 分布式消息队列
#[allow(dead_code)]
pub struct DistributedMessageQueue {
    topics: Arc<RwLock<HashMap<String, Topic>>>,
    consumers: Arc<RwLock<HashMap<String, Vec<Consumer>>>>,
}

#[derive(Debug, Clone)]
pub struct Topic {
    pub name: String,
    pub partitions: Vec<Partition>,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub struct Partition {
    pub id: u32,
    pub messages: VecDeque<Message>,
    pub offset: u64,
}

#[derive(Debug, Clone)]
pub struct Message {
    pub id: String,
    pub payload: String,
    pub timestamp: Instant,
    pub partition: u32,
}

#[derive(Debug, Clone)]
pub struct Consumer {
    pub id: String,
    pub group_id: String,
    pub partitions: Vec<u32>,
    pub offset: u64,
}

impl DistributedMessageQueue {
    pub fn new() -> Self {
        Self {
            topics: Arc::new(RwLock::new(HashMap::new())),
            consumers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn create_topic(&self, name: String, partitions: u32) -> Result<()> {
        let mut topics = self.topics.write().await;
        
        let topic_partitions = (0..partitions)
            .map(|i| Partition {
                id: i,
                messages: VecDeque::new(),
                offset: 0,
            })
            .collect();

        let topic = Topic {
            name: name.clone(),
            partitions: topic_partitions,
            created_at: Instant::now(),
        };

        topics.insert(name, topic);
        Ok(())
    }

    pub async fn produce(&self, topic: &str, message: String) -> Result<()> {
        let mut topics = self.topics.write().await;
        if let Some(topic_data) = topics.get_mut(topic) {
            let partition = (rand::random::<u32>() as usize) % topic_data.partitions.len();
            
            let msg = Message {
                id: Uuid::new_v4().to_string(),
                payload: message,
                timestamp: Instant::now(),
                partition: partition as u32,
            };

            topic_data.partitions[partition].messages.push_back(msg);
        }
        Ok(())
    }

    pub async fn consume(&self, topic: &str, consumer_id: String, group_id: String) -> Result<Option<Message>> {
        let mut topics = self.topics.write().await;
        let mut consumers = self.consumers.write().await;

        // 注册消费者
        if !consumers.contains_key(&consumer_id) {
            consumers.insert(consumer_id.clone(), vec![Consumer {
                id: consumer_id.clone(),
                group_id: group_id.clone(),
                partitions: vec![],
                offset: 0,
            }]);
        }

        if let Some(topic_data) = topics.get_mut(topic) {
            let consumer_group = consumers.get_mut(&consumer_id).unwrap();
            let consumer = &mut consumer_group[0];
            
            // 分配分区（简化实现）
            if consumer.partitions.is_empty() {
                consumer.partitions = (0..topic_data.partitions.len() as u32).collect();
            }

            // 从分配的分区中消费消息
            for &partition_id in &consumer.partitions {
                if let Some(partition) = topic_data.partitions.get_mut(partition_id as usize) {
                    if let Some(message) = partition.messages.pop_front() {
                        consumer.offset += 1;
                        return Ok(Some(message));
                    }
                }
            }
        }

        Ok(None)
    }

    pub async fn get_topic_stats(&self, topic: &str) -> Option<TopicStats> {
        let topics = self.topics.read().await;
        if let Some(topic_data) = topics.get(topic) {
            let total_messages = topic_data.partitions.iter()
                .map(|p| p.messages.len())
                .sum();

            Some(TopicStats {
                name: topic.to_string(),
                partitions: topic_data.partitions.len(),
                total_messages,
                created_at: topic_data.created_at,
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct TopicStats {
    pub name: String,
    pub partitions: usize,
    pub total_messages: usize,
    pub created_at: Instant,
}

/// 分布式事务协调器
#[allow(dead_code)]
pub struct DistributedTransactionCoordinator {
    transactions: Arc<RwLock<HashMap<String, Transaction>>>,
    participants: Arc<RwLock<HashMap<String, Participant>>>,
}

#[derive(Debug, Clone)]
pub struct Transaction {
    pub id: String,
    pub status: TransactionStatus,
    pub participants: Vec<String>,
    pub created_at: Instant,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub enum TransactionStatus {
    Active,
    Prepared,
    Committed,
    Aborted,
    Timeout,
}

#[derive(Debug, Clone)]
pub struct Participant {
    pub id: String,
    pub service_name: String,
    pub prepared: bool,
    pub committed: bool,
    pub aborted: bool,
}

impl DistributedTransactionCoordinator {
    pub fn new() -> Self {
        Self {
            transactions: Arc::new(RwLock::new(HashMap::new())),
            participants: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn begin_transaction(&self, participants: Vec<String>) -> String {
        let transaction_id = Uuid::new_v4().to_string();
        
        let transaction = Transaction {
            id: transaction_id.clone(),
            status: TransactionStatus::Active,
            participants: participants.clone(),
            created_at: Instant::now(),
            timeout: Duration::from_secs(30),
        };

        {
            let mut transactions = self.transactions.write().await;
            transactions.insert(transaction_id.clone(), transaction);
        }

        // 注册参与者
        {
            let mut participants_guard = self.participants.write().await;
            for participant_id in participants {
                participants_guard.insert(participant_id.clone(), Participant {
                    id: participant_id,
                    service_name: "unknown".to_string(),
                    prepared: false,
                    committed: false,
                    aborted: false,
                });
            }
        }

        transaction_id
    }

    #[allow(dead_code)]
    pub async fn prepare(&self, _transaction_id: &str, participant_id: &str) -> Result<bool> {
        let mut participants = self.participants.write().await;
        if let Some(participant) = participants.get_mut(participant_id) {
            participant.prepared = true;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    #[allow(dead_code)]
    pub async fn commit(&self, transaction_id: &str) -> Result<()> {
        let mut transactions = self.transactions.write().await;
        let mut participants = self.participants.write().await;

        if let Some(transaction) = transactions.get_mut(transaction_id) {
            // 检查所有参与者是否已准备
            let all_prepared = transaction.participants.iter()
                .all(|p| participants.get(p).map(|p| p.prepared).unwrap_or(false));

            if all_prepared {
                transaction.status = TransactionStatus::Committed;
                
                // 提交所有参与者
                for participant_id in &transaction.participants {
                    if let Some(participant) = participants.get_mut(participant_id) {
                        participant.committed = true;
                    }
                }
            } else {
                transaction.status = TransactionStatus::Aborted;
                
                // 中止所有参与者
                for participant_id in &transaction.participants {
                    if let Some(participant) = participants.get_mut(participant_id) {
                        participant.aborted = true;
                    }
                }
            }
        }

        Ok(())
    }

    pub async fn abort(&self, transaction_id: &str) -> Result<()> {
        let mut transactions = self.transactions.write().await;
        let mut participants = self.participants.write().await;

        if let Some(transaction) = transactions.get_mut(transaction_id) {
            transaction.status = TransactionStatus::Aborted;
            
            // 中止所有参与者
            for participant_id in &transaction.participants {
                if let Some(participant) = participants.get_mut(participant_id) {
                    participant.aborted = true;
                }
            }
        }

        Ok(())
    }
}

struct DistributedSystemsDemo;

impl DistributedSystemsDemo {
    async fn run() -> Result<()> {
        println!("🌐 分布式系统异步演示");
        println!("================================");

        // 1. 分布式锁演示
        println!("\n🔒 1. 分布式锁演示");
        Self::demo_distributed_lock().await?;

        // 2. 一致性哈希演示
        println!("\n🎯 2. 一致性哈希演示");
        Self::demo_consistent_hash().await?;

        // 3. 分布式缓存演示
        println!("\n💾 3. 分布式缓存演示");
        Self::demo_distributed_cache().await?;

        // 4. 分布式消息队列演示
        println!("\n📨 4. 分布式消息队列演示");
        Self::demo_distributed_message_queue().await?;

        // 5. 分布式事务演示
        println!("\n🔄 5. 分布式事务演示");
        Self::demo_distributed_transaction().await?;

        Ok(())
    }

    async fn demo_distributed_lock() -> Result<()> {
        let lock = DistributedLock::new("shared-resource".to_string(), Duration::from_secs(30));

        // 客户端 1 尝试获取锁
        let client1 = "client-1".to_string();
        let acquired1 = lock.acquire(client1.clone()).await?;
        println!("    客户端 1 获取锁: {}", if acquired1 { "成功" } else { "失败" });

        // 客户端 2 尝试获取锁
        let client2 = "client-2".to_string();
        let acquired2 = lock.acquire(client2.clone()).await?;
        println!("    客户端 2 获取锁: {}", if acquired2 { "成功" } else { "失败" });

        // 客户端 1 释放锁
        lock.release(client1).await?;
        println!("    客户端 1 释放锁");

        // 客户端 2 再次尝试获取锁
        let acquired2_again = lock.acquire(client2.clone()).await?;
        println!("    客户端 2 再次获取锁: {}", if acquired2_again { "成功" } else { "失败" });

        lock.release(client2).await?;

        Ok(())
    }

    async fn demo_consistent_hash() -> Result<()> {
        let ring = ConsistentHashRing::new(100);

        // 添加节点
        let nodes = vec!["node-1", "node-2", "node-3"];
        for node in &nodes {
            ring.add_node(node.to_string()).await?;
            println!("    添加节点: {}", node);
        }

        // 测试键的分布
        let test_keys = vec!["key-1", "key-2", "key-3", "key-4", "key-5"];
        println!("    键分布测试:");
        
        for key in &test_keys {
            if let Some(node) = ring.get_node(key).await {
                println!("      {} -> {}", key, node);
            }
        }

        // 移除一个节点
        ring.remove_node(&"node-2".to_string()).await?;
        println!("    移除节点: node-2");

        // 重新测试键的分布
        println!("    移除节点后的键分布:");
        for key in &test_keys {
            if let Some(node) = ring.get_node(key).await {
                println!("      {} -> {}", key, node);
            }
        }

        Ok(())
    }

    async fn demo_distributed_cache() -> Result<()> {
        let cache = DistributedCache::new();

        // 添加缓存节点
        let nodes = vec!["cache-node-1", "cache-node-2", "cache-node-3"];
        for node in &nodes {
            cache.add_node(node.to_string()).await?;
            println!("    添加缓存节点: {}", node);
        }

        // 设置缓存数据
        let test_data = vec![
            ("user:1", "Alice"),
            ("user:2", "Bob"),
            ("user:3", "Charlie"),
            ("order:1", "Order-123"),
            ("order:2", "Order-456"),
        ];

        for (key, value) in &test_data {
            cache.set(key.to_string(), value.to_string(), Some(Duration::from_secs(60))).await?;
            println!("    设置缓存: {} = {}", key, value);
        }

        // 读取缓存数据
        println!("    读取缓存数据:");
        for (key, _) in &test_data {
            if let Some(value) = cache.get(key).await {
                println!("      {} = {}", key, value);
            } else {
                println!("      {} = 未找到", key);
            }
        }

        // 显示缓存统计
        let stats = cache.get_stats().await;
        println!("    缓存统计:");
        println!("      节点数: {}", stats.total_nodes);
        println!("      条目数: {}", stats.total_entries);
        println!("      总大小: {} 字节", stats.total_size);

        Ok(())
    }

    async fn demo_distributed_message_queue() -> Result<()> {
        let queue = DistributedMessageQueue::new();

        // 创建主题
        queue.create_topic("user-events".to_string(), 3).await?;
        println!("    创建主题: user-events (3个分区)");

        // 生产者发送消息
        let messages = vec![
            "用户注册",
            "用户登录",
            "用户注销",
            "用户更新资料",
            "用户删除账户",
        ];

        for message in &messages {
            queue.produce("user-events", message.to_string()).await?;
            println!("    发送消息: {}", message);
        }

        // 消费者消费消息
        println!("    消费者消费消息:");
        let consumer_id = "consumer-1".to_string();
        let group_id = "user-service".to_string();

        for i in 0..messages.len() {
            if let Some(message) = queue.consume("user-events", consumer_id.clone(), group_id.clone()).await? {
                println!("      消费消息 {}: {} (分区: {})", i + 1, message.payload, message.partition);
            } else {
                println!("      没有更多消息");
                break;
            }
        }

        // 显示主题统计
        if let Some(stats) = queue.get_topic_stats("user-events").await {
            println!("    主题统计:");
            println!("      主题名: {}", stats.name);
            println!("      分区数: {}", stats.partitions);
            println!("      剩余消息数: {}", stats.total_messages);
        }

        Ok(())
    }

    async fn demo_distributed_transaction() -> Result<()> {
        let coordinator = DistributedTransactionCoordinator::new();

        // 开始分布式事务
        let participants = vec!["service-a".to_string(), "service-b".to_string(), "service-c".to_string()];
        let transaction_id = coordinator.begin_transaction(participants.clone()).await;
        println!("    开始分布式事务: {}", transaction_id);

        // 准备阶段
        println!("    准备阶段:");
        for participant in &participants {
            let prepared = coordinator.prepare(&transaction_id, participant).await?;
            println!("      {} 准备: {}", participant, if prepared { "成功" } else { "失败" });
        }

        // 提交事务
        coordinator.commit(&transaction_id).await?;
        println!("    事务提交完成");

        // 模拟失败的事务
        println!("    模拟失败事务:");
        let participants2 = vec!["service-x".to_string(), "service-y".to_string()];
        let transaction_id2 = coordinator.begin_transaction(participants2.clone()).await;
        
        // 只让一个服务准备成功
        coordinator.prepare(&transaction_id2, "service-x").await?;
        println!("      service-x 准备: 成功");
        println!("      service-y 准备: 失败");

        // 提交事务（应该失败）
        coordinator.commit(&transaction_id2).await?;
        println!("    事务提交结果: 部分失败，事务中止");

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    DistributedSystemsDemo::run().await?;

    println!("\n🎉 分布式系统异步演示完成！");
    Ok(())
}
