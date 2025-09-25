use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, broadcast};
use tokio::time::{sleep};
use tracing::{info, warn, debug};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
//use std::sync::atomic::{AtomicUsize, AtomicU64, Ordering};
use uuid::Uuid;

/// 2025年分布式异步模式演示
/// 展示最新的分布式系统异步编程模式和最佳实践

/// 1. 分布式服务发现
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub health_status: HealthStatus,
    pub metadata: HashMap<String, String>,
    pub registered_at: u64,
    pub last_heartbeat: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct ServiceDiscovery {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    heartbeat_interval: Duration,
    health_check_interval: Duration,
    discovery_stats: Arc<RwLock<DiscoveryStats>>,
}

#[derive(Debug, Clone, Default)]
pub struct DiscoveryStats {
    pub total_registrations: usize,
    pub total_deregistrations: usize,
    pub health_checks_performed: usize,
    pub services_discovered: usize,
}

impl ServiceDiscovery {
    pub fn new(heartbeat_interval: Duration, health_check_interval: Duration) -> Self {
        let discovery = Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_interval,
            health_check_interval,
            discovery_stats: Arc::new(RwLock::new(DiscoveryStats::default())),
        };
        
        // 启动心跳监控任务
        let discovery_clone = discovery.clone();
        tokio::spawn(async move {
            discovery_clone.heartbeat_monitor().await;
        });
        
        // 启动健康检查任务
        let discovery_clone = discovery.clone();
        tokio::spawn(async move {
            discovery_clone.health_check_monitor().await;
        });
        
        discovery
    }

    pub async fn register_service(&self, service_name: String, instance: ServiceInstance) -> Result<()> {
        let mut services = self.services.write().await;
        let service_instances = services.entry(service_name.clone()).or_insert_with(Vec::new);
        
        // 检查是否已存在相同ID的实例
        if service_instances.iter().any(|i| i.id == instance.id) {
            return Err(anyhow::anyhow!("服务实例 {} 已存在", instance.id));
        }
        
        service_instances.push(instance.clone());
        
        let mut stats = self.discovery_stats.write().await;
        stats.total_registrations += 1;
        
        info!("注册服务实例: {} ({})", service_name, instance.id);
        Ok(())
    }

    pub async fn deregister_service(&self, service_name: &str, instance_id: &str) -> Result<()> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            instances.retain(|instance| instance.id != instance_id);
            
            if instances.is_empty() {
                services.remove(service_name);
            }
            
            let mut stats = self.discovery_stats.write().await;
            stats.total_deregistrations += 1;
            
            info!("注销服务实例: {} ({})", service_name, instance_id);
            Ok(())
        } else {
            Err(anyhow::anyhow!("服务 {} 不存在", service_name))
        }
    }

    pub async fn discover_services(&self, service_name: &str) -> Result<Vec<ServiceInstance>> {
        let services = self.services.read().await;
        if let Some(instances) = services.get(service_name) {
            // 只返回健康的实例
            let healthy_instances: Vec<ServiceInstance> = instances
                .iter()
                .filter(|instance| instance.health_status == HealthStatus::Healthy)
                .cloned()
                .collect();
            
            info!("发现服务 {} 的 {} 个健康实例", service_name, healthy_instances.len());
            Ok(healthy_instances)
        } else {
            Ok(Vec::new())
        }
    }

    pub async fn update_heartbeat(&self, service_name: &str, instance_id: &str) -> Result<()> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            if let Some(instance) = instances.iter_mut().find(|i| i.id == instance_id) {
                instance.last_heartbeat = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
                instance.health_status = HealthStatus::Healthy;
                return Ok(());
            }
        }
        Err(anyhow::anyhow!("服务实例 {} 未找到", instance_id))
    }

    #[allow(unused_variables)]
    async fn heartbeat_monitor(&self) {
        let mut interval = tokio::time::interval(self.heartbeat_interval);
        loop {
            interval.tick().await;
            
            let mut services = self.services.write().await;
            let mut stats = self.discovery_stats.write().await;
            let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
            
            for (service_name, instances) in services.iter_mut() {
                for instance in instances.iter_mut() {
                    let time_since_heartbeat = now - instance.last_heartbeat;
                    if time_since_heartbeat > self.heartbeat_interval.as_secs() * 3 {
                        instance.health_status = HealthStatus::Unhealthy;
                        warn!("服务实例 {} 心跳超时", instance.id);
                    }
                }
            }
            
            stats.health_checks_performed += 1;
        }
    }

    async fn health_check_monitor(&self) {
        let mut interval = tokio::time::interval(self.health_check_interval);
        loop {
            interval.tick().await;
            
            let services = self.services.read().await;
            for (service_name, instances) in services.iter() {
                for instance in instances {
                    if instance.health_status == HealthStatus::Healthy {
                        // 模拟健康检查
                        let is_healthy = self.perform_health_check(instance).await;
                        if !is_healthy {
                            warn!("健康检查失败: {} ({})", service_name, instance.id);
                        }
                    }
                }
            }
        }
    }

    async fn perform_health_check(&self, instance: &ServiceInstance) -> bool {
        // 模拟健康检查逻辑
        sleep(Duration::from_millis(10)).await;
        // 90% 的概率返回健康
        (instance.id.len() % 10) != 0
    }

    pub async fn get_stats(&self) -> DiscoveryStats {
        self.discovery_stats.read().await.clone()
    }
}

// 移除Clone实现，因为DashMap不支持Clone
// impl Clone for ServiceDiscovery {
//     fn clone(&self) -> Self {
//         Self {
//             services: self.services.clone(),
//             heartbeat_interval: self.heartbeat_interval,
//             health_check_interval: self.health_check_interval,
//             discovery_stats: self.discovery_stats.clone(),
//         }
//     }
// }

/// 2. 分布式负载均衡器
#[derive(Debug)]
pub struct LoadBalancer {
    discovery: ServiceDiscovery,
    strategy: LoadBalancingStrategy,
    circuit_breakers: Arc<RwLock<HashMap<String, CircuitBreaker>>>,
    lb_stats: Arc<RwLock<LoadBalancerStats>>,
}

#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
    ConsistentHash,
}

#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    pub failure_count: usize,
    pub failure_threshold: usize,
    pub recovery_timeout: Duration,
    pub state: CircuitState,
    pub last_failure_time: Option<Instant>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

#[derive(Debug, Clone, Default)]
pub struct LoadBalancerStats {
    pub total_requests: usize,
    pub successful_requests: usize,
    pub failed_requests: usize,
    pub circuit_breaker_trips: usize,
}

impl LoadBalancer {
    pub fn new(discovery: ServiceDiscovery, strategy: LoadBalancingStrategy) -> Self {
        Self {
            discovery,
            strategy,
            circuit_breakers: Arc::new(RwLock::new(HashMap::new())),
            lb_stats: Arc::new(RwLock::new(LoadBalancerStats::default())),
        }
    }

    pub async fn select_instance(&self, service_name: &str) -> Result<ServiceInstance> {
        let instances = self.discovery.discover_services(service_name).await?;
        
        if instances.is_empty() {
            return Err(anyhow::anyhow!("没有可用的服务实例: {}", service_name));
        }

        let selected_instance = match self.strategy {
            LoadBalancingStrategy::RoundRobin => self.round_robin_select(&instances).await,
            LoadBalancingStrategy::Random => self.random_select(&instances).await,
            LoadBalancingStrategy::LeastConnections => self.least_connections_select(&instances).await,
            LoadBalancingStrategy::WeightedRoundRobin => self.weighted_round_robin_select(&instances).await,
            LoadBalancingStrategy::ConsistentHash => self.consistent_hash_select(&instances).await,
        };

        // 检查熔断器状态
        let circuit_breaker = self.get_circuit_breaker(&selected_instance.id).await;
        if circuit_breaker.state == CircuitState::Open {
            return Err(anyhow::anyhow!("服务实例 {} 熔断器开启", selected_instance.id));
        }

        let mut stats = self.lb_stats.write().await;
        stats.total_requests += 1;

        Ok(selected_instance)
    }

    async fn round_robin_select(&self, instances: &[ServiceInstance]) -> ServiceInstance {
        let index = (Instant::now().elapsed().as_nanos() % instances.len() as u128) as usize;
        instances[index].clone()
    }

    async fn random_select(&self, instances: &[ServiceInstance]) -> ServiceInstance {
        let index = (Uuid::new_v4().as_u128() % instances.len() as u128) as usize;
        instances[index].clone()
    }

    async fn least_connections_select(&self, instances: &[ServiceInstance]) -> ServiceInstance {
        // 简化实现，返回第一个实例
        instances[0].clone()
    }

    async fn weighted_round_robin_select(&self, instances: &[ServiceInstance]) -> ServiceInstance {
        // 简化实现，返回第一个实例
        instances[0].clone()
    }

    async fn consistent_hash_select(&self, instances: &[ServiceInstance]) -> ServiceInstance {
        // 简化实现，返回第一个实例
        instances[0].clone()
    }

    pub async fn record_request_result(&self, instance_id: &str, success: bool) {
        let mut circuit_breaker = self.get_circuit_breaker(instance_id).await;
        
        if success {
            circuit_breaker.failure_count = 0;
            circuit_breaker.state = CircuitState::Closed;
        } else {
            circuit_breaker.failure_count += 1;
            circuit_breaker.last_failure_time = Some(Instant::now());
            
            if circuit_breaker.failure_count >= circuit_breaker.failure_threshold {
                circuit_breaker.state = CircuitState::Open;
                let mut stats = self.lb_stats.write().await;
                stats.circuit_breaker_trips += 1;
                warn!("熔断器开启: {}", instance_id);
            }
        }

        let mut stats = self.lb_stats.write().await;
        if success {
            stats.successful_requests += 1;
        } else {
            stats.failed_requests += 1;
        }
    }

    async fn get_circuit_breaker(&self, instance_id: &str) -> CircuitBreaker {
        let mut breakers = self.circuit_breakers.write().await;
        breakers.entry(instance_id.to_string()).or_insert_with(|| CircuitBreaker {
            failure_count: 0,
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(30),
            state: CircuitState::Closed,
            last_failure_time: None,
        }).clone()
    }

    pub async fn get_stats(&self) -> LoadBalancerStats {
        self.lb_stats.read().await.clone()
    }
}

/// 3. 分布式消息队列
#[derive(Debug, Clone)]
pub struct DistributedMessageQueue {
    queues: Arc<RwLock<HashMap<String, Vec<Message>>>>,
    subscribers: Arc<RwLock<HashMap<String, Vec<Subscriber>>>>,
    message_stats: Arc<RwLock<MessageQueueStats>>,
    broadcast_tx: broadcast::Sender<MessageEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub topic: String,
    pub payload: String,
    pub created_at: u64,
    pub ttl: Option<Duration>,
}

#[derive(Debug, Clone)]
pub struct Subscriber {
    pub id: String,
    pub topic: String,
    pub callback: String, // 简化为字符串标识
}

#[derive(Debug, Clone)]
pub enum MessageEvent {
    MessagePublished(String, Message),
    MessageConsumed(String, String),
    SubscriberAdded(String, Subscriber),
    SubscriberRemoved(String, String),
}

#[derive(Debug, Clone, Default)]
pub struct MessageQueueStats {
    pub total_published: usize,
    pub total_consumed: usize,
    pub active_subscribers: usize,
    pub queue_sizes: HashMap<String, usize>,
}

impl DistributedMessageQueue {
    pub fn new() -> Self {
        let (broadcast_tx, _) = broadcast::channel(1000);
        
        Self {
            queues: Arc::new(RwLock::new(HashMap::new())),
            subscribers: Arc::new(RwLock::new(HashMap::new())),
            message_stats: Arc::new(RwLock::new(MessageQueueStats::default())),
            broadcast_tx,
        }
    }

    pub async fn publish(&self, topic: String, payload: String) -> Result<String> {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            topic: topic.clone(),
            payload,
            created_at: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs(),
            ttl: Some(Duration::from_secs(300)),
        };

        let mut queues = self.queues.write().await;
        let queue = queues.entry(topic.clone()).or_insert_with(Vec::new);
        queue.push(message.clone());

        let mut stats = self.message_stats.write().await;
        stats.total_published += 1;
        stats.queue_sizes.insert(topic.clone(), queue.len());

        // 广播消息发布事件
        let _ = self.broadcast_tx.send(MessageEvent::MessagePublished(topic.clone(), message.clone()));

        info!("发布消息到主题 {}: {}", topic, message.id);
        Ok(message.id)
    }

    pub async fn subscribe(&self, topic: String, subscriber_id: String) -> Result<()> {
        let subscriber = Subscriber {
            id: subscriber_id.clone(),
            topic: topic.clone(),
            callback: format!("callback_{}", subscriber_id),
        };

        let mut subscribers = self.subscribers.write().await;
        let topic_subscribers = subscribers.entry(topic.clone()).or_insert_with(Vec::new);
        topic_subscribers.push(subscriber.clone());

        let mut stats = self.message_stats.write().await;
        stats.active_subscribers += 1;

        // 广播订阅者添加事件
        let _ = self.broadcast_tx.send(MessageEvent::SubscriberAdded(topic.clone(), subscriber));

        info!("订阅者 {} 订阅主题 {}", subscriber_id, topic);
        Ok(())
    }

    pub async fn consume(&self, topic: &str, subscriber_id: &str) -> Result<Option<Message>> {
        let mut queues = self.queues.write().await;
        if let Some(queue) = queues.get_mut(topic) {
            if let Some(message) = queue.pop() {
                // 检查消息TTL
                if let Some(ttl) = message.ttl {
                    if (std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() - message.created_at) > ttl.as_secs() {
                        return Ok(None);
                    }
                }

                let mut stats = self.message_stats.write().await;
                stats.total_consumed += 1;
                stats.queue_sizes.insert(topic.to_string(), queue.len());

                // 广播消息消费事件
                let _ = self.broadcast_tx.send(MessageEvent::MessageConsumed(topic.to_string(), message.id.clone()));

                info!("订阅者 {} 消费消息 {} 从主题 {}", subscriber_id, message.id, topic);
                return Ok(Some(message));
            }
        }
        Ok(None)
    }

    pub async fn get_queue_stats(&self, topic: &str) -> Result<QueueStats> {
        let queues = self.queues.read().await;
        let queue_size = queues.get(topic).map(|q| q.len()).unwrap_or(0);
        
        let subscribers = self.subscribers.read().await;
        let subscriber_count = subscribers.get(topic).map(|s| s.len()).unwrap_or(0);

        Ok(QueueStats {
            topic: topic.to_string(),
            queue_size,
            subscriber_count,
        })
    }

    pub async fn get_stats(&self) -> MessageQueueStats {
        self.message_stats.read().await.clone()
    }
}

#[derive(Debug, Clone)]
pub struct QueueStats {
    pub topic: String,
    pub queue_size: usize,
    pub subscriber_count: usize,
}

/// 4. 分布式配置管理
#[derive(Debug, Clone)]
pub struct DistributedConfigManager {
    configurations: Arc<RwLock<HashMap<String, Configuration>>>,
    watchers: Arc<RwLock<HashMap<String, Vec<ConfigWatcher>>>>,
    config_stats: Arc<RwLock<ConfigStats>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Configuration {
    pub key: String,
    pub value: String,
    pub version: u64,
    pub created_at: u64,
    pub updated_at: u64,
}

#[derive(Debug, Clone)]
pub struct ConfigWatcher {
    pub id: String,
    pub key: String,
    pub callback: String,
}

#[derive(Debug, Clone, Default)]
pub struct ConfigStats {
    pub total_configs: usize,
    pub config_updates: usize,
    pub watcher_notifications: usize,
}

impl DistributedConfigManager {
    pub fn new() -> Self {
        Self {
            configurations: Arc::new(RwLock::new(HashMap::new())),
            watchers: Arc::new(RwLock::new(HashMap::new())),
            config_stats: Arc::new(RwLock::new(ConfigStats::default())),
        }
    }

    pub async fn set_config(&self, key: String, value: String) -> Result<()> {
        let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
        let mut configs = self.configurations.write().await;
        
        let config = Configuration {
            key: key.clone(),
            value: value.clone(),
            version: configs.get(&key).map(|c| c.version + 1).unwrap_or(1),
            created_at: configs.get(&key).map(|c| c.created_at).unwrap_or(now),
            updated_at: now,
        };
        
        configs.insert(key.clone(), config);
        
        let mut stats = self.config_stats.write().await;
        stats.config_updates += 1;
        if configs.len() > stats.total_configs {
            stats.total_configs = configs.len();
        }
        
        // 通知观察者
        self.notify_watchers(&key, &value).await;
        
        info!("设置配置: {} = {}", key, value);
        Ok(())
    }

    pub async fn get_config(&self, key: &str) -> Result<Option<Configuration>> {
        let configs = self.configurations.read().await;
        Ok(configs.get(key).cloned())
    }

    pub async fn watch_config(&self, key: String, watcher_id: String) -> Result<()> {
        let watcher = ConfigWatcher {
            id: watcher_id.clone(),
            key: key.clone(),
            callback: format!("callback_{}", watcher_id),
        };
        
        let mut watchers = self.watchers.write().await;
        let key_watchers = watchers.entry(key.clone()).or_insert_with(Vec::new);
        key_watchers.push(watcher);
        
        info!("配置观察者 {} 开始监听 {}", watcher_id, key);
        Ok(())
    }

    async fn notify_watchers(&self, key: &str, value: &str) {
        let watchers = self.watchers.read().await;
        if let Some(key_watchers) = watchers.get(key) {
            let mut stats = self.config_stats.write().await;
            stats.watcher_notifications += key_watchers.len();
            
            for watcher in key_watchers {
                debug!("通知观察者 {}: {} = {}", watcher.id, key, value);
            }
        }
    }

    pub async fn get_stats(&self) -> ConfigStats {
        self.config_stats.read().await.clone()
    }
}

#[tokio::main]
#[allow(unused_variables)]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    info!("🚀 开始 2025 年分布式异步模式演示");

    // 1. 演示分布式服务发现
    info!("🔍 演示分布式服务发现");
    let discovery = ServiceDiscovery::new(
        Duration::from_secs(10),
        Duration::from_secs(30)
    );
    
    // 注册一些服务实例
    for i in 0..5 {
        let instance = ServiceInstance {
            id: format!("instance_{}", i),
            name: "user-service".to_string(),
            address: format!("192.168.1.{}", 100 + i),
            port: 8080 + i as u16,
            health_status: HealthStatus::Healthy,
            metadata: HashMap::new(),
            registered_at: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs(),
            last_heartbeat: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs(),
        };
        
        discovery.register_service("user-service".to_string(), instance).await?;
    }
    
    // 发现服务
    let instances = discovery.discover_services("user-service").await?;
    info!("发现 {} 个用户服务实例", instances.len());
    
    let stats = discovery.get_stats().await;
    info!("服务发现统计: 注册 {}, 注销 {}", stats.total_registrations, stats.total_deregistrations);

    // 2. 演示分布式负载均衡器
    info!("⚖️ 演示分布式负载均衡器");
    let load_balancer = LoadBalancer::new(discovery.clone(), LoadBalancingStrategy::RoundRobin);
    
    // 模拟负载均衡请求
    for i in 0..10 {
        match load_balancer.select_instance("user-service").await {
            Ok(instance) => {
                info!("请求 {} 路由到实例 {}", i, instance.id);
                // 模拟请求结果
                let success = i % 7 != 0; // 85% 成功率
                load_balancer.record_request_result(&instance.id, success).await;
            }
            Err(e) => {
                warn!("请求 {} 失败: {}", i, e);
            }
        }
    }
    
    let lb_stats = load_balancer.get_stats().await;
    info!("负载均衡统计: 总请求 {}, 成功 {}, 失败 {}", 
          lb_stats.total_requests, lb_stats.successful_requests, lb_stats.failed_requests);

    // 3. 演示分布式消息队列
    info!("📨 演示分布式消息队列");
    let message_queue = DistributedMessageQueue::new();
    
    // 订阅主题
    for i in 0..3 {
        message_queue.subscribe("user-events".to_string(), format!("subscriber_{}", i)).await?;
    }
    
    // 发布消息
    for i in 0..10 {
        let payload = format!("用户事件 {}", i);
        message_queue.publish("user-events".to_string(), payload).await?;
    }
    
    // 消费消息
    for i in 0..3 {
        for j in 0..3 {
            if let Some(message) = message_queue.consume("user-events", &format!("subscriber_{}", i)).await? {
                info!("订阅者 {} 消费消息: {}", i, message.payload);
            }
        }
    }
    
    let queue_stats = message_queue.get_stats().await;
    info!("消息队列统计: 发布 {}, 消费 {}", queue_stats.total_published, queue_stats.total_consumed);

    // 4. 演示分布式配置管理
    info!("⚙️ 演示分布式配置管理");
    let config_manager = DistributedConfigManager::new();
    
    // 设置配置
    config_manager.set_config("database.url".to_string(), "postgresql://localhost:5432/mydb".to_string()).await?;
    config_manager.set_config("redis.host".to_string(), "localhost".to_string()).await?;
    config_manager.set_config("api.timeout".to_string(), "30".to_string()).await?;
    
    // 监听配置变化
    config_manager.watch_config("database.url".to_string(), "watcher_1".to_string()).await?;
    config_manager.watch_config("redis.host".to_string(), "watcher_2".to_string()).await?;
    
    // 更新配置
    config_manager.set_config("database.url".to_string(), "postgresql://prod-db:5432/mydb".to_string()).await?;
    
    // 获取配置
    if let Some(config) = config_manager.get_config("database.url").await? {
        info!("数据库配置: {} = {} (版本: {})", config.key, config.value, config.version);
    }
    
    let config_stats = config_manager.get_stats().await;
    info!("配置管理统计: 总配置 {}, 更新 {}, 通知 {}", 
          config_stats.total_configs, config_stats.config_updates, config_stats.watcher_notifications);

    info!("✅ 2025 年分布式异步模式演示完成!");
    
    Ok(())
}
