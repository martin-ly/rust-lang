//! 消息队列管理器
//! 
//! 提供统一的消息队列管理和事件处理

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, broadcast};
use uuid::Uuid;
use chrono::{DateTime, Utc};
use std::time::Duration;

use super::queue::MessageQueue;
use super::producer::MessageProducer;
use super::consumer::MessageConsumer;
use super::broker::MessageBroker;
use super::events::Event;

/// 消息队列管理器
#[derive(Debug)]
pub struct MessagingManager {
    queues: Arc<RwLock<HashMap<String, Arc<MessageQueue>>>>,
    producers: Arc<RwLock<HashMap<String, Arc<MessageProducer>>>>,
    consumers: Arc<RwLock<HashMap<String, Arc<MessageConsumer>>>>,
    brokers: Arc<RwLock<HashMap<String, Arc<MessageBroker>>>>,
    event_sender: broadcast::Sender<Event>,
    config: MessagingConfig,
}

/// 消息队列配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessagingConfig {
    pub default_queue_size: usize,
    pub max_message_size: usize,
    pub message_ttl: Duration,
    pub retry_attempts: u32,
    pub retry_delay: Duration,
    pub dead_letter_queue: Option<String>,
    pub persistence_enabled: bool,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
}

impl Default for MessagingConfig {
    fn default() -> Self {
        Self {
            default_queue_size: 10000,
            max_message_size: 1024 * 1024, // 1MB
            message_ttl: Duration::from_secs(3600), // 1 hour
            retry_attempts: 3,
            retry_delay: Duration::from_secs(5),
            dead_letter_queue: Some("dead_letter".to_string()),
            persistence_enabled: true,
            compression_enabled: true,
            encryption_enabled: false,
        }
    }
}

/// 消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub topic: String,
    pub payload: serde_json::Value,
    pub headers: HashMap<String, String>,
    pub priority: MessagePriority,
    pub created_at: DateTime<Utc>,
    pub expires_at: Option<DateTime<Utc>>,
    pub retry_count: u32,
    pub correlation_id: Option<String>,
    pub reply_to: Option<String>,
}

/// 消息优先级
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessagePriority {
    Low,
    Normal,
    High,
    Critical,
}

/// 消息状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageStatus {
    Pending,
    Processing,
    Completed,
    Failed,
    DeadLetter,
}

/// 消息处理结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageResult {
    pub message_id: String,
    pub status: MessageStatus,
    pub processed_at: DateTime<Utc>,
    pub error: Option<String>,
    pub retry_count: u32,
}

/// 队列统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueStats {
    pub queue_name: String,
    pub message_count: u64,
    pub consumer_count: u32,
    pub producer_count: u32,
    pub messages_per_second: f64,
    pub average_processing_time: Duration,
    pub error_rate: f64,
    pub last_updated: DateTime<Utc>,
}

impl Default for QueueStats {
    fn default() -> Self {
        Self {
            queue_name: String::new(),
            message_count: 0,
            consumer_count: 0,
            producer_count: 0,
            messages_per_second: 0.0,
            average_processing_time: Duration::from_secs(0),
            error_rate: 0.0,
            last_updated: Utc::now(),
        }
    }
}

/// 消息订阅
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageSubscription {
    pub id: String,
    pub topic: String,
    pub consumer_id: String,
    pub filter: Option<MessageFilter>,
    pub created_at: DateTime<Utc>,
    pub is_active: bool,
}

/// 消息过滤器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessageFilter {
    pub headers: HashMap<String, String>,
    pub payload_pattern: Option<String>,
    pub priority: Option<MessagePriority>,
}

impl MessagingManager {
    /// 创建新的消息队列管理器
    pub fn new(config: MessagingConfig) -> Self {
        let (event_sender, _) = broadcast::channel(1000);
        
        Self {
            queues: Arc::new(RwLock::new(HashMap::new())),
            producers: Arc::new(RwLock::new(HashMap::new())),
            consumers: Arc::new(RwLock::new(HashMap::new())),
            brokers: Arc::new(RwLock::new(HashMap::new())),
            event_sender,
            config,
        }
    }

    /// 创建消息队列
    pub async fn create_queue(&self, name: String, config: Option<QueueConfig>) -> Result<Arc<MessageQueue>> {
        let _queue_config = config.unwrap_or_else(|| QueueConfig {
            max_size: self.config.default_queue_size,
            message_ttl: self.config.message_ttl,
            dead_letter_queue: self.config.dead_letter_queue.clone(),
            persistence_enabled: self.config.persistence_enabled,
            compression_enabled: self.config.compression_enabled,
            encryption_enabled: self.config.encryption_enabled,
        });

        let queue = Arc::new(MessageQueue::new(name.clone()));
        
        {
            let mut queues = self.queues.write().await;
            queues.insert(name.clone(), queue.clone());
        }

        // 发送队列创建事件
        let event = Event::QueueCreated {
            queue_id: name.clone(),
            queue_name: name,
            created_at: Utc::now(),
        };
        let _ = self.event_sender.send(event);

        Ok(queue)
    }

    /// 创建消息生产者
    pub async fn create_producer(&self, queue_name: &str, config: Option<ProducerConfig>) -> Result<Arc<MessageProducer>> {
        let _queue = self.get_queue(queue_name).await?;
        let _producer_config = config.unwrap_or_default();
        
        let producer = Arc::new(MessageProducer::new("producer".to_string()));

        let producer_id = producer.get_id().clone();
        {
            let mut producers = self.producers.write().await;
            producers.insert(producer_id.to_string(), producer.clone());
        }

        Ok(producer)
    }

    /// 创建消息消费者
    pub async fn create_consumer(&self, queue_name: &str, config: Option<ConsumerConfig>) -> Result<Arc<MessageConsumer>> {
        let _queue = self.get_queue(queue_name).await?;
        let _consumer_config = config.unwrap_or_default();
        
        let consumer = Arc::new(MessageConsumer::new("consumer".to_string()));

        let consumer_id = consumer.get_id().clone();
        {
            let mut consumers = self.consumers.write().await;
            consumers.insert(consumer_id.to_string(), consumer.clone());
        }

        Ok(consumer)
    }

    /// 发布消息
    pub async fn publish(&self, topic: &str, payload: serde_json::Value, headers: Option<HashMap<String, String>>) -> Result<String> {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            topic: topic.to_string(),
            payload,
            headers: headers.unwrap_or_default(),
            priority: MessagePriority::Normal,
            created_at: Utc::now(),
            expires_at: Some(Utc::now() + chrono::Duration::from_std(self.config.message_ttl).unwrap_or_default()),
            retry_count: 0,
            correlation_id: None,
            reply_to: None,
        };

        // 发送到默认队列或根据topic路由
        let queue = self.get_queue(topic).await?;
        queue.enqueue(message.clone()).await?;

        // 发送消息发布事件
        let event = Event::MessagePublished {
            message_id: message.id.clone(),
            queue_id: topic.to_string(),
            published_at: Utc::now(),
        };
        let _ = self.event_sender.send(event);

        Ok(message.id)
    }

    /// 订阅消息
    pub async fn subscribe<F>(&self, topic: &str, handler: F) -> Result<String>
    where
        F: Fn(Message) -> anyhow::Result<()> + Send + Sync + 'static,
    {
        let consumer = self.create_consumer(topic, None).await?;
        let subscription_id = consumer.subscribe(Box::new(handler)).await?;

        // 发送订阅事件
        let event = Event::SubscriptionCreated {
            subscription_id: subscription_id.clone(),
            queue_id: topic.to_string(),
            consumer_id: "consumer".to_string(),
            created_at: Utc::now(),
        };
        let _ = self.event_sender.send(event);

        Ok(subscription_id)
    }

    /// 取消订阅
    pub async fn unsubscribe(&self, subscription_id: &str) -> Result<()> {
        // 查找并取消订阅
        let consumers = self.consumers.read().await;
        for consumer in consumers.values() {
            if consumer.unsubscribe(subscription_id).await.is_ok() {
                break;
            }
        }

        // 发送取消订阅事件
        let event = Event::SubscriptionCancelled {
            subscription_id: subscription_id.to_string(),
            queue_id: "queue".to_string(),
            cancelled_at: Utc::now(),
        };
        let _ = self.event_sender.send(event);

        Ok(())
    }

    /// 获取队列
    async fn get_queue(&self, name: &str) -> Result<Arc<MessageQueue>> {
        let queues = self.queues.read().await;
        queues.get(name)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Queue not found: {}", name))
    }

    /// 获取队列统计
    pub async fn get_queue_stats(&self, queue_name: &str) -> Result<QueueStats> {
        let queue = self.get_queue(queue_name).await?;
        Ok(queue.get_stats().await)
    }

    /// 获取所有队列统计
    pub async fn get_all_queue_stats(&self) -> HashMap<String, QueueStats> {
        let queues = self.queues.read().await;
        let mut stats = HashMap::new();

        for (name, queue) in queues.iter() {
            stats.insert(name.clone(), queue.get_stats().await);
        }

        stats
    }

    /// 获取消息
    pub async fn get_message(&self, queue_name: &str, message_id: &str) -> Result<Option<Message>> {
        let queue = self.get_queue(queue_name).await?;
        queue.get_message(message_id).await
    }

    /// 删除消息
    pub async fn delete_message(&self, queue_name: &str, message_id: &str) -> Result<()> {
        let queue = self.get_queue(queue_name).await?;
        queue.delete_message(message_id).await
    }

    /// 清空队列
    pub async fn clear_queue(&self, queue_name: &str) -> Result<()> {
        let queue = self.get_queue(queue_name).await?;
        queue.clear().await
    }

    /// 删除队列
    pub async fn delete_queue(&self, queue_name: &str) -> Result<()> {
        {
            let mut queues = self.queues.write().await;
            queues.remove(queue_name);
        }

        // 发送队列删除事件
        let event = Event::QueueDeleted {
            queue_id: queue_name.to_string(),
            queue_name: queue_name.to_string(),
            deleted_at: Utc::now(),
        };
        let _ = self.event_sender.send(event);

        Ok(())
    }

    /// 获取事件接收器
    pub fn get_event_receiver(&self) -> broadcast::Receiver<Event> {
        self.event_sender.subscribe()
    }

    /// 健康检查
    pub async fn health_check(&self) -> MessagingHealthStatus {
        let queues = self.queues.read().await;
        let producers = self.producers.read().await;
        let consumers = self.consumers.read().await;

        let mut status = MessagingHealthStatus {
            total_queues: queues.len(),
            total_producers: producers.len(),
            total_consumers: consumers.len(),
            healthy_queues: 0,
            unhealthy_queues: 0,
            queue_details: HashMap::new(),
        };

        for (name, queue) in queues.iter() {
            let stats = queue.get_stats().await;
            let is_healthy = stats.error_rate < 0.1; // 错误率低于10%认为健康

            if is_healthy {
                status.healthy_queues += 1;
            } else {
                status.unhealthy_queues += 1;
            }

            status.queue_details.insert(name.clone(), QueueHealthDetail {
                is_healthy,
                stats,
            });
        }

        status
    }

    /// 清理过期消息
    pub async fn cleanup_expired_messages(&self) -> Result<CleanupResult> {
        let queues = self.queues.read().await;
        let mut result = CleanupResult {
            deleted_messages: 0,
            freed_space: 0,
            errors: Vec::new(),
        };

        for (name, queue) in queues.iter() {
            match queue.cleanup_expired().await {
                Ok(_cleanup_result) => {
                    // TODO: Handle cleanup result fields
                    result.deleted_messages += 0;
                    result.freed_space += 0;
                }
                Err(e) => {
                    result.errors.push(format!("Queue {}: {}", name, e));
                }
            }
        }

        Ok(result)
    }

    /// 批量操作
    pub async fn batch_publish(&self, messages: Vec<(String, serde_json::Value)>) -> Result<Vec<String>> {
        let mut message_ids = Vec::new();

        for (topic, payload) in messages {
            match self.publish(&topic, payload, None).await {
                Ok(message_id) => message_ids.push(message_id),
                Err(e) => {
                    // 记录错误但继续处理其他消息
                    eprintln!("Failed to publish message to topic {}: {}", topic, e);
                }
            }
        }

        Ok(message_ids)
    }

    /// 获取消息历史
    pub async fn get_message_history(&self, queue_name: &str, limit: Option<usize>) -> Result<Vec<Message>> {
        let queue = self.get_queue(queue_name).await?;
        queue.get_message_history(limit.unwrap_or(100)).await
    }

    /// 重试失败的消息
    pub async fn retry_failed_messages(&self, queue_name: &str) -> Result<u32> {
        let queue = self.get_queue(queue_name).await?;
        queue.retry_failed_messages().await
    }

    /// 移动到死信队列
    pub async fn move_to_dead_letter(&self, queue_name: &str, message_id: &str) -> Result<()> {
        let queue = self.get_queue(queue_name).await?;
        queue.move_to_dead_letter(message_id).await
    }
}

/// 队列配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueConfig {
    pub max_size: usize,
    pub message_ttl: Duration,
    pub dead_letter_queue: Option<String>,
    pub persistence_enabled: bool,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
}

/// 生产者配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProducerConfig {
    pub batch_size: usize,
    pub flush_interval: Duration,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
}

impl Default for ProducerConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            flush_interval: Duration::from_secs(1),
            compression_enabled: true,
            encryption_enabled: false,
        }
    }
}

/// 消费者配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsumerConfig {
    pub batch_size: usize,
    pub poll_interval: Duration,
    pub max_concurrent_messages: usize,
    pub auto_ack: bool,
    pub prefetch_count: usize,
}

impl Default for ConsumerConfig {
    fn default() -> Self {
        Self {
            batch_size: 10,
            poll_interval: Duration::from_millis(100),
            max_concurrent_messages: 5,
            auto_ack: true,
            prefetch_count: 10,
        }
    }
}

/// 消息队列健康状态
#[derive(Debug, Serialize, Deserialize)]
pub struct MessagingHealthStatus {
    pub total_queues: usize,
    pub total_producers: usize,
    pub total_consumers: usize,
    pub healthy_queues: usize,
    pub unhealthy_queues: usize,
    pub queue_details: HashMap<String, QueueHealthDetail>,
}

/// 队列健康详情
#[derive(Debug, Serialize, Deserialize)]
pub struct QueueHealthDetail {
    pub is_healthy: bool,
    pub stats: QueueStats,
}

/// 清理结果
#[derive(Debug, Serialize, Deserialize)]
pub struct CleanupResult {
    pub deleted_messages: u64,
    pub freed_space: u64,
    pub errors: Vec<String>,
}
