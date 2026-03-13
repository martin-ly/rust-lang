use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, broadcast, mpsc};
use tokio::time::sleep;
use tracing::{debug, error, info, warn};
use uuid::Uuid;

/// 2025年异步消息队列演示
/// 展示最新的异步消息队列编程模式和最佳实践

/// 1. 异步消息队列核心
#[derive(Debug, Clone)]
pub struct AsyncMessageQueue {
    queues: Arc<RwLock<HashMap<String, MessageQueue>>>,
    dead_letter_queues: Arc<RwLock<HashMap<String, VecDeque<Message>>>>,
    queue_stats: Arc<RwLock<QueueStats>>,
    global_config: QueueConfig,
    event_broadcaster: broadcast::Sender<QueueEvent>,
}

#[derive(Debug, Clone)]
pub struct MessageQueue {
    pub name: String,
    pub messages: VecDeque<Message>,
    pub max_size: usize,
    pub visibility_timeout: Duration,
    pub message_retention: Duration,
    pub dead_letter_queue: Option<String>,
    pub created_at: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub body: String,
    pub attributes: HashMap<String, String>,
    pub created_at: u64,
    pub visible_at: Option<u64>,
    pub receive_count: usize,
    pub max_receives: usize,
    pub priority: MessagePriority,
    pub delay_seconds: Option<Duration>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MessagePriority {
    Low,
    Normal,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct QueueConfig {
    pub default_visibility_timeout: Duration,
    pub default_message_retention: Duration,
    pub max_receive_count: usize,
    pub enable_dead_letter_queue: bool,
    pub batch_size: usize,
    pub polling_interval: Duration,
}

impl Default for QueueConfig {
    fn default() -> Self {
        Self {
            default_visibility_timeout: Duration::from_secs(300),
            default_message_retention: Duration::from_secs(1209600), // 14 days
            max_receive_count: 3,
            enable_dead_letter_queue: true,
            batch_size: 10,
            polling_interval: Duration::from_millis(100),
        }
    }
}

#[derive(Debug, Clone)]
pub enum QueueEvent {
    MessagePublished(String, Message),
    MessageReceived(String, String),
    MessageDeleted(String, String),
    MessageDeadLettered(String, String, String),
    QueueCreated(String),
    QueueDeleted(String),
}

#[derive(Debug, Clone, Default)]
pub struct QueueStats {
    pub total_queues: usize,
    pub total_messages: usize,
    pub messages_published: usize,
    pub messages_received: usize,
    pub messages_deleted: usize,
    pub dead_letter_messages: usize,
    pub total_polling_requests: usize,
}

impl AsyncMessageQueue {
    pub fn new(config: QueueConfig) -> Self {
        let (event_broadcaster, _) = broadcast::channel(1000);

        Self {
            queues: Arc::new(RwLock::new(HashMap::new())),
            dead_letter_queues: Arc::new(RwLock::new(HashMap::new())),
            queue_stats: Arc::new(RwLock::new(QueueStats::default())),
            global_config: config,
            event_broadcaster,
        }
    }

    pub async fn create_queue(&self, name: String, max_size: Option<usize>) -> Result<()> {
        let queue = MessageQueue {
            name: name.clone(),
            messages: VecDeque::new(),
            max_size: max_size.unwrap_or(10000),
            visibility_timeout: self.global_config.default_visibility_timeout,
            message_retention: self.global_config.default_message_retention,
            dead_letter_queue: if self.global_config.enable_dead_letter_queue {
                Some(format!("{}-dlq", name))
            } else {
                None
            },
            created_at: std::time::Instant::now(),
        };

        let mut queues = self.queues.write().await;
        queues.insert(name.clone(), queue);

        let mut stats = self.queue_stats.write().await;
        stats.total_queues += 1;

        // 创建死信队列
        if self.global_config.enable_dead_letter_queue {
            let mut dlqs = self.dead_letter_queues.write().await;
            dlqs.insert(format!("{}-dlq", name), VecDeque::new());
        }

        // 广播事件
        let _ = self
            .event_broadcaster
            .send(QueueEvent::QueueCreated(name.clone()));

        info!("创建消息队列: {}", name);
        Ok(())
    }

    pub async fn publish_message(&self, queue_name: &str, message: Message) -> Result<String> {
        let mut queues = self.queues.write().await;
        if let Some(queue) = queues.get_mut(queue_name) {
            // 检查队列大小限制
            if queue.messages.len() >= queue.max_size {
                return Err(anyhow::anyhow!("队列 {} 已满", queue_name));
            }

            queue.messages.push_back(message.clone());

            let mut stats = self.queue_stats.write().await;
            stats.total_messages += 1;
            stats.messages_published += 1;

            // 广播事件
            let _ = self.event_broadcaster.send(QueueEvent::MessagePublished(
                queue_name.to_string(),
                message.clone(),
            ));

            info!("发布消息到队列 {}: {}", queue_name, message.id);
            Ok(message.id)
        } else {
            Err(anyhow::anyhow!("队列 {} 不存在", queue_name))
        }
    }

    pub async fn receive_message(
        &self,
        queue_name: &str,
        visibility_timeout: Option<Duration>,
    ) -> Result<Option<ReceivedMessage>> {
        let mut queues = self.queues.write().await;
        if let Some(queue) = queues.get_mut(queue_name) {
            let timeout = visibility_timeout.unwrap_or(queue.visibility_timeout);
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();

            // 查找可见的消息
            for i in 0..queue.messages.len() {
                let message = &mut queue.messages[i];

                // 检查消息是否可见
                if message
                    .visible_at
                    .map_or(true, |visible_at| now >= visible_at)
                {
                    // 更新消息状态
                    message.receive_count += 1;
                    message.visible_at = Some(now + timeout.as_secs());

                    let mut stats = self.queue_stats.write().await;
                    stats.messages_received += 1;
                    stats.total_polling_requests += 1;

                    // 广播事件
                    let _ = self.event_broadcaster.send(QueueEvent::MessageReceived(
                        queue_name.to_string(),
                        message.id.clone(),
                    ));

                    let received_message = ReceivedMessage {
                        message: message.clone(),
                        receipt_handle: format!("receipt_{}", Uuid::new_v4()),
                        queue_name: queue_name.to_string(),
                    };

                    info!("接收消息: {} (队列: {})", message.id, queue_name);
                    return Ok(Some(received_message));
                }
            }

            let mut stats = self.queue_stats.write().await;
            stats.total_polling_requests += 1;

            Ok(None)
        } else {
            Err(anyhow::anyhow!("队列 {} 不存在", queue_name))
        }
    }

    pub async fn delete_message(&self, queue_name: &str, receipt_handle: &str) -> Result<()> {
        let mut queues = self.queues.write().await;
        if let Some(queue) = queues.get_mut(queue_name) {
            // 查找并删除消息
            if let Some(pos) = queue
                .messages
                .iter()
                .position(|msg| format!("receipt_{}", msg.id) == receipt_handle)
            {
                let message = queue.messages.remove(pos).unwrap();

                let mut stats = self.queue_stats.write().await;
                stats.total_messages -= 1;
                stats.messages_deleted += 1;

                // 广播事件
                let _ = self.event_broadcaster.send(QueueEvent::MessageDeleted(
                    queue_name.to_string(),
                    message.id.clone(),
                ));

                info!("删除消息: {} (队列: {})", message.id, queue_name);
                Ok(())
            } else {
                Err(anyhow::anyhow!("消息未找到"))
            }
        } else {
            Err(anyhow::anyhow!("队列 {} 不存在", queue_name))
        }
    }

    pub async fn cleanup_expired_messages(&self) -> Result<()> {
        let mut queues = self.queues.write().await;
        let mut dlqs = self.dead_letter_queues.write().await;
        let mut stats = self.queue_stats.write().await;

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let mut total_cleaned = 0;

        for (queue_name, queue) in queues.iter_mut() {
            let mut to_remove = Vec::new();
            let mut to_dlq = Vec::new();

            for (i, message) in queue.messages.iter().enumerate() {
                // 检查消息是否过期
                if (now - message.created_at) > queue.message_retention.as_secs() {
                    to_remove.push(i);
                    continue;
                }

                // 检查是否超过最大接收次数
                if message.receive_count >= self.global_config.max_receive_count {
                    to_dlq.push(i);
                    continue;
                }
            }

            // 移除过期消息
            for &i in to_remove.iter().rev() {
                queue.messages.remove(i);
                stats.total_messages -= 1;
                total_cleaned += 1;
            }

            // 移动到死信队列
            for &i in to_dlq.iter().rev() {
                if let Some(message) = queue.messages.remove(i) {
                    if let Some(dlq_name) = &queue.dead_letter_queue {
                        if let Some(dlq) = dlqs.get_mut(dlq_name) {
                            dlq.push_back(message.clone());

                            // 广播事件
                            let _ = self.event_broadcaster.send(QueueEvent::MessageDeadLettered(
                                queue_name.clone(),
                                message.id.clone(),
                                dlq_name.clone(),
                            ));

                            stats.dead_letter_messages += 1;
                            info!("消息移动到死信队列: {} -> {}", message.id, dlq_name);
                        }
                    }
                    stats.total_messages -= 1;
                }
            }
        }

        if total_cleaned > 0 {
            info!("清理过期消息: {} 个", total_cleaned);
        }

        Ok(())
    }

    pub async fn get_queue_stats(&self) -> QueueStats {
        self.queue_stats.read().await.clone()
    }
}

#[derive(Debug, Clone)]
pub struct ReceivedMessage {
    pub message: Message,
    pub receipt_handle: String,
    pub queue_name: String,
}

/// 2. 异步消息生产者
#[derive(Debug, Clone)]
pub struct AsyncMessageProducer {
    queue: AsyncMessageQueue,
    producer_config: ProducerConfig,
    producer_stats: Arc<RwLock<ProducerStats>>,
    batch_sender: mpsc::UnboundedSender<MessageBatch>,
}

#[derive(Debug, Clone)]
pub struct ProducerConfig {
    pub batch_size: usize,
    pub batch_timeout: Duration,
    pub retry_attempts: usize,
    pub retry_delay: Duration,
    pub enable_compression: bool,
    pub enable_encryption: bool,
}

impl Default for ProducerConfig {
    fn default() -> Self {
        Self {
            batch_size: 10,
            batch_timeout: Duration::from_millis(500),
            retry_attempts: 3,
            retry_delay: Duration::from_millis(100),
            enable_compression: false,
            enable_encryption: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MessageBatch {
    pub queue_name: String,
    pub messages: Vec<Message>,
    pub created_at: Instant,
    pub retry_count: usize,
}

#[derive(Debug, Clone, Default)]
pub struct ProducerStats {
    pub total_messages_sent: usize,
    pub successful_sends: usize,
    pub failed_sends: usize,
    pub batch_sends: usize,
    pub retry_attempts: usize,
}

impl AsyncMessageProducer {
    pub fn new(queue: AsyncMessageQueue, config: ProducerConfig) -> Self {
        let (batch_sender, mut batch_receiver) = mpsc::unbounded_channel();

        let producer = Self {
            queue: queue.clone(),
            producer_config: config,
            producer_stats: Arc::new(RwLock::new(ProducerStats::default())),
            batch_sender,
        };

        // 启动批处理任务
        let producer_clone = producer.clone();
        tokio::spawn(async move {
            while let Some(batch) = batch_receiver.recv().await {
                if let Err(e) = producer_clone.process_batch(batch).await {
                    error!("批处理失败: {}", e);
                }
            }
        });

        producer
    }

    pub async fn send_message(
        &self,
        queue_name: &str,
        body: String,
        attributes: Option<HashMap<String, String>>,
    ) -> Result<String> {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            body,
            attributes: attributes.unwrap_or_default(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            visible_at: None,
            receive_count: 0,
            max_receives: self.queue.global_config.max_receive_count,
            priority: MessagePriority::Normal,
            delay_seconds: None,
        };

        self.send_message_with_retry(queue_name, message).await
    }

    pub async fn send_message_with_priority(
        &self,
        queue_name: &str,
        body: String,
        priority: MessagePriority,
    ) -> Result<String> {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            body,
            attributes: HashMap::new(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            visible_at: None,
            receive_count: 0,
            max_receives: self.queue.global_config.max_receive_count,
            priority,
            delay_seconds: None,
        };

        self.send_message_with_retry(queue_name, message).await
    }

    pub async fn send_delayed_message(
        &self,
        queue_name: &str,
        body: String,
        delay: Duration,
    ) -> Result<String> {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            body,
            attributes: HashMap::new(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            visible_at: Some(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs()
                    + delay.as_secs(),
            ),
            receive_count: 0,
            max_receives: self.queue.global_config.max_receive_count,
            priority: MessagePriority::Normal,
            delay_seconds: Some(delay),
        };

        self.send_message_with_retry(queue_name, message).await
    }

    async fn send_message_with_retry(&self, queue_name: &str, message: Message) -> Result<String> {
        let mut last_error = None;

        for attempt in 0..=self.producer_config.retry_attempts {
            match self
                .queue
                .publish_message(queue_name, message.clone())
                .await
            {
                Ok(message_id) => {
                    let mut stats = self.producer_stats.write().await;
                    stats.successful_sends += 1;
                    stats.total_messages_sent += 1;

                    return Ok(message_id);
                }
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.producer_config.retry_attempts {
                        sleep(self.producer_config.retry_delay).await;

                        let mut stats = self.producer_stats.write().await;
                        stats.retry_attempts += 1;
                    }
                }
            }
        }

        let mut stats = self.producer_stats.write().await;
        stats.failed_sends += 1;

        Err(anyhow::anyhow!("发送消息失败: {:?}", last_error))
    }

    pub async fn send_batch(&self, queue_name: &str, messages: Vec<Message>) -> Result<()> {
        let batch = MessageBatch {
            queue_name: queue_name.to_string(),
            messages,
            created_at: std::time::Instant::now(),
            retry_count: 0,
        };

        let _ = self.batch_sender.send(batch);
        Ok(())
    }

    #[allow(unused_variables)]
    async fn process_batch(&self, batch: MessageBatch) -> Result<()> {
        let mut successful = 0;
        let mut failed = 0;

        for message in batch.messages {
            match self.queue.publish_message(&batch.queue_name, message).await {
                Ok(_) => successful += 1,
                Err(_) => failed += 1,
            }
        }

        let mut stats = self.producer_stats.write().await;
        stats.batch_sends += 1;
        stats.successful_sends += successful;
        stats.failed_sends += failed;
        stats.total_messages_sent += successful;

        info!("批处理完成: 成功 {}, 失败 {}", successful, failed);
        Ok(())
    }

    pub async fn get_producer_stats(&self) -> ProducerStats {
        self.producer_stats.read().await.clone()
    }
}

/// 3. 异步消息消费者
#[derive(Debug, Clone)]
pub struct AsyncMessageConsumer {
    queue: AsyncMessageQueue,
    consumer_config: ConsumerConfig,
    consumer_stats: Arc<RwLock<ConsumerStats>>,
    message_handlers: Arc<RwLock<HashMap<String, MessageHandler>>>,
    is_running: Arc<AtomicBool>,
}

#[derive(Debug, Clone)]
pub struct ConsumerConfig {
    pub max_concurrent_messages: usize,
    pub polling_interval: Duration,
    pub visibility_timeout: Duration,
    pub enable_auto_delete: bool,
    pub message_timeout: Duration,
    pub enable_dlq: bool,
}

impl Default for ConsumerConfig {
    fn default() -> Self {
        Self {
            max_concurrent_messages: 10,
            polling_interval: Duration::from_millis(100),
            visibility_timeout: Duration::from_secs(300),
            enable_auto_delete: true,
            message_timeout: Duration::from_secs(30),
            enable_dlq: true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MessageHandler {
    pub handler_id: String,
    pub queue_name: String,
    pub handler_fn: String, // 简化为字符串标识
    pub max_concurrent: usize,
    pub created_at: Instant,
}

#[derive(Debug, Clone, Default)]
pub struct ConsumerStats {
    pub total_messages_processed: usize,
    pub successful_processing: usize,
    pub failed_processing: usize,
    pub messages_deleted: usize,
    pub messages_returned: usize,
    pub processing_time: Duration,
}

impl AsyncMessageConsumer {
    pub fn new(queue: AsyncMessageQueue, config: ConsumerConfig) -> Self {
        Self {
            queue,
            consumer_config: config,
            consumer_stats: Arc::new(RwLock::new(ConsumerStats::default())),
            message_handlers: Arc::new(RwLock::new(HashMap::new())),
            is_running: Arc::new(AtomicBool::new(false)),
        }
    }

    pub async fn register_handler(&self, queue_name: &str, handler_id: &str) -> Result<()> {
        let handler = MessageHandler {
            handler_id: handler_id.to_string(),
            queue_name: queue_name.to_string(),
            handler_fn: format!("handler_{}", handler_id),
            max_concurrent: self.consumer_config.max_concurrent_messages,
            created_at: std::time::Instant::now(),
        };

        let mut handlers = self.message_handlers.write().await;
        handlers.insert(handler_id.to_string(), handler);

        info!("注册消息处理器: {} (队列: {})", handler_id, queue_name);
        Ok(())
    }

    pub async fn start_consuming(&self) -> Result<()> {
        if self.is_running.load(Ordering::Relaxed) {
            return Err(anyhow::anyhow!("消费者已在运行"));
        }

        self.is_running.store(true, Ordering::Relaxed);

        let handlers = self.message_handlers.read().await;
        let mut consumer_tasks = Vec::new();

        for (handler_id, handler) in handlers.iter() {
            let consumer_clone = self.clone();
            let handler_id_clone = handler_id.clone();
            let queue_name_clone = handler.queue_name.clone();

            let task = tokio::spawn(async move {
                consumer_clone
                    .consumer_loop(&handler_id_clone, &queue_name_clone)
                    .await;
            });

            consumer_tasks.push(task);
        }

        // 等待所有消费者任务
        for task in consumer_tasks {
            let _ = task.await;
        }

        Ok(())
    }

    #[allow(unused_variables)]
    async fn consumer_loop(&self, handler_id: &str, queue_name: &str) {
        let mut interval = tokio::time::interval(self.consumer_config.polling_interval);

        while self.is_running.load(Ordering::Relaxed) {
            interval.tick().await;

            match self
                .queue
                .receive_message(queue_name, Some(self.consumer_config.visibility_timeout))
                .await
            {
                Ok(Some(received_message)) => {
                    let start_time = Instant::now();

                    // 处理消息
                    match self.process_message(&received_message).await {
                        Ok(_) => {
                            // 删除消息
                            if self.consumer_config.enable_auto_delete {
                                let _ = self
                                    .queue
                                    .delete_message(
                                        &received_message.queue_name,
                                        &received_message.receipt_handle,
                                    )
                                    .await;
                            }

                            let mut stats = self.consumer_stats.write().await;
                            stats.successful_processing += 1;
                            stats.total_messages_processed += 1;
                            stats.processing_time += start_time.elapsed();

                            debug!("消息处理成功: {}", received_message.message.id);
                        }
                        Err(e) => {
                            let mut stats = self.consumer_stats.write().await;
                            stats.failed_processing += 1;
                            stats.total_messages_processed += 1;

                            warn!("消息处理失败: {} - {}", received_message.message.id, e);

                            // 检查是否需要移动到死信队列
                            if received_message.message.receive_count
                                >= self.queue.global_config.max_receive_count
                            {
                                info!(
                                    "消息达到最大接收次数，将移动到死信队列: {}",
                                    received_message.message.id
                                );
                            }
                        }
                    }
                }
                Ok(None) => {
                    // 没有消息，继续轮询
                }
                Err(e) => {
                    error!("接收消息失败: {}", e);
                }
            }
        }
    }

    async fn process_message(&self, received_message: &ReceivedMessage) -> Result<()> {
        // 模拟消息处理
        sleep(Duration::from_millis(50)).await;

        // 模拟处理可能失败
        if rand::random::<f64>() < 0.1 {
            return Err(anyhow::anyhow!("消息处理失败"));
        }

        info!(
            "处理消息: {} (内容: {})",
            received_message.message.id, received_message.message.body
        );
        Ok(())
    }

    pub async fn stop_consuming(&self) -> Result<()> {
        self.is_running.store(false, Ordering::Relaxed);
        info!("停止消息消费");
        Ok(())
    }

    pub async fn get_consumer_stats(&self) -> ConsumerStats {
        self.consumer_stats.read().await.clone()
    }
}

/// 4. 异步消息路由和过滤
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct AsyncMessageRouter {
    routes: Arc<RwLock<Vec<RouteRule>>>,
    router_stats: Arc<RwLock<RouterStats>>,
    routing_config: RoutingConfig,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct RouteRule {
    pub id: String,
    pub name: String,
    pub source_queue: String,
    pub target_queues: Vec<String>,
    pub filter_conditions: Vec<FilterCondition>,
    pub routing_strategy: RoutingStrategy,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum FilterCondition {
    AttributeEquals(String, String),
    AttributeContains(String, String),
    BodyContains(String),
    PriorityEquals(MessagePriority),
    CreatedAfter(Instant),
}

#[derive(Debug, Clone)]
pub enum RoutingStrategy {
    Broadcast,  // 广播到所有目标队列
    RoundRobin, // 轮询
    Priority,   // 基于优先级
    Hash,       // 基于哈希
}

#[derive(Debug, Clone)]
pub struct RoutingConfig {
    pub max_route_attempts: usize,
    pub route_timeout: Duration,
    pub enable_route_metrics: bool,
    pub default_routing_strategy: RoutingStrategy,
}

impl Default for RoutingConfig {
    fn default() -> Self {
        Self {
            max_route_attempts: 3,
            route_timeout: Duration::from_secs(30),
            enable_route_metrics: true,
            default_routing_strategy: RoutingStrategy::Broadcast,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct RouterStats {
    pub total_routed_messages: usize,
    pub successful_routes: usize,
    pub failed_routes: usize,
    pub filtered_messages: usize,
    pub routing_time: Duration,
}

impl AsyncMessageRouter {
    pub fn new(config: RoutingConfig) -> Self {
        Self {
            routes: Arc::new(RwLock::new(Vec::new())),
            router_stats: Arc::new(RwLock::new(RouterStats::default())),
            routing_config: config,
        }
    }

    pub async fn add_route(&self, rule: RouteRule) -> Result<()> {
        let mut routes = self.routes.write().await;
        routes.push(rule.clone());

        info!(
            "添加路由规则: {} (源队列: {}, 目标队列: {:?})",
            rule.name, rule.source_queue, rule.target_queues
        );
        Ok(())
    }

    pub async fn route_message(&self, source_queue: &str, message: Message) -> Result<Vec<String>> {
        let start_time = Instant::now();
        let routes = self.routes.read().await;

        let mut routed_queues = Vec::new();

        for route in routes.iter() {
            if route.source_queue == source_queue && route.enabled {
                // 检查过滤条件
                if self
                    .matches_filters(&message, &route.filter_conditions)
                    .await
                {
                    // 选择目标队列
                    let target_queues = self.select_target_queues(&route, &message).await;

                    for target_queue in target_queues {
                        routed_queues.push(target_queue);
                    }
                }
            }
        }

        let routing_time = start_time.elapsed();
        let mut stats = self.router_stats.write().await;
        stats.total_routed_messages += 1;
        stats.successful_routes += routed_queues.len();
        stats.routing_time += routing_time;

        if routed_queues.is_empty() {
            stats.filtered_messages += 1;
        }

        info!(
            "消息路由: {} -> {:?} (耗时: {:?})",
            message.id, routed_queues, routing_time
        );
        Ok(routed_queues)
    }

    async fn matches_filters(&self, message: &Message, conditions: &[FilterCondition]) -> bool {
        for condition in conditions {
            match condition {
                FilterCondition::AttributeEquals(key, value) => {
                    if message.attributes.get(key) != Some(value) {
                        return false;
                    }
                }
                FilterCondition::AttributeContains(key, value) => {
                    if let Some(attr_value) = message.attributes.get(key) {
                        if !attr_value.contains(value) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                FilterCondition::BodyContains(value) => {
                    if !message.body.contains(value) {
                        return false;
                    }
                }
                FilterCondition::PriorityEquals(priority) => {
                    if &message.priority != priority {
                        return false;
                    }
                }
                FilterCondition::CreatedAfter(time) => {
                    // 将 Instant 转换为 u64 时间戳（毫秒）
                    let time_ms = time.elapsed().as_millis() as u64;
                    if message.created_at <= time_ms {
                        return false;
                    }
                }
            }
        }
        true
    }

    async fn select_target_queues(&self, route: &RouteRule, message: &Message) -> Vec<String> {
        match &route.routing_strategy {
            RoutingStrategy::Broadcast => route.target_queues.clone(),
            RoutingStrategy::RoundRobin => {
                let index = (std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
                    - message.created_at as u128) as usize
                    % route.target_queues.len();
                vec![route.target_queues[index].clone()]
            }
            RoutingStrategy::Priority => {
                let target_count = match message.priority {
                    MessagePriority::Critical => route.target_queues.len(),
                    MessagePriority::High => (route.target_queues.len() + 1) / 2,
                    MessagePriority::Normal => 1,
                    MessagePriority::Low => 1,
                };

                route
                    .target_queues
                    .iter()
                    .take(target_count)
                    .cloned()
                    .collect()
            }
            RoutingStrategy::Hash => {
                let hash = self.hash_message(&message);
                let index = (hash as usize) % route.target_queues.len();
                vec![route.target_queues[index].clone()]
            }
        }
    }

    fn hash_message(&self, message: &Message) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        message.id.hash(&mut hasher);
        hasher.finish()
    }

    pub async fn get_router_stats(&self) -> RouterStats {
        self.router_stats.read().await.clone()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    info!("🚀 开始 2025 年异步消息队列演示");

    // 1. 演示异步消息队列核心
    info!("📨 演示异步消息队列核心");
    let config = QueueConfig::default();
    let queue = AsyncMessageQueue::new(config);

    // 创建队列
    queue
        .create_queue("user-events".to_string(), Some(1000))
        .await?;
    queue
        .create_queue("order-events".to_string(), Some(500))
        .await?;
    queue
        .create_queue("notification-queue".to_string(), None)
        .await?;

    // 发布消息
    for i in 0..10 {
        let message = Message {
            id: Uuid::new_v4().to_string(),
            body: format!("用户事件 {}", i),
            attributes: [("event_type".to_string(), "user_action".to_string())]
                .iter()
                .cloned()
                .collect(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            visible_at: None,
            receive_count: 0,
            max_receives: 3,
            priority: MessagePriority::Normal,
            delay_seconds: None,
        };

        queue.publish_message("user-events", message).await?;
    }

    // 接收消息
    for _ in 0..5 {
        if let Some(received_message) = queue.receive_message("user-events", None).await? {
            info!(
                "接收消息: {} -> {}",
                received_message.message.id, received_message.message.body
            );

            // 模拟处理消息
            sleep(Duration::from_millis(100)).await;

            // 删除消息
            queue
                .delete_message("user-events", &received_message.receipt_handle)
                .await?;
        }
    }

    let queue_stats = queue.get_queue_stats().await;
    info!(
        "队列统计: 总队列 {}, 发布 {}, 接收 {}, 删除 {}",
        queue_stats.total_queues,
        queue_stats.messages_published,
        queue_stats.messages_received,
        queue_stats.messages_deleted
    );

    // 2. 演示异步消息生产者
    info!("📤 演示异步消息生产者");
    let producer_config = ProducerConfig::default();
    let producer = AsyncMessageProducer::new(queue.clone(), producer_config);

    // 发送普通消息
    for i in 0..5 {
        let body = format!("生产者消息 {}", i);
        let attributes = [("source".to_string(), "producer_demo".to_string())]
            .iter()
            .cloned()
            .collect();
        producer
            .send_message("user-events", body, Some(attributes))
            .await?;
    }

    // 发送优先级消息
    producer
        .send_message_with_priority(
            "user-events",
            "高优先级消息".to_string(),
            MessagePriority::High,
        )
        .await?;

    // 发送延迟消息
    producer
        .send_delayed_message(
            "user-events",
            "延迟消息".to_string(),
            Duration::from_secs(1),
        )
        .await?;

    // 批量发送消息
    let batch_messages = (0..3)
        .map(|i| Message {
            id: Uuid::new_v4().to_string(),
            body: format!("批量消息 {}", i),
            attributes: HashMap::new(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            visible_at: None,
            receive_count: 0,
            max_receives: 3,
            priority: MessagePriority::Normal,
            delay_seconds: None,
        })
        .collect();

    producer.send_batch("user-events", batch_messages).await?;

    let producer_stats = producer.get_producer_stats().await;
    info!(
        "生产者统计: 总发送 {}, 成功 {}, 失败 {}",
        producer_stats.total_messages_sent,
        producer_stats.successful_sends,
        producer_stats.failed_sends
    );

    // 3. 演示异步消息消费者
    info!("📥 演示异步消息消费者");
    let consumer_config = ConsumerConfig::default();
    let consumer = AsyncMessageConsumer::new(queue.clone(), consumer_config);

    // 注册处理器
    consumer
        .register_handler("user-events", "user_event_handler")
        .await?;
    consumer
        .register_handler("order-events", "order_event_handler")
        .await?;

    // 启动消费者（短时间运行）
    let consumer_clone = consumer.clone();
    let consumer_task = tokio::spawn(async move { consumer_clone.start_consuming().await });

    // 让消费者运行一段时间
    sleep(Duration::from_millis(1000)).await;

    // 停止消费者
    consumer.stop_consuming().await?;
    consumer_task.abort();

    let consumer_stats = consumer.get_consumer_stats().await;
    info!(
        "消费者统计: 总处理 {}, 成功 {}, 失败 {}",
        consumer_stats.total_messages_processed,
        consumer_stats.successful_processing,
        consumer_stats.failed_processing
    );

    // 4. 演示异步消息路由和过滤
    info!("🛣️ 演示异步消息路由和过滤");
    let routing_config = RoutingConfig::default();
    let router = AsyncMessageRouter::new(routing_config);

    // 添加路由规则
    let route_rule = RouteRule {
        id: "route_1".to_string(),
        name: "用户事件路由".to_string(),
        source_queue: "user-events".to_string(),
        target_queues: vec!["notification-queue".to_string(), "order-events".to_string()],
        filter_conditions: vec![
            FilterCondition::AttributeEquals("event_type".to_string(), "user_action".to_string()),
            FilterCondition::PriorityEquals(MessagePriority::High),
        ],
        routing_strategy: RoutingStrategy::Broadcast,
        enabled: true,
    };

    router.add_route(route_rule).await?;

    // 创建测试消息并路由
    let test_message = Message {
        id: Uuid::new_v4().to_string(),
        body: "测试路由消息".to_string(),
        attributes: [("event_type".to_string(), "user_action".to_string())]
            .iter()
            .cloned()
            .collect(),
        created_at: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        visible_at: None,
        receive_count: 0,
        max_receives: 3,
        priority: MessagePriority::High,
        delay_seconds: None,
    };

    let routed_queues = router.route_message("user-events", test_message).await?;
    info!("消息路由结果: {:?}", routed_queues);

    let router_stats = router.get_router_stats().await;
    info!(
        "路由器统计: 总路由 {}, 成功路由 {}, 过滤消息 {}",
        router_stats.total_routed_messages,
        router_stats.successful_routes,
        router_stats.filtered_messages
    );

    // 清理过期消息
    queue.cleanup_expired_messages().await?;

    info!("✅ 2025 年异步消息队列演示完成!");

    Ok(())
}
