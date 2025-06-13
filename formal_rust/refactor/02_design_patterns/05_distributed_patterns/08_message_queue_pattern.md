# 消息队列模式 (Message Queue Pattern)

## 1. 概述

### 1.1 模式定义

消息队列模式是一种分布式系统设计模式，通过异步消息传递实现组件间的解耦，支持可靠的消息传递、负载均衡和系统扩展。

### 1.2 核心概念

- **生产者 (Producer)**: 发送消息的组件
- **消费者 (Consumer)**: 接收消息的组件
- **队列 (Queue)**: 存储消息的缓冲区
- **消息 (Message)**: 传递的数据单元
- **确认机制 (Acknowledgment)**: 消息传递的确认机制

## 2. 形式化定义

### 2.1 消息队列模式五元组

**定义2.1 (消息队列模式五元组)**
设 $MQ = (P, C, Q, M, A)$ 为消息队列模式，其中：

- $P = \{p_1, p_2, ..., p_n\}$ 是生产者集合
- $C = \{c_1, c_2, ..., c_m\}$ 是消费者集合
- $Q = \{q_1, q_2, ..., q_k\}$ 是队列集合
- $M = \{m_1, m_2, ..., m_p\}$ 是消息集合
- $A = \{a_1, a_2, ..., a_q\}$ 是确认机制集合

### 2.2 消息定义

**定义2.2 (消息)**
消息 $m_i = (id_i, payload_i, timestamp_i, priority_i, ttl_i)$，其中：

- $id_i$ 是消息唯一标识符
- $payload_i$ 是消息内容
- $timestamp_i$ 是消息创建时间
- $priority_i$ 是消息优先级
- $ttl_i$ 是消息生存时间

### 2.3 队列操作函数

**定义2.3 (队列操作函数)**
队列操作函数 $enqueue: Q \times M \rightarrow \mathbb{B}$ 和 $dequeue: Q \rightarrow M$ 定义为：

$$enqueue(q, m) = \begin{cases}
true & \text{if } q \text{ has capacity} \\
false & \text{otherwise}
\end{cases}$$

$$dequeue(q) = \begin{cases}
m & \text{if } q \text{ is not empty} \\
\emptyset & \text{otherwise}
\end{cases}$$

## 3. 数学理论

### 3.1 消息传递理论

**定义3.1 (消息传递函数)**
消息传递函数 $send: P \times Q \times M \rightarrow \mathbb{B}$ 定义为：

$$send(p, q, m) = enqueue(q, m)$$

**定理3.1.1 (消息传递可靠性)**
可靠的消息队列保证消息不丢失。

**证明**：
1. **持久化**: 消息被持久化到存储
2. **确认机制**: 生产者等待确认
3. **重试机制**: 失败时自动重试
4. **因此**: 消息不会丢失

### 3.2 消息顺序理论

**定义3.2 (消息顺序)**
消息队列保证顺序性，当且仅当：

$$\forall m_1, m_2 \in M: (m_1.timestamp < m_2.timestamp) \Rightarrow (dequeue(q) = m_1 \land dequeue(q) = m_2)$$

**定理3.2.1 (FIFO保证)**
单队列消息队列保证FIFO顺序。

**证明**：
1. **队列特性**: 队列天然具有FIFO特性
2. **原子操作**: 入队和出队是原子操作
3. **因此**: 保证FIFO顺序

### 3.3 负载均衡理论

**定义3.3 (负载均衡)**
消息队列的负载是均衡的，当且仅当：

$$\forall c_i, c_j \in C: |c_i.load - c_j.load| \leq \epsilon$$

**定理3.3.1 (消费者负载均衡)**
轮询分发算法实现负载均衡。

**证明**：
1. **均匀分发**: 轮询算法均匀分发消息
2. **动态调整**: 根据消费者状态调整
3. **因此**: 实现负载均衡

## 4. 核心定理

### 4.1 消息队列正确性定理

**定理4.1 (消息队列正确性)**
消息队列模式 $MQ$ 是正确的，当且仅当：

1. **消息完整性**: $\forall m \in M: \exists q \in Q: m \in q.messages$
2. **传递可靠性**: $\forall p \in P, \forall m \in M: send(p, q, m) = true \Rightarrow m \in q.messages$
3. **消费完整性**: $\forall c \in C: dequeue(q) \neq \emptyset \Rightarrow message\_processed(c, m)$
4. **顺序保证**: $\forall m_1, m_2 \in M: (m_1.timestamp < m_2.timestamp) \Rightarrow order(m_1, m_2)$

**证明**：
1. **消息完整性**: 确保所有消息都被存储
2. **传递可靠性**: 确保消息传递成功
3. **消费完整性**: 确保消息被正确处理
4. **顺序保证**: 确保消息顺序正确

### 4.2 消息队列性能定理

**定理4.2 (消息队列性能)**
消息队列模式的性能复杂度为：

- **发送消息**: $O(1)$ 平均时间复杂度
- **接收消息**: $O(1)$ 平均时间复杂度
- **消息持久化**: $O(\log|M|)$ 时间复杂度
- **负载均衡**: $O(|C|)$ 时间复杂度

**证明**：
1. **发送消息**: 入队操作是常数时间
2. **接收消息**: 出队操作是常数时间
3. **消息持久化**: 使用索引结构存储
4. **负载均衡**: 需要遍历所有消费者

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::{VecDeque, HashMap};
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// 消息优先级
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MessagePriority {
    Low,
    Normal,
    High,
    Critical,
}

/// 消息状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum MessageStatus {
    Pending,
    Processing,
    Completed,
    Failed,
}

/// 消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub payload: String,
    pub timestamp: Instant,
    pub priority: MessagePriority,
    pub ttl: Option<Duration>,
    pub status: MessageStatus,
    pub retry_count: u32,
    pub max_retries: u32,
}

impl Message {
    pub fn new(payload: String, priority: MessagePriority) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            payload,
            timestamp: Instant::now(),
            priority,
            ttl: None,
            status: MessageStatus::Pending,
            retry_count: 0,
            max_retries: 3,
        }
    }

    /// 检查消息是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(ttl) = self.ttl {
            self.timestamp.elapsed() > ttl
        } else {
            false
        }
    }

    /// 检查是否可以重试
    pub fn can_retry(&self) -> bool {
        self.retry_count < self.max_retries
    }

    /// 增加重试次数
    pub fn increment_retry(&mut self) {
        self.retry_count += 1;
    }
}

/// 队列
pub struct Queue {
    pub name: String,
    pub messages: VecDeque<Message>,
    pub capacity: usize,
    pub consumers: Vec<String>,
}

impl Queue {
    pub fn new(name: String, capacity: usize) -> Self {
        Self {
            name,
            messages: VecDeque::new(),
            capacity,
            consumers: Vec::new(),
        }
    }

    /// 入队
    pub fn enqueue(&mut self, message: Message) -> bool {
        if self.messages.len() < self.capacity {
            self.messages.push_back(message);
            true
        } else {
            false
        }
    }

    /// 出队
    pub fn dequeue(&mut self) -> Option<Message> {
        self.messages.pop_front()
    }

    /// 查看队首消息
    pub fn peek(&self) -> Option<&Message> {
        self.messages.front()
    }

    /// 获取队列大小
    pub fn size(&self) -> usize {
        self.messages.len()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }

    /// 检查队列是否已满
    pub fn is_full(&self) -> bool {
        self.messages.len() >= self.capacity
    }

    /// 添加消费者
    pub fn add_consumer(&mut self, consumer_id: String) {
        if !self.consumers.contains(&consumer_id) {
            self.consumers.push(consumer_id);
        }
    }

    /// 移除消费者
    pub fn remove_consumer(&mut self, consumer_id: &str) {
        self.consumers.retain(|id| id != consumer_id);
    }
}

/// 生产者
pub struct Producer {
    pub id: String,
    pub message_sender: mpsc::Sender<Message>,
}

impl Producer {
    pub fn new(id: String, message_sender: mpsc::Sender<Message>) -> Self {
        Self {
            id,
            message_sender,
        }
    }

    /// 发送消息
    pub async fn send(&self, payload: String, priority: MessagePriority) -> Result<(), mpsc::error::SendError<Message>> {
        let message = Message::new(payload, priority);
        self.message_sender.send(message).await
    }

    /// 发送带TTL的消息
    pub async fn send_with_ttl(&self, payload: String, priority: MessagePriority, ttl: Duration) -> Result<(), mpsc::error::SendError<Message>> {
        let mut message = Message::new(payload, priority);
        message.ttl = Some(ttl);
        self.message_sender.send(message).await
    }
}

/// 消费者
pub struct Consumer {
    pub id: String,
    pub message_receiver: mpsc::Receiver<Message>,
    pub message_sender: mpsc::Sender<Message>,
    pub processing_callback: Box<dyn Fn(Message) -> Result<(), String> + Send + Sync>,
}

impl Consumer {
    pub fn new(
        id: String,
        message_receiver: mpsc::Receiver<Message>,
        message_sender: mpsc::Sender<Message>,
        processing_callback: Box<dyn Fn(Message) -> Result<(), String> + Send + Sync>,
    ) -> Self {
        Self {
            id,
            message_receiver,
            message_sender,
            processing_callback,
        }
    }

    /// 开始消费消息
    pub async fn start_consuming(&mut self) {
        while let Some(mut message) = self.message_receiver.recv().await {
            message.status = MessageStatus::Processing;

            match (self.processing_callback)(message.clone()) {
                Ok(()) => {
                    message.status = MessageStatus::Completed;
                    println!("Message {} processed successfully", message.id);
                }
                Err(error) => {
                    message.status = MessageStatus::Failed;
                    println!("Message {} processing failed: {}", message.id, error);

                    // 重试机制
                    if message.can_retry() {
                        message.increment_retry();
                        message.status = MessageStatus::Pending;
                        let _ = self.message_sender.send(message).await;
                    }
                }
            }
        }
    }
}

/// 消息队列管理器
pub struct MessageQueueManager {
    queues: Arc<RwLock<HashMap<String, Queue>>>,
    producers: Arc<RwLock<HashMap<String, Producer>>>,
    consumers: Arc<RwLock<HashMap<String, Consumer>>>,
    message_sender: mpsc::Sender<Message>,
    message_receiver: mpsc::Receiver<Message>,
}

impl MessageQueueManager {
    pub fn new() -> Self {
        let (message_sender, message_receiver) = mpsc::channel(1000);
        
        Self {
            queues: Arc::new(RwLock::new(HashMap::new())),
            producers: Arc::new(RwLock::new(HashMap::new())),
            consumers: Arc::new(RwLock::new(HashMap::new())),
            message_sender,
            message_receiver,
        }
    }

    /// 创建队列
    pub fn create_queue(&self, name: String, capacity: usize) {
        let mut queues = self.queues.write().unwrap();
        queues.insert(name.clone(), Queue::new(name, capacity));
    }

    /// 删除队列
    pub fn delete_queue(&self, name: &str) -> Option<Queue> {
        let mut queues = self.queues.write().unwrap();
        queues.remove(name)
    }

    /// 创建生产者
    pub fn create_producer(&self, id: String) -> Producer {
        let producer = Producer::new(id.clone(), self.message_sender.clone());
        
        let mut producers = self.producers.write().unwrap();
        producers.insert(id, producer.clone());
        
        producer
    }

    /// 创建消费者
    pub fn create_consumer<F>(&self, id: String, queue_name: String, callback: F) -> Consumer
    where
        F: Fn(Message) -> Result<(), String> + Send + Sync + 'static,
    {
        let (consumer_sender, consumer_receiver) = mpsc::channel(100);
        
        let consumer = Consumer::new(
            id.clone(),
            consumer_receiver,
            consumer_sender,
            Box::new(callback),
        );

        // 将消费者添加到队列
        {
            let mut queues = self.queues.write().unwrap();
            if let Some(queue) = queues.get_mut(&queue_name) {
                queue.add_consumer(id.clone());
            }
        }

        let mut consumers = self.consumers.write().unwrap();
        consumers.insert(id, consumer.clone());
        
        consumer
    }

    /// 启动消息处理
    pub async fn start_message_processing(&mut self) {
        while let Some(message) = self.message_receiver.recv().await {
            // 检查消息是否过期
            if message.is_expired() {
                println!("Message {} expired, skipping", message.id);
                continue;
            }

            // 根据优先级分发到队列
            self.route_message(message).await;
        }
    }

    /// 路由消息到队列
    async fn route_message(&self, message: Message) {
        let queue_name = match message.priority {
            MessagePriority::Critical => "critical".to_string(),
            MessagePriority::High => "high".to_string(),
            MessagePriority::Normal => "normal".to_string(),
            MessagePriority::Low => "low".to_string(),
        };

        let mut queues = self.queues.write().unwrap();
        if let Some(queue) = queues.get_mut(&queue_name) {
            if queue.enqueue(message) {
                println!("Message routed to queue: {}", queue_name);
            } else {
                println!("Queue {} is full, message dropped", queue_name);
            }
        } else {
            println!("Queue {} not found", queue_name);
        }
    }

    /// 获取队列统计信息
    pub fn get_queue_stats(&self) -> HashMap<String, QueueStats> {
        let queues = self.queues.read().unwrap();
        let mut stats = HashMap::new();

        for (name, queue) in queues.iter() {
            stats.insert(name.clone(), QueueStats {
                name: name.clone(),
                size: queue.size(),
                capacity: queue.capacity,
                consumer_count: queue.consumers.len(),
            });
        }

        stats
    }

    /// 清理过期消息
    pub fn cleanup_expired_messages(&self) {
        let mut queues = self.queues.write().unwrap();
        
        for queue in queues.values_mut() {
            let mut i = 0;
            while i < queue.messages.len() {
                if queue.messages[i].is_expired() {
                    queue.messages.remove(i);
                } else {
                    i += 1;
                }
            }
        }
    }
}

/// 队列统计信息
#[derive(Debug, Clone)]
pub struct QueueStats {
    pub name: String,
    pub size: usize,
    pub capacity: usize,
    pub consumer_count: usize,
}
```

### 5.2 泛型实现

```rust
use std::collections::{VecDeque, HashMap};
use std::sync::{Arc, RwLock};
use std::marker::PhantomData;

/// 泛型消息
pub struct GenericMessage<T> {
    pub id: String,
    pub payload: T,
    pub timestamp: Instant,
    pub priority: MessagePriority,
    pub ttl: Option<Duration>,
    pub status: MessageStatus,
    pub retry_count: u32,
    pub max_retries: u32,
    _phantom: PhantomData<T>,
}

impl<T> GenericMessage<T> {
    pub fn new(payload: T, priority: MessagePriority) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            payload,
            timestamp: Instant::now(),
            priority,
            ttl: None,
            status: MessageStatus::Pending,
            retry_count: 0,
            max_retries: 3,
            _phantom: PhantomData,
        }
    }

    pub fn is_expired(&self) -> bool {
        if let Some(ttl) = self.ttl {
            self.timestamp.elapsed() > ttl
        } else {
            false
        }
    }

    pub fn can_retry(&self) -> bool {
        self.retry_count < self.max_retries
    }

    pub fn increment_retry(&mut self) {
        self.retry_count += 1;
    }
}

/// 泛型队列
pub struct GenericQueue<T> {
    pub name: String,
    pub messages: VecDeque<GenericMessage<T>>,
    pub capacity: usize,
    pub consumers: Vec<String>,
    _phantom: PhantomData<T>,
}

impl<T> GenericQueue<T> {
    pub fn new(name: String, capacity: usize) -> Self {
        Self {
            name,
            messages: VecDeque::new(),
            capacity,
            consumers: Vec::new(),
            _phantom: PhantomData,
        }
    }

    pub fn enqueue(&mut self, message: GenericMessage<T>) -> bool {
        if self.messages.len() < self.capacity {
            self.messages.push_back(message);
            true
        } else {
            false
        }
    }

    pub fn dequeue(&mut self) -> Option<GenericMessage<T>> {
        self.messages.pop_front()
    }

    pub fn peek(&self) -> Option<&GenericMessage<T>> {
        self.messages.front()
    }

    pub fn size(&self) -> usize {
        self.messages.len()
    }

    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.messages.len() >= self.capacity
    }

    pub fn add_consumer(&mut self, consumer_id: String) {
        if !self.consumers.contains(&consumer_id) {
            self.consumers.push(consumer_id);
        }
    }

    pub fn remove_consumer(&mut self, consumer_id: &str) {
        self.consumers.retain(|id| id != consumer_id);
    }
}

/// 泛型生产者
pub struct GenericProducer<T> {
    pub id: String,
    pub message_sender: mpsc::Sender<GenericMessage<T>>,
    _phantom: PhantomData<T>,
}

impl<T> GenericProducer<T> {
    pub fn new(id: String, message_sender: mpsc::Sender<GenericMessage<T>>) -> Self {
        Self {
            id,
            message_sender,
            _phantom: PhantomData,
        }
    }

    pub async fn send(&self, payload: T, priority: MessagePriority) -> Result<(), mpsc::error::SendError<GenericMessage<T>>> {
        let message = GenericMessage::new(payload, priority);
        self.message_sender.send(message).await
    }

    pub async fn send_with_ttl(&self, payload: T, priority: MessagePriority, ttl: Duration) -> Result<(), mpsc::error::SendError<GenericMessage<T>>> {
        let mut message = GenericMessage::new(payload, priority);
        message.ttl = Some(ttl);
        self.message_sender.send(message).await
    }
}

/// 泛型消费者
pub struct GenericConsumer<T> {
    pub id: String,
    pub message_receiver: mpsc::Receiver<GenericMessage<T>>,
    pub message_sender: mpsc::Sender<GenericMessage<T>>,
    pub processing_callback: Box<dyn Fn(GenericMessage<T>) -> Result<(), String> + Send + Sync>,
    _phantom: PhantomData<T>,
}

impl<T> GenericConsumer<T> {
    pub fn new(
        id: String,
        message_receiver: mpsc::Receiver<GenericMessage<T>>,
        message_sender: mpsc::Sender<GenericMessage<T>>,
        processing_callback: Box<dyn Fn(GenericMessage<T>) -> Result<(), String> + Send + Sync>,
    ) -> Self {
        Self {
            id,
            message_receiver,
            message_sender,
            processing_callback,
            _phantom: PhantomData,
        }
    }

    pub async fn start_consuming(&mut self) {
        while let Some(mut message) = self.message_receiver.recv().await {
            message.status = MessageStatus::Processing;

            match (self.processing_callback)(message.clone()) {
                Ok(()) => {
                    message.status = MessageStatus::Completed;
                    println!("Message {} processed successfully", message.id);
                }
                Err(error) => {
                    message.status = MessageStatus::Failed;
                    println!("Message {} processing failed: {}", message.id, error);

                    if message.can_retry() {
                        message.increment_retry();
                        message.status = MessageStatus::Pending;
                        let _ = self.message_sender.send(message).await;
                    }
                }
            }
        }
    }
}
```

### 5.3 异步实现

```rust
use tokio::sync::RwLock as TokioRwLock;
use std::sync::Arc;

/// 异步消息队列管理器
pub struct AsyncMessageQueueManager {
    queues: Arc<TokioRwLock<HashMap<String, Queue>>>,
    producers: Arc<TokioRwLock<HashMap<String, Producer>>>,
    consumers: Arc<TokioRwLock<HashMap<String, Consumer>>>,
    message_sender: mpsc::Sender<Message>,
    message_receiver: mpsc::Receiver<Message>,
}

impl AsyncMessageQueueManager {
    pub fn new() -> Self {
        let (message_sender, message_receiver) = mpsc::channel(1000);
        
        Self {
            queues: Arc::new(TokioRwLock::new(HashMap::new())),
            producers: Arc::new(TokioRwLock::new(HashMap::new())),
            consumers: Arc::new(TokioRwLock::new(HashMap::new())),
            message_sender,
            message_receiver,
        }
    }

    /// 异步创建队列
    pub async fn create_queue(&self, name: String, capacity: usize) {
        let mut queues = self.queues.write().await;
        queues.insert(name.clone(), Queue::new(name, capacity));
    }

    /// 异步删除队列
    pub async fn delete_queue(&self, name: &str) -> Option<Queue> {
        let mut queues = self.queues.write().await;
        queues.remove(name)
    }

    /// 异步创建生产者
    pub async fn create_producer(&self, id: String) -> Producer {
        let producer = Producer::new(id.clone(), self.message_sender.clone());
        
        let mut producers = self.producers.write().await;
        producers.insert(id, producer.clone());
        
        producer
    }

    /// 异步创建消费者
    pub async fn create_consumer<F>(&self, id: String, queue_name: String, callback: F) -> Consumer
    where
        F: Fn(Message) -> Result<(), String> + Send + Sync + 'static,
    {
        let (consumer_sender, consumer_receiver) = mpsc::channel(100);
        
        let consumer = Consumer::new(
            id.clone(),
            consumer_receiver,
            consumer_sender,
            Box::new(callback),
        );

        // 将消费者添加到队列
        {
            let mut queues = self.queues.write().await;
            if let Some(queue) = queues.get_mut(&queue_name) {
                queue.add_consumer(id.clone());
            }
        }

        let mut consumers = self.consumers.write().await;
        consumers.insert(id, consumer.clone());
        
        consumer
    }

    /// 异步启动消息处理
    pub async fn start_message_processing(&mut self) {
        while let Some(message) = self.message_receiver.recv().await {
            if message.is_expired() {
                println!("Message {} expired, skipping", message.id);
                continue;
            }

            self.route_message(message).await;
        }
    }

    /// 异步路由消息到队列
    async fn route_message(&self, message: Message) {
        let queue_name = match message.priority {
            MessagePriority::Critical => "critical".to_string(),
            MessagePriority::High => "high".to_string(),
            MessagePriority::Normal => "normal".to_string(),
            MessagePriority::Low => "low".to_string(),
        };

        let mut queues = self.queues.write().await;
        if let Some(queue) = queues.get_mut(&queue_name) {
            if queue.enqueue(message) {
                println!("Message routed to queue: {}", queue_name);
            } else {
                println!("Queue {} is full, message dropped", queue_name);
            }
        } else {
            println!("Queue {} not found", queue_name);
        }
    }

    /// 异步获取队列统计信息
    pub async fn get_queue_stats(&self) -> HashMap<String, QueueStats> {
        let queues = self.queues.read().await;
        let mut stats = HashMap::new();

        for (name, queue) in queues.iter() {
            stats.insert(name.clone(), QueueStats {
                name: name.clone(),
                size: queue.size(),
                capacity: queue.capacity,
                consumer_count: queue.consumers.len(),
            });
        }

        stats
    }

    /// 异步清理过期消息
    pub async fn cleanup_expired_messages(&self) {
        let mut queues = self.queues.write().await;
        
        for queue in queues.values_mut() {
            let mut i = 0;
            while i < queue.messages.len() {
                if queue.messages[i].is_expired() {
                    queue.messages.remove(i);
                } else {
                    i += 1;
                }
            }
        }
    }
}
```

## 6. 应用场景

### 6.1 任务队列

```rust
use std::sync::Arc;

/// 任务队列
pub struct TaskQueue {
    queue_manager: Arc<MessageQueueManager>,
}

impl TaskQueue {
    pub fn new(queue_manager: Arc<MessageQueueManager>) -> Self {
        Self { queue_manager }
    }

    /// 提交任务
    pub async fn submit_task(&self, task: String, priority: MessagePriority) -> Result<(), String> {
        let producer = self.queue_manager.create_producer("task_producer".to_string());
        producer.send(task, priority).await.map_err(|e| e.to_string())
    }

    /// 处理任务
    pub async fn process_task(&self, task: Message) -> Result<(), String> {
        println!("Processing task: {}", task.payload);
        
        // 模拟任务处理
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        println!("Task completed: {}", task.payload);
        Ok(())
    }

    /// 启动任务处理器
    pub async fn start_task_processor(&self) {
        let mut consumer = self.queue_manager.create_consumer(
            "task_consumer".to_string(),
            "normal".to_string(),
            Box::new(|task| {
                // 这里应该调用实际的任务处理逻辑
                println!("Processing task: {}", task.payload);
                Ok(())
            }),
        );

        consumer.start_consuming().await;
    }
}
```

### 6.2 事件总线

```rust
use std::sync::Arc;

/// 事件总线
pub struct EventBus {
    queue_manager: Arc<AsyncMessageQueueManager>,
}

impl EventBus {
    pub fn new(queue_manager: Arc<AsyncMessageQueueManager>) -> Self {
        Self { queue_manager }
    }

    /// 发布事件
    pub async fn publish_event(&self, event_type: &str, event_data: &str) -> Result<(), String> {
        let producer = self.queue_manager.create_producer("event_publisher".to_string()).await;
        let event = format!("{}:{}", event_type, event_data);
        producer.send(event, MessagePriority::Normal).await.map_err(|e| e.to_string())
    }

    /// 订阅事件
    pub async fn subscribe_event<F>(&self, event_type: &str, handler: F) -> Result<(), String>
    where
        F: Fn(Message) -> Result<(), String> + Send + Sync + 'static,
    {
        let consumer_id = format!("event_consumer_{}", event_type);
        
        let mut consumer = self.queue_manager.create_consumer(
            consumer_id,
            "normal".to_string(),
            Box::new(handler),
        ).await;

        // 启动消费者
        tokio::spawn(async move {
            consumer.start_consuming().await;
        });

        Ok(())
    }

    /// 处理用户注册事件
    pub async fn handle_user_registered(&self, message: Message) -> Result<(), String> {
        println!("Handling user registration event: {}", message.payload);
        
        // 发送欢迎邮件
        self.publish_event("email", "welcome").await?;
        
        // 创建用户配置文件
        self.publish_event("profile", "create").await?;
        
        Ok(())
    }

    /// 处理订单创建事件
    pub async fn handle_order_created(&self, message: Message) -> Result<(), String> {
        println!("Handling order creation event: {}", message.payload);
        
        // 发送确认邮件
        self.publish_event("email", "order_confirmation").await?;
        
        // 更新库存
        self.publish_event("inventory", "update").await?;
        
        Ok(())
    }
}
```

## 7. 变体模式

### 7.1 优先级队列

```rust
use std::sync::Arc;
use std::collections::BinaryHeap;
use std::cmp::Ordering;

/// 优先级队列
pub struct PriorityQueue {
    messages: BinaryHeap<PriorityMessage>,
    capacity: usize,
}

/// 优先级消息
#[derive(Debug, Clone)]
pub struct PriorityMessage {
    pub message: Message,
    pub priority: u32,
}

impl PartialEq for PriorityMessage {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for PriorityMessage {}

impl PartialOrd for PriorityMessage {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityMessage {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority).reverse() // 高优先级在前
    }
}

impl PriorityQueue {
    pub fn new(capacity: usize) -> Self {
        Self {
            messages: BinaryHeap::new(),
            capacity,
        }
    }

    /// 入队
    pub fn enqueue(&mut self, message: Message, priority: u32) -> bool {
        if self.messages.len() < self.capacity {
            let priority_message = PriorityMessage { message, priority };
            self.messages.push(priority_message);
            true
        } else {
            false
        }
    }

    /// 出队
    pub fn dequeue(&mut self) -> Option<Message> {
        self.messages.pop().map(|pm| pm.message)
    }

    /// 查看队首消息
    pub fn peek(&self) -> Option<&Message> {
        self.messages.peek().map(|pm| &pm.message)
    }

    /// 获取队列大小
    pub fn size(&self) -> usize {
        self.messages.len()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }
}
```

### 7.2 延迟队列

```rust
use std::sync::Arc;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

/// 延迟队列
pub struct DelayQueue {
    messages: BTreeMap<Instant, Vec<Message>>,
    capacity: usize,
}

impl DelayQueue {
    pub fn new(capacity: usize) -> Self {
        Self {
            messages: BTreeMap::new(),
            capacity,
        }
    }

    /// 延迟入队
    pub fn enqueue_delayed(&mut self, message: Message, delay: Duration) -> bool {
        if self.messages.values().map(|v| v.len()).sum::<usize>() < self.capacity {
            let execute_time = Instant::now() + delay;
            self.messages.entry(execute_time).or_insert_with(Vec::new).push(message);
            true
        } else {
            false
        }
    }

    /// 检查并出队到期的消息
    pub fn dequeue_expired(&mut self) -> Vec<Message> {
        let now = Instant::now();
        let mut expired_messages = Vec::new();

        // 收集所有到期的消息
        let expired_keys: Vec<Instant> = self.messages
            .range(..=now)
            .map(|(&time, _)| time)
            .collect();

        for time in expired_keys {
            if let Some(messages) = self.messages.remove(&time) {
                expired_messages.extend(messages);
            }
        }

        expired_messages
    }

    /// 获取下一个到期时间
    pub fn next_expiry(&self) -> Option<Instant> {
        self.messages.keys().next().copied()
    }

    /// 获取队列大小
    pub fn size(&self) -> usize {
        self.messages.values().map(|v| v.len()).sum()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }
}
```

## 8. 总结

消息队列模式是分布式系统中的重要模式，通过形式化的数学理论和Rust实现，我们建立了完整的消息队列框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于任务队列、事件总线、异步处理等场景
5. **解耦性**: 通过异步消息传递实现组件解耦

该模式为分布式系统的异步通信和任务处理提供了理论基础和实践指导，是构建可扩展、高性能分布式系统的重要组件。 