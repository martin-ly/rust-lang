# 分布式设计模式语义分析

> **Rust版本**: 1.94
> **难度级别**: 🔴 高级
> **阅读时间**: 约6-8小时
> **覆盖范围**: 分布式系统语义理论、通信模式、一致性算法、容错机制
> **权威参考**: *Designing Data-Intensive Applications* (Martin Kleppmann), CAP Theorem, Raft/Paxos Papers

---

## 目录

- [分布式设计模式语义分析](#分布式设计模式语义分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 分布式系统的语义挑战](#11-分布式系统的语义挑战)
    - [1.2 Rust 在分布式系统中的优势](#12-rust-在分布式系统中的优势)
    - [1.3 CAP 定理语义](#13-cap-定理语义)
  - [2. 分布式通信模式](#2-分布式通信模式)
    - [2.1 远程过程调用 (RPC)](#21-远程过程调用-rpc)
    - [2.2 消息队列模式](#22-消息队列模式)
    - [2.3 发布-订阅模式](#23-发布-订阅模式)
  - [3. 服务发现模式](#3-服务发现模式)
    - [3.1 注册中心模式](#31-注册中心模式)
    - [3.2 去中心化发现](#32-去中心化发现)
  - [4. 一致性与共识模式](#4-一致性与共识模式)
    - [4.1 强一致性模式](#41-强一致性模式)
    - [4.2 最终一致性模式](#42-最终一致性模式)
    - [4.3 分布式事务](#43-分布式事务)
  - [5. 容错与弹性模式](#5-容错与弹性模式)
    - [5.1 熔断器模式](#51-熔断器模式)
    - [5.2 重试模式](#52-重试模式)
    - [5.3 舱壁隔离模式](#53-舱壁隔离模式)
    - [5.4 限流模式](#54-限流模式)
  - [6. 数据分区模式](#6-数据分区模式)
    - [6.1 分片模式](#61-分片模式)
    - [6.2 复制模式](#62-复制模式)
  - [7. 缓存模式](#7-缓存模式)
    - [7.1 本地缓存](#71-本地缓存)
    - [7.2 分布式缓存](#72-分布式缓存)
  - [8. 事件溯源模式](#8-事件溯源模式)
    - [8.1 事件存储](#81-事件存储)
    - [8.2 状态重建](#82-状态重建)
  - [9. CQRS 模式](#9-cqrs-模式)
    - [9.1 命令端语义](#91-命令端语义)
    - [9.2 查询端语义](#92-查询端语义)
  - [10. 分布式调度模式](#10-分布式调度模式)
    - [10.1 任务调度](#101-任务调度)
    - [10.2 分布式锁](#102-分布式锁)

---

## 1. 引言

### 1.1 分布式系统的语义挑战

分布式系统引入了一系列单机系统不具备的语义复杂性。从形式化语义的角度，分布式系统可以建模为：

$$
\text{DistributedSystem} = \langle N, C, M, F \rangle
$$

其中：

- $N = \{n_1, n_2, ..., n_k\}$ 是节点集合
- $C \subseteq N \times N$ 是通信链路
- $M$ 是消息空间
- $F: N \times M \to N \times M$ 是状态转换函数

**核心语义挑战：**

```text
┌─────────────────────────────────────────────────────────────────┐
│                    分布式语义挑战                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 部分失败 (Partial Failure)                                  │
│     ∀ n ∈ N: healthy(n) ∨ failed(n) ∨ partitioned(n)          │
│                                                                 │
│  2. 网络不确定性 (Network Uncertainty)                          │
│     send(m) ⇏ receive(m)  (消息可能丢失)                        │
│     send(m₁) → send(m₂) ⇏ receive(m₁) → receive(m₂)            │
│                                                                 │
│  3. 时钟不同步 (Clock Desynchronization)                        │
│     ∀ nᵢ, nⱼ ∈ N: |clock(nᵢ) - clock(nⱼ)| ≤ ε                  │
│                                                                 │
│  4. 状态一致性 (State Consistency)                              │
│     ∀ nᵢ, nⱼ ∈ N, ∀ t: state(nᵢ, t) ?= state(nⱼ, t)            │
│                                                                 │
│  5. 并发控制 (Concurrency Control)                              │
│     operations(o₁, o₂) → result(o₁ ∘ o₂)                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Rust 在分布式系统中的优势

Rust 的类型系统和所有权模型为分布式系统开发提供了独特的语义保证：

```rust
/// 分布式节点语义模型
///
/// Rust 通过类型系统保证：
/// 1. 消息所有权明确转移
/// 2. 并发访问安全
/// 3. 资源自动释放
pub struct DistributedNode<S, M>
where
    S: NodeState,
    M: Message + Send + 'static,
{
    /// 节点 ID（不可变）
    id: NodeId,

    /// 状态机（受 Mutex/RwLock 保护）
    state: Arc<RwLock<S>>,

    /// 消息通道（所有权转移语义）
    inbox: mpsc::Receiver<M>,
    outbox: mpsc::Sender<M>,

    /// 对等节点（共享引用）
    peers: Arc<Vec<NodeId>>,
}

/// 消息 trait：要求实现序列化和 Send
pub trait Message: Serialize + for<'de> Deserialize<'de> + Clone + Send {
    fn message_id(&self) -> MessageId;
    fn timestamp(&self) -> Timestamp;
}

/// 状态 trait：要求 Clone 用于快照
pub trait NodeState: Clone + Send + Sync + 'static {
    fn apply(&mut self, entry: LogEntry) -> Result<(), StateError>;
    fn snapshot(&self) -> Self;
}
```

**Rust 的分布式语义保证：**

| 特性 | 语义保证 | 分布式系统价值 |
|------|---------|---------------|
| 所有权 | `Send`/`Sync` 边界 | 线程/节点间安全传递 |
| 生命周期 | `'static` 约束 | 异步任务安全 |
| 错误处理 | `Result<T, E>` | 显式处理网络失败 |
| 类型安全 | 编译时检查 | 协议兼容性保证 |
| RAII | 自动资源释放 | 连接/锁自动清理 |

### 1.3 CAP 定理语义

CAP 定理的形式化语义：

$$
\forall S: \text{DistributedSystem}. \quad \neg(C(S) \land A(S) \land P(S))
$$

其中：

- $C(S)$: **一致性 (Consistency)** - 所有节点在同一时间看到相同数据
- $A(S)$: **可用性 (Availability)** - 每个请求都能获得响应
- $P(S)$: **分区容错性 (Partition Tolerance)** - 系统在网络分区时继续运行

```rust
/// CAP 策略枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CAPStrategy {
    /// CP: 一致性和分区容错性
    /// 在网络分区时牺牲可用性
    ConsistencyPartitionTolerance,

    /// AP: 可用性和分区容错性
    /// 允许数据暂时不一致
    AvailabilityPartitionTolerance,

    /// CA: 仅在非分布式环境可能
    #[deprecated(note = "分布式系统必须容忍分区")]
    ConsistencyAvailability,
}

/// 一致性级别（从强到弱）
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConsistencyLevel {
    /// 线性一致性：所有操作原子可见
    Linearizable,

    /// 顺序一致性：保持程序顺序
    Sequential,

    /// 因果一致性：保持因果关系
    Causal,

    /// 读己之写
    ReadYourWrites,

    /// 单调读
    MonotonicReads,

    /// 最终一致性
    Eventual,
}

/// CAP 配置验证
pub struct CAPConfig {
    strategy: CAPStrategy,
    consistency: ConsistencyLevel,
    replication_factor: u32,
}

impl CAPConfig {
    /// 验证 CAP 配置一致性
    ///
    /// 定理：CP 系统不能使用最终一致性
    pub fn validate(&self) -> Result<(), CAPError> {
        match (self.strategy, self.consistency) {
            (CAPStrategy::ConsistencyPartitionTolerance, ConsistencyLevel::Eventual) => {
                Err(CAPError::InconsistentStrategy(
                    "CP system requires stronger consistency".to_string()
                ))
            }
            (CAPStrategy::AvailabilityPartitionTolerance, ConsistencyLevel::Linearizable) => {
                tracing::warn!("AP system with linearizable consistency may impact availability");
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// 计算仲裁数
    pub fn quorum_size(&self) -> usize {
        match self.strategy {
            CAPStrategy::ConsistencyPartitionTolerance => {
                // CP: 多数派 (N/2 + 1)
                (self.replication_factor as usize / 2) + 1
            }
            CAPStrategy::AvailabilityPartitionTolerance => {
                // AP: 单一副本即可响应
                1
            }
            _ => 1,
        }
    }
}

#[derive(Debug)]
pub enum CAPError {
    InconsistentStrategy(String),
    InsufficientReplicas { required: usize, actual: usize },
}
```

---

## 2. 分布式通信模式

### 2.1 远程过程调用 (RPC)

**RPC 语义模型：**

RPC 试图让远程调用看起来像本地调用，但从语义角度，它引入了根本性差异：

$$
\text{LocalCall}: f(x) \to y \quad \text{(同步、确定、同进程)}
$$

$$
\text{RemoteCall}: f(x) \xrightarrow{\text{network}} \{y, \text{timeout}, \text{failure}\} \quad \text{(异步、不确定、跨进程)}
$$

```rust
/// RPC 语义模型
///
/// 核心语义差异：
/// 1. 本地调用：确定性的成功或 panic
/// 2. 远程调用：可能超时、失败、重复执行
pub trait RpcSemantics<Req, Resp> {
    /// 调用语义
    ///
    /// 可能结果：
    /// - Ok(Response): 成功
    /// - Err(Timeout): 超时（未知是否执行）
    /// - Err(Network): 网络错误
    /// - Err(Service): 服务端错误
    async fn call(&self, request: Req) -> RpcResult<Resp>;

    /// 幂等性检查
    ///
    /// 定理：非幂等操作 + 重试 = 可能重复副作用
    fn is_idempotent(&self, op: &Req) -> bool;

    /// 至少一次语义
    async fn call_at_least_once(&self, request: Req) -> RpcResult<Resp>;

    /// 至多一次语义（需要服务端去重）
    async fn call_at_most_once(&self, request: Req) -> RpcResult<Resp>;
}

/// RPC 结果类型
#[derive(Debug, Clone)]
pub enum RpcResult<T> {
    Success(T),
    Timeout { elapsed: Duration, operation: String },
    NetworkError(String),
    ServiceError { code: u32, message: String },
    /// 关键：超时后可能实际成功
    Unknown { request_id: String },
}

/// gRPC 在 Rust 中的语义 (Tonic)
#[cfg(feature = "tonic")]
pub mod grpc_semantics {
    use tonic::{Request, Response, Status};

    /// gRPC 服务定义语义
    ///
    /// 1. Protocol Buffers 定义契约
    /// 2. 编译时生成 Rust 代码
    /// 3. 类型安全的消息传递
    #[tonic::async_trait]
    pub trait GreeterService: Send + Sync + 'static {
        /// 一元 RPC：请求-响应
        async fn say_hello(
            &self,
            request: Request<HelloRequest>,
        ) -> Result<Response<HelloReply>, Status>;

        /// 服务端流：一个请求，多个响应
        type SayHelloStreamStream: futures::Stream<Item = Result<HelloReply, Status>> + Send;
        async fn say_hello_stream(
            &self,
            request: Request<HelloRequest>,
        ) -> Result<Response<Self::SayHelloStreamStream>, Status>;

        /// 客户端流：多个请求，一个响应
        async fn client_stream(
            &self,
            request: Request<tonic::Streaming<HelloRequest>>,
        ) -> Result<Response<HelloReply>, Status>;

        /// 双向流：全双工通信
        type BidirectionalStream: futures::Stream<Item = Result<HelloReply, Status>> + Send;
        async fn bidirectional(
            &self,
            request: Request<tonic::Streaming<HelloRequest>>,
        ) -> Result<Response<Self::BidirectionalStream>, Status>;
    }

    #[derive(Clone, PartialEq, prost::Message)]
    pub struct HelloRequest {
        #[prost(string, tag = "1")]
        pub name: String,
        #[prost(string, optional, tag = "2")]
        pub request_id: Option<String>, // 用于幂等性
    }

    #[derive(Clone, PartialEq, prost::Message)]
    pub struct HelloReply {
        #[prost(string, tag = "1")]
        pub message: String,
    }
}
```

**序列化/反序列化语义：**

```rust
/// 序列化语义模型
///
/// 关键属性：
/// 1. 可逆性：deserialize(serialize(x)) = x
/// 2. 版本兼容性：旧代码能读取新数据（忽略未知字段）
/// 3. 平台无关性：不同语言可互操作
pub trait SerializationSemantics<T> {
    /// 序列化：内存结构 → 字节流
    fn serialize(value: &T) -> Result<Vec<u8>, SerializeError>;

    /// 反序列化：字节流 → 内存结构
    fn deserialize(bytes: &[u8]) -> Result<T, DeserializeError>;

    /// 模式演化检查
    fn check_compatibility(old_schema: &Schema, new_schema: &Schema) -> CompatibilityReport;
}

/// Serde 实现示例
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct UserEvent {
    /// 事件 ID（用于去重）
    pub event_id: uuid::Uuid,

    /// 事件类型（版本控制）
    pub event_type: String,

    /// 时间戳（因果排序）
    pub timestamp: u64,

    /// 用户数据
    pub user_id: String,
    pub payload: serde_json::Value,

    /// 版本号（模式演化）
    #[serde(default = "default_version")]
    pub schema_version: u32,
}

fn default_version() -> u32 { 1 }

/// 序列化示例
pub fn serialize_event(event: &UserEvent) -> Result<Vec<u8>, String> {
    // bincode：紧凑二进制格式
    let binary = bincode::serialize(event)
        .map_err(|e| format!("Serialization failed: {}", e))?;

    // 或 JSON（可读性好）
    let json = serde_json::to_vec(event)
        .map_err(|e| format!("JSON serialization failed: {}", e))?;

    Ok(binary)
}
```

**超时和重试语义：**

```rust
/// 重试策略语义
#[derive(Clone, Debug)]
pub enum RetryPolicy {
    /// 固定间隔重试
    FixedInterval {
        max_retries: u32,
        interval: Duration,
    },

    /// 指数退避
    ExponentialBackoff {
        max_retries: u32,
        initial_interval: Duration,
        max_interval: Duration,
        multiplier: f64,
    },

    /// 带抖动的指数退避（避免惊群效应）
    ExponentialBackoffWithJitter {
        max_retries: u32,
        initial_interval: Duration,
        max_interval: Duration,
        jitter_factor: f64,
    },
}

impl RetryPolicy {
    /// 计算下次重试延迟
    pub fn next_delay(&self, attempt: u32) -> Option<Duration> {
        match self {
            RetryPolicy::FixedInterval { max_retries, interval } => {
                if attempt >= *max_retries {
                    None
                } else {
                    Some(*interval)
                }
            }
            RetryPolicy::ExponentialBackoff {
                max_retries,
                initial_interval,
                max_interval,
                multiplier
            } => {
                if attempt >= *max_retries {
                    None
                } else {
                    let delay = initial_interval.as_millis() as f64
                        * multiplier.powi(attempt as i32);
                    let delay = delay.min(max_interval.as_millis() as f64);
                    Some(Duration::from_millis(delay as u64))
                }
            }
            RetryPolicy::ExponentialBackoffWithJitter {
                max_retries,
                initial_interval,
                max_interval,
                jitter_factor
            } => {
                if attempt >= *max_retries {
                    None
                } else {
                    let base = initial_interval.as_millis() as f64
                        * 2f64.powi(attempt as i32);
                    let base = base.min(max_interval.as_millis() as f64);
                    let jitter = base * jitter_factor * (rand::random::<f64>() - 0.5);
                    Some(Duration::from_millis((base + jitter) as u64))
                }
            }
        }
    }
}

/// 带重试的 RPC 调用
pub async fn call_with_retry<F, Fut, T>(
    operation: F,
    policy: RetryPolicy,
    is_retryable: impl Fn(&RpcError) -> bool,
) -> RpcResult<T>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = RpcResult<T>>,
{
    let mut attempt = 0;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(err) => {
                if !is_retryable(&err) {
                    return Err(err);
                }

                match policy.next_delay(attempt) {
                    Some(delay) => {
                        tracing::warn!("Retry attempt {} after {:?}", attempt, delay);
                        tokio::time::sleep(delay).await;
                        attempt += 1;
                    }
                    None => return Err(err),
                }
            }
        }
    }
}
```

### 2.2 消息队列模式

**生产者-消费者语义：**

```rust
/// 消息队列语义模型
///
/// 核心概念：
/// 1. 解耦：生产者和消费者独立运行
/// 2. 缓冲：队列作为中间缓冲
/// 3. 异步：发送非阻塞（通常）
pub trait MessageQueueSemantics<M> {
    /// 生产者语义
    async fn produce(&self, message: M) -> Result<(), ProduceError>;

    /// 消费者语义
    ///
    /// 返回消息和确认句柄
    /// 确认后消息从队列删除
    async fn consume(&self) -> Result<(M, AckHandle), ConsumeError>;

    /// 批量消费语义
    async fn consume_batch(&self, max_batch_size: usize) -> Result<Vec<(M, AckHandle)>, ConsumeError>;
}

/// 确认语义
pub struct AckHandle {
    message_id: MessageId,
    acknowledged: Arc<AtomicBool>,
}

impl AckHandle {
    /// 确认消息处理成功
    ///
    /// 语义：消息已安全处理，可从队列删除
    pub async fn ack(self) -> Result<(), AckError> {
        if self.acknowledged.swap(true, Ordering::SeqCst) {
            return Err(AckError::AlreadyAcknowledged);
        }
        // 发送确认到队列
        Ok(())
    }

    /// 否定确认（重新入队或丢弃）
    pub async fn nack(&self, requeue: bool) -> Result<(), AckError> {
        if requeue {
            // 重新入队，等待重试
        } else {
            // 发送到死信队列
        }
        Ok(())
    }
}

/// Rust 实现（使用 lapin - AMQP 客户端）
use lapin::{Connection, Channel, options::*, types::FieldTable};

pub struct AmqpMessageQueue {
    channel: Channel,
    queue_name: String,
}

impl AmqpMessageQueue {
    pub async fn new(amqp_url: &str, queue_name: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let connection = Connection::connect(amqp_url, ConnectionProperties::default()).await?;
        let channel = connection.create_channel().await?;

        // 声明队列（幂等操作）
        channel.queue_declare(
            queue_name,
            QueueDeclareOptions::default(),
            FieldTable::default(),
        ).await?;

        Ok(Self { channel, queue_name: queue_name.to_string() })
    }

    /// 生产者：发送消息
    pub async fn produce(&self, payload: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        let confirm = self.channel.basic_publish(
            "", // 默认 exchange
            &self.queue_name,
            BasicPublishOptions::default(),
            payload,
            BasicProperties::default()
                .with_delivery_mode(2), // 持久化
        ).await?;

        // 等待确认（Publisher Confirm 语义）
        confirm.await?;
        Ok(())
    }

    /// 消费者：拉取消息
    pub async fn consume(&self) -> Result<(Vec<u8>, DeliveryTag), Box<dyn std::error::Error>> {
        let delivery = self.channel.basic_get(
            &self.queue_name,
            BasicGetOptions::default(),
        ).await?;

        match delivery {
            Some(delivery) => {
                let tag = delivery.delivery_tag;
                let data = delivery.data;
                // 不自动确认，返回 ack 句柄
                Ok((data, tag))
            }
            None => Err("No message available".into()),
        }
    }

    /// 确认消息
    pub async fn ack(&self, delivery_tag: DeliveryTag) -> Result<(), Box<dyn std::error::Error>> {
        self.channel.basic_ack(
            delivery_tag,
            BasicAckOptions::default(),
        ).await?;
        Ok(())
    }
}

type DeliveryTag = u64;
```

**消息持久化语义：**

```rust
/// 消息持久化级别
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PersistenceLevel {
    /// 非持久化：仅内存，性能最高，可能丢失
    MemoryOnly,

    /// 异步持久化：批量写入磁盘，可能丢失少量消息
    AsyncDisk,

    /// 同步持久化：每条消息 fsync，最安全但最慢
    SyncDisk,

    /// 多副本持久化：复制到多个节点
    Replicated { replicas: u32 },
}

/// 持久化语义保证
///
/// 定理：持久化级别越高，性能越低，可靠性越高
impl PersistenceLevel {
    /// 计算持久化延迟
    pub fn expected_latency(&self) -> Duration {
        match self {
            PersistenceLevel::MemoryOnly => Duration::from_micros(10),
            PersistenceLevel::AsyncDisk => Duration::from_micros(100),
            PersistenceLevel::SyncDisk => Duration::from_millis(5),
            PersistenceLevel::Replicated { replicas } => {
                Duration::from_millis(10 * replicas)
            }
        }
    }

    /// 数据丢失概率（简化模型）
    pub fn data_loss_probability(&self, node_failure_rate: f64) -> f64 {
        match self {
            PersistenceLevel::MemoryOnly => node_failure_rate,
            PersistenceLevel::AsyncDisk => node_failure_rate * 0.1,
            PersistenceLevel::SyncDisk => node_failure_rate * 0.01,
            PersistenceLevel::Replicated { replicas } => {
                node_failure_rate.powi(*replicas as i32)
            }
        }
    }
}
```

**至少一次/恰好一次语义：**

```rust
/// 消息传递保证语义
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeliveryGuarantee {
    /// 至多一次：消息可能丢失，但不会重复
    ///
    /// 实现：发送即忘 (fire-and-forget)
    AtMostOnce,

    /// 至少一次：消息不会丢失，但可能重复
    ///
    /// 实现：生产者确认 + 消费者确认 + 重试
    AtLeastOnce,

    /// 恰好一次：消息既不丢失也不重复
    ///
    /// 实现：至少一次 + 幂等消费 + 去重
    ExactlyOnce,
}

/// 恰好一次语义实现
pub struct ExactlyOnceSemantics {
    /// 生产者端去重（防止重复发送）
    producer_dedup: Arc<DedupStore>,

    /// 消费者端去重（防止重复处理）
    consumer_dedup: Arc<DedupStore>,

    /// 事务支持（原子性确认）
    transaction_manager: Arc<TransactionManager>,
}

impl ExactlyOnceSemantics {
    /// 发送消息（生产者端去重）
    pub async fn send_with_dedup(
        &self,
        message: &Message,
    ) -> Result<(), SendError> {
        // 检查是否已发送
        if self.producer_dedup.contains(&message.id).await? {
            tracing::info!("Message {} already sent, skipping", message.id);
            return Ok(());
        }

        // 发送到队列
        self.produce(message).await?;

        // 记录已发送
        self.producer_dedup.insert(message.id).await?;

        Ok(())
    }

    /// 消费消息（消费者端去重）
    pub async fn consume_with_dedup<F, Fut, T>(
        &self,
        message: &Message,
        handler: F,
    ) -> Result<T, ConsumeError>
    where
        F: FnOnce(&Message) -> Fut,
        Fut: std::future::Future<Output = Result<T, HandlerError>>,
    {
        // 检查是否已处理
        if let Some(result) = self.consumer_dedup.get_result(&message.id).await? {
            tracing::info!("Message {} already processed, returning cached result", message.id);
            return Ok(result);
        }

        // 在事务中执行处理
        let mut txn = self.transaction_manager.begin().await?;

        // 执行处理器
        match handler(message).await {
            Ok(result) => {
                // 记录已处理结果
                txn.record_processed(message.id, &result).await?;
                txn.commit().await?;
                Ok(result)
            }
            Err(e) => {
                txn.rollback().await?;
                Err(ConsumeError::HandlerError(e))
            }
        }
    }
}

/// 去重存储（基于 Redis 示例）
pub struct DedupStore {
    redis: redis::aio::MultiplexedConnection,
    ttl: Duration,
}

impl DedupStore {
    pub async fn contains(&self, message_id: &MessageId) -> Result<bool, redis::RedisError> {
        let key = format!("dedup:{}", message_id);
        let exists: bool = redis::cmd("EXISTS")
            .arg(&key)
            .query_async(&mut self.redis.clone())
            .await?;
        Ok(exists)
    }

    pub async fn insert(&self, message_id: MessageId) -> Result<(), redis::RedisError> {
        let key = format!("dedup:{}", message_id);
        redis::cmd("SETEX")
            .arg(&key)
            .arg(self.ttl.as_secs() as usize)
            .arg("1")
            .query_async(&mut self.redis.clone())
            .await?;
        Ok(())
    }
}
```

**背压和流控制：**

```rust
/// 背压（Backpressure）语义
///
/// 当消费者处理速度慢于生产者时，需要流控制机制
pub enum BackpressureStrategy {
    /// 阻塞生产者：直到有空间
    Blocking,

    /// 丢弃新消息：当队列满时
    DropNew { max_size: usize },

    /// 丢弃旧消息：LRU 策略
    DropOld { max_size: usize },

    /// 采样：按比例丢弃
    Sampling { ratio: f64 },
}

/// Tokio mpsc 背压示例
use tokio::sync::mpsc;

pub struct BackpressureChannel<T> {
    sender: mpsc::Sender<T>,
    receiver: mpsc::Receiver<T>,
    capacity: usize,
}

impl<T> BackpressureChannel<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, receiver) = mpsc::channel(capacity);
        Self { sender, receiver, capacity }
    }

    /// 发送带背压
    ///
    /// 语义：如果缓冲区满，等待直到有空间
    pub async fn send(&self, value: T) -> Result<(), SendError> {
        // 背压发生在这里：如果缓冲区满，await 会挂起
        self.sender.send(value).await
            .map_err(|_| SendError::ChannelClosed)
    }

    /// 非阻塞发送
    pub fn try_send(&self, value: T) -> Result<(), TrySendError<T>> {
        self.sender.try_send(value)
    }

    /// 带超时的发送
    pub async fn send_timeout(
        &self,
        value: T,
        timeout: Duration
    ) -> Result<(), TimeoutSendError<T>> {
        tokio::time::timeout(timeout, self.sender.send(value))
            .await
            .map_err(|_| TimeoutSendError::Timeout)?
            .map_err(|_| TimeoutSendError::ChannelClosed)
    }
}

/// 更复杂的背压：使用 Semaphore
use tokio::sync::Semaphore;

pub struct RateLimitedProducer<T> {
    sender: mpsc::Sender<T>,
    /// 限流信号量
    rate_limiter: Arc<Semaphore>,
}

impl<T> RateLimitedProducer<T> {
    pub fn new(sender: mpsc::Sender<T>, max_in_flight: usize) -> Self {
        Self {
            sender,
            rate_limiter: Arc::new(Semaphore::new(max_in_flight)),
        }
    }

    pub async fn send(&self, value: T) -> Result<(), SendError> {
        // 获取许可（背压点）
        let permit = self.rate_limiter.clone().acquire_owned().await
            .map_err(|_| SendError::RateLimiterClosed)?;

        let limiter = self.rate_limiter.clone();

        // 发送消息
        self.sender.send(value).await.map_err(|_| SendError::ChannelClosed)?;

        // 启动任务监控完成，释放许可
        tokio::spawn(async move {
            // 等待消息处理完成...
            drop(permit);
        });

        Ok(())
    }
}
```

### 2.3 发布-订阅模式

**主题订阅语义：**

```rust
/// 发布-订阅语义模型
///
/// 核心概念：
/// 1. 主题（Topic）：消息分类
/// 2. 发布者（Publisher）：发送消息到主题
/// 3. 订阅者（Subscriber）：接收感兴趣的主题消息
/// 4. 代理（Broker）：消息路由
pub trait PubSubSemantics {
    /// 发布语义：发送消息到主题
    ///
    /// 语义：发布后，所有匹配的订阅者最终收到消息
    async fn publish(&self, topic: &Topic, message: &Message) -> PublishResult;

    /// 订阅语义：注册对主题的兴趣
    ///
    /// 语义：订阅后，后续发布的消息会被接收
    async fn subscribe(&self, pattern: &TopicPattern) -> Subscription;

    /// 取消订阅
    async fn unsubscribe(&self, subscription: Subscription) -> UnsubscribeResult;
}

/// 主题语义
///
/// 支持层次结构：order.created, order.updated, order.*
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Topic(String);

impl Topic {
    pub fn new(name: &str) -> Self {
        Topic(name.to_string())
    }

    /// 检查是否匹配通配符模式
    pub fn matches(&self, pattern: &TopicPattern) -> bool {
        match pattern {
            TopicPattern::Exact(t) => self.0 == t.0,
            TopicPattern::Wildcard(pattern) => {
                // 支持 * 单层通配，# 多层通配
                self.match_wildcard(pattern)
            }
        }
    }

    fn match_wildcard(&self, pattern: &str) -> bool {
        let pattern_parts: Vec<&str> = pattern.split('.').collect();
        let topic_parts: Vec<&str> = self.0.split('.').collect();

        let mut p = 0;
        let mut t = 0;

        while p < pattern_parts.len() && t < topic_parts.len() {
            match pattern_parts[p] {
                "#" => return true, // 匹配剩余所有
                "*" => { p += 1; t += 1; }
                part if part == topic_parts[t] => { p += 1; t += 1; }
                _ => return false,
            }
        }

        p == pattern_parts.len() && t == topic_parts.len()
    }
}

#[derive(Debug, Clone)]
pub enum TopicPattern {
    Exact(Topic),
    Wildcard(String),
}

/// Rust 实现（NATS 示例）
pub struct NatsPubSub {
    connection: nats::asynk::Connection,
}

impl NatsPubSub {
    pub async fn connect(server: &str) -> Result<Self, nats::Error> {
        let connection = nats::asynk::connect(server).await?;
        Ok(Self { connection })
    }

    /// 发布消息
    pub async fn publish(&self, subject: &str, payload: &[u8]) -> Result<(), nats::Error> {
        self.connection.publish(subject, payload).await
    }

    /// 订阅主题
    pub async fn subscribe(&self, subject: &str) -> Result<NatsSubscription, nats::Error> {
        let subscription = self.connection.subscribe(subject).await?;
        Ok(NatsSubscription { subscription })
    }

    /// 队列组订阅（负载均衡）
    pub async fn queue_subscribe(
        &self,
        subject: &str,
        queue: &str
    ) -> Result<NatsSubscription, nats::Error> {
        let subscription = self.connection.queue_subscribe(subject, queue).await?;
        Ok(NatsSubscription { subscription })
    }
}

pub struct NatsSubscription {
    subscription: nats::asynk::Subscription,
}

impl NatsSubscription {
    /// 接收消息（流式）
    pub async fn next(&self) -> Option<nats::Message> {
        self.subscription.next().await
    }

    /// 取消订阅
    pub async fn unsubscribe(&self) -> Result<(), nats::Error> {
        self.subscription.unsubscribe().await
    }
}
```

**消息过滤语义：**

```rust
/// 消息过滤语义
///
/// 支持多种过滤策略：
/// 1. 主题匹配：基于层次主题
/// 2. 内容过滤：基于消息内容
/// 3. 头部过滤：基于消息头
pub trait MessageFilter: Send + Sync {
    fn matches(&self, message: &Message) -> bool;
}

/// 复合过滤器
pub struct CompositeFilter {
    filters: Vec<Box<dyn MessageFilter>>,
    operator: FilterOperator,
}

#[derive(Debug, Clone, Copy)]
pub enum FilterOperator {
    And,
    Or,
    Not,
}

impl MessageFilter for CompositeFilter {
    fn matches(&self, message: &Message) -> bool {
        match self.operator {
            FilterOperator::And => self.filters.iter().all(|f| f.matches(message)),
            FilterOperator::Or => self.filters.iter().any(|f| f.matches(message)),
            FilterOperator::Not => self.filters.iter().all(|f| !f.matches(message)),
        }
    }
}

/// 头部过滤器（AMQP 风格）
pub struct HeaderFilter {
    conditions: Vec<(String, String, MatchType)>,
}

#[derive(Debug, Clone, Copy)]
pub enum MatchType {
    Exact,
    Contains,
    StartsWith,
    Regex,
    GreaterThan,
    LessThan,
}

impl MessageFilter for HeaderFilter {
    fn matches(&self, message: &Message) -> bool {
        self.conditions.iter().all(|(key, value, match_type)| {
            let header_value = message.headers.get(key);
            match match_type {
                MatchType::Exact => header_value.map(|v| v == value).unwrap_or(false),
                MatchType::Contains => header_value.map(|v| v.contains(value)).unwrap_or(false),
                MatchType::StartsWith => header_value.map(|v| v.starts_with(value)).unwrap_or(false),
                MatchType::Regex => {
                    header_value.map(|v| {
                        regex::Regex::new(value).ok().map(|re| re.is_match(v)).unwrap_or(false)
                    }).unwrap_or(false)
                }
                MatchType::GreaterThan => {
                    header_value.and_then(|v| v.parse::<f64>().ok())
                        .zip(value.parse::<f64>().ok())
                        .map(|(a, b)| a > b)
                        .unwrap_or(false)
                }
                MatchType::LessThan => {
                    header_value.and_then(|v| v.parse::<f64>().ok())
                        .zip(value.parse::<f64>().ok())
                        .map(|(a, b)| a < b)
                        .unwrap_or(false)
                }
            }
        })
    }
}
```

**订阅者管理语义：**

```rust
/// 订阅者管理器
pub struct SubscriptionManager {
    /// 主题 → 订阅者列表
    subscriptions: Arc<RwLock<HashMap<Topic, Vec<SubscriberHandle>>>>,

    /// 订阅者 ID → 订阅信息
    subscriber_info: Arc<RwLock<HashMap<SubscriberId, SubscriberInfo>>>,
}

#[derive(Debug, Clone)]
pub struct SubscriberInfo {
    id: SubscriberId,
    subscribed_topics: Vec<Topic>,
    created_at: Instant,
    last_activity: Instant,
    message_count: AtomicU64,
}

impl SubscriptionManager {
    /// 添加订阅者
    pub async fn subscribe(
        &self,
        topic: Topic,
        subscriber: SubscriberHandle
    ) -> SubscriptionId {
        let id = SubscriptionId::new();

        let mut subs = self.subscriptions.write().await;
        subs.entry(topic.clone())
            .or_insert_with(Vec::new)
            .push(subscriber.clone());

        let mut info = self.subscriber_info.write().await;
        info.entry(subscriber.id.clone())
            .and_modify(|i| i.subscribed_topics.push(topic.clone()))
            .or_insert(SubscriberInfo {
                id: subscriber.id.clone(),
                subscribed_topics: vec![topic],
                created_at: Instant::now(),
                last_activity: Instant::now(),
                message_count: AtomicU64::new(0),
            });

        id
    }

    /// 移除订阅者（优雅关闭）
    pub async fn unsubscribe(&self, subscription_id: &SubscriptionId) -> Result<(), UnsubscribeError> {
        // 找到并移除订阅
        // 通知订阅者即将停止
        // 等待未确认消息处理或超时
        Ok(())
    }

    /// 广播消息到所有匹配的订阅者
    pub async fn broadcast(&self, topic: &Topic, message: &Message) -> BroadcastResult {
        let subs = self.subscriptions.read().await;
        let mut sent = 0;
        let mut failed = 0;

        // 收集匹配的订阅者
        let matching: Vec<_> = subs.iter()
            .filter(|(t, _)| t.matches(&TopicPattern::Exact(topic.clone())))
            .flat_map(|(_, subscribers)| subscribers.iter())
            .cloned()
            .collect();

        drop(subs); // 释放读锁

        // 并行发送
        for subscriber in matching {
            match subscriber.send(message.clone()).await {
                Ok(_) => sent += 1,
                Err(_) => failed += 1,
            }
        }

        BroadcastResult { sent, failed }
    }

    /// 清理不活跃的订阅者
    pub async fn cleanup_inactive(&self, timeout: Duration) -> usize {
        let mut removed = 0;
        let mut info = self.subscriber_info.write().await;

        info.retain(|id, subscriber| {
            if subscriber.last_activity.elapsed() > timeout {
                removed += 1;
                false
            } else {
                true
            }
        });

        removed
    }
}

#[derive(Debug, Clone)]
pub struct SubscriberHandle {
    id: SubscriberId,
    sender: mpsc::Sender<Message>,
}

impl SubscriberHandle {
    pub async fn send(&self, message: Message) -> Result<(), SendError> {
        self.sender.send(message).await.map_err(|_| SendError::SubscriberDisconnected)
    }
}
```

**消息顺序保证：**

```rust
/// 消息顺序语义
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingGuarantee {
    /// 无序：消息可能乱序到达
    Unordered,

    /// 分区有序：同一分区内有序
    PartitionOrdered,

    /// 全局有序：所有消息严格有序
    GlobalOrdered,

    /// 因果有序：保持因果关系（Happens-Before）
    CausalOrdered,
}

/// 分区有序实现（Kafka 风格）
pub struct PartitionedOrdering {
    /// 分区数
    partition_count: usize,

    /// 分区函数
    partitioner: Box<dyn Fn(&Message) -> usize + Send + Sync>,
}

impl PartitionedOrdering {
    /// 计算消息分区
    pub fn partition(&self, message: &Message) -> usize {
        (self.partitioner)(message) % self.partition_count
    }

    /// 默认分区器：基于 key 的哈希
    pub fn default_partitioner() -> impl Fn(&Message) -> usize {
        |msg: &Message| {
            msg.key.as_ref()
                .map(|k| {
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hash::hash(k, &mut hasher);
                    std::hash::Hasher::finish(&hasher) as usize
                })
                .unwrap_or_else(|| rand::random::<usize>())
        }
    }
}

/// 序列号管理（保证顺序）
pub struct SequenceManager {
    /// 每个分区的当前序列号
    sequences: Arc<RwLock<HashMap<PartitionId, AtomicU64>>>,
}

impl SequenceManager {
    /// 分配下一个序列号
    pub async fn next_sequence(&self, partition: PartitionId) -> u64 {
        let mut seqs = self.sequences.write().await;
        seqs.entry(partition)
            .or_insert_with(|| AtomicU64::new(0))
            .fetch_add(1, Ordering::SeqCst)
    }

    /// 验证消息顺序
    pub async fn validate_order(
        &self,
        partition: PartitionId,
        sequence: u64
    ) -> OrderValidationResult {
        let seqs = self.sequences.read().await;
        let expected = seqs.get(&partition).map(|s| s.load(Ordering::SeqCst)).unwrap_or(0);

        match sequence.cmp(&expected) {
            std::cmp::Ordering::Equal => OrderValidationResult::InOrder,
            std::cmp::Ordering::Less => OrderValidationResult::OutOfOrder { expected, got: sequence },
            std::cmp::Ordering::Greater => OrderValidationResult::Gap { expected, got: sequence },
        }
    }
}

#[derive(Debug)]
pub enum OrderValidationResult {
    InOrder,
    OutOfOrder { expected: u64, got: u64 },
    Gap { expected: u64, got: u64 },
}
```

---

## 3. 服务发现模式

### 3.1 注册中心模式

**服务注册语义：**

```rust
/// 服务注册语义模型
///
/// 核心概念：
/// 1. 服务实例：提供特定服务的进程
/// 2. 注册表：存储服务实例信息的数据结构
/// 3. 租约：有时间限制的服务注册
/// 4. 健康检查：验证服务实例可用性

pub trait ServiceRegistry {
    /// 注册服务实例
    ///
    /// 语义：注册后，服务对消费者可见
    async fn register(&self, instance: ServiceInstance) -> RegistrationResult;

    /// 注销服务实例
    ///
    /// 语义：注销后，服务不再接收新请求
    async fn deregister(&self, instance_id: &InstanceId) -> DeregistrationResult;

    /// 续租（心跳）
    ///
    /// 语义：延长服务注册有效期
    async fn renew(&self, instance_id: &InstanceId) -> RenewalResult;

    /// 发现服务
    ///
    /// 语义：返回所有健康的服务实例
    async fn discover(&self, service_name: &str) -> Vec<ServiceInstance>;
}

/// 服务实例元数据
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ServiceInstance {
    /// 唯一标识
    pub id: InstanceId,

    /// 服务名称
    pub service_name: String,

    /// 网络地址
    pub address: SocketAddr,

    /// 元数据（版本、区域等）
    pub metadata: HashMap<String, String>,

    /// 租约到期时间
    pub lease_expiry: Instant,

    /// 健康状态
    pub health_status: HealthStatus,

    /// 权重（用于负载均衡）
    pub weight: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
    Starting,
    OutOfService,
}

/// 租约语义
pub struct Lease {
    /// 租约 ID
    pub id: LeaseId,

    /// 租约持续时间
    pub ttl: Duration,

    /// 创建时间
    pub created_at: Instant,

    /// 最后更新时间
    pub last_renewed: Instant,

    /// 最大续租次数（可选）
    pub max_renewals: Option<u32>,

    /// 当前续租次数
    pub renewal_count: u32,
}

impl Lease {
    /// 检查租约是否有效
    pub fn is_valid(&self) -> bool {
        let expiry = self.last_renewed + self.ttl;
        Instant::now() < expiry
    }

    /// 检查租约是否即将过期
    pub fn is_expiring_soon(&self, threshold: Duration) -> bool {
        let expiry = self.last_renewed + self.ttl;
        Instant::now() + threshold > expiry
    }

    /// 续租
    pub fn renew(&mut self) -> Result<(), RenewalError> {
        if let Some(max) = self.max_renewals {
            if self.renewal_count >= max {
                return Err(RenewalError::MaxRenewalsExceeded);
            }
        }

        if !self.is_valid() {
            return Err(RenewalError::LeaseExpired);
        }

        self.last_renewed = Instant::now();
        self.renewal_count += 1;
        Ok(())
    }
}
```

**服务发现语义：**

```rust
/// 服务发现语义
pub trait ServiceDiscovery {
    /// 同步发现：立即返回已知实例
    async fn discover(&self, service_name: &str) -> DiscoveryResult;

    /// 监听变化：订阅服务实例变更
    async fn watch(&self, service_name: &str) -> ChangeStream;

    /// 缓存感知发现：优先使用缓存
    async fn discover_cached(&self, service_name: &str) -> CachedDiscoveryResult;
}

/// 发现结果
#[derive(Debug, Clone)]
pub struct DiscoveryResult {
    pub service_name: String,
    pub instances: Vec<ServiceInstance>,
    pub from_cache: bool,
    pub cache_age: Option<Duration>,
}

/// 变更事件流
#[derive(Debug, Clone)]
pub enum ServiceChangeEvent {
    InstanceAdded { instance: ServiceInstance },
    InstanceRemoved { instance_id: InstanceId },
    InstanceUpdated { instance: ServiceInstance },
    HealthChanged { instance_id: InstanceId, status: HealthStatus },
}

/// 客户端发现模式（客户端直接查询注册中心）
pub struct ClientSideDiscovery<R: ServiceRegistry> {
    registry: R,
    cache: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    refresh_interval: Duration,
}

impl<R: ServiceRegistry> ClientSideDiscovery<R> {
    pub fn new(registry: R, refresh_interval: Duration) -> Self {
        let cache = Arc::new(RwLock::new(HashMap::new()));

        // 启动后台刷新任务
        let cache_clone = cache.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(refresh_interval);
            loop {
                interval.tick().await;
                // 刷新缓存
            }
        });

        Self { registry, cache, refresh_interval }
    }

    /// 选择服务实例（带负载均衡）
    pub async fn select_instance(
        &self,
        service_name: &str,
        strategy: LoadBalanceStrategy,
    ) -> Option<ServiceInstance> {
        // 先查缓存
        {
            let cache = self.cache.read().await;
            if let Some(instances) = cache.get(service_name) {
                let healthy: Vec<_> = instances.iter()
                    .filter(|i| i.health_status == HealthStatus::Healthy)
                    .cloned()
                    .collect();

                if !healthy.is_empty() {
                    return self.apply_strategy(&healthy, strategy);
                }
            }
        }

        // 缓存未命中或为空，查询注册中心
        match self.registry.discover(service_name).await {
            Ok(instances) => {
                // 更新缓存
                let mut cache = self.cache.write().await;
                cache.insert(service_name.to_string(), instances.clone());

                let healthy: Vec<_> = instances.into_iter()
                    .filter(|i| i.health_status == HealthStatus.Healthy)
                    .collect();

                self.apply_strategy(&healthy, strategy)
            }
            Err(_) => None,
        }
    }

    fn apply_strategy(&self, instances: &[ServiceInstance], strategy: LoadBalanceStrategy) -> Option<ServiceInstance> {
        match strategy {
            LoadBalanceStrategy::Random => {
                instances.choose(&mut rand::thread_rng()).cloned()
            }
            LoadBalanceStrategy::RoundRobin => {
                // 使用原子计数器实现
                static COUNTER: AtomicUsize = AtomicUsize::new(0);
                let idx = COUNTER.fetch_add(1, Ordering::SeqCst) % instances.len();
                instances.get(idx).cloned()
            }
            LoadBalanceStrategy::WeightedRoundRobin => {
                // 按权重选择
                let total_weight: u32 = instances.iter().map(|i| i.weight).sum();
                let mut rand_weight = rand::random::<u32>() % total_weight;

                for instance in instances {
                    if rand_weight < instance.weight {
                        return Some(instance.clone());
                    }
                    rand_weight -= instance.weight;
                }
                instances.first().cloned()
            }
            LoadBalanceStrategy::LeastConnections => {
                // 选择连接数最少的实例
                // 需要额外跟踪连接数
                instances.first().cloned()
            }
        }
    }
}

/// 服务端发现模式（通过负载均衡器）
pub struct ServerSideDiscovery {
    load_balancer: Arc<dyn LoadBalancer>,
}

impl ServerSideDiscovery {
    /// 客户端只需要知道负载均衡器地址
    pub async fn call_service(&self, service_name: &str, request: Request) -> Response {
        // 负载均衡器负责选择实例并转发
        self.load_balancer.route(service_name, request).await
    }
}
```

**健康检查语义：**

```rust
/// 健康检查语义模型
#[async_trait]
pub trait HealthChecker {
    /// 执行健康检查
    async fn check(&self, instance: &ServiceInstance) -> HealthStatus;

    /// 检查类型
    fn check_type(&self) -> CheckType;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckType {
    /// HTTP 端点检查
    Http { endpoint: &'static str, expected_status: u16 },
    /// TCP 端口检查
    Tcp { timeout: Duration },
    /// gRPC 健康检查
    Grpc { service: &'static str },
    /// 自定义命令检查
    Command { cmd: &'static str },
}

/// 健康检查调度器
pub struct HealthCheckScheduler {
    checkers: Vec<Arc<dyn HealthChecker>>,
    interval: Duration,
    timeout: Duration,
    results: Arc<RwLock<HashMap<InstanceId, HealthCheckResult>>>,
}

#[derive(Debug, Clone)]
pub struct HealthCheckResult {
    pub instance_id: InstanceId,
    pub status: HealthStatus,
    pub checked_at: Instant,
    pub response_time: Duration,
    pub consecutive_failures: u32,
    pub consecutive_successes: u32,
    pub last_error: Option<String>,
}

impl HealthCheckScheduler {
    pub fn new(interval: Duration, timeout: Duration) -> Self {
        Self {
            checkers: Vec::new(),
            interval,
            timeout,
            results: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 启动健康检查循环
    pub async fn start(&self, instances: Arc<RwLock<Vec<ServiceInstance>>>) {
        let mut interval = tokio::time::interval(self.interval);

        loop {
            interval.tick().await;

            let instances = instances.read().await.clone();

            for instance in instances {
                let checkers = self.checkers.clone();
                let results = self.results.clone();
                let timeout = self.timeout;

                // 并发执行所有检查器
                tokio::spawn(async move {
                    for checker in checkers {
                        let check_future = checker.check(&instance);

                        match tokio::time::timeout(timeout, check_future).await {
                            Ok(status) => {
                                let mut results = results.write().await;
                                let result = results.entry(instance.id.clone()).or_insert_with(|| {
                                    HealthCheckResult {
                                        instance_id: instance.id.clone(),
                                        status: HealthStatus::Unknown,
                                        checked_at: Instant::now(),
                                        response_time: Duration::ZERO,
                                        consecutive_failures: 0,
                                        consecutive_successes: 0,
                                        last_error: None,
                                    }
                                });

                                result.checked_at = Instant::now();

                                match status {
                                    HealthStatus::Healthy => {
                                        result.consecutive_successes += 1;
                                        result.consecutive_failures = 0;
                                        if result.consecutive_successes >= 2 {
                                            result.status = HealthStatus::Healthy;
                                        }
                                    }
                                    _ => {
                                        result.consecutive_failures += 1;
                                        result.consecutive_successes = 0;
                                        if result.consecutive_failures >= 3 {
                                            result.status = HealthStatus::Unhealthy;
                                        }
                                    }
                                }
                            }
                            Err(_) => {
                                // 超时
                                let mut results = results.write().await;
                                if let Some(result) = results.get_mut(&instance.id) {
                                    result.consecutive_failures += 1;
                                    result.status = HealthStatus::Unhealthy;
                                    result.last_error = Some("Health check timeout".to_string());
                                }
                            }
                        }
                    }
                });
            }
        }
    }
}

/// 负载均衡语义
#[async_trait]
pub trait LoadBalancer: Send + Sync {
    async fn select(&self, instances: &[ServiceInstance]) -> Option<InstanceId>;
    async fn report_result(&self, instance_id: &InstanceId, success: bool, latency: Duration);
}

/// 自适应负载均衡（考虑延迟和健康）
pub struct AdaptiveLoadBalancer {
    /// 实例性能统计
    stats: Arc<RwLock<HashMap<InstanceId, InstanceStats>>>,
}

#[derive(Debug, Clone, Default)]
struct InstanceStats {
    total_requests: u64,
    successful_requests: u64,
    failed_requests: u64,
    total_latency: Duration,
    last_used: Instant,
}

impl AdaptiveLoadBalancer {
    /// 计算实例得分（越低越好）
    fn calculate_score(&self, stats: &InstanceStats) -> f64 {
        if stats.total_requests == 0 {
            return 0.0; // 新实例优先
        }

        let error_rate = stats.failed_requests as f64 / stats.total_requests as f64;
        let avg_latency = stats.total_latency.as_millis() as f64 / stats.total_requests as f64;

        // 得分公式：错误率权重 0.7，延迟权重 0.3
        error_rate * 0.7 + (avg_latency / 1000.0) * 0.3
    }
}

#[async_trait]
impl LoadBalancer for AdaptiveLoadBalancer {
    async fn select(&self, instances: &[ServiceInstance]) -> Option<InstanceId> {
        let stats = self.stats.read().await;

        instances.iter()
            .filter(|i| i.health_status == HealthStatus::Healthy)
            .min_by_key(|i| {
                let instance_stats = stats.get(&i.id).cloned().unwrap_or_default();
                (self.calculate_score(&instance_stats) * 1000.0) as u64
            })
            .map(|i| i.id.clone())
    }

    async fn report_result(&self, instance_id: &InstanceId, success: bool, latency: Duration) {
        let mut stats = self.stats.write().await;
        let entry = stats.entry(instance_id.clone()).or_default();

        entry.total_requests += 1;
        entry.total_latency += latency;
        entry.last_used = Instant::now();

        if success {
            entry.successful_requests += 1;
        } else {
            entry.failed_requests += 1;
        }
    }
}
```

### 3.2 去中心化发现

**Gossip 协议语义：**

```rust
/// Gossip 协议语义模型
///
/// 核心概念：
/// 1. 流言传播：节点随机选择对等节点交换信息
/// 2. 最终一致性：信息最终会传播到所有节点
/// 3. 抗故障：不依赖中心节点

pub struct GossipProtocol {
    /// 本节点 ID
    node_id: NodeId,

    /// 已知节点列表（部分视图）
    membership: Arc<RwLock<MembershipList>>,

    /// Gossip 间隔
    gossip_interval: Duration,

    /// 每次 gossip 选择的节点数
    gossip_fanout: usize,
}

/// 成员列表（带版本向量）
#[derive(Debug, Clone)]
pub struct MembershipList {
    /// 节点 ID → 节点信息
    members: HashMap<NodeId, NodeInfo>,

    /// 版本向量（用于检测并发更新）
    version_vector: VersionVector,
}

#[derive(Debug, Clone)]
pub struct NodeInfo {
    pub id: NodeId,
    pub address: SocketAddr,
    pub heartbeat: u64,
    pub last_seen: Instant,
    pub metadata: HashMap<String, String>,
    pub incarnation: u64, // 用于解决冲突
}

/// 版本向量（因果一致性）
#[derive(Debug, Clone, Default)]
pub struct VersionVector {
    /// 节点 ID → 版本号
    versions: HashMap<NodeId, u64>,
}

impl VersionVector {
    /// 增加本节点版本
    pub fn increment(&mut self, node_id: &NodeId) {
        *self.versions.entry(node_id.clone()).or_insert(0) += 1;
    }

    /// 合并两个版本向量
    pub fn merge(&mut self, other: &VersionVector) {
        for (node, version) in &other.versions {
            let entry = self.versions.entry(node.clone()).or_insert(0);
            *entry = (*entry).max(*version);
        }
    }

    /// 比较版本向量
    pub fn compare(&self, other: &VersionVector) -> VersionComparison {
        let dominates = self.dominates(other);
        let dominated = other.dominates(self);

        match (dominates, dominated) {
            (true, false) => VersionComparison::Greater,
            (false, true) => VersionComparison::Less,
            (false, false) => VersionComparison::Concurrent,
            (true, true) => VersionComparison::Equal,
        }
    }

    fn dominates(&self, other: &VersionVector) -> bool {
        for (node, version) in &self.versions {
            let other_version = other.versions.get(node).copied().unwrap_or(0);
            if *version < other_version {
                return false;
            }
        }
        true
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionComparison {
    Greater,   // self > other
    Less,      // self < other
    Equal,     // self == other
    Concurrent,// 并发，无因果关系
}

impl GossipProtocol {
    /// 启动 gossip 协议
    pub async fn start(&self) {
        let mut interval = tokio::time::interval(self.gossip_interval);

        loop {
            interval.tick().await;
            self.gossip_round().await;
        }
    }

    /// 一轮 gossip
    async fn gossip_round(&self) {
        let members = self.membership.read().await;

        // 随机选择 gossip_fanout 个节点
        let targets: Vec<_> = members.members.values()
            .filter(|m| m.id != self.node_id)
            .filter(|m| m.last_seen.elapsed() < Duration::from_secs(30))
            .choose_multiple(&mut rand::thread_rng(), self.gossip_fanout);

        drop(members);

        // 并行向目标节点发送 gossip 消息
        for target in targets {
            let membership = self.membership.clone();
            let target = target.clone();

            tokio::spawn(async move {
                // 发送 gossip 消息
                let digest = Self::create_digest(&membership).await;

                // 模拟网络调用
                // let response = send_gossip(target.address, digest).await;

                // 合并响应
                // Self::merge_membership(membership, response).await;
            });
        }
    }

    /// 创建摘要（用于交换）
    async fn create_digest(membership: &Arc<RwLock<MembershipList>>) -> GossipDigest {
        let members = membership.read().await;

        GossipDigest {
            node_heartbeats: members.members.iter()
                .map(|(id, info)| (id.clone(), info.heartbeat))
                .collect(),
            version_vector: members.version_vector.clone(),
        }
    }

    /// 合并成员信息
    pub async fn merge_membership(&self, delta: Vec<NodeInfo>) {
        let mut members = self.membership.write().await;

        for info in delta {
            match members.members.get_mut(&info.id) {
                Some(existing) => {
                    // 解决冲突：选择更大的心跳或化身号
                    if info.heartbeat > existing.heartbeat ||
                       (info.heartbeat == existing.heartbeat && info.incarnation > existing.incarnation) {
                        *existing = info;
                    }
                }
                None => {
                    members.members.insert(info.id.clone(), info);
                }
            }
        }

        members.version_vector.increment(&self.node_id);
    }

    /// 检测故障节点（基于心跳超时）
    pub async fn detect_failures(&self, timeout: Duration) -> Vec<NodeId> {
        let mut members = self.membership.write().await;
        let mut failed = Vec::new();

        members.members.retain(|id, info| {
            if info.last_seen.elapsed() > timeout && *id != self.node_id {
                failed.push(id.clone());
                false
            } else {
                true
            }
        });

        failed
    }
}

#[derive(Debug, Clone)]
pub struct GossipDigest {
    pub node_heartbeats: HashMap<NodeId, u64>,
    pub version_vector: VersionVector,
}
```

**一致性哈希语义：**

```rust
/// 一致性哈希语义
///
/// 核心特性：
/// 1. 单调性：添加/移除节点不会导致大量重新映射
/// 2. 平衡性：数据均匀分布
/// 3. 分散性：相同 key 在不同节点集上映射到相同节点

pub struct ConsistentHashRing {
    /// 虚拟节点数量（提高平衡性）
    virtual_nodes: usize,

    /// 哈希环：哈希值 → 物理节点
    ring: BTreeMap<u64, NodeId>,

    /// 物理节点 → 虚拟节点哈希值
    node_to_hashes: HashMap<NodeId, Vec<u64>>,

    /// 哈希函数
    hasher: Box<dyn Fn(&str) -> u64 + Send + Sync>,
}

impl ConsistentHashRing {
    pub fn new(virtual_nodes: usize) -> Self {
        Self {
            virtual_nodes,
            ring: BTreeMap::new(),
            node_to_hashes: HashMap::new(),
            hasher: Box::new(|s| {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                s.hash(&mut hasher);
                hasher.finish()
            }),
        }
    }

    /// 添加节点
    pub fn add_node(&mut self, node_id: NodeId) {
        let mut hashes = Vec::with_capacity(self.virtual_nodes);

        for i in 0..self.virtual_nodes {
            // 为每个虚拟节点生成哈希值
            let virtual_key = format!("{}:{}", node_id, i);
            let hash = (self.hasher)(&virtual_key);

            self.ring.insert(hash, node_id.clone());
            hashes.push(hash);
        }

        self.node_to_hashes.insert(node_id, hashes);
    }

    /// 移除节点
    pub fn remove_node(&mut self, node_id: &NodeId) -> Vec<u64> {
        let hashes = self.node_to_hashes.remove(node_id).unwrap_or_default();

        for hash in &hashes {
            self.ring.remove(hash);
        }

        hashes
    }

    /// 获取 key 对应的节点
    pub fn get_node(&self, key: &str) -> Option<&NodeId> {
        if self.ring.is_empty() {
            return None;
        }

        let hash = (self.hasher)(key);

        // 顺时针查找第一个节点
        self.ring.range(hash..).next().map(|(_, node)| node)
            .or_else(|| self.ring.values().next()) // 回环到第一个
    }

    /// 获取 key 对应的多个节点（用于副本）
    pub fn get_nodes(&self, key: &str, count: usize) -> Vec<&NodeId> {
        if self.ring.is_empty() {
            return Vec::new();
        }

        let hash = (self.hasher)(key);
        let mut result = Vec::with_capacity(count);
        let mut seen = HashSet::new();

        // 从 hash 位置开始顺时针遍历
        for (_, node) in self.ring.range(hash..).chain(self.ring.iter()) {
            if seen.insert(node) {
                result.push(node);
                if result.len() >= count {
                    break;
                }
            }
        }

        result
    }

    /// 计算添加节点时的迁移数据量
    pub fn migration_cost(&self, new_node: &NodeId) -> usize {
        // 添加虚拟节点后，每个虚拟节点接管一部分数据
        // 估算迁移成本
        let total_range = u64::MAX;
        let virtual_range = total_range / (self.ring.len() + self.virtual_nodes) as u64;

        self.virtual_nodes * virtual_range as usize
    }
}

/// 带权重的改进版一致性哈希
pub struct WeightedConsistentHash {
    ring: ConsistentHashRing,
    node_weights: HashMap<NodeId, u32>,
}

impl WeightedConsistentHash {
    pub fn add_node_weighted(&mut self, node_id: NodeId, weight: u32) {
        // 根据权重决定虚拟节点数量
        let virtual_nodes = (weight as usize) * 10; // 每个权重单位 10 个虚拟节点

        // 创建临时环计算虚拟节点位置
        for i in 0..virtual_nodes {
            let hash = self.hash_virtual_node(&node_id, i);
            // ...
        }

        self.node_weights.insert(node_id, weight);
    }

    fn hash_virtual_node(&self, node: &NodeId, index: usize) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        format!("{}:{}", node, index).hash(&mut hasher);
        hasher.finish()
    }
}
```

**虚拟节点语义：**

```rust
/// 虚拟节点语义
///
/// 目的：
/// 1. 提高负载均衡性
/// 2. 减少节点加入/离开时的影响范围
/// 3. 支持异构节点权重

#[derive(Debug, Clone)]
pub struct VirtualNode {
    /// 虚拟节点哈希值
    pub hash: u64,

    /// 所属物理节点
    pub physical_node: NodeId,

    /// 虚拟节点序号
    pub index: usize,
}

/// 虚拟节点管理器
pub struct VirtualNodeManager {
    /// 虚拟节点到物理节点的映射
    virtual_to_physical: HashMap<u64, NodeId>,

    /// 物理节点到虚拟节点的映射
    physical_to_virtual: HashMap<NodeId, Vec<u64>>,

    /// 虚拟节点数因子（每个物理节点的虚拟节点数）
    replication_factor: usize,
}

impl VirtualNodeManager {
    /// 创建虚拟节点
    pub fn create_virtual_nodes(&mut self, physical_node: NodeId) -> Vec<VirtualNode> {
        let mut virtual_nodes = Vec::with_capacity(self.replication_factor);
        let mut hashes = Vec::with_capacity(self.replication_factor);

        for i in 0..self.replication_factor {
            let hash = self.compute_hash(&physical_node, i);

            virtual_nodes.push(VirtualNode {
                hash,
                physical_node: physical_node.clone(),
                index: i,
            });

            hashes.push(hash);
            self.virtual_to_physical.insert(hash, physical_node.clone());
        }

        self.physical_to_virtual.insert(physical_node, hashes);
        virtual_nodes
    }

    /// 计算虚拟节点哈希
    fn compute_hash(&self, node: &NodeId, index: usize) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        // 使用多种哈希算法减少冲突
        format!("vn:{}:{}", node, index).hash(&mut hasher);
        hasher.finish()
    }

    /// 获取物理节点
    pub fn get_physical_node(&self, hash: u64) -> Option<&NodeId> {
        self.virtual_to_physical.get(&hash)
    }

    /// 获取虚拟节点数量
    pub fn virtual_node_count(&self) -> usize {
        self.virtual_to_physical.len()
    }

    /// 计算节点负载（拥有的虚拟节点数）
    pub fn node_load(&self, node: &NodeId) -> usize {
        self.physical_to_virtual
            .get(node)
            .map(|v| v.len())
            .unwrap_or(0)
    }
}
```

---

## 4. 一致性与共识模式

### 4.1 强一致性模式

**两阶段提交 (2PC) 语义：**

```rust
/// 两阶段提交语义模型
///
/// Phase 1 (Prepare): 协调者询问所有参与者是否可提交
/// Phase 2 (Commit/Rollback): 根据响应决定提交或回滚
///
/// 关键问题：协调者单点故障可能导致阻塞

pub struct TwoPhaseCommit {
    /// 事务 ID
    tx_id: TransactionId,

    /// 协调者
    coordinator: Coordinator,

    /// 参与者
    participants: Vec<Participant>,

    /// 事务日志（用于恢复）
    tx_log: Arc<RwLock<TransactionLog>>,
}

/// 协调者
pub struct Coordinator {
    id: NodeId,
    timeout: Duration,
}

/// 参与者
pub struct Participant {
    id: NodeId,
    resource_manager: Arc<dyn ResourceManager>,
}

#[async_trait]
pub trait ResourceManager: Send + Sync {
    /// 准备阶段：执行本地事务，锁定资源
    async fn prepare(&self, tx_id: &TransactionId, operation: &Operation) -> PrepareResult;

    /// 提交阶段：提交本地事务
    async fn commit(&self, tx_id: &TransactionId) -> CommitResult;

    /// 回滚阶段：回滚本地事务
    async fn rollback(&self, tx_id: &TransactionId) -> RollbackResult;
}

#[derive(Debug, Clone)]
pub enum PrepareResult {
    Yes,                 // 可以提交
    No(String),         // 无法提交（理由）
    Timeout,
}

impl TwoPhaseCommit {
    /// 执行两阶段提交
    pub async fn execute(&self, operation: Operation) -> TxResult {
        // Phase 1: Prepare
        let prepare_results = self.phase_one_prepare(&operation).await?;

        // 检查所有参与者是否同意
        let all_prepared = prepare_results.iter().all(|r| matches!(r, PrepareResult::Yes));

        // Phase 2: Commit 或 Rollback
        if all_prepared {
            // 先写日志（WAL 原则）
            self.log_decision(&self.tx_id, TxDecision::Commit).await?;

            // 发送 Commit 给所有参与者
            self.phase_two_commit().await?;

            Ok(TxOutcome::Committed)
        } else {
            // 记录回滚决定
            self.log_decision(&self.tx_id, TxDecision::Rollback).await?;

            // 发送 Rollback 给所有参与者
            self.phase_two_rollback().await?;

            Ok(TxOutcome::RolledBack)
        }
    }

    /// Phase 1: Prepare
    async fn phase_one_prepare(&self, operation: &Operation) -> TxResult<Vec<PrepareResult>> {
        let mut futures = Vec::new();

        for participant in &self.participants {
            let tx_id = self.tx_id.clone();
            let op = operation.clone();
            let participant_id = participant.id.clone();

            // 并行发送 Prepare 请求
            let future = tokio::time::timeout(
                self.coordinator.timeout,
                participant.resource_manager.prepare(&tx_id, &op)
            );

            futures.push(future);
        }

        let results = futures::future::join_all(futures).await;

        Ok(results.into_iter()
            .map(|r| match r {
                Ok(Ok(result)) => result,
                Ok(Err(_)) => PrepareResult::No("Resource manager error".to_string()),
                Err(_) => PrepareResult::Timeout,
            })
            .collect())
    }

    /// Phase 2: Commit
    async fn phase_two_commit(&self) -> TxResult<()> {
        let mut futures = Vec::new();

        for participant in &self.participants {
            let tx_id = self.tx_id.clone();
            let rm = participant.resource_manager.clone();

            let future = tokio::spawn(async move {
                tokio::time::timeout(
                    Duration::from_secs(30),
                    rm.commit(&tx_id)
                ).await
            });

            futures.push(future);
        }

        // 等待所有提交完成（部分失败需要记录以便恢复）
        let results = futures::future::join_all(futures).await;

        // 记录提交结果
        for (idx, result) in results.iter().enumerate() {
            if let Err(e) = result {
                tracing::error!("Participant {} commit failed: {:?}", idx, e);
                // 记录到未解决事务列表，需要人工介入或自动恢复
            }
        }

        Ok(())
    }

    /// Phase 2: Rollback
    async fn phase_two_rollback(&self) -> TxResult<()> {
        // 类似 commit，发送 rollback 给所有参与者
        Ok(())
    }

    /// 记录事务决策（用于协调者故障恢复）
    async fn log_decision(&self, tx_id: &TransactionId, decision: TxDecision) -> TxResult<()> {
        let mut log = self.tx_log.write().await;
        log.record(TransactionRecord {
            tx_id: tx_id.clone(),
            decision,
            timestamp: Instant::now(),
            participants: self.participants.iter().map(|p| p.id.clone()).collect(),
        });

        // 强制刷盘
        log.flush().await?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum TxDecision {
    Commit,
    Rollback,
}

#[derive(Debug, Clone)]
pub enum TxOutcome {
    Committed,
    RolledBack,
    InDoubt,  // 协调者故障，结果未知
}
```

**三阶段提交 (3PC) 语义：**

```rust
/// 三阶段提交语义模型
///
/// 解决 2PC 的协调者单点故障阻塞问题：
/// Phase 1 (CanCommit): 协调者询问参与者是否可以执行
/// Phase 2 (PreCommit): 参与者预提交，准备就绪
/// Phase 3 (DoCommit): 实际提交
///
/// 关键改进：引入超时机制，允许参与者在超时后单方面决定

pub struct ThreePhaseCommit {
    tx_id: TransactionId,
    coordinator: Coordinator,
    participants: Vec<Participant>,
    tx_log: Arc<RwLock<TransactionLog>>,
}

impl ThreePhaseCommit {
    /// 执行三阶段提交
    pub async fn execute(&self, operation: Operation) -> TxResult {
        // Phase 1: CanCommit
        let can_commit_results = self.phase_one_can_commit(&operation).await?;

        if !can_commit_results.iter().all(|r| r.agreed) {
            return self.abort().await;
        }

        // Phase 2: PreCommit
        self.phase_two_pre_commit().await?;

        // Phase 3: DoCommit
        self.phase_three_do_commit().await?;

        Ok(TxOutcome::Committed)
    }

    /// Phase 1: CanCommit
    ///
    /// 语义：询问参与者是否可以执行事务（不锁定资源）
    async fn phase_one_can_commit(&self, operation: &Operation) -> TxResult<Vec<CanCommitResponse>> {
        // 发送 CanCommit 请求，收集响应
        Ok(Vec::new())
    }

    /// Phase 2: PreCommit
    ///
    /// 语义：参与者预提交，锁定资源，但不最终提交
    async fn phase_two_pre_commit(&self) -> TxResult<()> {
        self.log_decision(&self.tx_id, TxDecision::PreCommit).await?;

        // 发送 PreCommit 给所有参与者
        // 参与者收到后进入 PREPARED 状态，启动超时定时器

        Ok(())
    }

    /// Phase 3: DoCommit
    ///
    /// 语义：最终提交
    async fn phase_three_do_commit(&self) -> TxResult<()> {
        self.log_decision(&self.tx_id, TxDecision::Commit).await?;

        // 发送 DoCommit 给所有参与者

        Ok(())
    }

    /// 参与者超时处理
    ///
    /// 关键语义：
    /// - 如果在 PreCommit 之后超时：可以安全提交（因为协调者已经决定）
    /// - 如果在 CanCommit 之后、PreCommit 之前超时：必须回滚
    pub async fn handle_participant_timeout(&self, state: ParticipantState) -> TimeoutDecision {
        match state {
            ParticipantState::WaitingCanCommit => TimeoutDecision::Abort,
            ParticipantState::PreCommitted => TimeoutDecision::Commit, // 3PC 的关键改进
            ParticipantState::WaitingDoCommit => TimeoutDecision::Commit,
            _ => TimeoutDecision::Abort,
        }
    }

    async fn abort(&self) -> TxResult<TxOutcome> {
        self.log_decision(&self.tx_id, TxDecision::Rollback).await?;
        // 发送 Abort 给所有参与者
        Ok(TxOutcome::RolledBack)
    }
}

#[derive(Debug, Clone)]
pub struct CanCommitResponse {
    pub agreed: bool,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Copy)]
pub enum ParticipantState {
    Initial,
    WaitingCanCommit,
    PreCommitted,
    WaitingDoCommit,
    Committed,
    Aborted,
}

#[derive(Debug, Clone, Copy)]
pub enum TimeoutDecision {
    Commit,
    Abort,
}
```

**Paxos 语义：**

```rust
/// Paxos 共识算法语义模型
///
/// 核心概念：
/// 1. Proposer：提议者，发起提案
/// 2. Acceptor：接受者，对提案投票
/// 3. Learner：学习者，学习已选定的值
///
/// 两阶段：
/// Phase 1 (Prepare): Proposer 获取承诺
/// Phase 2 (Accept): Proposer 请求接受

pub struct PaxosNode {
    node_id: NodeId,
    role: PaxosRole,

    /// 已承诺的最大提案号
    promised_proposal: Arc<AtomicU64>,

    /// 已接受的提案
    accepted_proposal: Arc<RwLock<Option<(ProposalNumber, Value)>>>,

    /// 已选定的值
    chosen_value: Arc<RwLock<Option<Value>>>,
}

#[derive(Debug, Clone, Copy)]
pub enum PaxosRole {
    Proposer,
    Acceptor,
    Learner,
    MultiRole, // 可以扮演多个角色
}

/// 提案号（全局唯一且递增）
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProposalNumber {
    /// 轮次号
    round: u64,
    /// 节点 ID（确保全局唯一）
    node_id: u64,
}

impl ProposalNumber {
    pub fn new(round: u64, node_id: u64) -> Self {
        Self { round, node_id }
    }

    /// 生成下一个提案号
    pub fn next(&self, node_id: u64) -> Self {
        Self {
            round: self.round + 1,
            node_id,
        }
    }
}

/// Paxos 消息
#[derive(Debug, Clone)]
pub enum PaxosMessage {
    /// Phase 1a: Prepare 请求
    Prepare {
        proposal_number: ProposalNumber,
    },

    /// Phase 1b: Promise 响应
    Promise {
        proposal_number: ProposalNumber,
        last_accepted: Option<(ProposalNumber, Value)>,
    },

    /// Phase 2a: Accept 请求
    AcceptRequest {
        proposal_number: ProposalNumber,
        value: Value,
    },

    /// Phase 2b: Accepted 响应
    Accepted {
        proposal_number: ProposalNumber,
        value: Value,
    },
}

impl PaxosNode {
    /// Phase 1: Prepare
    ///
    /// Proposer 发送 Prepare 请求，收集 Promise
    pub async fn phase_one_prepare(
        &self,
        proposal_number: ProposalNumber,
        acceptors: &[NodeId],
    ) -> Result<Value, PaxosError> {
        let prepare_msg = PaxosMessage::Prepare { proposal_number };

        // 发送 Prepare 给大多数 Acceptor
        let promises = self.broadcast_and_collect::<PromiseResponse>(
            acceptors,
            &prepare_msg,
            acceptors.len() / 2 + 1, // 大多数
        ).await?;

        // 如果有 Acceptor 已经接受了值，使用那个值
        let mut highest_accepted: Option<(ProposalNumber, Value)> = None;
        for promise in promises {
            if let Some((prop_num, value)) = promise.last_accepted {
                if highest_accepted.is_none() || prop_num > highest_accepted.as_ref().unwrap().0 {
                    highest_accepted = Some((prop_num, value));
                }
            }
        }

        // 如果已有接受的值，必须提案那个值；否则可以提案自己的值
        Ok(highest_accepted.map(|(_, v)| v).unwrap_or_else(|| self.propose_value()))
    }

    /// Phase 2: Accept
    ///
    /// Proposer 发送 Accept 请求，收集 Accepted
    pub async fn phase_two_accept(
        &self,
        proposal_number: ProposalNumber,
        value: Value,
        acceptors: &[NodeId],
    ) -> Result<(), PaxosError> {
        let accept_msg = PaxosMessage::AcceptRequest { proposal_number, value: value.clone() };

        // 发送 AcceptRequest 给大多数 Acceptor
        let accepted = self.broadcast_and_collect::<AcceptedResponse>(
            acceptors,
            &accept_msg,
            acceptors.len() / 2 + 1,
        ).await?;

        // 如果大多数 Acceptor 接受了，值被选定
        if accepted.len() >= acceptors.len() / 2 + 1 {
            // 广播 Chosen 消息给所有 Learner
            self.broadcast_learn(&value).await?;
            Ok(())
        } else {
            Err(PaxosError::NotEnoughAccepts)
        }
    }

    /// 处理 Prepare 请求（Acceptor 行为）
    pub async fn handle_prepare(&self, proposal_number: ProposalNumber) -> PaxosMessage {
        let promised = self.promised_proposal.load(Ordering::SeqCst);

        if proposal_number.round > promised {
            // 承诺不接受更小的提案号
            self.promised_proposal.store(proposal_number.round, Ordering::SeqCst);

            // 返回已接受的值（如果有）
            let last_accepted = self.accepted_proposal.read().await.clone();

            PaxosMessage::Promise {
                proposal_number,
                last_accepted,
            }
        } else {
            // 拒绝（可以返回拒绝消息或忽略）
            PaxosMessage::Promise {
                proposal_number: ProposalNumber::new(promised, 0),
                last_accepted: None,
            }
        }
    }

    /// 处理 AcceptRequest（Acceptor 行为）
    pub async fn handle_accept_request(
        &self,
        proposal_number: ProposalNumber,
        value: Value,
    ) -> PaxosMessage {
        let promised = self.promised_proposal.load(Ordering::SeqCst);

        // 只接受已承诺的提案号或更大的
        if proposal_number.round >= promised {
            let mut accepted = self.accepted_proposal.write().await;
            *accepted = Some((proposal_number, value.clone()));

            PaxosMessage::Accepted { proposal_number, value }
        } else {
            // 拒绝
            PaxosMessage::Accepted {
                proposal_number: ProposalNumber::new(promised, 0),
                value: Value::empty(),
            }
        }
    }

    /// 完整 Paxos 流程
    pub async fn propose(&self, value: Value, acceptors: &[NodeId]) -> Result<(), PaxosError> {
        let proposal_number = self.generate_proposal_number();

        // Phase 1
        let value_to_propose = self.phase_one_prepare(proposal_number, acceptors).await?;

        // Phase 2
        self.phase_two_accept(proposal_number, value_to_propose, acceptors).await?;

        Ok(())
    }

    fn generate_proposal_number(&self) -> ProposalNumber {
        ProposalNumber::new(
            rand::random(),
            self.node_id.parse().unwrap_or(0),
        )
    }

    fn propose_value(&self) -> Value {
        Value::from_bytes(b"proposed_value")
    }

    async fn broadcast_and_collect<T>(&self, nodes: &[NodeId], msg: &PaxosMessage, quorum: usize) -> Result<Vec<T>, PaxosError> {
        // 实际实现需要网络通信
        Ok(Vec::new())
    }

    async fn broadcast_learn(&self, value: &Value) -> Result<(), PaxosError> {
        Ok(())
    }
}

#[derive(Debug)]
pub enum PaxosError {
    NotEnoughPromises,
    NotEnoughAccepts,
    Timeout,
    NetworkError(String),
}

#[derive(Debug, Clone)]
pub struct PromiseResponse {
    proposal_number: ProposalNumber,
    last_accepted: Option<(ProposalNumber, Value)>,
}

#[derive(Debug, Clone)]
pub struct AcceptedResponse {
    proposal_number: ProposalNumber,
    value: Value,
}

#[derive(Debug, Clone)]
pub struct Value {
    data: Vec<u8>,
}

impl Value {
    pub fn from_bytes(data: &[u8]) -> Self {
        Self { data: data.to_vec() }
    }

    pub fn empty() -> Self {
        Self { data: Vec::new() }
    }
}
```

**Raft 语义：**

```rust
/// Raft 共识算法语义模型
///
/// 三个子问题：
/// 1. 领导者选举：选举唯一的领导者
/// 2. 日志复制：领导者复制日志到跟随者
/// 3. 安全性：保证所有节点以相同顺序应用相同的日志条目

pub struct RaftNode {
    /// 节点 ID
    id: NodeId,

    /// 当前任期
    current_term: Arc<AtomicU64>,

    /// 投票给哪个候选人（任期内）
    voted_for: Arc<RwLock<Option<NodeId>>>,

    /// 日志条目
    log: Arc<RwLock<Vec<LogEntry>>>,

    /// 已提交的最高日志索引
    commit_index: Arc<AtomicU64>,

    /// 已应用到状态机的最高日志索引
    last_applied: Arc<AtomicU64>,

    /// 状态机
    state: Arc<RwLock<RaftState>>,

    /// 选举配置
    config: ElectionConfig,
}

/// Raft 节点状态
#[derive(Debug, Clone)]
pub enum RaftState {
    Follower {
        leader_id: Option<NodeId>,
        /// 选举超时定时器
        election_timer: Instant,
    },
    Candidate {
        /// 获得的票数
        votes_received: HashSet<NodeId>,
        /// 选举开始时间
        election_start: Instant,
    },
    Leader {
        /// 每个跟随者的下一个日志索引
        next_index: HashMap<NodeId, u64>,
        /// 每个跟随者已复制的最高日志索引
        match_index: HashMap<NodeId, u64>,
    },
}

/// 日志条目
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogEntry {
    /// 创建时的任期
    pub term: u64,
    /// 在日志中的索引
    pub index: u64,
    /// 命令数据
    pub command: Vec<u8>,
}

/// Raft RPC 消息
#[derive(Debug, Clone)]
pub enum RaftMessage {
    /// 请求投票（候选人 → 其他节点）
    RequestVote {
        term: u64,
        candidate_id: NodeId,
        last_log_index: u64,
        last_log_term: u64,
    },

    /// 请求投票响应
    RequestVoteResponse {
        term: u64,
        vote_granted: bool,
    },

    /// 追加日志条目（领导者 → 跟随者）
    AppendEntries {
        term: u64,
        leader_id: NodeId,
        prev_log_index: u64,
        prev_log_term: u64,
        entries: Vec<LogEntry>,
        leader_commit: u64,
    },

    /// 追加日志条目响应
    AppendEntriesResponse {
        term: u64,
        success: bool,
        match_index: u64,
    },
}

impl RaftNode {
    /// 处理 RequestVote（跟随者行为）
    pub async fn handle_request_vote(
        &self,
        req: RequestVote,
    ) -> RequestVoteResponse {
        let mut state = self.state.write().await;
        let current_term = self.current_term.load(Ordering::SeqCst);

        // 如果任期更小，拒绝
        if req.term < current_term {
            return RequestVoteResponse {
                term: current_term,
                vote_granted: false,
            };
        }

        // 如果任期更大，更新自己的任期，转为跟随者
        if req.term > current_term {
            self.current_term.store(req.term, Ordering::SeqCst);
            *state = RaftState::Follower {
                leader_id: None,
                election_timer: Instant::now(),
            };
        }

        // 检查是否已经投票给其他人
        let voted_for = self.voted_for.read().await.clone();
        let can_vote = voted_for.is_none() || voted_for == Some(req.candidate_id.clone());

        // 检查候选人的日志是否至少和自己一样新
        let log = self.log.read().await;
        let last_log = log.last();
        let (last_log_index, last_log_term) = last_log
            .map(|e| (e.index, e.term))
            .unwrap_or((0, 0));

        let log_is_up_to_date =
            req.last_log_term > last_log_term ||
            (req.last_log_term == last_log_term && req.last_log_index >= last_log_index);

        if can_vote && log_is_up_to_date {
            // 投票给候选人
            *self.voted_for.write().await = Some(req.candidate_id);

            RequestVoteResponse {
                term: req.term,
                vote_granted: true,
            }
        } else {
            RequestVoteResponse {
                term: current_term,
                vote_granted: false,
            }
        }
    }

    /// 处理 AppendEntries（跟随者行为）
    pub async fn handle_append_entries(
        &self,
        req: AppendEntries,
    ) -> AppendEntriesResponse {
        let mut state = self.state.write().await;
        let current_term = self.current_term.load(Ordering::SeqCst);

        // 如果任期更小，拒绝
        if req.term < current_term {
            return AppendEntriesResponse {
                term: current_term,
                success: false,
                match_index: 0,
            };
        }

        // 重置选举定时器（收到有效领导者心跳）
        *state = RaftState::Follower {
            leader_id: Some(req.leader_id),
            election_timer: Instant::now(),
        };

        if req.term > current_term {
            self.current_term.store(req.term, Ordering::SeqCst);
            *self.voted_for.write().await = None;
        }

        let mut log = self.log.write().await;

        // 检查 prev_log_index 处的日志条目是否匹配
        if req.prev_log_index > 0 {
            let prev_entry = log.get((req.prev_log_index - 1) as usize);

            if prev_entry.map(|e| e.term) != Some(req.prev_log_term) {
                // 日志不一致
                return AppendEntriesResponse {
                    term: req.term,
                    success: false,
                    match_index: 0,
                };
            }
        }

        // 追加新条目或覆盖冲突条目
        for (i, entry) in req.entries.iter().enumerate() {
            let index = (req.prev_log_index as usize) + i;

            if index < log.len() {
                // 检查是否有冲突
                if log[index].term != entry.term {
                    // 删除冲突条目及其后的所有条目
                    log.truncate(index);
                    log.push(entry.clone());
                }
                // 否则条目已存在且匹配，跳过
            } else {
                log.push(entry.clone());
            }
        }

        // 更新 commit_index
        if req.leader_commit > self.commit_index.load(Ordering::SeqCst) {
            let new_commit = req.leader_commit.min(log.last().map(|e| e.index).unwrap_or(0));
            self.commit_index.store(new_commit, Ordering::SeqCst);
        }

        AppendEntriesResponse {
            term: req.term,
            success: true,
            match_index: req.prev_log_index + req.entries.len() as u64,
        }
    }

    /// 领导者追加日志条目
    pub async fn leader_append(&self, command: Vec<u8>) -> Result<u64, RaftError> {
        let state = self.state.read().await;

        match &*state {
            RaftState::Leader { .. } => {
                let current_term = self.current_term.load(Ordering::SeqCst);
                let mut log = self.log.write().await;

                let index = (log.len() as u64) + 1;
                let entry = LogEntry {
                    term: current_term,
                    index,
                    command,
                };

                log.push(entry);
                Ok(index)
            }
            _ => Err(RaftError::NotLeader),
        }
    }

    /// 应用已提交的日志条目到状态机
    pub async fn apply_committed(&self) {
        let commit_index = self.commit_index.load(Ordering::SeqCst);
        let last_applied = self.last_applied.load(Ordering::SeqCst);

        if commit_index > last_applied {
            let log = self.log.read().await;

            for i in (last_applied + 1)..=commit_index {
                if let Some(entry) = log.get((i - 1) as usize) {
                    // 应用到状态机
                    self.apply_to_state_machine(entry).await;
                }
            }

            self.last_applied.store(commit_index, Ordering::SeqCst);
        }
    }

    async fn apply_to_state_machine(&self, entry: &LogEntry) {
        // 实际应用逻辑
    }
}

#[derive(Debug)]
pub enum RaftError {
    NotLeader,
    Timeout,
    NetworkError(String),
}

/// Raft 安全性定理
///
/// 定理 1（选举安全）：在给定任期内，最多只有一个领导者被选出。
///
/// 定理 2（领导者完备性）：如果一个日志条目在某任期内被提交，
///       那么这个条目会出现在所有更高任期的领导者的日志中。
///
/// 定理 3（状态机安全）：如果一个节点已将某日志条目应用到状态机，
///       那么其他节点不会在该索引处应用不同的日志条目。

#[cfg(test)]
mod raft_safety_tests {
    use super::*;

    /// 验证定理 1：选举安全
    #[test]
    fn test_election_safety() {
        // 在同一任期内，不能有两个不同的领导者
        // 证明：候选人必须获得大多数投票才能成为领导者
        // 而两个不同的候选人不可能同时获得大多数投票
    }

    /// 验证定理 2：领导者完备性
    #[test]
    fn test_leader_completeness() {
        // 已提交的条目必须存在于新领导者的日志中
        // 证明：候选人必须有最新的日志才能获得选举
    }
}
```

### 4.2 最终一致性模式

**向量时钟语义：**

```rust
/// 向量时钟语义
///
/// 用于跟踪分布式系统中的因果依赖关系
///
/// 向量时钟 V 是一个从节点 ID 到逻辑时钟的映射：
/// V: NodeId → LogicalClock
///
/// 比较规则：
/// - V1 ≤ V2 当且仅当 ∀i: V1[i] ≤ V2[i]
/// - V1 < V2 当且仅当 V1 ≤ V2 且 V1 ≠ V2
/// - V1 || V2（并发）当且仅当 V1 ≰ V2 且 V2 ≰ V1

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VectorClock {
    /// 节点 ID → 逻辑时钟值
    clocks: HashMap<NodeId, u64>,
}

impl VectorClock {
    /// 创建新的向量时钟
    pub fn new() -> Self {
        Self { clocks: HashMap::new() }
    }

    /// 递增本节点的时钟
    pub fn increment(&mut self, node_id: &NodeId) {
        *self.clocks.entry(node_id.clone()).or_insert(0) += 1;
    }

    /// 合并两个向量时钟（取逐元素最大值）
    pub fn merge(&mut self, other: &VectorClock) {
        for (node, clock) in &other.clocks {
            let entry = self.clocks.entry(node.clone()).or_insert(0);
            *entry = (*entry).max(*clock);
        }
    }

    /// 比较两个向量时钟
    ///
    /// 返回：
    /// - Some(Less): self 是 other 的原因（self → other）
    /// - Some(Greater): other 是 self 的原因（other → self）
    /// - Some(Equal): 相同事件
    /// - None: 并发事件
    pub fn compare(&self, other: &VectorClock) -> Option<Ordering> {
        let all_nodes: HashSet<_> = self.clocks.keys()
            .chain(other.clocks.keys())
            .collect();

        let mut has_less = false;
        let mut has_greater = false;

        for node in all_nodes {
            let self_clock = self.clocks.get(node).copied().unwrap_or(0);
            let other_clock = other.clocks.get(node).copied().unwrap_or(0);

            match self_clock.cmp(&other_clock) {
                Ordering::Less => has_less = true,
                Ordering::Greater => has_greater = true,
                Ordering::Equal => {}
            }
        }

        match (has_less, has_greater) {
            (true, true) => None,           // 并发
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => Some(Ordering::Equal),
        }
    }

    /// 检查因果关系：self 是否在 other 之前发生
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        matches!(self.compare(other), Some(Ordering::Less))
    }

    /// 检查是否并发
    pub fn is_concurrent_with(&self, other: &VectorClock) -> bool {
        self.compare(other).is_none()
    }
}

/// 带版本向量的值
#[derive(Debug, Clone)]
pub struct VersionedValue<T> {
    pub value: T,
    pub vector_clock: VectorClock,
    pub node_id: NodeId,
    pub timestamp: u64,
}

impl<T: Clone> VersionedValue<T> {
    /// 解决并发冲突
    pub fn resolve_conflict(&self, other: &VersionedValue<T>) -> ConflictResolution<T> {
        match self.vector_clock.compare(&other.vector_clock) {
            Some(Ordering::Less) => ConflictResolution::UseOther(other.value.clone()),
            Some(Ordering::Greater) => ConflictResolution::UseSelf(self.value.clone()),
            Some(Ordering::Equal) => ConflictResolution::Equal,
            None => ConflictResolution::Conflict(vec![self.value.clone(), other.value.clone()]),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConflictResolution<T> {
    UseSelf(T),
    UseOther(T),
    Equal,
    Conflict(Vec<T>),
}

/// 向量时钟优化：版本向量（Version Vector）
///
/// 当节点数量很多时，向量时钟会变得很大
/// 版本向量只跟踪副本节点的版本，更紧凑
#[derive(Debug, Clone)]
pub struct VersionVector {
    /// 副本 ID → 版本号
    versions: HashMap<ReplicaId, u64>,
}

impl VersionVector {
    pub fn increment(&mut self, replica: &ReplicaId) {
        *self.versions.entry(replica.clone()).or_insert(0) += 1;
    }

    pub fn dominates(&self, other: &VersionVector) -> bool {
        for (replica, version) in &self.versions {
            let other_version = other.versions.get(replica).copied().unwrap_or(0);
            if *version < other_version {
                return false;
            }
        }
        true
    }
}
```

**因果一致性语义：**

```rust
/// 因果一致性语义
///
/// 保证：如果事件 A 因果地先于事件 B（A → B），
/// 那么所有节点必须在看到 B 之前先看到 A。

pub struct CausalConsistency<K, V> {
    /// 本节点 ID
    node_id: NodeId,

    /// 本地数据存储
    store: HashMap<K, VersionedValue<V>>,

    /// 本节点的向量时钟
    vector_clock: VectorClock,

    /// 依赖图：跟踪操作的因果关系
    dependency_graph: DependencyGraph,
}

/// 依赖图
#[derive(Debug, Clone, Default)]
pub struct DependencyGraph {
    /// 操作 ID → 依赖的操作 ID 集合
    dependencies: HashMap<OpId, HashSet<OpId>>,
}

/// 因果一致性操作
#[derive(Debug, Clone)]
pub struct CausalOperation<K, V> {
    pub op_id: OpId,
    pub op_type: OpType<K, V>,
    pub vector_clock: VectorClock,
    pub dependencies: HashSet<OpId>,
}

#[derive(Debug, Clone)]
pub enum OpType<K, V> {
    Read { key: K },
    Write { key: K, value: V },
    Delete { key: K },
}

impl<K: Clone + Eq + std::hash::Hash, V: Clone> CausalConsistency<K, V> {
    /// 执行本地写操作
    pub fn write(&mut self, key: K, value: V) -> CausalOperation<K, V> {
        // 递增本节点时钟
        self.vector_clock.increment(&self.node_id);

        let op_id = OpId::new();

        // 存储带版本信息的值
        let versioned = VersionedValue {
            value: value.clone(),
            vector_clock: self.vector_clock.clone(),
            node_id: self.node_id.clone(),
            timestamp: current_timestamp(),
        };

        self.store.insert(key.clone(), versioned);

        // 记录依赖关系
        let dependencies = self.dependency_graph.get_recent_dependencies();

        CausalOperation {
            op_id: op_id.clone(),
            op_type: OpType::Write { key, value },
            vector_clock: self.vector_clock.clone(),
            dependencies,
        }
    }

    /// 接收远程操作
    pub fn receive_operation(&mut self, op: &CausalOperation<K, V>) -> Result<(), CausalViolation> {
        // 检查依赖是否满足
        for dep in &op.dependencies {
            if !self.dependency_graph.has_dependency(dep) {
                return Err(CausalViolation::MissingDependency(dep.clone()));
            }
        }

        // 应用操作
        match &op.op_type {
            OpType::Write { key, value } => {
                // 检查时钟关系，处理冲突
                if let Some(existing) = self.store.get(key) {
                    match existing.vector_clock.compare(&op.vector_clock) {
                        Some(Ordering::Greater) => {
                            // 本地版本更新，忽略远程操作
                            return Ok(());
                        }
                        Some(Ordering::Less) => {
                            // 远程版本更新，应用
                        }
                        _ => {
                            // 并发冲突，需要合并
                            let merged = self.merge_values(&existing.value, value);
                            // ...
                        }
                    }
                }

                let versioned = VersionedValue {
                    value: value.clone(),
                    vector_clock: op.vector_clock.clone(),
                    node_id: op.op_id.node_id(),
                    timestamp: current_timestamp(),
                };

                self.store.insert(key.clone(), versioned);
            }
            _ => {}
        }

        // 更新向量时钟
        self.vector_clock.merge(&op.vector_clock);

        // 记录依赖
        self.dependency_graph.record(op.op_id.clone(), op.dependencies.clone());

        Ok(())
    }

    fn merge_values(&self, v1: &V, v2: &V) -> V {
        // 根据值类型选择合适的合并策略
        // 例如：集合的并集、计数器的加法等
        v2.clone() // 简化实现
    }
}

#[derive(Debug)]
pub enum CausalViolation {
    MissingDependency(OpId),
    ClockRegression,
}
```

**读修复语义：**

```rust
/// 读修复语义
///
/// 在读取时检测并修复副本之间的不一致

pub struct ReadRepair<K, V> {
    /// 复制因子
    replication_factor: usize,

    /// 读仲裁数
    read_quorum: usize,

    /// 写仲裁数
    write_quorum: usize,

    /// 存储后端
    storage: Arc<dyn DistributedStorage<K, V>>,
}

impl<K: Clone + Eq + std::hash::Hash, V: Clone + PartialEq> ReadRepair<K, V> {
    /// 执行读操作（带修复）
    pub async fn read(&self, key: &K) -> ReadResult<V> {
        // 并行读取所有副本
        let replicas = self.storage.read_all_replicas(key).await;

        // 收集响应
        let mut versions = Vec::new();
        for (node_id, result) in replicas {
            match result {
                Ok(value) => versions.push((node_id, value)),
                Err(e) => {
                    tracing::warn!("Read from {} failed: {:?}", node_id, e);
                }
            }
        }

        // 检查是否达到读仲裁
        if versions.len() < self.read_quorum {
            return ReadResult::QuorumFailure {
                received: versions.len(),
                required: self.read_quorum,
            };
        }

        // 分析版本
        let version_analysis = self.analyze_versions(&versions);

        match version_analysis {
            VersionAnalysis::Consistent { value } => {
                ReadResult::Success(value)
            }
            VersionAnalysis::Inconsistent { values } => {
                // 执行读修复
                let repaired_value = self.resolve_and_repair(key, &versions).await;
                ReadResult::Repaired(repaired_value)
            }
            VersionAnalysis::MissingReplicas { value, missing } => {
                // 部分副本缺失，触发后台修复
                self.trigger_background_repair(key, &value, &missing).await;
                ReadResult::Success(value)
            }
        }
    }

    /// 分析版本一致性
    fn analyze_versions(&self, versions: &[(NodeId, VersionedValue<V>)]) -> VersionAnalysis<V> {
        if versions.is_empty() {
            return VersionAnalysis::Inconsistent { values: Vec::new() };
        }

        // 检查是否所有版本相同
        let first = &versions[0].1;
        let all_same = versions.iter().all(|(_, v)| v.value == first.value);

        if all_same {
            return VersionAnalysis::Consistent {
                value: first.value.clone(),
            };
        }

        // 检查因果关系
        let mut concurrent = Vec::new();
        for (_, v1) in versions {
            let mut is_dominated = false;
            for (_, v2) in versions {
                if v1.vector_clock.happens_before(&v2.vector_clock) {
                    is_dominated = true;
                    break;
                }
            }
            if !is_dominated {
                concurrent.push(v1.value.clone());
            }
        }

        if concurrent.len() == 1 {
            VersionAnalysis::Consistent {
                value: concurrent[0].clone(),
            }
        } else {
            VersionAnalysis::Inconsistent {
                values: concurrent,
            }
        }
    }

    /// 解决冲突并修复
    async fn resolve_and_repair(
        &self,
        key: &K,
        versions: &[(NodeId, VersionedValue<V>)],
    ) -> V {
        // 使用最后写入胜利（LWW）策略
        let latest = versions.iter()
            .max_by_key(|(_, v)| v.timestamp)
            .map(|(_, v)| v.value.clone())
            .unwrap();

        // 异步修复过时副本
        for (node_id, version) in versions {
            if version.value != latest {
                let key = key.clone();
                let value = latest.clone();
                let node_id = node_id.clone();
                let storage = self.storage.clone();

                tokio::spawn(async move {
                    if let Err(e) = storage.write(&node_id, &key, &value).await {
                        tracing::error!("Repair to {} failed: {:?}", node_id, e);
                    }
                });
            }
        }

        latest
    }

    async fn trigger_background_repair(&self, key: &K, value: &V, missing: &[NodeId]) {
        for node_id in missing {
            let key = key.clone();
            let value = value.clone();
            let node_id = node_id.clone();
            let storage = self.storage.clone();

            tokio::spawn(async move {
                if let Err(e) = storage.write(&node_id, &key, &value).await {
                    tracing::error!("Background repair to {} failed: {:?}", node_id, e);
                }
            });
        }
    }
}

#[derive(Debug)]
pub enum VersionAnalysis<V> {
    Consistent { value: V },
    Inconsistent { values: Vec<V> },
    MissingReplicas { value: V, missing: Vec<NodeId> },
}

#[derive(Debug)]
pub enum ReadResult<V> {
    Success(V),
    Repaired(V),
    QuorumFailure { received: usize, required: usize },
    NotFound,
}
```

**反熵机制：**

```rust
/// 反熵（Anti-Entropy）机制
///
/// 定期比较和同步副本之间的差异，减少不一致

pub struct AntiEntropy<K, V> {
    /// 本地存储
    local_store: Arc<dyn Storage<K, V>>,

    /// 对等节点列表
    peers: Vec<NodeId>,

    /// 同步间隔
    sync_interval: Duration,

    /// Merkle 树用于高效比较
    merkle_tree: MerkleTree,
}

/// Merkle 树：用于高效比较大量数据
#[derive(Debug, Clone)]
pub struct MerkleTree {
    root: MerkleNode,
}

#[derive(Debug, Clone)]
pub enum MerkleNode {
    Leaf {
        hash: [u8; 32],
        key: String,
    },
    Branch {
        hash: [u8; 32],
        children: Vec<MerkleNode>,
    },
}

impl<K: AsRef<[u8]>, V: AsRef<[u8]>> AntiEntropy<K, V> {
    /// 启动反熵进程
    pub async fn start(&self) {
        let mut interval = tokio::time::interval(self.sync_interval);

        loop {
            interval.tick().await;

            // 随机选择对等节点进行同步
            if let Some(peer) = self.peers.choose(&mut rand::thread_rng()) {
                if let Err(e) = self.sync_with_peer(peer).await {
                    tracing::error!("Anti-entropy sync with {} failed: {:?}", peer, e);
                }
            }
        }
    }

    /// 与对等节点同步
    pub async fn sync_with_peer(&self, peer: &NodeId) -> Result<(), SyncError> {
        // 1. 交换 Merkle 树根哈希
        let local_root = self.merkle_tree.root_hash();
        let remote_root = self.request_merkle_root(peer).await?;

        if local_root == remote_root {
            // 数据一致，无需同步
            return Ok(());
        }

        // 2. 递归比较 Merkle 树，找出差异
        let diffs = self.compare_merkle_trees(peer).await?;

        // 3. 交换差异数据
        for diff in diffs {
            match diff {
                Diff::LocalMissing { key } => {
                    // 从对等节点拉取
                    let value = self.request_value(peer, &key).await?;
                    self.local_store.write(&key, &value).await?;
                }
                Diff::RemoteMissing { key, value } => {
                    // 向对等节点推送
                    self.send_value(peer, &key, &value).await?;
                }
                Diff::Conflict { key, local_value, remote_value } => {
                    // 解决冲突
                    let resolved = self.resolve_conflict(&key, &local_value, &remote_value);
                    self.local_store.write(&key, &resolved).await?;
                    self.send_value(peer, &key, &resolved).await?;
                }
            }
        }

        Ok(())
    }

    /// 递归比较 Merkle 树
    async fn compare_merkle_trees(&self, peer: &NodeId) -> Result<Vec<Diff<V>>, SyncError> {
        // 构建差异列表
        let mut diffs = Vec::new();

        // 层级遍历，比较哈希值不同的节点
        self.traverse_and_compare(&self.merkle_tree.root, peer, &mut diffs).await?;

        Ok(diffs)
    }

    async fn traverse_and_compare(
        &self,
        node: &MerkleNode,
        peer: &NodeId,
        diffs: &mut Vec<Diff<V>>,
    ) -> Result<(), SyncError> {
        match node {
            MerkleNode::Leaf { hash, key } => {
                // 请求对等节点的对应叶节点
                let remote_hash = self.request_leaf_hash(peer, key).await?;

                if *hash != remote_hash {
                    // 值不同，需要同步
                    let local_value = self.local_store.read(key).await?;
                    diffs.push(Diff::Conflict {
                        key: key.clone(),
                        local_value,
                        remote_value: self.request_value(peer, key).await?,
                    });
                }
            }
            MerkleNode::Branch { hash: _, children } => {
                // 递归比较子节点
                for child in children {
                    Box::pin(self.traverse_and_compare(child, peer, diffs)).await?;
                }
            }
        }

        Ok(())
    }

    fn resolve_conflict(&self, _key: &str, local: &V, remote: &V) -> V {
        // 使用 LWW 策略
        // 实际实现应基于时间戳或向量时钟
        remote.clone()
    }

    // 网络请求辅助方法
    async fn request_merkle_root(&self, peer: &NodeId) -> Result<[u8; 32], SyncError> {
        // 实际网络请求
        Ok([0; 32])
    }

    async fn request_leaf_hash(&self, peer: &NodeId, key: &str) -> Result<[u8; 32], SyncError> {
        Ok([0; 32])
    }

    async fn request_value(&self, peer: &NodeId, key: &str) -> Result<V, SyncError> {
        // 实际网络请求
        Err(SyncError::NetworkError)
    }

    async fn send_value(&self, peer: &NodeId, key: &str, value: &V) -> Result<(), SyncError> {
        // 实际网络请求
        Ok(())
    }
}

#[derive(Debug)]
pub enum Diff<V> {
    LocalMissing { key: String },
    RemoteMissing { key: String, value: V },
    Conflict { key: String, local_value: V, remote_value: V },
}

#[derive(Debug)]
pub enum SyncError {
    NetworkError,
    StorageError,
    Timeout,
}

impl MerkleTree {
    pub fn root_hash(&self) -> [u8; 32] {
        match &self.root {
            MerkleNode::Leaf { hash, .. } => *hash,
            MerkleNode::Branch { hash, .. } => *hash,
        }
    }
}
```

### 4.3 分布式事务

**Saga 模式语义：**

```rust
/// Saga 模式语义
///
/// 将长事务拆分为一系列本地事务，每个本地事务有对应的补偿操作
///
/// 执行方式：
/// 1. 顺序执行：按顺序执行，失败时倒序补偿
/// 2. 并行执行：无依赖的步骤并行，失败时补偿所有已完成步骤

pub struct Saga<T> {
    /// Saga 名称
    name: String,

    /// 步骤列表
    steps: Vec<SagaStep<T>>,

    /// 已完成步骤（用于补偿）
    completed_steps: Vec<usize>,

    /// 执行状态
    state: SagaState,
}

#[derive(Debug, Clone)]
pub struct SagaStep<T> {
    /// 步骤名称
    name: String,

    /// 执行操作
    action: Box<dyn Fn() -> BoxFuture<'static, Result<T, SagaError>> + Send>,

    /// 补偿操作
    compensate: Box<dyn Fn() -> BoxFuture<'static, Result<(), SagaError>> + Send>,

    /// 依赖的步骤索引
    dependencies: Vec<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SagaState {
    Pending,
    Running,
    Completed,
    Compensating,
    Compensated,
    Failed,
}

impl<T: Clone + Send + 'static> Saga<T> {
    /// 添加步骤
    pub fn add_step<F, Fut, C, Cfg>(
        &mut self,
        name: &str,
        action: F,
        compensate: C,
    ) where
        F: Fn() -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, SagaError>> + Send + 'static,
        C: Fn() -> Cfg + Send + 'static,
        Cfg: Future<Output = Result<(), SagaError>> + Send + 'static,
    {
        self.steps.push(SagaStep {
            name: name.to_string(),
            action: Box::new(move || Box::pin(action())),
            compensate: Box::new(move || Box::pin(compensate())),
            dependencies: Vec::new(),
        });
    }

    /// 添加带依赖的步骤
    pub fn add_step_with_deps<F, Fut, C, Cfg>(
        &mut self,
        name: &str,
        action: F,
        compensate: C,
        deps: Vec<usize>,
    ) where
        F: Fn() -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, SagaError>> + Send + 'static,
        C: Fn() -> Cfg + Send + 'static,
        Cfg: Future<Output = Result<(), SagaError>> + Send + 'static,
    {
        self.steps.push(SagaStep {
            name: name.to_string(),
            action: Box::new(move || Box::pin(action())),
            compensate: Box::new(move || Box::pin(compensate())),
            dependencies: deps,
        });
    }

    /// 执行 Saga（顺序执行版本）
    pub async fn execute_sequential(mut self) -> SagaResult<T> {
        self.state = SagaState::Running;

        for (idx, step) in self.steps.iter().enumerate() {
            tracing::info!("Executing saga step: {}", step.name);

            match (step.action)().await {
                Ok(result) => {
                    self.completed_steps.push(idx);
                }
                Err(e) => {
                    tracing::error!("Saga step {} failed: {:?}", step.name, e);

                    // 执行补偿
                    self.state = SagaState::Compensating;
                    self.compensate().await;

                    return SagaResult::Failed {
                        failed_step: step.name.clone(),
                        error: e,
                        compensated: self.state == SagaState::Compensated,
                    };
                }
            }
        }

        self.state = SagaState::Completed;
        SagaResult::Success
    }

    /// 执行 Saga（并行执行版本）
    pub async fn execute_parallel(mut self) -> SagaResult<T> {
        self.state = SagaState::Running;

        // 拓扑排序，确定执行顺序
        let execution_order = self.topological_sort();

        for batch in execution_order {
            // 同一批次内的步骤并行执行
            let mut futures = Vec::new();

            for &step_idx in &batch {
                let step = &self.steps[step_idx];
                let action = &step.action;
                let name = step.name.clone();

                futures.push(async move {
                    let result = action().await;
                    (step_idx, name, result)
                });
            }

            let results = futures::future::join_all(futures).await;

            // 检查结果
            for (idx, name, result) in results {
                match result {
                    Ok(_) => {
                        self.completed_steps.push(idx);
                    }
                    Err(e) => {
                        tracing::error!("Saga step {} failed: {:?}", name, e);
                        self.state = SagaState::Compensating;
                        self.compensate().await;

                        return SagaResult::Failed {
                            failed_step: name,
                            error: e,
                            compensated: self.state == SagaState::Compensated,
                        };
                    }
                }
            }
        }

        self.state = SagaState::Completed;
        SagaResult::Success
    }

    /// 执行补偿（倒序）
    async fn compensate(&mut self) {
        for &idx in self.completed_steps.iter().rev() {
            let step = &self.steps[idx];
            tracing::info!("Compensating saga step: {}", step.name);

            if let Err(e) = (step.compensate)().await {
                // 补偿失败，需要人工介入或记录到待处理队列
                tracing::error!("Compensation for {} failed: {:?}", step.name, e);
                // 记录到日志或死信队列
            }
        }

        self.state = SagaState::Compensated;
    }

    /// 拓扑排序（用于并行执行）
    fn topological_sort(&self) -> Vec<Vec<usize>> {
        let n = self.steps.len();
        let mut in_degree = vec![0; n];
        let mut adj = vec![vec![]; n];

        // 构建依赖图
        for (i, step) in self.steps.iter().enumerate() {
            for &dep in &step.dependencies {
                adj[dep].push(i);
                in_degree[i] += 1;
            }
        }

        let mut batches = Vec::new();
        let mut visited = vec![false; n];

        while batches.iter().flatten().count() < n {
            let mut current_batch = Vec::new();

            for i in 0..n {
                if !visited[i] && in_degree[i] == 0 {
                    current_batch.push(i);
                    visited[i] = true;
                }
            }

            if current_batch.is_empty() {
                // 存在循环依赖
                panic!("Circular dependency detected in saga");
            }

            // 减少依赖计数
            for &i in &current_batch {
                for &j in &adj[i] {
                    in_degree[j] -= 1;
                }
            }

            batches.push(current_batch);
        }

        batches
    }
}

#[derive(Debug)]
pub enum SagaResult<T> {
    Success,
    Failed {
        failed_step: String,
        error: SagaError,
        compensated: bool,
    },
    PartiallyCompleted {
        completed_steps: Vec<String>,
        failed_step: String,
        error: SagaError,
    },
}

#[derive(Debug, Clone)]
pub enum SagaError {
    ServiceError(String),
    Timeout,
    NetworkError,
    CompensationFailed(String),
}

/// Saga 编排器（协调多个 Saga）
pub struct SagaOrchestrator {
    sagas: HashMap<String, Box<dyn AnySaga>>,
    event_log: Arc<dyn EventLog>,
}

impl SagaOrchestrator {
    /// 注册 Saga
    pub fn register_saga(&mut self, name: &str, saga: impl AnySaga) {
        self.sagas.insert(name.to_string(), Box::new(saga));
    }

    /// 执行 Saga
    pub async fn execute(&self, saga_name: &str, context: SagaContext) -> SagaResult<()> {
        // 记录开始事件
        self.event_log.append(SagaEvent::Started {
            saga_name: saga_name.to_string(),
            context: context.clone(),
        }).await;

        // 实际执行
        let result = if let Some(saga) = self.sagas.get(saga_name) {
            saga.execute(context).await
        } else {
            return SagaResult::Failed {
                failed_step: "init".to_string(),
                error: SagaError::ServiceError(format!("Saga {} not found", saga_name)),
                compensated: false,
            };
        };

        // 记录结果事件
        match &result {
            SagaResult::Success => {
                self.event_log.append(SagaEvent::Completed {
                    saga_name: saga_name.to_string(),
                }).await;
            }
            SagaResult::Failed { failed_step, error, compensated } => {
                self.event_log.append(SagaEvent::Failed {
                    saga_name: saga_name.to_string(),
                    failed_step: failed_step.clone(),
                    error: format!("{:?}", error),
                    compensated: *compensated,
                }).await;
            }
            _ => {}
        }

        result
    }
}

pub trait AnySaga: Send + Sync {
    fn execute(&self, context: SagaContext) -> BoxFuture<'static, SagaResult<()>>;
}
```

**补偿事务语义：**

```rust
/// 补偿事务语义
///
/// 每个业务操作必须有对应的补偿操作
/// 补偿操作语义：将系统状态恢复到操作前的状态

#[async_trait]
pub trait CompensatableAction {
    /// 执行操作
    async fn execute(&self) -> Result<ActionResult, ActionError>;

    /// 补偿操作
    ///
    /// 语义：
    /// - 幂等：多次补偿不会产生副作用
    /// - 最终：补偿后系统状态与操作前等价
    async fn compensate(&self) -> Result<(), CompensationError>;

    /// 检查是否需要补偿
    fn needs_compensation(&self, result: &ActionResult) -> bool;
}

/// 补偿管理器
pub struct CompensationManager {
    /// 已执行的操作（用于补偿）
    executed_actions: Vec<Box<dyn CompensatableAction>>,

    /// 补偿日志（用于故障恢复）
    compensation_log: Arc<dyn CompensationLog>,
}

impl CompensationManager {
    /// 执行带补偿的操作
    pub async fn execute_with_compensation<A>(
        &mut self,
        action: A,
    ) -> Result<ActionResult, CompensationError>
    where
        A: CompensatableAction + 'static,
    {
        // 记录操作开始
        self.compensation_log.log_action_start(&action).await;

        match action.execute().await {
            Ok(result) => {
                if action.needs_compensation(&result) {
                    // 保存操作以便后续补偿
                    self.executed_actions.push(Box::new(action));
                }

                self.compensation_log.log_action_success(&result).await;
                Ok(result)
            }
            Err(e) => {
                // 执行补偿
                self.compensate_all().await;
                Err(CompensationError::ActionFailed(e))
            }
        }
    }

    /// 补偿所有已执行的操作（倒序）
    pub async fn compensate_all(&mut self) {
        while let Some(action) = self.executed_actions.pop() {
            if let Err(e) = action.compensate().await {
                // 补偿失败，记录到待处理队列
                self.compensation_log.log_compensation_failure(&e).await;
            }
        }
    }
}

/// 补偿日志 trait
#[async_trait]
pub trait CompensationLog: Send + Sync {
    async fn log_action_start(&self, action: &dyn CompensatableAction);
    async fn log_action_success(&self, result: &ActionResult);
    async fn log_compensation_failure(&self, error: &CompensationError);
}

/// 示例：订单补偿
pub struct CreateOrderAction {
    order_service: Arc<dyn OrderService>,
    order_data: OrderData,
}

#[async_trait]
impl CompensatableAction for CreateOrderAction {
    async fn execute(&self) -> Result<ActionResult, ActionError> {
        let order = self.order_service.create_order(&self.order_data).await?;
        Ok(ActionResult::OrderCreated(order.id))
    }

    async fn compensate(&self) -> Result<(), CompensationError> {
        // 幂等取消订单
        if let ActionResult::OrderCreated(order_id) = self.execute().await.unwrap() {
            self.order_service.cancel_order(&order_id).await
                .map_err(|e| CompensationError::CompensationFailed(e.to_string()))?;
        }
        Ok(())
    }

    fn needs_compensation(&self, _result: &ActionResult) -> bool {
        true // 创建订单后如果失败需要取消
    }
}
```

**TCC 模式语义：**

```rust
/// TCC (Try-Confirm-Cancel) 模式语义
///
/// 三个阶段：
/// 1. Try：预留资源，执行业务检查
/// 2. Confirm：确认执行业务
/// 3. Cancel：释放预留资源

#[async_trait]
pub trait TccAction {
    /// Try 阶段
    ///
    /// 语义：
    /// - 执行业务检查
    /// - 预留必要资源
    /// - 返回预留结果
    async fn try_action(&self) -> Result<TryResult, TccError>;

    /// Confirm 阶段
    ///
    /// 语义：
    /// - 使用预留的资源执行业务
    /// - 必须成功（需要重试直到成功）
    /// - 幂等性保证
    async fn confirm(&self, try_result: &TryResult) -> Result<(), TccError>;

    /// Cancel 阶段
    ///
    /// 语义：
    /// - 释放预留的资源
    /// - 回滚业务状态
    /// - 幂等性保证
    async fn cancel(&self, try_result: &TryResult) -> Result<(), TccError>;
}

/// TCC 事务管理器
pub struct TccTransactionManager {
    /// 当前事务
    transactions: HashMap<TxId, TccTransaction>,

    /// 确认超时
    confirm_timeout: Duration,

    /// 事务日志
    tx_log: Arc<dyn TccTransactionLog>,
}

#[derive(Debug, Clone)]
pub struct TccTransaction {
    tx_id: TxId,
    state: TccState,
    try_results: Vec<TryResult>,
    actions: Vec<Box<dyn TccAction>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccState {
    Trying,
    TrySucceeded,
    Confirming,
    Confirmed,
    Cancelling,
    Cancelled,
}

impl TccTransactionManager {
    /// 执行 TCC 事务
    pub async fn execute(&self, actions: Vec<Box<dyn TccAction>>) -> TccResult {
        let tx_id = TxId::new();
        let mut try_results = Vec::new();

        // 1. Try 阶段
        for action in &actions {
            match action.try_action().await {
                Ok(result) => {
                    try_results.push(result);
                }
                Err(e) => {
                    // Try 失败，执行 Cancel
                    for (idx, result) in try_results.iter().enumerate().rev() {
                        if let Err(cancel_err) = actions[idx].cancel(result).await {
                            // 记录待处理取消
                            self.tx_log.log_pending_cancel(&tx_id, idx).await;
                        }
                    }
                    return TccResult::Failed(TccFailure::TryFailed(e));
                }
            }
        }

        // 记录 Try 成功
        self.tx_log.log_try_succeeded(&tx_id, &try_results).await;

        // 2. Confirm 阶段
        for (idx, action) in actions.iter().enumerate() {
            let result = &try_results[idx];

            // 需要幂等重试直到成功
            loop {
                match action.confirm(result).await {
                    Ok(_) => break,
                    Err(e) => {
                        tracing::error!("Confirm failed, retrying: {:?}", e);
                        tokio::time::sleep(Duration::from_millis(100)).await;
                    }
                }
            }
        }

        self.tx_log.log_confirmed(&tx_id).await;
        TccResult::Success
    }

    /// 恢复未完成的 TCC 事务
    pub async fn recover(&self) {
        // 从日志中加载未完成的 transaction
        let pending_txs = self.tx_log.load_pending_transactions().await;

        for tx in pending_txs {
            match tx.state {
                TccState::TrySucceeded | TccState::Confirming => {
                    // 继续 Confirm
                    for (idx, action) in tx.actions.iter().enumerate() {
                        if let Some(result) = tx.try_results.get(idx) {
                            // 幂等重试 confirm
                            let _ = action.confirm(result).await;
                        }
                    }
                }
                TccState::Cancelling => {
                    // 继续 Cancel
                    for (idx, action) in tx.actions.iter().enumerate().rev() {
                        if let Some(result) = tx.try_results.get(idx) {
                            let _ = action.cancel(result).await;
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TryResult {
    /// 预留的资源标识
    pub reservation_id: String,
    /// 预留数量
    pub reserved_amount: u64,
    /// 预留过期时间
    pub expiry: Instant,
}

#[derive(Debug)]
pub enum TccResult {
    Success,
    Failed(TccFailure),
}

#[derive(Debug)]
pub enum TccFailure {
    TryFailed(TccError),
    ConfirmFailed(Vec<TccError>),
    CancelFailed(Vec<TccError>),
}

#[derive(Debug)]
pub enum TccError {
    ResourceUnavailable,
    ReservationFailed(String),
    ConfirmFailed(String),
    CancelFailed(String),
    Timeout,
}

/// TCC 示例：库存扣减
pub struct InventoryDeductAction {
    inventory_service: Arc<dyn InventoryService>,
    product_id: String,
    quantity: u64,
}

#[async_trait]
impl TccAction for InventoryDeductAction {
    async fn try_action(&self) -> Result<TryResult, TccError> {
        // 1. 检查库存
        let available = self.inventory_service.check_stock(&self.product_id).await?;

        if available < self.quantity {
            return Err(TccError::ResourceUnavailable);
        }

        // 2. 预留库存（冻结）
        let reservation = self.inventory_service
            .reserve_stock(&self.product_id, self.quantity)
            .await?;

        Ok(TryResult {
            reservation_id: reservation.id,
            reserved_amount: self.quantity,
            expiry: Instant::now() + Duration::from_secs(300), // 5分钟过期
        })
    }

    async fn confirm(&self, try_result: &TryResult) -> Result<(), TccError> {
        // 将预留转为实际扣减
        self.inventory_service
            .confirm_deduction(&try_result.reservation_id)
            .await
    }

    async fn cancel(&self, try_result: &TryResult) -> Result<(), TccError> {
        // 释放预留
        self.inventory_service
            .release_reservation(&try_result.reservation_id)
            .await
    }
}

/// TCC 示例：账户扣款
pub struct AccountDebitAction {
    account_service: Arc<dyn AccountService>,
    account_id: String,
    amount: u64,
}

#[async_trait]
impl TccAction for AccountDebitAction {
    async fn try_action(&self) -> Result<TryResult, TccError> {
        // 检查余额并冻结金额
        let freeze = self.account_service
            .freeze_amount(&self.account_id, self.amount)
            .await?;

        Ok(TryResult {
            reservation_id: freeze.freeze_id,
            reserved_amount: self.amount,
            expiry: freeze.expiry,
        })
    }

    async fn confirm(&self, try_result: &TryResult) -> Result<(), TccError> {
        // 解冻并扣款
        self.account_service
            .confirm_debit(&try_result.reservation_id)
            .await
    }

    async fn cancel(&self, try_result: &TryResult) -> Result<(), TccError> {
        // 解冻金额
        self.account_service
            .unfreeze(&try_result.reservation_id)
            .await
    }
}
```

---

## 5. 容错与弹性模式

### 5.1 熔断器模式

**熔断器状态机语义：**

```rust
/// 熔断器模式语义模型
///
/// 三个状态：
/// - Closed：正常，请求通过
/// - Open：熔断，请求快速失败
/// - HalfOpen：试探，允许部分请求测试恢复
///
/// 状态转换：
/// - Closed → Open：失败率超过阈值
/// - Open → HalfOpen：熔断超时
/// - HalfOpen → Closed：探测成功
/// - HalfOpen → Open：探测失败

pub struct CircuitBreaker {
    /// 配置
    config: CircuitConfig,

    /// 当前状态
    state: Arc<RwLock<CircuitState>>,

    /// 失败计数
    failure_count: AtomicU32,

    /// 成功计数（用于 HalfOpen 状态）
    success_count: AtomicU32,

    /// 请求计数
    request_count: AtomicU32,

    /// 上次失败时间
    last_failure_time: Arc<RwLock<Option<Instant>>>,

    /// 状态变更监听器
    state_listeners: Vec<Box<dyn Fn(CircuitStateTransition) + Send + Sync>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    Closed,
    Open { opened_at: Instant },
    HalfOpen,
}

#[derive(Debug, Clone)]
pub struct CircuitConfig {
    /// 失败率阈值（0.0 - 1.0）
    pub failure_threshold: f64,

    /// 连续失败阈值（触发熔断的最小失败次数）
    pub consecutive_failure_threshold: u32,

    /// 熔断持续时间
    pub open_duration: Duration,

    /// HalfOpen 状态下的探测请求数
    pub half_open_max_calls: u32,

    /// 从 HalfOpen 恢复所需的连续成功次数
    pub half_open_success_threshold: u32,

    /// 滑动窗口大小（用于计算失败率）
    pub sliding_window_size: Duration,
}

impl Default for CircuitConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 0.5,
            consecutive_failure_threshold: 5,
            open_duration: Duration::from_secs(30),
            half_open_max_calls: 3,
            half_open_success_threshold: 2,
            sliding_window_size: Duration::from_secs(60),
        }
    }
}

/// 状态转换事件
#[derive(Debug, Clone)]
pub struct CircuitStateTransition {
    pub from: CircuitState,
    pub to: CircuitState,
    pub reason: StateChangeReason,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub enum StateChangeReason {
    FailureThresholdExceeded { failure_rate: f64 },
    ConsecutiveFailuresExceeded { count: u32 },
    TimeoutExpired,
    ProbeSucceeded { consecutive_successes: u32 },
    ProbeFailed,
}

impl CircuitBreaker {
    /// 创建新的熔断器
    pub fn new(config: CircuitConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_count: AtomicU32::new(0),
            success_count: AtomicU32::new(0),
            request_count: AtomicU32::new(0),
            last_failure_time: Arc::new(RwLock::new(None)),
            state_listeners: Vec::new(),
        }
    }

    /// 执行受保护的调用
    pub async fn call<F, Fut, T>(&self, operation: F) -> CircuitResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, CircuitError>>,
    {
        // 检查并更新状态
        self.update_state().await;

        let state = *self.state.read().await;

        match state {
            CircuitState::Open { .. } => {
                // 熔断状态，快速失败
                CircuitResult::Rejected(RejectionReason::CircuitOpen)
            }
            CircuitState::HalfOpen => {
                // 半开状态，检查是否允许探测
                let current_requests = self.request_count.fetch_add(1, Ordering::SeqCst);

                if current_requests >= self.config.half_open_max_calls {
                    // 已达最大探测数
                    CircuitResult::Rejected(RejectionReason::TooManyHalfOpenRequests)
                } else {
                    // 执行探测
                    self.execute_with_tracking(operation).await
                }
            }
            CircuitState::Closed => {
                // 正常执行
                self.request_count.fetch_add(1, Ordering::SeqCst);
                self.execute_with_tracking(operation).await
            }
        }
    }

    /// 执行并跟踪结果
    async fn execute_with_tracking<F, Fut, T>(&self, operation: F) -> CircuitResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, CircuitError>>,
    {
        match operation().await {
            Ok(result) => {
                self.on_success().await;
                CircuitResult::Success(result)
            }
            Err(error) => {
                self.on_failure().await;
                CircuitResult::Failure(error)
            }
        }
    }

    /// 更新状态（检查是否需要状态转换）
    async fn update_state(&self) {
        let mut state = self.state.write().await;

        match *state {
            CircuitState::Open { opened_at } => {
                // 检查是否超时，可以进入 HalfOpen
                if opened_at.elapsed() >= self.config.open_duration {
                    let old_state = *state;
                    *state = CircuitState::HalfOpen;

                    // 重置计数器
                    self.failure_count.store(0, Ordering::SeqCst);
                    self.success_count.store(0, Ordering::SeqCst);
                    self.request_count.store(0, Ordering::SeqCst);

                    self.notify_state_change(CircuitStateTransition {
                        from: old_state,
                        to: CircuitState::HalfOpen,
                        reason: StateChangeReason::TimeoutExpired,
                        timestamp: Instant::now(),
                    });
                }
            }
            _ => {}
        }
    }

    /// 处理成功
    async fn on_success(&self) {
        let state = *self.state.read().await;

        match state {
            CircuitState::HalfOpen => {
                let successes = self.success_count.fetch_add(1, Ordering::SeqCst) + 1;

                // 检查是否可以恢复到 Closed
                if successes >= self.config.half_open_success_threshold {
                    let mut state_guard = self.state.write().await;
                    let old_state = *state_guard;
                    *state_guard = CircuitState::Closed;
                    drop(state_guard);

                    // 重置计数器
                    self.failure_count.store(0, Ordering::SeqCst);
                    self.success_count.store(0, Ordering::SeqCst);
                    self.request_count.store(0, Ordering::SeqCst);

                    self.notify_state_change(CircuitStateTransition {
                        from: old_state,
                        to: CircuitState::Closed,
                        reason: StateChangeReason::ProbeSucceeded { consecutive_successes: successes },
                        timestamp: Instant::now(),
                    });
                }
            }
            CircuitState::Closed => {
                // 重置连续失败计数
                self.failure_count.store(0, Ordering::SeqCst);
            }
            _ => {}
        }
    }

    /// 处理失败
    async fn on_failure(&self) {
        let state = *self.state.read().await;

        let failures = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;
        *self.last_failure_time.write().await = Some(Instant::now());

        match state {
            CircuitState::Closed => {
                // 检查是否超过阈值
                let requests = self.request_count.load(Ordering::SeqCst);
                let failure_rate = failures as f64 / requests as f64;

                let should_open =
                    failure_rate >= self.config.failure_threshold ||
                    failures >= self.config.consecutive_failure_threshold;

                if should_open && requests > 0 {
                    let mut state_guard = self.state.write().await;
                    let old_state = *state_guard;
                    *state_guard = CircuitState::Open { opened_at: Instant::now() };
                    drop(state_guard);

                    let reason = if failures >= self.config.consecutive_failure_threshold {
                        StateChangeReason::ConsecutiveFailuresExceeded { count: failures }
                    } else {
                        StateChangeReason::FailureThresholdExceeded { failure_rate }
                    };

                    self.notify_state_change(CircuitStateTransition {
                        from: old_state,
                        to: CircuitState::Open { opened_at: Instant::now() },
                        reason,
                        timestamp: Instant::now(),
                    });
                }
            }
            CircuitState::HalfOpen => {
                // 探测失败，回到 Open
                let mut state_guard = self.state.write().await;
                let old_state = *state_guard;
                *state_guard = CircuitState::Open { opened_at: Instant::now() };
                drop(state_guard);

                self.notify_state_change(CircuitStateTransition {
                    from: old_state,
                    to: CircuitState::Open { opened_at: Instant::now() },
                    reason: StateChangeReason::ProbeFailed,
                    timestamp: Instant::now(),
                });
            }
            _ => {}
        }
    }

    fn notify_state_change(&self, transition: CircuitStateTransition) {
        for listener in &self.state_listeners {
            listener(transition.clone());
        }
    }

    /// 获取当前状态
    pub async fn current_state(&self) -> CircuitState {
        *self.state.read().await
    }

    /// 手动强制熔断（用于运维）
    pub async fn force_open(&self) {
        let mut state = self.state.write().await;
        *state = CircuitState::Open { opened_at: Instant::now() };
    }

    /// 手动恢复（用于运维）
    pub async fn force_close(&self) {
        let mut state = self.state.write().await;
        *state = CircuitState::Closed;
        self.failure_count.store(0, Ordering::SeqCst);
    }
}

#[derive(Debug)]
pub enum CircuitResult<T> {
    Success(T),
    Failure(CircuitError),
    Rejected(RejectionReason),
}

#[derive(Debug, Clone)]
pub enum RejectionReason {
    CircuitOpen,
    TooManyHalfOpenRequests,
}

#[derive(Debug, Clone)]
pub enum CircuitError {
    ServiceError(String),
    Timeout,
}

/// 分布式熔断器（在多个实例间共享状态）
pub struct DistributedCircuitBreaker {
    local_breaker: CircuitBreaker,
    state_store: Arc<dyn CircuitStateStore>,
}

#[async_trait]
pub trait CircuitStateStore: Send + Sync {
    async fn save_state(&self, breaker_id: &str, state: &CircuitState);
    async fn load_state(&self, breaker_id: &str) -> Option<CircuitState>;
}
```

**失败计数语义：**

```rust
/// 失败计数策略
#[derive(Debug, Clone)]
pub enum FailureCountStrategy {
    /// 简单计数器：总失败次数
    SimpleCounter,

    /// 连续失败计数器
    ConsecutiveCounter,

    /// 滑动窗口计数器（时间或数量）
    SlidingWindow {
        window_size: Duration,
        bucket_count: usize,
    },

    /// 指数加权移动平均
    ExponentialMovingAverage { alpha: f64 },
}

/// 滑动窗口失败计数器
pub struct SlidingWindowFailureCounter {
    /// 窗口大小
    window_size: Duration,

    /// 桶数量
    bucket_count: usize,

    /// 桶持续时间
    bucket_duration: Duration,

    /// 桶：索引 → (失败数, 总数)
    buckets: Arc<RwLock<Vec<(u32, u32)>>>,

    /// 当前桶索引
    current_bucket: AtomicUsize,

    /// 上次更新时间
    last_rotation: Arc<RwLock<Instant>>,
}

impl SlidingWindowFailureCounter {
    pub fn new(window_size: Duration, bucket_count: usize) -> Self {
        Self {
            window_size,
            bucket_count,
            bucket_duration: window_size / bucket_count as u32,
            buckets: Arc::new(RwLock::new(vec![(0, 0); bucket_count])),
            current_bucket: AtomicUsize::new(0),
            last_rotation: Arc::new(RwLock::new(Instant::now())),
        }
    }

    /// 记录结果
    pub async fn record(&self, success: bool) {
        self.rotate_if_needed().await;

        let current = self.current_bucket.load(Ordering::SeqCst);
        let mut buckets = self.buckets.write().await;

        if success {
            buckets[current].1 += 1;
        } else {
            buckets[current].0 += 1;
            buckets[current].1 += 1;
        }
    }

    /// 获取当前失败率
    pub async fn failure_rate(&self) -> f64 {
        self.rotate_if_needed().await;

        let buckets = self.buckets.read().await;
        let total_failures: u32 = buckets.iter().map(|(f, _)| f).sum();
        let total_requests: u32 = buckets.iter().map(|(_, t)| t).sum();

        if total_requests == 0 {
            0.0
        } else {
            total_failures as f64 / total_requests as f64
        }
    }

    /// 获取总失败次数
    pub async fn total_failures(&self) -> u32 {
        let buckets = self.buckets.read().await;
        buckets.iter().map(|(f, _)| f).sum()
    }

    /// 轮转桶
    async fn rotate_if_needed(&self) {
        let mut last_rotation = self.last_rotation.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last_rotation);

        let buckets_to_advance = (elapsed.as_millis() / self.bucket_duration.as_millis()) as usize;

        if buckets_to_advance > 0 {
            let mut buckets = self.buckets.write().await;
            let current = self.current_bucket.load(Ordering::SeqCst);

            // 清空经过的桶
            for i in 0..buckets_to_advance.min(self.bucket_count) {
                let bucket_to_clear = (current + i + 1) % self.bucket_count;
                buckets[bucket_to_clear] = (0, 0);
            }

            // 更新当前桶索引
            let new_current = (current + buckets_to_advance) % self.bucket_count;
            self.current_bucket.store(new_current, Ordering::SeqCst);

            *last_rotation = now;
        }
    }

    /// 重置
    pub async fn reset(&self) {
        let mut buckets = self.buckets.write().await;
        for bucket in buckets.iter_mut() {
            *bucket = (0, 0);
        }
        self.current_bucket.store(0, Ordering::SeqCst);
        *self.last_rotation.write().await = Instant::now();
    }
}
```

**恢复探测语义：**

```rust
/// 恢复探测策略
#[derive(Debug, Clone)]
pub enum RecoveryProbeStrategy {
    /// 简单计数：允许 N 个探测请求
    SimpleCount { max_probes: u32 },

    /// 渐进式：逐步增加请求比例
    Progressive {
        /// 初始比例
        initial_ratio: f64,
        /// 每次成功后的增长因子
        growth_factor: f64,
        /// 最大比例
        max_ratio: f64,
    },

    /// 金丝雀：只对特定流量探测
    Canary {
        /// 金丝雀选择器
        selector: Box<dyn Fn(&Request) -> bool + Send + Sync>,
    },
}

/// 渐进式恢复管理器
pub struct ProgressiveRecovery {
    /// 当前流量比例
    current_ratio: AtomicU64,

    /// 配置
    config: ProgressiveRecoveryConfig,

    /// 成功计数
    consecutive_successes: AtomicU32,
}

#[derive(Debug, Clone)]
pub struct ProgressiveRecoveryConfig {
    pub initial_ratio: f64,
    pub growth_factor: f64,
    pub max_ratio: f64,
    pub success_threshold: u32,
}

impl ProgressiveRecovery {
    pub fn new(config: ProgressiveRecoveryConfig) -> Self {
        Self {
            current_ratio: AtomicU64::new((config.initial_ratio * 1_000_000.0) as u64),
            config,
            consecutive_successes: AtomicU32::new(0),
        }
    }

    /// 检查是否应该允许请求（基于当前比例）
    pub fn should_allow(&self) -> bool {
        let ratio = self.current_ratio.load(Ordering::SeqCst) as f64 / 1_000_000.0;
        rand::random::<f64>() < ratio
    }

    /// 记录成功
    pub fn record_success(&self) -> bool {
        let successes = self.consecutive_successes.fetch_add(1, Ordering::SeqCst) + 1;

        if successes >= self.config.success_threshold {
            // 增加流量比例
            let current = self.current_ratio.load(Ordering::SeqCst) as f64 / 1_000_000.0;
            let new_ratio = (current * self.config.growth_factor).min(self.config.max_ratio);
            self.current_ratio.store((new_ratio * 1_000_000.0) as u64, Ordering::SeqCst);

            // 重置成功计数
            self.consecutive_successes.store(0, Ordering::SeqCst);

            // 返回是否已达到最大比例
            new_ratio >= self.config.max_ratio
        } else {
            false
        }
    }

    /// 记录失败（重置进度）
    pub fn record_failure(&self) {
        self.consecutive_successes.store(0, Ordering::SeqCst);
        // 可选：降低比例
        let current = self.current_ratio.load(Ordering::SeqCst) as f64 / 1_000_000.0;
        let new_ratio = current / self.config.growth_factor;
        self.current_ratio.store((new_ratio * 1_000_000.0) as u64, Ordering::SeqCst);
    }

    pub fn current_ratio(&self) -> f64 {
        self.current_ratio.load(Ordering::SeqCst) as f64 / 1_000_000.0
    }
}

struct Request;
```

### 5.2 重试模式

**指数退避语义：**

```rust
/// 指数退避语义
///
/// 公式：delay = min(base * 2^attempt + jitter, max_delay)

pub struct ExponentialBackoff {
    /// 基础延迟
    base_delay: Duration,

    /// 最大延迟
    max_delay: Duration,

    /// 最大重试次数
    max_retries: u32,

    /// 退避乘数
    multiplier: f64,

    /// 抖动策略
    jitter: JitterStrategy,
}

#[derive(Debug, Clone)]
pub enum JitterStrategy {
    /// 无抖动
    None,

    /// 完全随机：0 到计算延迟之间随机
    Full,

    /// 等宽抖动：计算延迟 ± 固定范围
    Equal { width: Duration },

    ///  decorrelated 抖动：减少相关性
    Decorrelated { max_delay: Duration },
}

impl ExponentialBackoff {
    pub fn new(base_delay: Duration, max_delay: Duration) -> Self {
        Self {
            base_delay,
            max_delay,
            max_retries: 3,
            multiplier: 2.0,
            jitter: JitterStrategy::Full,
        }
    }

    /// 计算下次延迟
    pub fn next_delay(&self, attempt: u32) -> Option<Duration> {
        if attempt >= self.max_retries {
            return None;
        }

        // 计算指数退避
        let exponential = self.base_delay.as_millis() as f64
            * self.multiplier.powi(attempt as i32);

        let base_delay = Duration::from_millis(exponential as u64)
            .min(self.max_delay);

        // 应用抖动
        let delay = match &self.jitter {
            JitterStrategy::None => base_delay,
            JitterStrategy::Full => {
                let jitter_ms = rand::random::<u64>() % base_delay.as_millis() as u64;
                Duration::from_millis(jitter_ms)
            }
            JitterStrategy::Equal { width } => {
                let jitter_ms = if rand::random::<bool>() {
                    -(width.as_millis() as i64)
                } else {
                    width.as_millis() as i64
                };
                let new_ms = (base_delay.as_millis() as i64 + jitter_ms).max(0) as u64;
                Duration::from_millis(new_ms)
            }
            JitterStrategy::Decorrelated { max_delay } => {
                // decorrelated 抖动公式：random(base, prev_delay * 3)
                let upper = (base_delay * 3).min(*max_delay);
                let range = upper - base_delay;
                let jitter = Duration::from_millis(
                    rand::random::<u64>() % range.as_millis().max(1) as u64
                );
                base_delay + jitter
            }
        };

        Some(delay)
    }

    /// 创建重试迭代器
    pub fn iter(&self) -> impl Iterator<Item = Duration> + '_ {
        (0..self.max_retries).filter_map(move |i| self.next_delay(i))
    }
}

/// 使用示例
pub async fn with_exponential_retry<F, Fut, T>(
    operation: F,
    backoff: ExponentialBackoff,
) -> Result<T, RetryExhausted>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T, RetryableError>>,
{
    let mut last_error = None;

    for (attempt, delay) in backoff.iter().enumerate() {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(error) => {
                last_error = Some(error);

                if attempt < backoff.max_retries as usize - 1 {
                    tracing::warn!("Retry attempt {} after {:?}", attempt + 1, delay);
                    tokio::time::sleep(delay).await;
                }
            }
        }
    }

    Err(RetryExhausted {
        attempts: backoff.max_retries,
        last_error: last_error.unwrap(),
    })
}
```

**抖动语义：**

```rust
/// 抖动策略详细说明
///
/// 目的：避免惊群效应（Thundering Herd）
/// 当服务恢复时，所有客户端同时重试可能导致服务再次过载

impl JitterStrategy {
    /// 计算带抖动的延迟
    ///
    /// 各种策略的数学表达：
    /// - None: delay = base * 2^attempt
    /// - Full: delay = random(0, base * 2^attempt)
    /// - Equal: delay = base * 2^attempt ± width
    /// - Decorrelated: delay = random(base, min(prev * 3, max))
    pub fn calculate(&self, base_delay: Duration, attempt: u32, multiplier: f64) -> Duration {
        let exponential = base_delay.as_millis() as f64 * multiplier.powi(attempt as i32);
        let delay = Duration::from_millis(exponential as u64);

        match self {
            JitterStrategy::None => delay,

            JitterStrategy::Full => {
                // 在 [0, delay] 之间均匀分布
                let jitter = (rand::random::<f64>() * delay.as_millis() as f64) as u64;
                Duration::from_millis(jitter)
            }

            JitterStrategy::Equal { width } => {
                // 在 [delay - width, delay + width] 之间均匀分布
                let jitter = (rand::random::<f64>() * 2.0 - 1.0) * width.as_millis() as f64;
                let new_delay = (delay.as_millis() as f64 + jitter).max(0.0) as u64;
                Duration::from_millis(new_delay)
            }

            JitterStrategy::Decorrelated { max_delay } => {
                // 减少连续重试之间的相关性
                let upper = (delay * 3).min(*max_delay);
                let jitter_range = upper.as_millis() as f64 - delay.as_millis() as f64;
                let jitter = rand::random::<f64>() * jitter_range;
                let new_delay = delay.as_millis() as f64 + jitter;
                Duration::from_millis(new_delay as u64)
            }
        }
    }
}
```

**断路器集成：**

```rust
/// 重试与熔断器集成
///
/// 语义：
/// - 重试是局部的：单个请求的重试
/// - 熔断是全局的：服务级别的保护
/// - 熔断器应该只在最终失败时触发，而不是每次重试失败

pub struct RetryWithCircuitBreaker {
    retry_policy: ExponentialBackoff,
    circuit_breaker: CircuitBreaker,
}

impl RetryWithCircuitBreaker {
    /// 执行带熔断器的重试
    pub async fn call<F, Fut, T>(&self, operation: F) -> RetryCircuitResult<T>
    where
        F: Fn() -> Fut + Clone,
        Fut: std::future::Future<Output = Result<T, RetryableError>>,
    {
        // 先检查熔断器
        match self.circuit_breaker.current_state().await {
            CircuitState::Open { .. } => {
                return RetryCircuitResult::CircuitOpen;
            }
            _ => {}
        }

        let mut last_error = None;

        for (attempt, delay) in self.retry_policy.iter().enumerate() {
            let op = operation.clone();

            match op().await {
                Ok(result) => {
                    // 成功，记录到熔断器
                    self.circuit_breaker.call(|| async { Ok::<_, CircuitError>(result) }).await;
                    return RetryCircuitResult::Success(result);
                }
                Err(error) => {
                    last_error = Some(error);

                    if attempt < self.retry_policy.max_retries as usize - 1 {
                        tracing::warn!(
                            "Retry attempt {} after {:?}",
                            attempt + 1,
                            delay
                        );
                        tokio::time::sleep(delay).await;
                    }
                }
            }
        }

        // 所有重试都失败了，记录到熔断器
        let final_error = last_error.unwrap();
        let _ = self.circuit_breaker.call(|| async {
            Err::<(), _>(CircuitError::ServiceError(final_error.to_string()))
        }).await;

        RetryCircuitResult::RetryExhausted {
            attempts: self.retry_policy.max_retries,
            error: final_error,
        }
    }
}

#[derive(Debug)]
pub enum RetryCircuitResult<T> {
    Success(T),
    CircuitOpen,
    RetryExhausted { attempts: u32, error: RetryableError },
}

#[derive(Debug, Clone)]
pub enum RetryableError {
    Timeout,
    ServiceUnavailable,
    NetworkError(String),
}

impl std::fmt::Display for RetryableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
```

### 5.3 舱壁隔离模式

**资源隔离语义：**

```rust
/// 舱壁隔离模式（Bulkhead）
///
/// 原理：将资源分成独立的池，一个池的故障不会影响其他池
/// 类比：船舱的隔板，一个舱进水不会淹没整艘船

pub struct Bulkhead {
    /// 舱壁配置
    config: BulkheadConfig,

    /// 各舱壁的状态
    compartments: HashMap<String, Compartment>,
}

#[derive(Debug, Clone)]
pub struct BulkheadConfig {
    /// 默认最大并发数
    pub default_max_concurrent: usize,

    /// 默认最大等待队列长度
    pub default_max_wait_queue: usize,
}

/// 舱壁（资源池）
pub struct Compartment {
    /// 名称
    name: String,

    /// 信号量（限制并发）
    semaphore: Arc<Semaphore>,

    /// 等待队列
    wait_queue: Arc<Mutex<Vec<WaitEntry>>>,

    /// 最大并发数
    max_concurrent: usize,

    /// 最大等待队列长度
    max_wait_queue: usize,

    /// 指标
    metrics: Arc<RwLock<CompartmentMetrics>>,
}

#[derive(Debug, Default)]
pub struct CompartmentMetrics {
    pub active_calls: u32,
    pub queued_calls: u32,
    pub rejected_calls: u64,
    pub completed_calls: u64,
    pub failed_calls: u64,
}

struct WaitEntry {
    permit_tx: oneshot::Sender<OwnedSemaphorePermit>,
    requested_at: Instant,
}

impl Bulkhead {
    pub fn new(config: BulkheadConfig) -> Self {
        Self {
            config,
            compartments: HashMap::new(),
        }
    }

    /// 注册舱壁
    pub fn register_compartment(&mut self, name: &str) {
        let compartment = Compartment {
            name: name.to_string(),
            semaphore: Arc::new(Semaphore::new(self.config.default_max_concurrent)),
            wait_queue: Arc::new(Mutex::new(Vec::new())),
            max_concurrent: self.config.default_max_concurrent,
            max_wait_queue: self.config.default_max_wait_queue,
            metrics: Arc::new(RwLock::new(CompartmentMetrics::default())),
        };

        self.compartments.insert(name.to_string(), compartment);
    }

    /// 在指定舱壁中执行
    pub async fn execute<F, Fut, T>(
        &self,
        compartment_name: &str,
        operation: F,
    ) -> BulkheadResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, BulkheadError>>,
    {
        let compartment = self.compartments.get(compartment_name)
            .ok_or(BulkheadError::CompartmentNotFound)?;

        // 尝试获取许可
        match compartment.semaphore.clone().try_acquire_owned() {
            Ok(permit) => {
                // 成功获取，直接执行
                self.execute_with_permit(compartment, permit, operation).await
            }
            Err(TryAcquireError::NoPermits) => {
                // 没有可用许可，尝试加入等待队列
                self.enqueue_or_reject(compartment, operation).await
            }
            Err(TryAcquireError::Closed) => {
                Err(BulkheadError::CompartmentClosed)
            }
        }
    }

    async fn execute_with_permit<F, Fut, T>(
        &self,
        compartment: &Compartment,
        _permit: OwnedSemaphorePermit,
        operation: F,
    ) -> BulkheadResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, BulkheadError>>,
    {
        // 更新指标
        {
            let mut metrics = compartment.metrics.write().await;
            metrics.active_calls += 1;
        }

        // 执行操作
        let result = operation().await;

        // 更新指标
        {
            let mut metrics = compartment.metrics.write().await;
            metrics.active_calls -= 1;
            match &result {
                Ok(_) => metrics.completed_calls += 1,
                Err(_) => metrics.failed_calls += 1,
            }
        }

        // 处理等待队列
        self.process_wait_queue(compartment).await;

        result.map_err(BulkheadError::OperationFailed)
    }

    async fn enqueue_or_reject<F, Fut, T>(
        &self,
        compartment: &Compartment,
        operation: F,
    ) -> BulkheadResult<T>
    where
        F: FnOnce() -> Fut + 'static,
        Fut: std::future::Future<Output = Result<T, BulkheadError>> + 'static,
    {
        let mut queue = compartment.wait_queue.lock().await;

        if queue.len() >= compartment.max_wait_queue {
            // 队列已满，拒绝
            let mut metrics = compartment.metrics.write().await;
            metrics.rejected_calls += 1;

            return Err(BulkheadError::QueueFull);
        }

        // 加入等待队列
        let (tx, rx) = oneshot::channel();
        queue.push(WaitEntry {
            permit_tx: tx,
            requested_at: Instant::now(),
        });

        {
            let mut metrics = compartment.metrics.write().await;
            metrics.queued_calls += 1;
        }

        drop(queue);

        // 等待许可
        match rx.await {
            Ok(permit) => {
                self.execute_with_permit(compartment, permit, operation).await
            }
            Err(_) => {
                Err(BulkheadError::WaitCancelled)
            }
        }
    }

    async fn process_wait_queue(&self, compartment: &Compartment) {
        let mut queue = compartment.wait_queue.lock().await;

        while let Some(entry) = queue.pop() {
            // 尝试获取许可
            match compartment.semaphore.clone().try_acquire_owned() {
                Ok(permit) => {
                    // 发送许可给等待者
                    if entry.permit_tx.send(permit).is_err() {
                        // 接收者已取消，继续尝试下一个
                        continue;
                    }

                    {
                        let mut metrics = compartment.metrics.write().await;
                        metrics.queued_calls -= 1;
                    }

                    break; // 只处理一个
                }
                Err(_) => {
                    // 没有可用许可，放回队列
                    queue.push(entry);
                    break;
                }
            }
        }
    }

    /// 获取舱壁指标
    pub async fn metrics(&self, compartment_name: &str) -> Option<CompartmentMetrics> {
        self.compartments.get(compartment_name)
            .map(|c| c.metrics.read().await.clone())
    }
}

#[derive(Debug)]
pub enum BulkheadResult<T> {
    Success(T),
    Err(BulkheadError),
}

#[derive(Debug)]
pub enum BulkheadError {
    CompartmentNotFound,
    CompartmentClosed,
    QueueFull,
    WaitCancelled,
    WaitTimeout,
    OperationFailed(Box<dyn std::error::Error + Send + Sync>),
}
```

**线程池隔离：**

```rust
/// 线程池隔离
///
/// 不同服务使用独立的线程池，避免一个服务耗尽所有线程

pub struct ThreadPoolBulkhead {
    /// 各服务的线程池
    pools: HashMap<String, DedicatedThreadPool>,
}

pub struct DedicatedThreadPool {
    name: String,
    pool: rayon::ThreadPool,
    max_tasks: usize,
    active_tasks: AtomicUsize,
    pending_tasks: AtomicUsize,
}

impl DedicatedThreadPool {
    pub fn new(name: &str, num_threads: usize, max_tasks: usize) -> Self {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .thread_name(move |i| format!("{}-{}", name, i))
            .build()
            .expect("Failed to create thread pool");

        Self {
            name: name.to_string(),
            pool,
            max_tasks,
            active_tasks: AtomicUsize::new(0),
            pending_tasks: AtomicUsize::new(0),
        }
    }

    /// 在线程池中执行异步任务
    pub async fn spawn<F, R>(&self, task: F) -> ThreadPoolResult<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        // 检查是否超过最大任务数
        let active = self.active_tasks.fetch_add(1, Ordering::SeqCst);

        if active >= self.max_tasks {
            self.active_tasks.fetch_sub(1, Ordering::SeqCst);
            return ThreadPoolResult::Rejected(RejectReason::PoolFull);
        }

        // 在线程池中执行
        let (tx, rx) = oneshot::channel();

        self.pool.spawn(move || {
            let result = task();
            let _ = tx.send(result);
        });

        match rx.await {
            Ok(result) => {
                self.active_tasks.fetch_sub(1, Ordering::SeqCst);
                ThreadPoolResult::Success(result)
            }
            Err(_) => {
                self.active_tasks.fetch_sub(1, Ordering::SeqCst);
                ThreadPoolResult::Cancelled
            }
        }
    }

    pub fn metrics(&self) -> ThreadPoolMetrics {
        ThreadPoolMetrics {
            active_tasks: self.active_tasks.load(Ordering::SeqCst),
            pending_tasks: self.pending_tasks.load(Ordering::SeqCst),
            available_slots: self.max_tasks.saturating_sub(
                self.active_tasks.load(Ordering::SeqCst)
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ThreadPoolMetrics {
    pub active_tasks: usize,
    pub pending_tasks: usize,
    pub available_slots: usize,
}

#[derive(Debug)]
pub enum ThreadPoolResult<T> {
    Success(T),
    Rejected(RejectReason),
    Cancelled,
}

#[derive(Debug)]
pub enum RejectReason {
    PoolFull,
    QueueFull,
    Timeout,
}
```

**信号量隔离：**

```rust
/// 基于信号量的隔离（异步友好）

pub struct SemaphoreBulkhead {
    compartments: HashMap<String, AsyncCompartment>,
}

pub struct AsyncCompartment {
    name: String,
    /// 并发信号量
    concurrency_limit: Arc<Semaphore>,
    /// 等待队列信号量
    queue_limit: Arc<Semaphore>,
    /// 超时配置
    timeout: Duration,
}

impl AsyncCompartment {
    pub fn new(name: &str, max_concurrent: usize, max_queue: usize, timeout: Duration) -> Self {
        Self {
            name: name.to_string(),
            concurrency_limit: Arc::new(Semaphore::new(max_concurrent)),
            queue_limit: Arc::new(Semaphore::new(max_queue)),
            timeout,
        }
    }

    /// 执行操作
    pub async fn execute<F, Fut, T>(&self, operation: F) -> SemaphoreResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
    {
        // 首先获取队列许可
        let queue_permit = match tokio::time::timeout(
            self.timeout,
            self.queue_limit.clone().acquire_owned()
        ).await {
            Ok(Ok(permit)) => permit,
            Ok(Err(_)) => return SemaphoreResult::Rejected("Queue semaphore closed".to_string()),
            Err(_) => return SemaphoreResult::Rejected("Queue timeout".to_string()),
        };

        // 然后获取执行许可
        let exec_permit = match tokio::time::timeout(
            self.timeout,
            self.concurrency_limit.clone().acquire_owned()
        ).await {
            Ok(Ok(permit)) => permit,
            Ok(Err(_)) => return SemaphoreResult::Rejected("Exec semaphore closed".to_string()),
            Err(_) => return SemaphoreResult::Rejected("Execution timeout".to_string()),
        };

        // 已获得执行许可，可以释放队列许可
        drop(queue_permit);

        // 执行操作
        match operation().await {
            Ok(result) => SemaphoreResult::Success(result),
            Err(e) => SemaphoreResult::Error(e),
        }

        // exec_permit 在这里自动释放
    }
}

#[derive(Debug)]
pub enum SemaphoreResult<T> {
    Success(T),
    Rejected(String),
    Error(Box<dyn std::error::Error>),
}
```

### 5.4 限流模式

**令牌桶语义：**

```rust
/// 令牌桶限流算法
///
/// 原理：
/// - 桶以固定速率产生令牌
/// - 每个请求需要消耗一个令牌
/// - 桶有最大容量，满了不再产生新令牌

pub struct TokenBucket {
    /// 桶容量
    capacity: u64,

    /// 当前令牌数
    tokens: Arc<AtomicU64>,

    ///  refill 速率（每秒令牌数）
    refill_rate: f64,

    /// 上次 refill 时间
    last_refill: Arc<Mutex<Instant>>,
}

impl TokenBucket {
    pub fn new(capacity: u64, refill_rate: f64) -> Self {
        Self {
            capacity,
            tokens: Arc::new(AtomicU64::new(capacity)),
            refill_rate,
            last_refill: Arc::new(Mutex::new(Instant::now())),
        }
    }

    /// 尝试消耗令牌
    pub fn try_consume(&self, tokens: u64) -> ConsumeResult {
        // 先 refill
        self.refill();

        // 原子操作：获取当前令牌数，如果足够则减少
        let current = self.tokens.load(Ordering::SeqCst);

        if current >= tokens {
            let new_tokens = current - tokens;
            match self.tokens.compare_exchange(
                current,
                new_tokens,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => ConsumeResult::Allowed { remaining: new_tokens },
                Err(_) => ConsumeResult::Retry, // 竞争失败，需要重试
            }
        } else {
            ConsumeResult::Rejected {
                available: current,
                requested: tokens,
            }
        }
    }

    /// 阻塞式消费（带超时）
    pub async fn consume(&self, tokens: u64, timeout: Duration) -> ConsumeResult {
        let deadline = Instant::now() + timeout;

        loop {
            match self.try_consume(tokens) {
                ConsumeResult::Allowed { remaining } => {
                    return ConsumeResult::Allowed { remaining };
                }
                ConsumeResult::Rejected { available, requested } => {
                    // 计算需要等待的时间
                    let needed = requested - available;
                    let wait_time = Duration::from_secs_f64(needed as f64 / self.refill_rate);

                    if Instant::now() + wait_time > deadline {
                        return ConsumeResult::Timeout;
                    }

                    tokio::time::sleep(wait_time.min(Duration::from_millis(10))).await;
                }
                ConsumeResult::Retry => {
                    tokio::task::yield_now().await;
                }
                _ => {}
            }
        }
    }

    /// refill 令牌
    fn refill(&self) {
        let mut last_refill = self.last_refill.lock().unwrap();
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill).as_secs_f64();

        if elapsed > 0.0 {
            let new_tokens = (elapsed * self.refill_rate) as u64;

            if new_tokens > 0 {
                let current = self.tokens.load(Ordering::SeqCst);
                let updated = (current + new_tokens).min(self.capacity);
                self.tokens.store(updated, Ordering::SeqCst);
                *last_refill = now;
            }
        }
    }

    /// 获取当前令牌数
    pub fn available_tokens(&self) -> u64 {
        self.refill();
        self.tokens.load(Ordering::SeqCst)
    }
}

#[derive(Debug)]
pub enum ConsumeResult {
    Allowed { remaining: u64 },
    Rejected { available: u64, requested: u64 },
    Retry,
    Timeout,
}

/// 分布式令牌桶（基于 Redis）
pub struct DistributedTokenBucket {
    redis: redis::aio::MultiplexedConnection,
    key: String,
    capacity: u64,
    refill_rate: f64,
}

impl DistributedTokenBucket {
    pub async fn try_consume(&mut self, tokens: u64) -> Result<ConsumeResult, redis::RedisError> {
        let script = redis::Script::new(r#"
            local key = KEYS[1]
            local capacity = tonumber(ARGV[1])
            local refill_rate = tonumber(ARGV[2])
            local now = tonumber(ARGV[3])
            local requested = tonumber(ARGV[4])

            -- 获取上次 refill 时间和当前令牌数
            local bucket = redis.call('HMGET', key, 'tokens', 'last_refill')
            local current_tokens = tonumber(bucket[1]) or capacity
            local last_refill = tonumber(bucket[2]) or now

            -- 计算新的令牌数
            local elapsed = now - last_refill
            local new_tokens = math.min(
                capacity,
                current_tokens + elapsed * refill_rate
            )

            -- 检查是否有足够令牌
            if new_tokens >= requested then
                new_tokens = new_tokens - requested
                redis.call('HMSET', key, 'tokens', new_tokens, 'last_refill', now)
                redis.call('EXPIRE', key, 3600)
                return {1, new_tokens}  -- 允许
            else
                redis.call('HMSET', key, 'tokens', new_tokens, 'last_refill', now)
                redis.call('EXPIRE', key, 3600)
                return {0, new_tokens}  -- 拒绝
            end
        "#");

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs_f64();

        let result: Vec<i64> = script
            .key(&self.key)
            .arg(self.capacity)
            .arg(self.refill_rate)
            .arg(now)
            .arg(tokens)
            .invoke_async(&mut self.redis)
            .await?;

        if result[0] == 1 {
            Ok(ConsumeResult::Allowed { remaining: result[1] as u64 })
        } else {
            Ok(ConsumeResult::Rejected {
                available: result[1] as u64,
                requested: tokens,
            })
        }
    }
}
```

**漏桶语义：**

```rust
/// 漏桶限流算法
///
/// 原理：
/// - 请求进入桶中（桶有容量限制）
/// - 桶以固定速率漏出（处理）请求
/// - 桶满时新请求被拒绝

pub struct LeakyBucket {
    /// 桶容量
    capacity: usize,

    /// 漏水速率（每秒请求数）
    leak_rate: f64,

    /// 当前桶中水量（请求数）
    water: Arc<Mutex<f64>>,

    /// 上次漏水时间
    last_leak: Arc<Mutex<Instant>>,

    /// 等待队列
    wait_queue: Arc<Mutex<VecDeque<oneshot::Sender<()>>>>,
}

impl LeakyBucket {
    pub fn new(capacity: usize, leak_rate: f64) -> Self {
        let bucket = Self {
            capacity,
            leak_rate,
            water: Arc::new(Mutex::new(0.0)),
            last_leak: Arc::new(Mutex::new(Instant::now())),
            wait_queue: Arc::new(Mutex::new(VecDeque::new())),
        };

        // 启动漏水任务
        let water = bucket.water.clone();
        let last_leak = bucket.last_leak.clone();
        let wait_queue = bucket.wait_queue.clone();
        let leak_rate = leak_rate;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_millis(10));

            loop {
                interval.tick().await;

                // 漏水
                let mut last = last_leak.lock().unwrap();
                let now = Instant::now();
                let elapsed = now.duration_since(*last).as_secs_f64();

                if elapsed > 0.0 {
                    let mut water_level = water.lock().unwrap();
                    let leaked = elapsed * leak_rate;
                    *water_level = (*water_level - leaked).max(0.0);
                    *last = now;

                    // 唤醒等待的请求
                    if *water_level < 1.0 {
                        let mut queue = wait_queue.lock().unwrap();
                        if let Some(tx) = queue.pop_front() {
                            *water_level += 1.0;
                            let _ = tx.send(());
                        }
                    }
                }
            }
        });

        bucket
    }

    /// 尝试进入桶
    pub fn try_acquire(&self) -> LeakyResult {
        let mut water = self.water.lock().unwrap();

        if *water < self.capacity as f64 {
            *water += 1.0;
            LeakyResult::Acquired
        } else {
            LeakyResult::Rejected
        }
    }

    /// 阻塞式获取（带超时）
    pub async fn acquire(&self, timeout: Duration) -> LeakyResult {
        // 先尝试直接获取
        match self.try_acquire() {
            LeakyResult::Acquired => return LeakyResult::Acquired,
            _ => {}
        }

        // 加入等待队列
        let (tx, rx) = oneshot::channel();
        {
            let mut queue = self.wait_queue.lock().unwrap();
            queue.push_back(tx);
        }

        // 等待被唤醒或超时
        match tokio::time::timeout(timeout, rx).await {
            Ok(Ok(())) => LeakyResult::Acquired,
            Ok(Err(_)) => LeakyResult::Cancelled,
            Err(_) => LeakyResult::Timeout,
        }
    }

    /// 完成请求处理（减少水量）
    pub fn release(&self) {
        let mut water = self.water.lock().unwrap();
        *water = (*water - 1.0).max(0.0);
    }
}

#[derive(Debug)]
pub enum LeakyResult {
    Acquired,
    Rejected,
    Cancelled,
    Timeout,
}
```

**固定窗口语义：**

```rust
/// 固定窗口限流
///
/// 原理：将时间划分为固定窗口，每个窗口有独立的计数器
/// 问题：窗口边界可能出现双倍流量（临界问题）

pub struct FixedWindowRateLimiter {
    /// 窗口大小
    window_size: Duration,

    /// 每个窗口最大请求数
    max_requests: u32,

    /// 当前窗口计数
    current_count: AtomicU32,

    /// 当前窗口开始时间
    window_start: Arc<Mutex<Instant>>,
}

impl FixedWindowRateLimiter {
    pub fn new(window_size: Duration, max_requests: u32) -> Self {
        Self {
            window_size,
            max_requests,
            current_count: AtomicU32::new(0),
            window_start: Arc::new(Mutex::new(Instant::now())),
        }
    }

    /// 检查并增加计数
    pub fn try_acquire(&self) -> WindowResult {
        // 检查是否需要重置窗口
        {
            let mut start = self.window_start.lock().unwrap();
            if start.elapsed() >= self.window_size {
                // 新窗口
                *start = Instant::now();
                self.current_count.store(0, Ordering::SeqCst);
            }
        }

        // 尝试增加计数
        let current = self.current_count.fetch_add(1, Ordering::SeqCst);

        if current < self.max_requests {
            WindowResult::Allowed {
                remaining: self.max_requests - current - 1,
                reset_time: self.window_start.lock().unwrap().clone() + self.window_size,
            }
        } else {
            // 超限，需要减回（不太精确，但简单）
            self.current_count.fetch_sub(1, Ordering::SeqCst);

            WindowResult::Rejected {
                retry_after: self.window_size - self.window_start.lock().unwrap().elapsed(),
            }
        }
    }
}

#[derive(Debug)]
pub enum WindowResult {
    Allowed { remaining: u32, reset_time: Instant },
    Rejected { retry_after: Duration },
}
```

**滑动窗口语义：**

```rust
/// 滑动窗口限流
///
/// 原理：使用滑动窗口计算最近 window_size 时间内的请求数
/// 解决固定窗口的临界问题

pub struct SlidingWindowRateLimiter {
    /// 窗口大小
    window_size: Duration,

    /// 最大请求数
    max_requests: u32,

    /// 请求时间戳队列
    requests: Arc<Mutex<VecDeque<Instant>>>,
}

impl SlidingWindowRateLimiter {
    pub fn new(window_size: Duration, max_requests: u32) -> Self {
        Self {
            window_size,
            max_requests,
            requests: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// 尝试获取许可
    pub fn try_acquire(&self) -> WindowResult {
        let mut requests = self.requests.lock().unwrap();
        let now = Instant::now();

        // 移除窗口外的旧请求
        while let Some(front) = requests.front() {
            if now.duration_since(*front) > self.window_size {
                requests.pop_front();
            } else {
                break;
            }
        }

        // 检查当前窗口内的请求数
        let current_count = requests.len() as u32;

        if current_count < self.max_requests {
            requests.push_back(now);
            WindowResult::Allowed {
                remaining: self.max_requests - current_count - 1,
                reset_time: now + self.window_size,
            }
        } else {
            // 计算下次可重试时间
            let oldest = requests.front().unwrap();
            WindowResult::Rejected {
                retry_after: self.window_size - now.duration_since(*oldest),
            }
        }
    }

    /// 获取当前窗口统计
    pub fn current_stats(&self) -> WindowStats {
        let mut requests = self.requests.lock().unwrap();
        let now = Instant::now();

        // 清理旧请求
        while let Some(front) = requests.front() {
            if now.duration_since(*front) > self.window_size {
                requests.pop_front();
            } else {
                break;
            }
        }

        WindowStats {
            current_requests: requests.len() as u32,
            max_requests: self.max_requests,
            oldest_request: requests.front().copied(),
            newest_request: requests.back().copied(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct WindowStats {
    pub current_requests: u32,
    pub max_requests: u32,
    pub oldest_request: Option<Instant>,
    pub newest_request: Option<Instant>,
}

/// 分布式滑动窗口（基于 Redis Sorted Set）
pub struct DistributedSlidingWindow {
    redis: redis::aio::MultiplexedConnection,
    key: String,
    window_size: Duration,
    max_requests: u32,
}

impl DistributedSlidingWindow {
    pub async fn try_acquire(&mut self) -> Result<WindowResult, redis::RedisError> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as f64;

        let window_start = now - self.window_size.as_millis() as f64;

        let script = redis::Script::new(r#"
            local key = KEYS[1]
            local now = tonumber(ARGV[1])
            local window_start = tonumber(ARGV[2])
            local max_requests = tonumber(ARGV[3])
            local window_size = tonumber(ARGV[4])

            -- 移除窗口外的旧请求
            redis.call('ZREMRANGEBYSCORE', key, 0, window_start)

            -- 获取当前请求数
            local current = redis.call('ZCARD', key)

            if current < max_requests then
                -- 添加当前请求
                redis.call('ZADD', key, now, now)
                redis.call('EXPIRE', key, window_size)
                return {1, max_requests - current - 1}
            else
                -- 获取最早请求的过期时间
                local oldest = redis.call('ZRANGE', key, 0, 0, 'WITHSCORES')[2]
                local retry_after = window_start + window_size - oldest
                return {0, retry_after}
            end
        "#");

        let result: Vec<i64> = script
            .key(&self.key)
            .arg(now)
            .arg(window_start)
            .arg(self.max_requests)
            .arg(self.window_size.as_secs())
            .invoke_async(&mut self.redis)
            .await?;

        if result[0] == 1 {
            Ok(WindowResult::Allowed {
                remaining: result[1] as u32,
                reset_time: Instant::now() + self.window_size,
            })
        } else {
            Ok(WindowResult::Rejected {
                retry_after: Duration::from_millis(result[1] as u64),
            })
        }
    }
}
```

---

## 6. 数据分区模式

### 6.1 分片模式

**水平分片语义：**

```rust
/// 水平分片（Sharding）语义
///
/// 将数据按行分散到多个节点
/// 每个分片包含完整数据结构的一部分数据

pub struct ShardedStorage<K, V> {
    /// 分片策略
    sharder: Box<dyn Sharder<K>>,

    /// 分片列表
    shards: Vec<Shard>,

    /// 分片到节点的映射
    shard_placement: ShardPlacement,
}

/// 分片策略 trait
pub trait Sharder<K>: Send + Sync {
    /// 计算 key 所属的分片
    fn shard_for_key(&self, key: &K, shard_count: usize) -> ShardId;
}

/// 哈希分片
pub struct HashSharder;

impl<K: Hash> Sharder<K> for HashSharder {
    fn shard_for_key(&self, key: &K, shard_count: usize) -> ShardId {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;
        ShardId(hash % shard_count)
    }
}

/// 范围分片
pub struct RangeSharder<K: Ord> {
    /// 分片边界
    boundaries: Vec<K>,
}

impl<K: Ord + Clone> Sharder<K> for RangeSharder<K> {
    fn shard_for_key(&self, key: &K, _shard_count: usize) -> ShardId {
        // 二分查找确定分片
        match self.boundaries.binary_search(key) {
            Ok(idx) => ShardId(idx),
            Err(idx) => ShardId(idx.min(self.boundaries.len())),
        }
    }
}

/// 目录分片（查表）
pub struct DirectorySharder<K: Eq + Hash> {
    /// key → 分片 映射表
    directory: HashMap<K, ShardId>,
}

impl<K: Eq + Hash + Clone> Sharder<K> for DirectorySharder<K> {
    fn shard_for_key(&self, key: &K, _shard_count: usize) -> ShardId {
        self.directory.get(key).copied().unwrap_or(ShardId(0))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ShardId(pub usize);

/// 分片
pub struct Shard {
    pub id: ShardId,
    pub node: NodeId,
    pub storage: Arc<dyn Storage>,
}

/// 分片放置策略
pub struct ShardPlacement {
    /// 分片 → 主节点
    primary: HashMap<ShardId, NodeId>,
    /// 分片 → 副本节点列表
    replicas: HashMap<ShardId, Vec<NodeId>>,
}

impl<K, V> ShardedStorage<K, V> {
    /// 读取数据
    pub async fn get(&self, key: &K) -> Result<Option<V>, ShardError> {
        let shard_id = self.sharder.shard_for_key(key, self.shards.len());
        let shard = self.shards.get(shard_id.0)
            .ok_or(ShardError::ShardNotFound)?;

        shard.storage.get(key).await
            .map_err(|e| ShardError::StorageError(e.to_string()))
    }

    /// 写入数据
    pub async fn put(&self, key: K, value: V) -> Result<(), ShardError> {
        let shard_id = self.sharder.shard_for_key(&key, self.shards.len());
        let shard = self.shards.get(shard_id.0)
            .ok_or(ShardError::ShardNotFound)?;

        shard.storage.put(&key, &value).await
            .map_err(|e| ShardError::StorageError(e.to_string()))
    }

    /// 跨分片查询（Scatter-Gather）
    pub async fn query_all<F, R>(&self, query: F) -> Vec<R>
    where
        F: Fn(&dyn Storage) -> R + Send + Sync,
        R: Send,
    {
        let futures: Vec<_> = self.shards.iter()
            .map(|shard| {
                let query = &query;
                async move {
                    query(&*shard.storage)
                }
            })
            .collect();

        futures::future::join_all(futures).await
    }
}

#[derive(Debug)]
pub enum ShardError {
    ShardNotFound,
    StorageError(String),
    NetworkError,
}
```

**垂直分片语义：**

```rust
/// 垂直分片语义
///
/// 按列分片，不同字段存储在不同节点
/// 适用于宽表，某些字段访问频率更高

pub struct VerticalSharder {
    /// 字段 → 分片 映射
    column_shards: HashMap<String, ShardId>,

    /// 主键所在分片（用于连接）
    primary_key_shard: ShardId,
}

impl VerticalSharder {
    /// 确定字段所属分片
    pub fn shard_for_column(&self, column: &str) -> ShardId {
        self.column_shards.get(column)
            .copied()
            .unwrap_or(self.primary_key_shard)
    }

    /// 跨分片组装完整记录
    pub async fn assemble_record(
        &self,
        primary_key: &PrimaryKey,
        shards: &HashMap<ShardId, Arc<dyn ColumnStorage>>,
        columns: &[String],
    ) -> Result<Record, ShardError> {
        let mut record = Record::new(primary_key.clone());

        // 按分片分组字段
        let mut shard_columns: HashMap<ShardId, Vec<String>> = HashMap::new();
        for col in columns {
            let shard = self.shard_for_column(col);
            shard_columns.entry(shard).or_default().push(col.clone());
        }

        // 并行从各分片获取数据
        let mut futures = Vec::new();
        for (shard_id, cols) in shard_columns {
            let storage = shards.get(&shard_id)
                .ok_or(ShardError::ShardNotFound)?;

            let pk = primary_key.clone();
            futures.push(async move {
                storage.get_columns(&pk, &cols).await
            });
        }

        // 合并结果
        let results = futures::future::join_all(futures).await;
        for result in results {
            let partial = result.map_err(|e| ShardError::StorageError(e.to_string()))?;
            record.merge(partial);
        }

        Ok(record)
    }
}

/// 列存储 trait
#[async_trait]
pub trait ColumnStorage: Send + Sync {
    async fn get_columns(
        &self,
        primary_key: &PrimaryKey,
        columns: &[String],
    ) -> Result<PartialRecord, StorageError>;

    async fn put_columns(
        &self,
        primary_key: &PrimaryKey,
        data: &PartialRecord,
    ) -> Result<(), StorageError>;
}

#[derive(Debug, Clone)]
pub struct PrimaryKey(Vec<u8>);

#[derive(Debug, Default)]
pub struct Record {
    pub primary_key: PrimaryKey,
    pub fields: HashMap<String, FieldValue>,
}

impl Record {
    pub fn new(pk: PrimaryKey) -> Self {
        Self {
            primary_key: pk,
            fields: HashMap::new(),
        }
    }

    pub fn merge(&mut self, partial: PartialRecord) {
        self.fields.extend(partial.fields);
    }
}

#[derive(Debug, Default)]
pub struct PartialRecord {
    pub fields: HashMap<String, FieldValue>,
}

#[derive(Debug, Clone)]
pub enum FieldValue {
    Int(i64),
    Float(f64),
    String(String),
    Bytes(Vec<u8>),
    Null,
}
```

**分片键选择：**

```rust
/// 分片键选择策略
///
/// 好的分片键应该：
/// 1. 高基数：避免热点
/// 2. 均匀分布：数据均衡
/// 3. 访问局部性：相关数据在同一分片
/// 4. 稳定性：不常变更

#[derive(Debug, Clone)]
pub struct ShardKeySelector {
    /// 候选键列表
    candidates: Vec<String>,

    /// 键的基数统计
    cardinality: HashMap<String, u64>,

    /// 访问模式分析
    access_patterns: AccessPatternAnalysis,
}

#[derive(Debug, Clone)]
pub struct AccessPatternAnalysis {
    /// 查询频率
    query_frequency: HashMap<String, u64>,

    /// 事务边界（经常一起访问的键）
    transaction_boundaries: Vec<Vec<String>>,

    /// 关联度矩阵
    correlation_matrix: HashMap<(String, String), f64>,
}

impl ShardKeySelector {
    /// 评估分片键质量
    pub fn evaluate(&self, key: &str) -> ShardKeyScore {
        let cardinality_score = self.score_cardinality(key);
        let distribution_score = self.score_distribution(key);
        let locality_score = self.score_locality(key);
        let stability_score = self.score_stability(key);

        ShardKeyScore {
            key: key.to_string(),
            cardinality: cardinality_score,
            distribution: distribution_score,
            locality: locality_score,
            stability: stability_score,
            overall: (cardinality_score + distribution_score + locality_score + stability_score) / 4.0,
        }
    }

    /// 基数评分（越高越好）
    fn score_cardinality(&self, key: &str) -> f64 {
        let cardinality = self.cardinality.get(key).copied().unwrap_or(0);
        let max_cardinality = self.cardinality.values().max().copied().unwrap_or(1);

        // 归一化到 0-1
        (cardinality as f64 / max_cardinality as f64).min(1.0)
    }

    /// 分布均匀性评分（越高越好）
    fn score_distribution(&self, key: &str) -> f64 {
        // 基于实际数据分布计算方差
        // 方差越小，分数越高
        1.0 // 简化实现
    }

    /// 访问局部性评分（越高越好）
    fn score_locality(&self, key: &str) -> f64 {
        // 检查事务边界内的相关性
        let mut score = 0.0;

        for boundary in &self.access_patterns.transaction_boundaries {
            if boundary.contains(&key.to_string()) {
                // 计算与边界内其他键的相关性
                for other in boundary {
                    if other != key {
                        let correlation = self.access_patterns.correlation_matrix
                            .get(&(key.to_string(), other.clone()))
                            .or_else(|| self.access_patterns.correlation_matrix
                                .get(&(other.clone(), key.to_string())))
                            .copied()
                            .unwrap_or(0.0);
                        score += correlation;
                    }
                }
            }
        }

        score.min(1.0)
    }

    /// 稳定性评分（越高越好）
    fn score_stability(&self, _key: &str) -> f64 {
        // 基于变更频率评估
        0.9 // 简化实现
    }

    /// 推荐最佳分片键
    pub fn recommend(&self) -> Option<ShardKeyScore> {
        self.candidates.iter()
            .map(|c| self.evaluate(c))
            .max_by(|a, b| a.overall.partial_cmp(&b.overall).unwrap())
    }
}

#[derive(Debug, Clone)]
pub struct ShardKeyScore {
    pub key: String,
    pub cardinality: f64,
    pub distribution: f64,
    pub locality: f64,
    pub stability: f64,
    pub overall: f64,
}
```

**分片再平衡：**

```rust
/// 分片再平衡管理器
///
/// 处理数据迁移，最小化对服务的影响

pub struct RebalanceManager {
    /// 分片分配策略
    allocator: Box<dyn ShardAllocator>,

    /// 当前分配
    current_allocation: ShardAllocation,

    /// 迁移状态
    migration_state: Arc<RwLock<MigrationState>>,
}

/// 分片分配器
#[async_trait]
pub trait ShardAllocator: Send + Sync {
    /// 计算最优分片分配
    async fn compute_allocation(
        &self,
        shards: &[Shard],
        nodes: &[Node],
        constraints: &AllocationConstraints,
    ) -> ShardAllocation;
}

#[derive(Debug, Clone)]
pub struct ShardAllocation {
    /// 分片 → 节点 映射
    pub shard_to_node: HashMap<ShardId, NodeId>,

    /// 节点负载统计
    pub node_loads: HashMap<NodeId, NodeLoad>,
}

#[derive(Debug, Clone)]
pub struct NodeLoad {
    pub shard_count: usize,
    pub data_size: u64,
    pub qps: u32,
}

#[derive(Debug, Clone)]
pub struct AllocationConstraints {
    /// 每节点最大分片数
    pub max_shards_per_node: usize,

    /// 每节点最大数据量
    pub max_data_per_node: u64,

    /// 副本距离（不同机架）
    pub replica_rack_aware: bool,
}

/// 迁移状态
#[derive(Debug, Clone)]
pub struct MigrationState {
    pub active_migrations: Vec<ShardMigration>,
    pub pending_migrations: Vec<ShardMigration>,
    pub completed_migrations: Vec<ShardMigration>,
}

#[derive(Debug, Clone)]
pub struct ShardMigration {
    pub migration_id: MigrationId,
    pub shard_id: ShardId,
    pub source_node: NodeId,
    pub target_node: NodeId,
    pub status: MigrationStatus,
    pub progress: f64,
    pub started_at: Instant,
    pub estimated_completion: Instant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MigrationStatus {
    Pending,
    InProgress,
    Verifying,
    Completing,
    Completed,
    Failed,
    RolledBack,
}

impl RebalanceManager {
    /// 触发再平衡
    pub async fn rebalance(&self) -> Result<RebalancePlan, RebalanceError> {
        // 1. 收集当前状态
        let current_state = self.collect_cluster_state().await?;

        // 2. 计算目标分配
        let target_allocation = self.allocator.compute_allocation(
            &current_state.shards,
            &current_state.nodes,
            &current_state.constraints,
        ).await;

        // 3. 计算差异，生成迁移计划
        let plan = self.generate_migration_plan(&self.current_allocation, &target_allocation);

        Ok(plan)
    }

    /// 生成迁移计划
    fn generate_migration_plan(
        &self,
        current: &ShardAllocation,
        target: &ShardAllocation,
    ) -> RebalancePlan {
        let mut migrations = Vec::new();

        for (shard_id, target_node) in &target.shard_to_node {
            let current_node = current.shard_to_node.get(shard_id);

            if current_node != Some(target_node) {
                // 需要迁移
                migrations.push(ShardMigration {
                    migration_id: MigrationId::new(),
                    shard_id: *shard_id,
                    source_node: current_node.cloned().unwrap_or_default(),
                    target_node: target_node.clone(),
                    status: MigrationStatus::Pending,
                    progress: 0.0,
                    started_at: Instant::now(),
                    estimated_completion: Instant::now() + Duration::from_secs(3600), // 估算
                });
            }
        }

        // 排序迁移优先级（考虑数据大小、QPS 等）
        migrations.sort_by(|a, b| {
            // 优先迁移小分片，影响最小
            let a_size = self.get_shard_size(&a.shard_id);
            let b_size = self.get_shard_size(&b.shard_id);
            a_size.cmp(&b_size)
        });

        RebalancePlan { migrations }
    }

    /// 执行迁移
    pub async fn execute_migration(&self, migration: &ShardMigration) -> Result<(), MigrationError> {
        let mut state = self.migration_state.write().await;

        // 更新状态为进行中
        let mut migration = migration.clone();
        migration.status = MigrationStatus::InProgress;
        migration.started_at = Instant::now();

        // 执行分片迁移
        self.migrate_shard(&migration).await?;

        // 验证数据一致性
        migration.status = MigrationStatus::Verifying;
        self.verify_migration(&migration).await?;

        // 切换流量
        migration.status = MigrationStatus::Completing;
        self.switch_traffic(&migration).await?;

        migration.status = MigrationStatus::Completed;
        state.completed_migrations.push(migration);

        Ok(())
    }

    async fn migrate_shard(&self, migration: &ShardMigration) -> Result<(), MigrationError> {
        // 实际数据迁移逻辑
        Ok(())
    }

    async fn verify_migration(&self, migration: &ShardMigration) -> Result<(), MigrationError> {
        // 校验和比较等验证逻辑
        Ok(())
    }

    async fn switch_traffic(&self, migration: &ShardMigration) -> Result<(), MigrationError> {
        // 路由切换逻辑
        Ok(())
    }

    fn get_shard_size(&self, _shard_id: &ShardId) -> u64 {
        // 获取分片大小
        0
    }

    async fn collect_cluster_state(&self) -> Result<ClusterState, RebalanceError> {
        Ok(ClusterState {
            shards: Vec::new(),
            nodes: Vec::new(),
            constraints: AllocationConstraints {
                max_shards_per_node: 10,
                max_data_per_node: 1024 * 1024 * 1024 * 100, // 100GB
                replica_rack_aware: true,
            },
        })
    }
}

#[derive(Debug, Clone)]
pub struct RebalancePlan {
    pub migrations: Vec<ShardMigration>,
}

#[derive(Debug, Clone)]
pub struct ClusterState {
    pub shards: Vec<Shard>,
    pub nodes: Vec<Node>,
    pub constraints: AllocationConstraints,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub id: NodeId,
    pub rack: String,
    pub capacity: NodeCapacity,
}

#[derive(Debug, Clone)]
pub struct NodeCapacity {
    pub disk_bytes: u64,
    pub memory_bytes: u64,
    pub max_qps: u32,
}

#[derive(Debug)]
pub enum RebalanceError {
    InsufficientCapacity,
    MigrationFailed(MigrationError),
}

#[derive(Debug)]
pub enum MigrationError {
    SourceUnavailable,
    TargetUnavailable,
    DataCorruption,
    Timeout,
}
```

### 6.2 复制模式

**主从复制语义：**

```rust
/// 主从复制语义模型
///
/// 一主多从架构：
/// - 主节点：处理写操作，复制到从节点
/// - 从节点：处理读操作，复制主节点数据

pub struct MasterSlaveReplication {
    /// 主节点
    master: Arc<dyn ReplicationNode>,

    /// 从节点列表
    slaves: Vec<Arc<dyn ReplicationNode>>,

    /// 复制配置
    config: ReplicationConfig,

    /// 复制状态
    replication_state: Arc<RwLock<ReplicationState>>,
}

#[derive(Debug, Clone)]
pub struct ReplicationConfig {
    /// 同步复制（需要 N 个从节点确认）
    pub sync_replicas: usize,

    /// 异步复制超时
    pub async_timeout: Duration,

    /// 复制缓冲区大小
    pub replication_buffer_size: usize,

    /// 从节点心跳间隔
    pub slave_heartbeat_interval: Duration,
}

/// 复制状态
#[derive(Debug, Clone)]
pub struct ReplicationState {
    /// 主节点复制偏移
    pub master_offset: u64,

    /// 各从节点的复制偏移
    pub slave_offsets: HashMap<NodeId, u64>,

    /// 各从节点的滞后时间
    pub slave_lags: HashMap<NodeId, Duration>,

    /// 复制连接状态
    pub connection_states: HashMap<NodeId, ConnectionState>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionState {
    Connected,
    Disconnected,
    Syncing,
    Error,
}

#[async_trait]
pub trait ReplicationNode: Send + Sync {
    async fn apply_command(&self, command: ReplicationCommand) -> Result<(), ReplicationError>;
    async fn get_offset(&self) -> u64;
    async fn sync(&self, from_offset: u64) -> Result<ReplicationStream, ReplicationError>;
}

#[derive(Debug, Clone)]
pub enum ReplicationCommand {
    Insert { key: Vec<u8>, value: Vec<u8> },
    Update { key: Vec<u8>, value: Vec<u8> },
    Delete { key: Vec<u8> },
    Transaction { commands: Vec<ReplicationCommand> },
}

pub struct ReplicationStream;

impl MasterSlaveReplication {
    /// 主节点处理写操作
    pub async fn write(&self, command: ReplicationCommand) -> WriteResult {
        // 1. 先应用到主节点
        self.master.apply_command(command.clone()).await
            .map_err(|e| WriteResult::MasterError(e.to_string()))?;

        // 2. 更新主节点偏移
        let mut state = self.replication_state.write().await;
        state.master_offset += self.command_size(&command);
        let current_offset = state.master_offset;
        drop(state);

        // 3. 复制到从节点
        if self.config.sync_replicas > 0 {
            // 同步复制
            self.replicate_sync(command, current_offset).await?;
        } else {
            // 异步复制
            self.replicate_async(command);
        }

        Ok(WriteResult::Success)
    }

    /// 同步复制
    async fn replicate_sync(
        &self,
        command: ReplicationCommand,
        offset: u64,
    ) -> Result<(), WriteResult> {
        let slaves = self.slaves.clone();
        let acks_needed = self.config.sync_replicas.min(slaves.len());

        let mut ack_futures = Vec::new();

        for slave in &slaves {
            let cmd = command.clone();
            let slave = slave.clone();

            ack_futures.push(async move {
                tokio::time::timeout(
                    self.config.async_timeout,
                    slave.apply_command(cmd)
                ).await
            });
        }

        // 等待足够的确认
        let results = futures::future::join_all(ack_futures).await;
        let acks = results.iter().filter(|r| r.is_ok()).count();

        if acks >= acks_needed {
            Ok(())
        } else {
            Err(WriteResult::InsufficientReplicas {
                required: acks_needed,
                received: acks,
            })
        }
    }

    /// 异步复制
    fn replicate_async(&self, command: ReplicationCommand) {
        let slaves = self.slaves.clone();

        tokio::spawn(async move {
            for slave in slaves {
                let cmd = command.clone();
                if let Err(e) = slave.apply_command(cmd).await {
                    tracing::error!("Replication to slave failed: {:?}", e);
                }
            }
        });
    }

    /// 读操作（可以路由到从节点）
    pub async fn read(&self, consistency: ReadConsistency) -> ReadResult {
        match consistency {
            ReadConsistency::Strong => {
                // 强一致性：从主节点读
                self.read_from_master().await
            }
            ReadConsistency::Eventual => {
                // 最终一致性：从任意从节点读
                self.read_from_slave().await
            }
            ReadConsistency::BoundedStaleness(max_lag) => {
                // 有界陈旧性：找滞后小于阈值的从节点
                self.read_from_lagging_slave(max_lag).await
            }
        }
    }

    async fn read_from_master(&self) -> ReadResult {
        // 实际实现
        ReadResult::Success
    }

    async fn read_from_slave(&self) -> ReadResult {
        // 负载均衡选择从节点
        ReadResult::Success
    }

    async fn read_from_lagging_slave(&self, max_lag: Duration) -> ReadResult {
        let state = self.replication_state.read().await;

        // 找到滞后小于阈值的从节点
        for (node_id, lag) in &state.slave_lags {
            if *lag <= max_lag {
                // 使用这个从节点
                return ReadResult::Success;
            }
        }

        // 没有合适的从节点，回退到主节点
        self.read_from_master().await
    }

    fn command_size(&self, _command: &ReplicationCommand) -> u64 {
        // 计算命令大小
        1
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ReadConsistency {
    Strong,              // 强一致性
    Eventual,           // 最终一致性
    BoundedStaleness(Duration), // 有界陈旧性
}

#[derive(Debug)]
pub enum WriteResult {
    Success,
    MasterError(String),
    InsufficientReplicas { required: usize, received: usize },
}

#[derive(Debug)]
pub enum ReadResult {
    Success,
    SlaveNotAvailable,
    StaleRead { actual_lag: Duration },
}
```

**多主复制语义：**

```rust
/// 多主复制语义
///
/// 多个节点都可以处理写操作，需要冲突解决

pub struct MultiMasterReplication {
    /// 节点 ID
    node_id: NodeId,

    /// 所有主节点
    masters: Vec<NodeId>,

    /// 冲突解决策略
    conflict_resolver: Box<dyn ConflictResolver>,

    /// 向量时钟
    vector_clock: VectorClock,
}

#[async_trait]
pub trait ConflictResolver: Send + Sync {
    /// 解决冲突
    fn resolve(&self, conflicts: Vec<VersionedValue<Vec<u8>>>) -> ResolutionResult;
}

/// 冲突解决策略
pub struct LastWriteWinsResolver;

impl ConflictResolver for LastWriteWinsResolver {
    fn resolve(&self, mut conflicts: Vec<VersionedValue<Vec<u8>>>) -> ResolutionResult {
        // 选择时间戳最大的
        conflicts.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));
        ResolutionResult::Resolved(conflicts.into_iter().next().unwrap().value)
    }
}

pub struct VectorClockResolver;

impl ConflictResolver for VectorClockResolver {
    fn resolve(&self, conflicts: Vec<VersionedValue<Vec<u8>>>) -> ResolutionResult {
        // 使用向量时钟找到没有因果关系的版本
        let mut concurrent = Vec::new();

        for v1 in &conflicts {
            let mut is_dominated = false;
            for v2 in &conflicts {
                if v1.vector_clock.happens_before(&v2.vector_clock) {
                    is_dominated = true;
                    break;
                }
            }
            if !is_dominated {
                concurrent.push(v1.clone());
            }
        }

        if concurrent.len() == 1 {
            ResolutionResult::Resolved(concurrent[0].value.clone())
        } else {
            // 需要应用层解决
            ResolutionResult::NeedsApplicationResolution(
                concurrent.into_iter().map(|v| v.value).collect()
            )
        }
    }
}

#[derive(Debug)]
pub enum ResolutionResult {
    Resolved(Vec<u8>),
    NeedsApplicationResolution(Vec<Vec<u8>>),
}

impl MultiMasterReplication {
    /// 本地写操作
    pub async fn write(&mut self, key: &[u8], value: Vec<u8>) -> WriteResult {
        // 递增向量时钟
        self.vector_clock.increment(&self.node_id);

        let versioned = VersionedValue {
            value,
            vector_clock: self.vector_clock.clone(),
            node_id: self.node_id.clone(),
            timestamp: current_timestamp(),
        };

        // 存储本地
        self.store_local(key, &versioned).await?;

        // 异步复制到其他主节点
        self.replicate_to_peers(key, &versioned).await;

        Ok(WriteResult::Success)
    }

    /// 接收远程写操作
    pub async fn receive_replication(
        &mut self,
        key: &[u8],
        remote: VersionedValue<Vec<u8>>,
    ) -> Result<(), ReplicationError> {
        // 合并向量时钟
        self.vector_clock.merge(&remote.vector_clock);

        // 检查本地版本
        let local = self.load_local(key).await?;

        match local {
            Some(local_version) => {
                // 比较版本
                match local_version.vector_clock.compare(&remote.vector_clock) {
                    Some(Ordering::Less) => {
                        // 远程版本更新，替换
                        self.store_local(key, &remote).await?;
                    }
                    Some(Ordering::Greater) => {
                        // 本地版本更新，忽略
                    }
                    Some(Ordering::Equal) => {
                        // 相同版本，可能重复
                    }
                    None => {
                        // 并发冲突，需要解决
                        let conflicts = vec![local_version, remote];
                        let resolution = self.conflict_resolver.resolve(conflicts);

                        match resolution {
                            ResolutionResult::Resolved(value) => {
                                let resolved = VersionedValue {
                                    value,
                                    vector_clock: self.vector_clock.clone(),
                                    node_id: self.node_id.clone(),
                                    timestamp: current_timestamp(),
                                };
                                self.store_local(key, &resolved).await?;
                            }
                            ResolutionResult::NeedsApplicationResolution(values) => {
                                // 记录冲突供应用层解决
                                self.record_conflict(key, values).await?;
                            }
                        }
                    }
                }
            }
            None => {
                // 本地无此 key，直接存储
                self.store_local(key, &remote).await?;
            }
        }

        Ok(())
    }

    async fn store_local(&self, _key: &[u8], _value: &VersionedValue<Vec<u8>>) -> Result<(), ReplicationError> {
        Ok(())
    }

    async fn load_local(&self, _key: &[u8]) -> Result<Option<VersionedValue<Vec<u8>>>, ReplicationError> {
        Ok(None)
    }

    async fn replicate_to_peers(&self, _key: &[u8], _value: &VersionedValue<Vec<u8>>) {
    }

    async fn record_conflict(&self, _key: &[u8], _values: Vec<Vec<u8>>) -> Result<(), ReplicationError> {
        Ok(())
    }
}
```

**读写分离语义：**

```rust
/// 读写分离路由
///
/// 自动根据操作类型和一致性要求路由到合适的节点

pub struct ReadWriteRouter {
    master: NodeId,
    slaves: Vec<SlaveInfo>,
    slave_selector: Box<dyn SlaveSelector>,
}

pub struct SlaveInfo {
    node_id: NodeId,
    lag: Duration,
    load: f64,
    health: HealthStatus,
}

#[async_trait]
pub trait SlaveSelector: Send + Sync {
    async fn select(&self, slaves: &[SlaveInfo], requirements: &ReadRequirements) -> Option<NodeId>;
}

#[derive(Debug, Clone)]
pub struct ReadRequirements {
    pub max_staleness: Option<Duration>,
    pub prefer_low_latency: bool,
    pub locality_hint: Option<String>,
}

pub struct AdaptiveSlaveSelector;

#[async_trait]
impl SlaveSelector for AdaptiveSlaveSelector {
    async fn select(&self, slaves: &[SlaveInfo], requirements: &ReadRequirements) -> Option<NodeId> {
        // 过滤满足条件的从节点
        let candidates: Vec<_> = slaves.iter()
            .filter(|s| s.health == HealthStatus::Healthy)
            .filter(|s| {
                requirements.max_staleness
                    .map(|max| s.lag <= max)
                    .unwrap_or(true)
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        // 按负载和延迟排序
        let selected = candidates.iter()
            .min_by(|a, b| {
                // 综合评分：负载权重 0.7，延迟权重 0.3
                let score_a = a.load * 0.7 + a.lag.as_millis() as f64 * 0.3;
                let score_b = b.load * 0.7 + b.lag.as_millis() as f64 * 0.3;
                score_a.partial_cmp(&score_b).unwrap()
            })
            .map(|s| s.node_id.clone());

        selected
    }
}

impl ReadWriteRouter {
    /// 路由写操作
    pub fn route_write(&self) -> NodeId {
        // 所有写操作都路由到主节点
        self.master.clone()
    }

    /// 路由读操作
    pub async fn route_read(&self, requirements: &ReadRequirements) -> ReadRoute {
        // 检查是否可以使用从节点
        if let Some(slave) = self.slave_selector.select(&self.slaves, requirements).await {
            ReadRoute::Slave(slave)
        } else {
            // 回退到主节点
            ReadRoute::Master(self.master.clone())
        }
    }
}

#[derive(Debug, Clone)]
pub enum ReadRoute {
    Master(NodeId),
    Slave(NodeId),
}
```

**复制延迟语义：**

```rust
/// 复制延迟监控与管理

pub struct ReplicationLagMonitor {
    /// 各从节点的复制延迟
    lag_stats: Arc<RwLock<HashMap<NodeId, LagStats>>>,

    /// 告警阈值
    alert_threshold: Duration,
}

#[derive(Debug, Clone)]
pub struct LagStats {
    /// 当前延迟
    pub current_lag: Duration,

    /// 历史延迟（用于趋势分析）
    pub history: VecDeque<(Instant, Duration)>,

    /// 平均延迟
    pub average_lag: Duration,

    /// 最大延迟
    pub max_lag: Duration,

    /// 延迟趋势
    pub trend: LagTrend,
}

#[derive(Debug, Clone, Copy)]
pub enum LagTrend {
    Improving,   // 延迟在改善
    Stable,      // 延迟稳定
    Degrading,   // 延迟在恶化
    Critical,    // 延迟超过阈值
}

impl ReplicationLagMonitor {
    /// 更新延迟统计
    pub async fn update_lag(&self, node_id: NodeId, lag: Duration) {
        let mut stats = self.lag_stats.write().await;
        let entry = stats.entry(node_id.clone()).or_insert_with(|| LagStats {
            current_lag: lag,
            history: VecDeque::with_capacity(100),
            average_lag: lag,
            max_lag: lag,
            trend: LagTrend::Stable,
        });

        // 更新当前延迟
        entry.current_lag = lag;

        // 添加到历史
        entry.history.push_back((Instant::now(), lag));
        if entry.history.len() > 100 {
            entry.history.pop_front();
        }

        // 重新计算统计
        if !entry.history.is_empty() {
            let total: u64 = entry.history.iter().map(|(_, l)| l.as_millis() as u64).sum();
            entry.average_lag = Duration::from_millis(total / entry.history.len() as u64);
            entry.max_lag = entry.history.iter().map(|(_, l)| *l).max().unwrap_or(lag);
        }

        // 计算趋势
        entry.trend = self.calculate_trend(entry);

        // 检查是否需要告警
        if lag > self.alert_threshold {
            self.alert_high_lag(&node_id, lag).await;
        }
    }

    fn calculate_trend(&self, stats: &LagStats) -> LagTrend {
        if stats.current_lag > self.alert_threshold {
            return LagTrend::Critical;
        }

        if stats.history.len() < 10 {
            return LagTrend::Stable;
        }

        // 简单线性回归判断趋势
        let recent: Vec<_> = stats.history.iter().rev().take(10).collect();
        let first_half: u64 = recent.iter().skip(5).map(|(_, l)| l.as_millis() as u64).sum();
        let second_half: u64 = recent.iter().take(5).map(|(_, l)| l.as_millis() as u64).sum();

        if first_half > second_half * 12 / 10 {
            LagTrend::Degrading
        } else if first_half < second_half * 8 / 10 {
            LagTrend::Improving
        } else {
            LagTrend::Stable
        }
    }

    async fn alert_high_lag(&self, node_id: &NodeId, lag: Duration) {
        tracing::error!(
            "High replication lag detected: node={}, lag={:?}",
            node_id, lag
        );
        // 发送告警通知
    }

    /// 获取最佳从节点（延迟最小）
    pub async fn get_best_slave(&self) -> Option<NodeId> {
        let stats = self.lag_stats.read().await;

        stats.iter()
            .filter(|(_, s)| s.trend != LagTrend::Critical)
            .min_by_key(|(_, s)| s.current_lag)
            .map(|(id, _)| id.clone())
    }
}
```

---

## 7. 缓存模式

### 7.1 本地缓存

**LRU 语义：**

```rust
/// LRU (Least Recently Used) 缓存
///
/// 语义：当缓存满时，淘汰最久未使用的条目

use std::collections::HashMap;
use std::collections::VecDeque;

pub struct LruCache<K, V> {
    /// 容量
    capacity: usize,

    /// 存储
    cache: HashMap<K, V>,

    /// 访问顺序队列（最久未使用在队头）
    lru_queue: VecDeque<K>,
}

impl<K: Eq + std::hash::Hash + Clone, V> LruCache<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            cache: HashMap::with_capacity(capacity),
            lru_queue: VecDeque::with_capacity(capacity),
        }
    }

    /// 获取值并更新访问顺序
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.cache.contains_key(key) {
            // 更新访问顺序
            self.update_access_order(key);
            self.cache.get(key)
        } else {
            None
        }
    }

    /// 插入值
    pub fn put(&mut self, key: K, value: V) -> Option<V> {
        // 如果 key 已存在，更新值和顺序
        if self.cache.contains_key(&key) {
            self.update_access_order(&key);
            return self.cache.insert(key, value);
        }

        // 检查是否需要淘汰
        if self.cache.len() >= self.capacity {
            self.evict_lru();
        }

        // 插入新值
        self.lru_queue.push_back(key.clone());
        self.cache.insert(key, value)
    }

    /// 更新访问顺序
    fn update_access_order(&mut self, key: &K) {
        // 从当前位置移除
        if let Some(pos) = self.lru_queue.iter().position(|k| k == key) {
            self.lru_queue.remove(pos);
        }
        // 添加到队尾（最近使用）
        self.lru_queue.push_back(key.clone());
    }

    /// 淘汰最久未使用的条目
    fn evict_lru(&mut self) -> Option<(K, V)> {
        if let Some(key) = self.lru_queue.pop_front() {
            self.cache.remove(&key).map(|v| (key, v))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.cache.len()
    }

    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

/// 更高效的 LRU 实现（使用双向链表 + HashMap）
pub struct EfficientLruCache<K, V> {
    capacity: usize,
    cache: HashMap<K, NodeRef<V>>,
    lru_list: LinkedList<K, V>,
}

struct NodeRef<V>(Rc<RefCell<Node<V>>>);

struct Node<V> {
    value: V,
    prev: Option<Weak<RefCell<Node<V>>>>,
    next: Option<Rc<RefCell<Node<V>>>>,
}

struct LinkedList<K, V> {
    head: Option<Rc<RefCell<Node<V>>>>,
    tail: Option<Rc<RefCell<Node<V>>>>,
    _phantom: std::marker::PhantomData<K>,
}
```

**LFU 语义：**

```rust
/// LFU (Least Frequently Used) 缓存
///
/// 语义：当缓存满时，淘汰访问频率最低的条目

pub struct LfuCache<K, V> {
    capacity: usize,
    min_frequency: u64,

    /// key → (value, frequency, 在 freq_map 中的位置)
    cache: HashMap<K, (V, u64)>,

    /// frequency → 该频率的所有 key 列表
    freq_map: HashMap<u64, VecDeque<K>>,

    /// 访问计数统计
    stats: CacheStats,
}

#[derive(Debug, Default)]
pub struct CacheStats {
    hits: u64,
    misses: u64,
    evictions: u64,
}

impl<K: Eq + std::hash::Hash + Clone, V> LfuCache<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            min_frequency: 1,
            cache: HashMap::new(),
            freq_map: HashMap::new(),
            stats: CacheStats::default(),
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some((value, freq)) = self.cache.get_mut(key) {
            // 增加访问频率
            self.increase_frequency(key.clone(), *freq);
            *freq += 1;
            self.stats.hits += 1;
            Some(value)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }

        // 如果 key 已存在，更新值
        if self.cache.contains_key(&key) {
            let freq = self.cache.get(&key).unwrap().1;
            self.increase_frequency(key.clone(), freq);
            self.cache.insert(key, (value, freq + 1));
            return;
        }

        // 如果缓存已满，淘汰 LFU 条目
        if self.cache.len() >= self.capacity {
            self.evict_lfu();
        }

        // 插入新条目，频率为 1
        self.cache.insert(key.clone(), (value, 1));
        self.freq_map.entry(1).or_default().push_back(key);
        self.min_frequency = 1;
    }

    fn increase_frequency(&mut self, key: K, old_freq: u64) {
        // 从旧频率列表中移除
        if let Some(keys) = self.freq_map.get_mut(&old_freq) {
            if let Some(pos) = keys.iter().position(|k| k == &key) {
                keys.remove(pos);
            }

            // 如果旧频率列表为空且等于 min_frequency，更新 min_frequency
            if keys.is_empty() && old_freq == self.min_frequency {
                self.min_frequency += 1;
            }
        }

        // 添加到新频率列表
        self.freq_map.entry(old_freq + 1).or_default().push_back(key);
    }

    fn evict_lfu(&mut self) -> Option<(K, V)> {
        // 找到最小频率的条目
        let keys = self.freq_map.get_mut(&self.min_frequency)?;
        let key_to_evict = keys.pop_front()?;

        if keys.is_empty() {
            self.freq_map.remove(&self.min_frequency);
        }

        let (value, _) = self.cache.remove(&key_to_evict)?;
        self.stats.evictions += 1;

        Some((key_to_evict, value))
    }

    pub fn hit_rate(&self) -> f64 {
        let total = self.stats.hits + self.stats.misses;
        if total == 0 {
            0.0
        } else {
            self.stats.hits as f64 / total as f64
        }
    }
}

/// W-TinyLFU：更现代的 LFU 实现
/// 结合 LRU 和 LFU 的优点，使用 Count-Min Sketch 估计频率
pub struct WTinyLfuCache<K, V> {
    capacity: usize,

    /// 窗口缓存（LRU，占 1%）
    window_cache: LruCache<K, V>,

    /// 主缓存（SLRU）
    main_cache: SlruCache<K, V>,

    /// 频率过滤器
    sketch: CountMinSketch,
}

/// Count-Min Sketch 用于频率估计
pub struct CountMinSketch {
    width: usize,
    depth: usize,
    counts: Vec<Vec<u32>>,
    hashes: Vec<Box<dyn Fn(&[u8]) -> u64>>,
}

impl CountMinSketch {
    pub fn new(width: usize, depth: usize) -> Self {
        let counts = vec![vec![0u32; width]; depth];

        // 创建不同的哈希函数
        let hashes: Vec<_> = (0..depth)
            .map(|i| {
                Box::new(move |bytes: &[u8]| {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    bytes.hash(&mut hasher);
                    i.hash(&mut hasher);
                    hasher.finish()
                }) as Box<dyn Fn(&[u8]) -> u64>
            })
            .collect();

        Self { width, depth, counts, hashes }
    }

    pub fn increment(&mut self, key: &[u8]) {
        for (i, hash_fn) in self.hashes.iter().enumerate() {
            let idx = (hash_fn(key) as usize) % self.width;
            self.counts[i][idx] = self.counts[i][idx].saturating_add(1);
        }
    }

    pub fn estimate(&self, key: &[u8]) -> u32 {
        self.hashes.iter()
            .enumerate()
            .map(|(i, hash_fn)| {
                let idx = (hash_fn(key) as usize) % self.width;
                self.counts[i][idx]
            })
            .min()
            .unwrap_or(0)
    }
}

/// Segmented LRU（用于 W-TinyLFU 的主缓存）
pub struct SlruCache<K, V> {
    protected: LruCache<K, V>,
    probationary: LruCache<K, V>,
}
```

**TTL 语义：**

```rust
/// TTL (Time To Live) 缓存
///
/// 条目在指定时间后过期

pub struct TtlCache<K, V> {
    cache: HashMap<K, TtlEntry<V>>,
    default_ttl: Duration,

    /// 过期检查间隔
    expiration_check_interval: Duration,
}

struct TtlEntry<V> {
    value: V,
    expires_at: Instant,
}

impl<K: Eq + std::hash::Hash, V> TtlCache<K, V> {
    pub fn new(default_ttl: Duration) -> Self {
        let cache = Self {
            cache: HashMap::new(),
            default_ttl,
            expiration_check_interval: Duration::from_secs(60),
        };

        // 启动过期清理任务
        cache.start_expiration_task();

        cache
    }

    fn start_expiration_task(&self) {
        let interval = self.expiration_check_interval;
        // 实际实现需要 Arc<Self> 和弱引用
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.cache.get(key).and_then(|entry| {
            if entry.expires_at > Instant::now() {
                Some(&entry.value)
            } else {
                None
            }
        })
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.insert_with_ttl(key, value, self.default_ttl);
    }

    pub fn insert_with_ttl(&mut self, key: K, value: V, ttl: Duration) {
        let entry = TtlEntry {
            value,
            expires_at: Instant::now() + ttl,
        };
        self.cache.insert(key, entry);
    }

    /// 主动清理过期条目
    pub fn remove_expired(&mut self) -> usize {
        let now = Instant::now();
        let expired: Vec<_> = self.cache.iter()
            .filter(|(_, entry)| entry.expires_at <= now)
            .map(|(k, _)| k.clone())
            .collect();

        let count = expired.len();
        for key in expired {
            self.cache.remove(&key);
        }

        count
    }

    /// 惰性过期检查
    pub fn get_with_cleanup(&mut self, key: &K) -> Option<&V> {
        let now = Instant::now();

        match self.cache.get(key) {
            Some(entry) if entry.expires_at > now => Some(&entry.value),
            Some(_) => {
                // 已过期，删除
                self.cache.remove(key);
                None
            }
            None => None,
        }
    }
}

/// 分层 TTL（不同条目类型不同 TTL）
pub struct TieredTtlCache<K, V> {
    cache: HashMap<K, TieredEntry<V>>,
}

struct TieredEntry<V> {
    value: V,
    tier: TtlTier,
    expires_at: Instant,
}

#[derive(Debug, Clone, Copy)]
pub enum TtlTier {
    Hot,     // 热点数据，长 TTL
    Warm,    // 温数据，中等 TTL
    Cold,    // 冷数据，短 TTL
}

impl TtlTier {
    pub fn ttl(&self) -> Duration {
        match self {
            TtlTier::Hot => Duration::from_secs(3600),    // 1小时
            TtlTier::Warm => Duration::from_secs(300),     // 5分钟
            TtlTier::Cold => Duration::from_secs(60),      // 1分钟
        }
    }
}
```

**缓存一致性：**

```rust
/// 缓存一致性模式

/// Cache-Aside 模式
///
/// 应用负责维护缓存一致性
pub struct CacheAside<K, V> {
    cache: Box<dyn Cache<K, V>>,
    store: Box<dyn Store<K, V>>,
}

impl<K: Clone + Eq + std::hash::Hash, V: Clone> CacheAside<K, V> {
    /// 读操作
    pub async fn get(&mut self, key: &K) -> Result<Option<V>, CacheError> {
        // 1. 先查缓存
        if let Some(value) = self.cache.get(key).await? {
            return Ok(Some(value));
        }

        // 2. 缓存未命中，查存储
        let value = self.store.get(key).await?;

        // 3. 回填缓存
        if let Some(ref v) = value {
            self.cache.put(key.clone(), v.clone()).await?;
        }

        Ok(value)
    }

    /// 写操作
    pub async fn put(&mut self, key: K, value: V) -> Result<(), CacheError> {
        // 1. 更新存储
        self.store.put(&key, &value).await?;

        // 2. 失效或更新缓存
        self.cache.invalidate(&key).await?;
        // 或者 self.cache.put(key, value).await?;

        Ok(())
    }

    /// 删除操作
    pub async fn delete(&mut self, key: &K) -> Result<(), CacheError> {
        // 1. 删除存储
        self.store.delete(key).await?;

        // 2. 删除缓存
        self.cache.invalidate(key).await?;

        Ok(())
    }
}

/// Read-Through 模式
///
/// 缓存自动从存储加载
pub struct ReadThroughCache<K, V> {
    cache: Box<dyn LoadingCache<K, V>>,
}

#[async_trait]
pub trait LoadingCache<K, V>: Send + Sync {
    async fn get(&self, key: &K) -> Result<Option<V>, CacheError>;
}

/// Write-Through 模式
///
/// 写操作同时更新缓存和存储
pub struct WriteThroughCache<K, V> {
    cache: Box<dyn Cache<K, V>>,
    store: Box<dyn Store<K, V>>,
}

#[async_trait]
pub trait Cache<K, V>: Send + Sync {
    async fn get(&self, key: &K) -> Result<Option<V>, CacheError>;
    async fn put(&mut self, key: K, value: V) -> Result<(), CacheError>;
    async fn invalidate(&mut self, key: &K) -> Result<(), CacheError>;
}

#[async_trait]
pub trait Store<K, V>: Send + Sync {
    async fn get(&self, key: &K) -> Result<Option<V>, StoreError>;
    async fn put(&self, key: &K, value: &V) -> Result<(), StoreError>;
    async fn delete(&self, key: &K) -> Result<(), StoreError>;
}
```

### 7.2 分布式缓存

**缓存穿透防护：**

```rust
/// 缓存穿透：查询不存在的数据，导致每次都打到存储层
/// 解决方案：布隆过滤器 + 空值缓存

pub struct CachePenetrationGuard<K, V> {
    /// 主缓存
    cache: Box<dyn Cache<K, V>>,

    /// 布隆过滤器
    bloom_filter: BloomFilter,

    /// 空值缓存 TTL
    null_value_ttl: Duration,
}

/// 布隆过滤器
pub struct BloomFilter {
    bits: Vec<bool>,
    hash_functions: Vec<Box<dyn Fn(&[u8]) -> usize>>,
}

impl BloomFilter {
    pub fn new(expected_items: usize, false_positive_rate: f64) -> Self {
        // 计算最优参数
        let bit_array_size = Self::optimal_m(expected_items, false_positive_rate);
        let num_hashes = Self::optimal_k(expected_items, bit_array_size);

        let bits = vec![false; bit_array_size];

        let hash_functions: Vec<_> = (0..num_hashes)
            .map(|i| {
                Box::new(move |bytes: &[u8]| {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    bytes.hash(&mut hasher);
                    i.hash(&mut hasher);
                    (hasher.finish() as usize) % bit_array_size
                }) as Box<dyn Fn(&[u8]) -> usize>
            })
            .collect();

        Self { bits, hash_functions }
    }

    /// 添加元素
    pub fn add(&mut self, item: &[u8]) {
        for hash_fn in &self.hash_functions {
            let idx = hash_fn(item);
            self.bits[idx] = true;
        }
    }

    /// 检查可能存在（可能有假阳性）
    pub fn may_contain(&self, item: &[u8]) -> bool {
        self.hash_functions.iter()
            .all(|hash_fn| self.bits[hash_fn(item)])
    }

    fn optimal_m(n: usize, p: f64) -> usize {
        (-(n as f64) * p.ln() / (2.0f64.ln().powi(2))).ceil() as usize
    }

    fn optimal_k(n: usize, m: usize) -> usize {
        ((m as f64 / n as f64) * 2.0f64.ln()).ceil() as usize
    }
}

impl<K: AsRef<[u8]> + Clone, V: Clone> CachePenetrationGuard<K, V> {
    pub async fn get(&mut self, key: &K) -> Result<Option<V>, CacheError> {
        // 1. 先查布隆过滤器
        if !self.bloom_filter.may_contain(key.as_ref()) {
            // 肯定不存在
            return Ok(None);
        }

        // 2. 查缓存
        match self.cache.get(key).await? {
            Some(value) => Ok(Some(value)),
            None => {
                // 3. 缓存未命中，查存储
                // 实际实现...
                Ok(None)
            }
        }
    }
}

/// 空值缓存（Cache Null）
pub struct NullValueCache<K> {
    /// 缓存空值的 key
    null_keys: HashMap<K, Instant>,
    ttl: Duration,
}

impl<K: Eq + std::hash::Hash> NullValueCache<K> {
    pub fn cache_null(&mut self, key: K) {
        self.null_keys.insert(key, Instant::now() + self.ttl);
    }

    pub fn is_null_cached(&self, key: &K) -> bool {
        self.null_keys.get(key)
            .map(|expires| *expires > Instant::now())
            .unwrap_or(false)
    }
}
```

**缓存雪崩防护：**

```rust
/// 缓存雪崩：大量缓存同时过期，导致请求打到存储层
/// 解决方案：随机过期时间 + 互斥锁 + 提前刷新

pub struct CacheAvalancheGuard<K, V> {
    cache: Box<dyn Cache<K, V>>,
    store: Box<dyn Store<K, V>>,

    /// 刷新互斥锁（防止缓存击穿）
    refresh_locks: Arc<RwLock<HashMap<K, Arc<tokio::sync::Mutex<()>>>>>,

    /// 随机过期时间范围
    jitter_range: Duration,

    /// 提前刷新阈值（过期前多久开始刷新）
    pre_refresh_threshold: Duration,
}

impl<K: Clone + Eq + std::hash::Hash, V: Clone> CacheAvalancheGuard<K, V> {
    /// 获取值（带防护）
    pub async fn get(&self, key: &K) -> Result<Option<V>, CacheError> {
        // 1. 查缓存
        if let Some(cached) = self.cache.get(key).await? {
            // 2. 检查是否需要提前刷新
            if self.should_pre_refresh(key).await {
                // 异步刷新，不阻塞当前请求
                let key = key.clone();
                let self_ref = self.clone();
                tokio::spawn(async move {
                    let _ = self_ref.refresh(&key).await;
                });
            }

            return Ok(Some(cached));
        }

        // 3. 缓存未命中，获取刷新锁
        self.refresh(key).await
    }

    /// 刷新缓存（互斥）
    async fn refresh(&self, key: &K) -> Result<Option<V>, CacheError> {
        // 获取或创建锁
        let lock = {
            let mut locks = self.refresh_locks.write().await;
            locks.entry(key.clone())
                .or_insert_with(|| Arc::new(tokio::sync::Mutex::new(())))
                .clone()
        };

        // 尝试获取锁
        let _guard = match lock.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                // 其他线程正在刷新，等待后重试
                let guard = lock.lock().await;
                drop(guard);
                return self.cache.get(key).await;
            }
        };

        // 双重检查
        if let Some(cached) = self.cache.get(key).await? {
            return Ok(Some(cached));
        }

        // 从存储加载
        let value = self.store.get(key).await
            .map_err(|e| CacheError::StoreError(e.to_string()))?;

        // 回填缓存（带随机过期时间）
        if let Some(ref v) = value {
            let ttl = self.calculate_ttl_with_jitter();
            self.cache_with_ttl(key.clone(), v.clone(), ttl).await?;
        }

        Ok(value)
    }

    /// 计算带抖动的 TTL
    fn calculate_ttl_with_jitter(&self) -> Duration {
        let base_ttl = Duration::from_secs(3600); // 1小时
        let jitter = Duration::from_millis(
            rand::random::<u64>() % self.jitter_range.as_millis() as u64
        );
        base_ttl + jitter
    }

    async fn should_pre_refresh(&self, _key: &K) -> bool {
        // 检查缓存条目的剩余 TTL
        false // 简化实现
    }

    async fn cache_with_ttl(&self, _key: K, _value: V, _ttl: Duration) -> Result<(), CacheError> {
        Ok(())
    }
}

impl<K, V> Clone for CacheAvalancheGuard<K, V> {
    fn clone(&self) -> Self {
        Self {
            cache: self.cache.clone(),
            store: self.store.clone(),
            refresh_locks: self.refresh_locks.clone(),
            jitter_range: self.jitter_range,
            pre_refresh_threshold: self.pre_refresh_threshold,
        }
    }
}
```

**缓存击穿防护：**

```rust
/// 缓存击穿：热点 key 过期瞬间，大量请求打到存储层
/// 解决方案：互斥锁 + 逻辑过期

pub struct CacheHotKeyProtection<K, V> {
    cache: Box<dyn Cache<K, V>>,
    store: Box<dyn Store<K, V>>,

    /// 热点 key 检测
    hot_key_detector: HotKeyDetector<K>,

    /// 互斥锁
    locks: Arc<RwLock<HashMap<K, Arc<tokio::sync::Semaphore>>>>,
}

/// 热点 key 检测
pub struct HotKeyDetector<K> {
    /// 访问计数滑动窗口
    access_counts: Arc<RwLock<HashMap<K, SlidingWindowCounter>>>,

    /// 热点阈值
    hot_threshold: u32,
}

impl<K: Clone + Eq + std::hash::Hash, V: Clone> CacheHotKeyProtection<K, V> {
    /// 逻辑过期：不真正删除数据，而是标记为过期，后台刷新
    pub async fn get_with_logical_expiry(&self, key: &K) -> Result<Option<V>, CacheError> {
        let entry = self.cache.get_with_metadata(key).await?;

        match entry {
            Some(CacheEntry { value, expires_at, .. }) => {
                if expires_at > Instant::now() {
                    // 未过期，直接返回
                    Ok(Some(value))
                } else {
                    // 逻辑过期，返回旧值并触发后台刷新
                    if self.try_acquire_refresh_lock(key).await {
                        let key = key.clone();
                        let self_ref = self.clone();
                        tokio::spawn(async move {
                            let _ = self_ref.refresh(&key).await;
                        });
                    }

                    Ok(Some(value)) // 返回旧值
                }
            }
            None => {
                // 真正未命中，需要加载
                self.refresh(key).await
            }
        }
    }

    /// 获取刷新锁
    async fn try_acquire_refresh_lock(&self, key: &K) -> bool {
        let locks = self.locks.read().await;
        if let Some(semaphore) = locks.get(key) {
            semaphore.try_acquire().is_ok()
        } else {
            drop(locks);
            let mut locks = self.locks.write().await;
            let semaphore = locks.entry(key.clone())
                .or_insert_with(|| Arc::new(tokio::sync::Semaphore::new(1)));
            semaphore.clone().try_acquire().is_ok()
        }
    }

    async fn refresh(&self, key: &K) -> Result<Option<V>, CacheError> {
        // 从存储加载并更新缓存
        let value = self.store.get(key).await
            .map_err(|e| CacheError::StoreError(e.to_string()))?;

        if let Some(ref v) = value {
            self.cache.put(key.clone(), v.clone()).await?;
        }

        Ok(value)
    }
}

struct CacheEntry<V> {
    value: V,
    expires_at: Instant,
}
```

**缓存预热：**

```rust
/// 缓存预热
///
/// 在系统启动或低峰期提前加载热点数据

pub struct CacheWarmer<K, V> {
    cache: Box<dyn Cache<K, V>>,
    store: Box<dyn Store<K, V>>,

    /// 热点数据预测器
    predictor: Box<dyn HotDataPredictor<K>>,
}

#[async_trait]
pub trait HotDataPredictor<K>: Send + Sync {
    /// 预测热点 key 列表
    async fn predict_hot_keys(&self) -> Vec<K>;
}

/// 基于历史访问模式的预测器
pub struct HistoricalAccessPredictor<K> {
    /// 访问日志
    access_log: Arc<dyn AccessLog<K>>,

    /// 预测窗口
    prediction_window: Duration,
}

#[async_trait]
impl<K: Clone> HotDataPredictor<K> for HistoricalAccessPredictor<K> {
    async fn predict_hot_keys(&self) -> Vec<K> {
        // 分析历史访问模式，预测未来热点
        self.access_log.get_top_keys(100).await
    }
}

impl<K: Clone, V: Clone> CacheWarmer<K, V> {
    /// 执行预热
    pub async fn warm(&self, concurrency: usize) -> WarmResult {
        let hot_keys = self.predictor.predict_hot_keys().await;

        let semaphore = Arc::new(tokio::sync::Semaphore::new(concurrency));
        let mut handles = Vec::new();

        for key in hot_keys {
            let permit = semaphore.clone().acquire_owned().await.unwrap();
            let cache = self.cache.clone();
            let store = self.store.clone();

            let handle = tokio::spawn(async move {
                let _permit = permit;

                match store.get(&key).await {
                    Ok(Some(value)) => {
                        if let Err(e) = cache.put(key, value).await {
                            WarmEntryResult::CacheError(e.to_string())
                        } else {
                            WarmEntryResult::Success
                        }
                    }
                    Ok(None) => WarmEntryResult::NotFound,
                    Err(e) => WarmEntryResult::StoreError(e.to_string()),
                }
            });

            handles.push(handle);
        }

        let results = futures::future::join_all(handles).await;

        let mut success = 0;
        let mut failed = 0;
        let mut not_found = 0;

        for result in results {
            match result {
                Ok(WarmEntryResult::Success) => success += 1,
                Ok(WarmEntryResult::NotFound) => not_found += 1,
                _ => failed += 1,
            }
        }

        WarmResult { success, failed, not_found }
    }

    /// 增量预热（运行时）
    pub async fn incremental_warm(&self, new_keys: Vec<K>) {
        for key in new_keys {
            if let Ok(Some(value)) = self.store.get(&key).await {
                let _ = self.cache.put(key, value).await;
            }
        }
    }
}

#[derive(Debug)]
pub struct WarmResult {
    pub success: usize,
    pub failed: usize,
    pub not_found: usize,
}

enum WarmEntryResult {
    Success,
    NotFound,
    CacheError(String),
    StoreError(String),
}
```

---

## 8. 事件溯源模式

### 8.1 事件存储

**事件追加语义：**

```rust
/// 事件存储语义
///
/// 核心原则：
/// 1. 只追加，不修改或删除
/// 2. 事件是事实的不可变记录
/// 3. 全局顺序或分区顺序

pub struct EventStore {
    /// 存储后端
    storage: Box<dyn EventStorage>,

    /// 序列号生成器
    sequence_generator: Box<dyn SequenceGenerator>,

    /// 事件序列化器
    serializer: Box<dyn EventSerializer>,
}

/// 存储的持久化事件
#[derive(Debug, Clone)]
pub struct StoredEvent {
    /// 全局序列号
    pub sequence_number: u64,

    /// 流 ID（聚合根 ID）
    pub stream_id: String,

    /// 流内版本号
    pub stream_version: u64,

    /// 事件类型
    pub event_type: String,

    /// 事件数据（JSON 或二进制）
    pub payload: Vec<u8>,

    /// 元数据（时间戳、用户等）
    pub metadata: EventMetadata,

    /// 时间戳
    pub timestamp: u64,
}

#[derive(Debug, Clone, Default)]
pub struct EventMetadata {
    pub correlation_id: Option<String>,
    pub causation_id: Option<String>,
    pub user_id: Option<String>,
    pub source_ip: Option<String>,
}

#[async_trait]
pub trait EventStorage: Send + Sync {
    /// 追加事件（乐观并发控制）
    async fn append(
        &self,
        stream_id: &str,
        expected_version: u64,
        events: Vec<StoredEvent>,
    ) -> Result<AppendResult, EventStoreError>;

    /// 读取流的所有事件
    async fn read_stream(&self, stream_id: &str) -> Result<Vec<StoredEvent>, EventStoreError>;

    /// 从指定版本读取
    async fn read_stream_from(
        &self,
        stream_id: &str,
        from_version: u64,
    ) -> Result<Vec<StoredEvent>, EventStoreError>;

    /// 读取所有事件（全局顺序）
    async fn read_all(&self) -> Result<Vec<StoredEvent>, EventStoreError>;

    /// 从全局位置读取
    async fn read_all_from(&self, position: u64) -> Result<EventStream, EventStoreError>;
}

/// 追加结果
#[derive(Debug, Clone)]
pub struct AppendResult {
    pub next_expected_version: u64,
    pub global_position: u64,
}

/// 乐观并发控制错误
#[derive(Debug)]
pub enum EventStoreError {
    ConcurrencyConflict {
        stream_id: String,
        expected: u64,
        actual: u64,
    },
    StreamNotFound(String),
    StorageError(String),
    SerializationError(String),
}

impl EventStore {
    /// 追加事件到流
    pub async fn append<E: DomainEvent>(
        &self,
        stream_id: &str,
        expected_version: u64,
        events: Vec<E>,
    ) -> Result<AppendResult, EventStoreError> {
        let stored_events: Vec<_> = events.into_iter()
            .enumerate()
            .map(|(i, event)| self.to_stored_event(stream_id, expected_version + i as u64 + 1, event))
            .collect();

        self.storage.append(stream_id, expected_version, stored_events).await
    }

    fn to_stored_event<E: DomainEvent>(
        &self,
        stream_id: &str,
        version: u64,
        event: E,
    ) -> StoredEvent {
        StoredEvent {
            sequence_number: 0, // 由存储分配
            stream_id: stream_id.to_string(),
            stream_version: version,
            event_type: event.event_type(),
            payload: self.serializer.serialize(&event),
            metadata: event.metadata(),
            timestamp: current_timestamp(),
        }
    }
}

/// 领域事件 trait
pub trait DomainEvent: Send + Sync {
    fn event_type(&self) -> String;
    fn event_version(&self) -> u32;
    fn metadata(&self) -> EventMetadata;
    fn aggregate_id(&self) -> String;
}
```

**事件版本语义：**

```rust
/// 事件版本管理
///
/// 处理事件模式的演化

pub struct EventVersionManager {
    /// 注册的事件升级器
    upgraders: HashMap<(String, u32, u32), Box<dyn EventUpgrader>>,

    /// 当前支持的最新版本
    current_versions: HashMap<String, u32>,
}

/// 事件升级器
pub trait EventUpgrader: Send + Sync {
    /// 升级事件从旧版本到新版本
    fn upgrade(&self, payload: &[u8]) -> Result<Vec<u8>, UpgradeError>;
}

/// 事件兼容性检查
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Compatibility {
    /// 完全兼容，无需转换
    FullyCompatible,

    /// 向上兼容（旧代码可以读新数据）
    ForwardCompatible,

    /// 向下兼容（新代码可以读旧数据）
    BackwardCompatible,

    /// 不兼容，需要升级
    BreakingChange,
}

impl EventVersionManager {
    /// 注册升级器
    pub fn register_upgrader(
        &mut self,
        event_type: &str,
        from_version: u32,
        to_version: u32,
        upgrader: Box<dyn EventUpgrader>,
    ) {
        self.upgraders.insert(
            (event_type.to_string(), from_version, to_version),
            upgrader,
        );
    }

    /// 读取并升级事件到当前版本
    pub fn read_and_upgrade(
        &self,
        event_type: &str,
        version: u32,
        payload: &[u8],
    ) -> Result<Vec<u8>, UpgradeError> {
        let target_version = self.current_versions
            .get(event_type)
            .copied()
            .ok_or(UpgradeError::UnknownEventType(event_type.to_string()))?;

        if version == target_version {
            return Ok(payload.to_vec());
        }

        if version > target_version {
            return Err(UpgradeError::NewerVersion {
                event_type: event_type.to_string(),
                stored: version,
                current: target_version,
            });
        }

        // 链式升级
        let mut current_version = version;
        let mut current_payload = payload.to_vec();

        while current_version < target_version {
            let upgrader = self.upgraders
                .get(&(event_type.to_string(), current_version, current_version + 1))
                .ok_or(UpgradeError::NoUpgradePath {
                    event_type: event_type.to_string(),
                    from: current_version,
                    to: target_version,
                })?;

            current_payload = upgrader.upgrade(&current_payload)?;
            current_version += 1;
        }

        Ok(current_payload)
    }

    /// 检查兼容性
    pub fn check_compatibility(
        &self,
        old_schema: &EventSchema,
        new_schema: &EventSchema,
    ) -> Compatibility {
        // 检查字段变化
        let old_fields: HashSet<_> = old_schema.fields.iter().map(|f| &f.name).collect();
        let new_fields: HashSet<_> = new_schema.fields.iter().map(|f| &f.name).collect();

        let added: HashSet<_> = new_fields.difference(&old_fields).collect();
        let removed: HashSet<_> = old_fields.difference(&new_fields).collect();

        if removed.is_empty() && added.is_empty() {
            return Compatibility::FullyCompatible;
        }

        if !removed.is_empty() {
            return Compatibility::BreakingChange;
        }

        // 检查新增字段是否有默认值
        let all_have_defaults = added.iter().all(|field_name| {
            new_schema.fields.iter()
                .find(|f| &f.name == *field_name)
                .map(|f| f.has_default)
                .unwrap_or(false)
        });

        if all_have_defaults {
            Compatibility::ForwardCompatible
        } else {
            Compatibility::BreakingChange
        }
    }
}

#[derive(Debug)]
pub struct EventSchema {
    pub event_type: String,
    pub version: u32,
    pub fields: Vec<FieldSchema>,
}

#[derive(Debug)]
pub struct FieldSchema {
    pub name: String,
    pub field_type: String,
    pub optional: bool,
    pub has_default: bool,
}

#[derive(Debug)]
pub enum UpgradeError {
    UnknownEventType(String),
    NewerVersion { event_type: String, stored: u32, current: u32 },
    NoUpgradePath { event_type: String, from: u32, to: u32 },
    SerializationError(String),
}
```

**事件序列化：**

```rust
/// 事件序列化策略

pub trait EventSerializer: Send + Sync {
    fn serialize<E: Serialize>(&self, event: &E) -> Vec<u8>;
    fn deserialize<T: for<'de> Deserialize<'de>>(&self, payload: &[u8]) -> Result<T, SerializationError>;
}

/// JSON 序列化（人类可读）
pub struct JsonSerializer;

impl EventSerializer for JsonSerializer {
    fn serialize<E: Serialize>(&self, event: &E) -> Vec<u8> {
        serde_json::to_vec(event).expect("Failed to serialize event")
    }

    fn deserialize<T: for<'de> Deserialize<'de>>(&self, payload: &[u8]) -> Result<T, SerializationError> {
        serde_json::from_slice(payload)
            .map_err(|e| SerializationError::JsonError(e.to_string()))
    }
}

/// MessagePack 序列化（紧凑）
pub struct MessagePackSerializer;

impl EventSerializer for MessagePackSerializer {
    fn serialize<E: Serialize>(&self, event: &E) -> Vec<u8> {
        rmp_serde::to_vec(event).expect("Failed to serialize event")
    }

    fn deserialize<T: for<'de> Deserialize<'de>>(&self, payload: &[u8]) -> Result<T, SerializationError> {
        rmp_serde::from_slice(payload)
            .map_err(|e| SerializationError::MsgPackError(e.to_string()))
    }
}

/// 带类型信息的封装（用于多态反序列化）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Envelope {
    pub event_type: String,
    pub version: u32,
    pub payload: Vec<u8>,
}
```

### 8.2 状态重建

**快照语义：**

```rust
/// 快照机制
///
/// 用于加速状态重建，避免重放所有历史事件

pub struct SnapshotManager<S> {
    /// 快照存储
    storage: Box<dyn SnapshotStorage<S>>,

    /// 快照策略
    strategy: SnapshotStrategy,
}

#[derive(Debug, Clone)]
pub struct SnapshotStrategy {
    /// 每 N 个事件创建一个快照
    pub events_per_snapshot: u32,

    /// 快照最大年龄
    pub max_age: Duration,

    /// 压缩策略
    pub compression: CompressionType,
}

#[derive(Debug, Clone, Copy)]
pub enum CompressionType {
    None,
    Zstd,
    Lz4,
}

/// 快照
#[derive(Debug, Clone)]
pub struct Snapshot<S> {
    /// 流 ID
    pub stream_id: String,

    /// 快照包含的最后一个事件版本
    pub version: u64,

    /// 状态数据
    pub state: S,

    /// 快照时间戳
    pub timestamp: u64,

    /// 快照序列号（用于清理旧快照）
    pub snapshot_sequence: u64,
}

#[async_trait]
pub trait SnapshotStorage<S>: Send + Sync {
    async fn save(&self, snapshot: &Snapshot<S>) -> Result<(), SnapshotError>;
    async fn load(&self, stream_id: &str) -> Result<Option<Snapshot<S>>, SnapshotError>;
    async fn delete_old_snapshots(&self, stream_id: &str, keep_count: usize) -> Result<(), SnapshotError>;
}

impl<S: Clone + Send> SnapshotManager<S> {
    /// 检查是否需要创建快照
    pub fn should_snapshot(&self, events_since_snapshot: u32, last_snapshot_age: Duration) -> bool {
        events_since_snapshot >= self.strategy.events_per_snapshot ||
        last_snapshot_age >= self.strategy.max_age
    }

    /// 创建快照
    pub async fn create_snapshot(
        &self,
        stream_id: &str,
        version: u64,
        state: &S,
    ) -> Result<(), SnapshotError> {
        let snapshot = Snapshot {
            stream_id: stream_id.to_string(),
            version,
            state: state.clone(),
            timestamp: current_timestamp(),
            snapshot_sequence: self.generate_sequence(),
        };

        self.storage.save(&snapshot).await?;

        // 清理旧快照
        self.storage.delete_old_snapshots(stream_id, 3).await?;

        Ok(())
    }

    /// 加载最新状态
    pub async fn load_state(&self, stream_id: &str) -> Result<Option<(u64, S)>, SnapshotError> {
        let snapshot = self.storage.load(stream_id).await?;

        Ok(snapshot.map(|s| (s.version, s.state)))
    }

    fn generate_sequence(&self) -> u64 {
        current_timestamp()
    }
}
```

**重放语义：**

```rust
/// 事件重放
///
/// 从事件流重建聚合状态

pub struct EventReplayer<A: Aggregate> {
    event_store: Arc<EventStore>,
    _phantom: std::marker::PhantomData<A>,
}

/// 聚合根 trait
pub trait Aggregate: Default + Send + Sync {
    type Event: DomainEvent;

    /// 应用单个事件
    fn apply(&mut self, event: &Self::Event);

    /// 获取当前版本
    fn version(&self) -> u64;
}

impl<A: Aggregate> EventReplayer<A> {
    /// 重放所有事件重建聚合
    pub async fn replay(&self, stream_id: &str) -> Result<A, ReplayError> {
        let events = self.event_store.storage.read_stream(stream_id).await
            .map_err(|e| ReplayError::StoreError(e.to_string()))?;

        if events.is_empty() {
            return Err(ReplayError::StreamNotFound(stream_id.to_string()));
        }

        let mut aggregate = A::default();

        for stored in events {
            let event: A::Event = self.deserialize_event(&stored)?;
            aggregate.apply(&event);
        }

        Ok(aggregate)
    }

    /// 从快照重放
    pub async fn replay_from_snapshot(
        &self,
        stream_id: &str,
        snapshot_manager: &SnapshotManager<A>,
    ) -> Result<A, ReplayError> {
        // 1. 尝试加载快照
        let (start_version, mut aggregate) = match snapshot_manager.load_state(stream_id).await {
            Ok(Some((version, state))) => (version, state),
            Ok(None) => (0, A::default()),
            Err(e) => return Err(ReplayError::SnapshotError(e.to_string())),
        };

        // 2. 加载快照之后的事件
        let events = self.event_store.storage
            .read_stream_from(stream_id, start_version + 1)
            .await
            .map_err(|e| ReplayError::StoreError(e.to_string()))?;

        // 3. 应用剩余事件
        for stored in events {
            let event: A::Event = self.deserialize_event(&stored)?;
            aggregate.apply(&event);
        }

        Ok(aggregate)
    }

    fn deserialize_event(&self, stored: &StoredEvent) -> Result<A::Event, ReplayError> {
        // 实际反序列化
        Err(ReplayError::SerializationError)
    }
}

#[derive(Debug)]
pub enum ReplayError {
    StreamNotFound(String),
    StoreError(String),
    SnapshotError(String),
    SerializationError,
    EventVersionMismatch { expected: u32, found: u32 },
}
```

**投影语义：**

```rust
/// 投影（Projection / Read Model）
///
/// 将事件流转换为查询优化的视图

pub struct ProjectionManager {
    /// 注册的投影处理器
    projections: HashMap<String, Box<dyn ProjectionHandler>>,

    /// 事件订阅
    subscription: EventSubscription,

    /// 投影存储
    projection_store: Arc<dyn ProjectionStore>,
}

#[async_trait]
pub trait ProjectionHandler: Send + Sync {
    /// 处理单个事件
    async fn handle(&mut self, event: &StoredEvent) -> Result<(), ProjectionError>;

    /// 重置投影（从快照重建）
    async fn reset(&mut self) -> Result<(), ProjectionError>;

    /// 获取投影位置
    fn position(&self) -> u64;
}

#[async_trait]
pub trait ProjectionStore: Send + Sync {
    async fn save_checkpoint(&self, projection_name: &str, position: u64) -> Result<(), ProjectionError>;
    async fn load_checkpoint(&self, projection_name: &str) -> Result<u64, ProjectionError>;
}

impl ProjectionManager {
    /// 运行投影（持续处理新事件）
    pub async fn run(&mut self) -> Result<(), ProjectionError> {
        let mut event_stream = self.subscription.subscribe().await;

        while let Some(event) = event_stream.next().await {
            for (name, handler) in &mut self.projections {
                // 检查位置
                if event.sequence_number <= handler.position() {
                    continue;
                }

                // 处理事件
                if let Err(e) = handler.handle(&event).await {
                    tracing::error!("Projection {} failed: {:?}", name, e);
                    // 错误处理策略：跳过、重试或暂停
                }

                // 保存检查点
                self.projection_store
                    .save_checkpoint(name, event.sequence_number)
                    .await?;
            }
        }

        Ok(())
    }

    /// 重建投影（从指定位置重放）
    pub async fn rebuild(&mut self, projection_name: &str) -> Result<(), ProjectionError> {
        let handler = self.projections.get_mut(projection_name)
            .ok_or(ProjectionError::ProjectionNotFound(projection_name.to_string()))?;

        // 重置投影
        handler.reset().await?;

        // 重放所有事件
        let events = self.event_store.storage.read_all().await
            .map_err(|e| ProjectionError::StoreError(e.to_string()))?;

        for event in events {
            handler.handle(&event).await?;

            // 定期保存检查点
            if event.sequence_number % 1000 == 0 {
                self.projection_store
                    .save_checkpoint(projection_name, event.sequence_number)
                    .await?;
            }
        }

        Ok(())
    }
}

/// 示例：订单统计投影
pub struct OrderStatisticsProjection {
    /// 统计存储
    stats_store: Arc<dyn StatisticsStore>,

    /// 当前位置
    position: u64,
}

#[async_trait]
impl ProjectionHandler for OrderStatisticsProjection {
    async fn handle(&mut self, event: &StoredEvent) -> Result<(), ProjectionError> {
        match event.event_type.as_str() {
            "OrderCreated" => {
                self.stats_store.increment_order_count().await?;
            }
            "OrderCompleted" => {
                let order_value = self.extract_order_value(&event.payload)?;
                self.stats_store.add_revenue(order_value).await?;
            }
            _ => {}
        }

        self.position = event.sequence_number;
        Ok(())
    }

    async fn reset(&mut self) -> Result<(), ProjectionError> {
        self.stats_store.clear().await?;
        self.position = 0;
        Ok(())
    }

    fn position(&self) -> u64 {
        self.position
    }
}

#[derive(Debug)]
pub enum ProjectionError {
    ProjectionNotFound(String),
    StoreError(String),
    SerializationError(String),
    HandlerError(String),
}

struct EventSubscription;
impl EventSubscription {
    async fn subscribe(&self) -> EventStream {
        EventStream
    }
}
struct EventStream;
impl EventStream {
    async fn next(&mut self) -> Option<StoredEvent> {
        None
    }
}
```

---

## 9. CQRS 模式

### 9.1 命令端语义

**写模型语义：**

```rust
/// CQRS 命令端（写模型）
///
/// 职责：处理命令，维护聚合状态，产生事件

pub struct CommandHandler<A: Aggregate> {
    /// 事件存储
    event_store: Arc<EventStore>,

    /// 快照管理器（可选）
    snapshot_manager: Option<Arc<SnapshotManager<A>>>,

    /// 事件发布器
    event_publisher: Arc<dyn EventPublisher>,

    /// 命令验证器
    validator: Box<dyn CommandValidator<A::Command>>,

    _phantom: std::marker::PhantomData<A>,
}

/// 命令 trait
pub trait Command: Send + Sync {
    fn aggregate_id(&self) -> String;
    fn command_id(&self) -> String;
}

#[async_trait]
pub trait CommandValidator<C: Command>: Send + Sync {
    async fn validate(&self, command: &C) -> Result<(), ValidationError>;
}

#[async_trait]
pub trait EventPublisher: Send + Sync {
    async fn publish(&self, events: Vec<StoredEvent>) -> Result<(), PublishError>;
}

impl<A: Aggregate> CommandHandler<A> {
    /// 处理命令
    pub async fn handle(&self, command: A::Command) -> Result<CommandResult, CommandError> {
        let aggregate_id = command.aggregate_id();

        // 1. 验证命令
        self.validator.validate(&command).await
            .map_err(CommandError::ValidationFailed)?;

        // 2. 加载聚合
        let mut aggregate = self.load_aggregate(&aggregate_id).await?;

        // 3. 执行命令，产生事件
        let events = aggregate.execute(command).await
            .map_err(CommandError::ExecutionFailed)?;

        if events.is_empty() {
            return Ok(CommandResult::NoOp);
        }

        // 4. 持久化事件
        let expected_version = aggregate.version();
        let append_result = self.event_store.append(
            &aggregate_id,
            expected_version,
            events.clone(),
        ).await.map_err(CommandError::PersistenceFailed)?;

        // 5. 创建快照（如果需要）
        if let Some(ref snapshot_manager) = self.snapshot_manager {
            if snapshot_manager.should_snapshot(events.len() as u32, Duration::ZERO) {
                snapshot_manager.create_snapshot(
                    &aggregate_id,
                    append_result.next_expected_version - 1,
                    &aggregate,
                ).await.ok();
            }
        }

        // 6. 发布事件
        let stored_events = events.into_iter()
            .enumerate()
            .map(|(i, e)| StoredEvent {
                sequence_number: append_result.global_position + i as u64,
                stream_id: aggregate_id.clone(),
                stream_version: expected_version + i as u64 + 1,
                event_type: e.event_type(),
                payload: vec![], // 序列化
                metadata: e.metadata(),
                timestamp: current_timestamp(),
            })
            .collect();

        self.event_publisher.publish(stored_events).await
            .map_err(CommandError::PublishFailed)?;

        Ok(CommandResult::Success {
            aggregate_id,
            new_version: append_result.next_expected_version - 1,
        })
    }

    /// 加载聚合
    async fn load_aggregate(&self, aggregate_id: &str) -> Result<A, CommandError> {
        if let Some(ref snapshot_manager) = self.snapshot_manager {
            let replayer = EventReplayer::<A> {
                event_store: self.event_store.clone(),
                _phantom: std::marker::PhantomData,
            };
            replayer.replay_from_snapshot(aggregate_id, snapshot_manager).await
                .map_err(|e| CommandError::ReplayFailed(e.to_string()))
        } else {
            // 从事件重建
            let replayer = EventReplayer::<A> {
                event_store: self.event_store.clone(),
                _phantom: std::marker::PhantomData,
            };
            replayer.replay(aggregate_id).await
                .map_err(|e| CommandError::ReplayFailed(e.to_string()))
        }
    }
}

#[derive(Debug)]
pub enum CommandResult {
    Success { aggregate_id: String, new_version: u64 },
    NoOp,
}

#[derive(Debug)]
pub enum CommandError {
    ValidationFailed(ValidationError),
    ExecutionFailed(String),
    PersistenceFailed(EventStoreError),
    ReplayFailed(String),
    PublishFailed(PublishError),
    ConcurrencyConflict { expected: u64, actual: u64 },
}

#[derive(Debug)]
pub enum ValidationError {
    InvalidData(String),
    BusinessRuleViolation(String),
    AggregateNotFound(String),
}

#[derive(Debug)]
pub enum PublishError {
    NetworkError(String),
    SubscriberUnavailable,
}
```

**验证语义：**

```rust
/// 命令验证
///
/// 确保命令满足业务规则和不变量

pub struct CommandValidationPipeline<C> {
    validators: Vec<Box<dyn Validator<C>>>,
}

#[async_trait]
pub trait Validator<C>: Send + Sync {
    async fn validate(&self, command: &C) -> Result<(), ValidationError>;
}

impl<C: Command> CommandValidationPipeline<C> {
    pub fn add_validator<V: Validator<C> + 'static>(&mut self, validator: V) {
        self.validators.push(Box::new(validator));
    }

    pub async fn validate(&self, command: &C) -> Result<(), ValidationError> {
        for validator in &self.validators {
            validator.validate(command).await?;
        }
        Ok(())
    }
}

/// 示例：订单命令验证器
pub struct OrderCommandValidator;

#[derive(Debug, Clone)]
pub struct CreateOrderCommand {
    pub order_id: String,
    pub customer_id: String,
    pub items: Vec<OrderItem>,
    pub total_amount: f64,
}

impl Command for CreateOrderCommand {
    fn aggregate_id(&self) -> String {
        self.order_id.clone()
    }

    fn command_id(&self) -> String {
        format!("cmd:create-order:{}", self.order_id)
    }
}

#[async_trait]
impl Validator<CreateOrderCommand> for OrderCommandValidator {
    async fn validate(&self, command: &CreateOrderCommand) -> Result<(), ValidationError> {
        // 验证订单项不为空
        if command.items.is_empty() {
            return Err(ValidationError::InvalidData(
                "Order must have at least one item".to_string()
            ));
        }

        // 验证金额
        if command.total_amount <= 0.0 {
            return Err(ValidationError::InvalidData(
                "Total amount must be positive".to_string()
            ));
        }

        // 验证金额与明细匹配
        let calculated_total: f64 = command.items.iter()
            .map(|item| item.price * item.quantity as f64)
            .sum();

        if (calculated_total - command.total_amount).abs() > 0.01 {
            return Err(ValidationError::InvalidData(
                "Total amount does not match sum of items".to_string()
            ));
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct OrderItem {
    pub product_id: String,
    pub quantity: u32,
    pub price: f64,
}
```

**事件发布语义：**

```rust
/// 事件发布策略

#[async_trait]
pub trait EventPublisher: Send + Sync {
    async fn publish(&self, events: Vec<StoredEvent>) -> Result<(), PublishError>;
}

/// 同步发布（阻塞直到所有订阅者确认）
pub struct SynchronousPublisher {
    subscribers: Vec<Box<dyn EventSubscriber>>,
    timeout: Duration,
}

#[async_trait]
pub trait EventSubscriber: Send + Sync {
    async fn handle(&self, event: &StoredEvent) -> Result<(), SubscriberError>;
}

#[async_trait]
impl EventPublisher for SynchronousPublisher {
    async fn publish(&self, events: Vec<StoredEvent>) -> Result<(), PublishError> {
        for event in events {
            let mut handles = Vec::new();

            for subscriber in &self.subscribers {
                let event = event.clone();
                let subscriber = subscriber.clone_box();

                handles.push(tokio::spawn(async move {
                    tokio::time::timeout(
                        Duration::from_secs(5),
                        subscriber.handle(&event)
                    ).await
                }));
            }

            // 等待所有订阅者处理
            for handle in handles {
                if let Err(e) = handle.await {
                    tracing::error!("Subscriber failed: {:?}", e);
                }
            }
        }

        Ok(())
    }
}

/// 异步发布（不等待确认）
pub struct AsynchronousPublisher {
    event_bus: Arc<dyn EventBus>,
}

#[async_trait]
impl EventPublisher for AsynchronousPublisher {
    async fn publish(&self, events: Vec<StoredEvent>) -> Result<(), PublishError> {
        for event in events {
            self.event_bus.publish(event).await?;
        }
        Ok(())
    }
}

#[async_trait]
pub trait EventBus: Send + Sync {
    async fn publish(&self, event: StoredEvent) -> Result<(), PublishError>;
}

/// 事务性发布（存储到 Outbox 表）
pub struct OutboxPublisher {
    db_pool: Arc<DbPool>,
    event_bus: Arc<dyn EventBus>,
}

impl OutboxPublisher {
    /// 发布到 Outbox（在同一事务中）
    pub async fn publish_to_outbox(
        &self,
        tx: &mut Transaction,
        events: Vec<StoredEvent>,
    ) -> Result<(), PublishError> {
        for event in events {
            tx.execute(
                "INSERT INTO outbox (event_type, payload, metadata) VALUES ($1, $2, $3)",
                &[&event.event_type, &event.payload, &serde_json::to_vec(&event.metadata).unwrap()],
            ).await?;
        }

        Ok(())
    }

    /// 后台任务：轮询 Outbox 并发布
    pub async fn run_outbox_polling(&self) {
        let mut interval = tokio::time::interval(Duration::from_millis(100));

        loop {
            interval.tick().await;

            if let Err(e) = self.process_outbox().await {
                tracing::error!("Outbox processing failed: {:?}", e);
            }
        }
    }

    async fn process_outbox(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 1. 读取未处理的事件
        let events = self.fetch_pending_events().await?;

        for event in events {
            // 2. 发布到消息总线
            match self.event_bus.publish(event.clone()).await {
                Ok(_) => {
                    // 3. 标记为已处理
                    self.mark_as_processed(event.sequence_number).await?;
                }
                Err(e) => {
                    tracing::error!("Failed to publish event {:?}: {:?}", event.sequence_number, e);
                }
            }
        }

        Ok(())
    }

    async fn fetch_pending_events(&self) -> Result<Vec<StoredEvent>, Box<dyn std::error::Error>> {
        // 实现...
        Ok(vec![])
    }

    async fn mark_as_processed(&self, _id: u64) -> Result<(), Box<dyn std::error::Error>> {
        // 实现...
        Ok(())
    }
}

struct DbPool;
struct Transaction;
impl Transaction {
    async fn execute(&mut self, _sql: &str, _params: &[&dyn std::any::Any]) -> Result<(), PublishError> {
        Ok(())
    }
}
```

### 9.2 查询端语义

**读模型语义：**

```rust
/// CQRS 查询端（读模型）
///
/// 职责：提供优化的查询视图

pub struct QueryHandler<Q: Query> {
    /// 读模型存储
    read_model: Arc<dyn ReadModel<Q::Result>>,

    /// 查询缓存
    cache: Option<Arc<dyn QueryCache<Q, Q::Result>>>,

    /// 查询优化器
    optimizer: Box<dyn QueryOptimizer<Q>>,
}

/// 查询 trait
#[async_trait]
pub trait Query: Send + Sync {
    type Result: Send;
    fn query_id(&self) -> String;
    fn cache_key(&self) -> Option<String>;
    fn cache_ttl(&self) -> Option<Duration>;
}

/// 读模型存储
#[async_trait]
pub trait ReadModel<R>: Send + Sync {
    async fn query(&self, criteria: &QueryCriteria) -> Result<R, QueryError>;
}

impl<Q: Query + 'static> QueryHandler<Q> {
    /// 处理查询
    pub async fn handle(&self, query: Q) -> Result<Q::Result, QueryError> {
        // 1. 尝试从缓存获取
        if let Some(ref cache) = self.cache {
            if let Some(key) = query.cache_key() {
                if let Some(cached) = cache.get(&key).await? {
                    return Ok(cached);
                }
            }
        }

        // 2. 优化查询
        let optimized_criteria = self.optimizer.optimize(&query);

        // 3. 执行查询
        let result = self.read_model.query(&optimized_criteria).await?;

        // 4. 缓存结果
        if let Some(ref cache) = self.cache {
            if let Some(key) = query.cache_key() {
                if let Some(ttl) = query.cache_ttl() {
                    cache.set(&key, &result, ttl).await.ok();
                }
            }
        }

        Ok(result)
    }
}

#[derive(Debug, Clone)]
pub struct QueryCriteria {
    pub filters: Vec<Filter>,
    pub sort: Vec<SortField>,
    pub pagination: Option<Pagination>,
}

#[derive(Debug, Clone)]
pub struct Filter {
    pub field: String,
    pub operator: FilterOperator,
    pub value: FilterValue,
}

#[derive(Debug, Clone)]
pub enum FilterOperator {
    Eq, Ne, Gt, Gte, Lt, Lte, In, Contains, StartsWith, EndsWith,
}

#[derive(Debug, Clone)]
pub enum FilterValue {
    String(String),
    Number(f64),
    Bool(bool),
    List(Vec<FilterValue>),
}

#[derive(Debug, Clone)]
pub struct SortField {
    pub field: String,
    pub direction: SortDirection,
}

#[derive(Debug, Clone, Copy)]
pub enum SortDirection {
    Asc,
    Desc,
}

#[derive(Debug, Clone)]
pub struct Pagination {
    pub page: u32,
    pub page_size: u32,
}

#[derive(Debug)]
pub enum QueryError {
    NotFound,
    InvalidCriteria(String),
    StorageError(String),
    Timeout,
}
```

**查询优化语义：**

```rust
/// 查询优化器
///
/// 转换和优化查询条件以利用索引

pub struct QueryOptimizer<Q> {
    indexes: Vec<IndexDefinition>,
    _phantom: std::marker::PhantomData<Q>,
}

#[derive(Debug, Clone)]
pub struct IndexDefinition {
    pub name: String,
    pub fields: Vec<String>,
    pub index_type: IndexType,
}

#[derive(Debug, Clone, Copy)]
pub enum IndexType {
    BTree,
    Hash,
    Gin,    // PostgreSQL 全文索引
    Gist,   // PostgreSQL 空间索引
}

impl<Q: Query> QueryOptimizer<Q> {
    /// 优化查询条件
    pub fn optimize(&self, query: &Q) -> QueryCriteria {
        let mut criteria = query.to_criteria();

        // 1. 重排过滤条件（选择性高的在前）
        criteria.filters.sort_by(|a, b| {
            let selectivity_a = self.estimate_selectivity(a);
            let selectivity_b = self.estimate_selectivity(b);
            selectivity_a.partial_cmp(&selectivity_b).unwrap()
        });

        // 2. 选择最佳索引
        let best_index = self.select_index(&criteria);

        // 3. 根据索引调整查询
        if let Some(index) = best_index {
            criteria = self.align_to_index(criteria, &index);
        }

        criteria
    }

    fn estimate_selectivity(&self, filter: &Filter) -> f64 {
        // 简单估计：等值查询选择性高
        match filter.operator {
            FilterOperator::Eq => 0.01,  // 假设 1% 匹配
            FilterOperator::In => 0.1,
            FilterOperator::Gt | FilterOperator::Lt => 0.5,
            FilterOperator::Contains => 0.3,
            _ => 0.8,
        }
    }

    fn select_index(&self, criteria: &QueryCriteria) -> Option<IndexDefinition> {
        let filter_fields: HashSet<_> = criteria.filters.iter()
            .map(|f| f.field.clone())
            .collect();

        // 选择覆盖最多过滤条件的索引
        self.indexes.iter()
            .filter(|idx| {
                // 索引的第一个字段必须在过滤条件中
                idx.fields.first()
                    .map(|f| filter_fields.contains(f))
                    .unwrap_or(false)
            })
            .max_by_key(|idx| {
                // 计算索引匹配度
                idx.fields.iter()
                    .filter(|f| filter_fields.contains(*f))
                    .count()
            })
            .cloned()
    }

    fn align_to_index(&self, criteria: QueryCriteria, index: &IndexDefinition) -> QueryCriteria {
        // 根据索引字段顺序重排过滤条件
        let mut ordered_filters = Vec::new();
        let filter_map: HashMap<_, _> = criteria.filters.iter()
            .map(|f| (f.field.clone(), f.clone()))
            .collect();

        for field in &index.fields {
            if let Some(filter) = filter_map.get(field) {
                ordered_filters.push(filter.clone());
            }
        }

        // 添加剩余的过滤条件
        for filter in &criteria.filters {
            if !index.fields.contains(&filter.field) {
                ordered_filters.push(filter.clone());
            }
        }

        QueryCriteria {
            filters: ordered_filters,
            ..criteria
        }
    }
}

impl<Q: Query> Query for Q {
    fn to_criteria(&self) -> QueryCriteria {
        // 默认实现，实际应由具体查询类型实现
        QueryCriteria {
            filters: vec![],
            sort: vec![],
            pagination: None,
        }
    }
}

trait QueryExt: Query {
    fn to_criteria(&self) -> QueryCriteria;
}
```

**物化视图语义：**

```rust
/// 物化视图（Materialized View）
///
/// 预计算的查询结果，由事件更新

pub struct MaterializedView {
    /// 视图名称
    name: String,

    /// 存储
    storage: Arc<dyn ViewStorage>,

    /// 最后更新时间
    last_updated: Arc<AtomicU64>,

    /// 刷新策略
    refresh_policy: RefreshPolicy,
}

#[derive(Debug, Clone)]
pub enum RefreshPolicy {
    /// 实时刷新（事件驱动）
    Realtime,

    /// 定期刷新
    Periodic { interval: Duration },

    /// 按需刷新
    OnDemand,
}

#[async_trait]
pub trait ViewStorage: Send + Sync {
    async fn read(&self, key: &str) -> Result<Option<Vec<u8>>, ViewError>;
    async fn write(&self, key: &str, value: &[u8]) -> Result<(), ViewError>;
    async fn query(&self, query: &ViewQuery) -> Result<Vec<ViewRecord>, ViewError>;
}

#[derive(Debug, Clone)]
pub struct ViewQuery {
    pub view_name: String,
    pub parameters: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct ViewRecord {
    pub key: String,
    pub data: Vec<u8>,
}

impl MaterializedView {
    /// 查询视图
    pub async fn query(&self, parameters: &HashMap<String, String>) -> Result<Vec<ViewRecord>, ViewError> {
        let view_query = ViewQuery {
            view_name: self.name.clone(),
            parameters: parameters.clone(),
        };

        self.storage.query(&view_query).await
    }

    /// 更新视图（由投影调用）
    pub async fn update(&self, key: &str, data: &[u8]) -> Result<(), ViewError> {
        self.storage.write(key, data).await?;
        self.last_updated.store(current_timestamp(), Ordering::SeqCst);
        Ok(())
    }

    /// 检查是否需要刷新
    pub fn needs_refresh(&self) -> bool {
        match self.refresh_policy {
            RefreshPolicy::Realtime => false, // 已经是最新
            RefreshPolicy::Periodic { interval } => {
                let last = self.last_updated.load(Ordering::SeqCst);
                let elapsed = current_timestamp() - last;
                elapsed >= interval.as_secs()
            }
            RefreshPolicy::OnDemand => true,
        }
    }

    /// 完全刷新（从源数据重建）
    pub async fn full_refresh(&self) -> Result<(), ViewError> {
        // 实际实现需要从源数据重新计算
        Ok(())
    }
}

/// 视图管理器
pub struct ViewManager {
    views: HashMap<String, Arc<MaterializedView>>,
    projection_manager: Arc<ProjectionManager>,
}

impl ViewManager {
    /// 注册视图
    pub fn register_view(&mut self, name: &str, view: Arc<MaterializedView>) {
        self.views.insert(name.to_string(), view);
    }

    /// 获取视图
    pub fn get_view(&self, name: &str) -> Option<Arc<MaterializedView>> {
        self.views.get(name).cloned()
    }

    /// 批量刷新过期视图
    pub async fn refresh_stale_views(&self) {
        for (name, view) in &self.views {
            if view.needs_refresh() {
                if let Err(e) = view.full_refresh().await {
                    tracing::error!("Failed to refresh view {}: {:?}", name, e);
                }
            }
        }
    }
}
```

---

## 10. 分布式调度模式

### 10.1 任务调度

**定时任务语义：**

```rust
/// 分布式定时任务调度
///
/// 确保任务在集群中只执行一次

pub struct DistributedScheduler {
    /// 任务存储
    job_store: Arc<dyn JobStore>,

    /// 分布式锁（确保单实例执行）
    lock_manager: Arc<dyn DistributedLock>,

    /// 执行器注册表
    executors: HashMap<String, Box<dyn JobExecutor>>,

    /// 调度配置
    config: SchedulerConfig,
}

#[derive(Debug, Clone)]
pub struct JobDefinition {
    pub id: JobId,
    pub name: String,
    pub cron_expression: String,
    pub executor: String,
    pub params: serde_json::Value,
    pub timeout: Duration,
    pub retry_policy: RetryPolicy,
}

#[derive(Debug, Clone)]
pub struct JobId(String);

#[async_trait]
pub trait JobExecutor: Send + Sync {
    async fn execute(&self, params: &serde_json::Value) -> JobResult;
}

#[async_trait]
pub trait JobStore: Send + Sync {
    async fn get_jobs(&self) -> Result<Vec<JobDefinition>, JobStoreError>;
    async fn record_execution(&self, execution: JobExecution) -> Result<(), JobStoreError>;
    async fn get_last_execution(&self, job_id: &JobId) -> Result<Option<JobExecution>, JobStoreError>;
}

#[derive(Debug, Clone)]
pub struct JobExecution {
    pub job_id: JobId,
    pub started_at: Instant,
    pub finished_at: Option<Instant>,
    pub status: ExecutionStatus,
    pub output: Option<String>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionStatus {
    Running,
    Success,
    Failed,
    Timeout,
    Cancelled,
}

impl DistributedScheduler {
    /// 启动调度器
    pub async fn start(&self) {
        let mut interval = tokio::time::interval(self.config.poll_interval);

        loop {
            interval.tick().await;

            if let Err(e) = self.schedule_jobs().await {
                tracing::error!("Job scheduling failed: {:?}", e);
            }
        }
    }

    /// 调度任务
    async fn schedule_jobs(&self) -> Result<(), SchedulerError> {
        let jobs = self.job_store.get_jobs().await?;
        let now = chrono::Utc::now();

        for job in jobs {
            // 检查是否应该执行
            if !self.should_execute(&job, &now).await? {
                continue;
            }

            // 获取分布式锁
            let lock_key = format!("scheduler:job:{}", job.id.0);
            let lock = self.lock_manager.acquire(&lock_key, job.timeout).await;

            match lock {
                Ok(_guard) => {
                    // 双重检查（防止竞争）
                    if !self.should_execute(&job, &now).await? {
                        continue;
                    }

                    // 执行任务
                    self.execute_job(job).await;
                }
                Err(_) => {
                    // 其他实例正在执行
                    tracing::debug!("Job {} is being executed by another instance", job.id.0);
                }
            }
        }

        Ok(())
    }

    /// 检查是否应该执行任务
    async fn should_execute(&self, job: &JobDefinition, now: &chrono::DateTime<chrono::Utc>) -> Result<bool, SchedulerError> {
        // 获取上次执行时间
        let last_execution = self.job_store.get_last_execution(&job.id).await?;

        // 解析 cron 表达式
        let schedule = cron_parser::parse(&job.cron_expression, now)
            .map_err(|e| SchedulerError::InvalidCron(e.to_string()))?;

        // 检查是否应该运行
        let should_run = match last_execution {
            Some(exec) => {
                let last_run = chrono::DateTime::from_timestamp(
                    exec.started_at.elapsed().as_secs() as i64,
                    0
                ).unwrap_or_else(|| chrono::DateTime::UNIX_EPOCH);

                schedule > last_run
            }
            None => true,
        };

        Ok(should_run)
    }

    /// 执行任务
    async fn execute_job(&self, job: JobDefinition) {
        let executor = self.executors.get(&job.executor)
            .expect("Executor not found");

        let execution = JobExecution {
            job_id: job.id.clone(),
            started_at: Instant::now(),
            finished_at: None,
            status: ExecutionStatus::Running,
            output: None,
            error: None,
        };

        // 记录开始执行
        if let Err(e) = self.job_store.record_execution(execution.clone()).await {
            tracing::error!("Failed to record job start: {:?}", e);
        }

        // 带超时执行
        let result = tokio::time::timeout(
            job.timeout,
            executor.execute(&job.params)
        ).await;

        let mut final_execution = execution.clone();
        final_execution.finished_at = Some(Instant::now());

        match result {
            Ok(Ok(_)) => {
                final_execution.status = ExecutionStatus::Success;
            }
            Ok(Err(e)) => {
                final_execution.status = ExecutionStatus::Failed;
                final_execution.error = Some(format!("{:?}", e));

                // 重试逻辑
                if let Err(retry_err) = self.retry_job(&job).await {
                    tracing::error!("Job retry failed: {:?}", retry_err);
                }
            }
            Err(_) => {
                final_execution.status = ExecutionStatus::Timeout;
                final_execution.error = Some("Execution timeout".to_string());
            }
        }

        // 记录执行结果
        if let Err(e) = self.job_store.record_execution(final_execution).await {
            tracing::error!("Failed to record job completion: {:?}", e);
        }
    }

    async fn retry_job(&self, _job: &JobDefinition) -> Result<(), SchedulerError> {
        // 实现重试逻辑
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    pub poll_interval: Duration,
    pub max_concurrent_jobs: usize,
}

#[derive(Debug)]
pub enum SchedulerError {
    StoreError(JobStoreError),
    InvalidCron(String),
    LockError,
}

#[derive(Debug)]
pub enum JobResult {
    Success,
    Failure(String),
}

#[derive(Debug)]
pub enum JobStoreError {
    ConnectionError,
    NotFound,
}
```

**延迟任务语义：**

```rust
/// 延迟任务队列
///
/// 任务在未来某个时间点执行

pub struct DelayedTaskQueue {
    /// 存储
    storage: Arc<dyn DelayedTaskStorage>,

    /// 就绪任务队列
    ready_queue: Arc<dyn TaskQueue>,

    /// 轮询间隔
    poll_interval: Duration,
}

#[derive(Debug, Clone)]
pub struct DelayedTask {
    pub id: TaskId,
    pub payload: Vec<u8>,
    pub execute_at: u64, // Unix timestamp
    pub priority: u8,
    pub retry_count: u32,
    pub max_retries: u32,
}

#[derive(Debug, Clone)]
pub struct TaskId(String);

#[async_trait]
pub trait DelayedTaskStorage: Send + Sync {
    async fn enqueue(&self, task: DelayedTask) -> Result<(), StorageError>;
    async fn dequeue_due(&self, before: u64, limit: usize) -> Result<Vec<DelayedTask>, StorageError>;
    async fn remove(&self, task_id: &TaskId) -> Result<(), StorageError>;
}

#[async_trait]
pub trait TaskQueue: Send + Sync {
    async fn push(&self, task: DelayedTask) -> Result<(), QueueError>;
}

impl DelayedTaskQueue {
    /// 添加延迟任务
    pub async fn schedule(&self, task: DelayedTask) -> Result<(), QueueError> {
        self.storage.enqueue(task).await
            .map_err(|e| QueueError::StorageError(e.to_string()))
    }

    /// 启动调度循环
    pub async fn start(&self) {
        let mut interval = tokio::time::interval(self.poll_interval);

        loop {
            interval.tick().await;

            let now = current_timestamp();

            match self.storage.dequeue_due(now, 100).await {
                Ok(tasks) => {
                    for task in tasks {
                        if let Err(e) = self.ready_queue.push(task).await {
                            tracing::error!("Failed to push task to ready queue: {:?}", e);
                        }
                    }
                }
                Err(e) => {
                    tracing::error!("Failed to dequeue due tasks: {:?}", e);
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum QueueError {
    StorageError(String),
    Full,
}

#[derive(Debug)]
pub enum StorageError {
    ConnectionError,
}
```

**工作流调度语义：**

```rust
/// 分布式工作流引擎
///
/// 管理复杂的多步骤业务流程

pub struct WorkflowEngine {
    /// 工作流定义存储
    definition_store: Arc<dyn WorkflowDefinitionStore>,

    /// 工作流实例存储
    instance_store: Arc<dyn WorkflowInstanceStore>,

    /// 活动执行器
    activity_executors: HashMap<String, Box<dyn ActivityExecutor>>,

    /// 事件发布器
    event_publisher: Arc<dyn WorkflowEventPublisher>,
}

/// 工作流定义
#[derive(Debug, Clone)]
pub struct WorkflowDefinition {
    pub id: String,
    pub version: u32,
    pub activities: Vec<ActivityDefinition>,
    pub transitions: Vec<Transition>,
}

#[derive(Debug, Clone)]
pub struct ActivityDefinition {
    pub id: String,
    pub activity_type: String,
    pub input_bindings: HashMap<String, String>,
    pub retry_policy: RetryPolicy,
}

#[derive(Debug, Clone)]
pub struct Transition {
    pub from: String,
    pub to: String,
    pub condition: Option<String>, // 条件表达式
}

/// 工作流实例
#[derive(Debug, Clone)]
pub struct WorkflowInstance {
    pub id: String,
    pub definition_id: String,
    pub status: WorkflowStatus,
    pub current_activity: Option<String>,
    pub context: WorkflowContext,
    pub history: Vec<ActivityExecution>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkflowStatus {
    Running,
    Completed,
    Failed,
    Suspended,
    Cancelled,
}

#[derive(Debug, Clone, Default)]
pub struct WorkflowContext {
    pub variables: HashMap<String, serde_json::Value>,
    pub input: serde_json::Value,
    pub output: Option<serde_json::Value>,
}

#[derive(Debug, Clone)]
pub struct ActivityExecution {
    pub activity_id: String,
    pub started_at: Instant,
    pub finished_at: Option<Instant>,
    pub status: ActivityStatus,
    pub input: serde_json::Value,
    pub output: Option<serde_json::Value>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivityStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Compensating,
    Compensated,
}

#[async_trait]
pub trait ActivityExecutor: Send + Sync {
    async fn execute(&self, input: &serde_json::Value) -> Result<serde_json::Value, ActivityError>;
    async fn compensate(&self, input: &serde_json::Value) -> Result<(), ActivityError>;
}

impl WorkflowEngine {
    /// 启动工作流
    pub async fn start_workflow(
        &self,
        definition_id: &str,
        input: serde_json::Value,
    ) -> Result<String, WorkflowError> {
        let definition = self.definition_store.get(definition_id).await
            .ok_or(WorkflowError::DefinitionNotFound)?;

        let instance_id = generate_id();
        let start_activity = definition.activities.first()
            .ok_or(WorkflowError::EmptyWorkflow)?;

        let instance = WorkflowInstance {
            id: instance_id.clone(),
            definition_id: definition_id.to_string(),
            status: WorkflowStatus::Running,
            current_activity: Some(start_activity.id.clone()),
            context: WorkflowContext {
                input: input.clone(),
                variables: HashMap::new(),
                output: None,
            },
            history: vec![],
        };

        self.instance_store.save(&instance).await?;

        // 触发第一个活动
        self.execute_activity(&instance_id, &start_activity.id).await?;

        Ok(instance_id)
    }

    /// 执行活动
    pub async fn execute_activity(
        &self,
        instance_id: &str,
        activity_id: &str,
    ) -> Result<(), WorkflowError> {
        let mut instance = self.instance_store.get(instance_id).await
            .ok_or(WorkflowError::InstanceNotFound)?;

        let definition = self.definition_store.get(&instance.definition_id).await
            .ok_or(WorkflowError::DefinitionNotFound)?;

        let activity_def = definition.activities.iter()
            .find(|a| a.id == activity_id)
            .ok_or(WorkflowError::ActivityNotFound)?;

        let executor = self.activity_executors.get(&activity_def.activity_type)
            .ok_or(WorkflowError::ExecutorNotFound)?;

        // 准备输入
        let input = self.prepare_input(&instance.context, &activity_def.input_bindings);

        // 记录执行开始
        let execution = ActivityExecution {
            activity_id: activity_id.to_string(),
            started_at: Instant::now(),
            finished_at: None,
            status: ActivityStatus::Running,
            input: input.clone(),
            output: None,
            error: None,
        };
        instance.history.push(execution.clone());
        self.instance_store.save(&instance).await?;

        // 执行活动
        match executor.execute(&input).await {
            Ok(output) => {
                // 更新活动状态
                if let Some(exec) = instance.history.last_mut() {
                    exec.status = ActivityStatus::Completed;
                    exec.finished_at = Some(Instant::now());
                    exec.output = Some(output.clone());
                }

                // 更新上下文
                instance.context.variables.insert(
                    format!("activity.{}", activity_id),
                    output.clone()
                );

                // 查找下一个活动
                if let Some(next) = self.find_next_activity(&definition, activity_id, &output) {
                    instance.current_activity = Some(next.clone());
                    self.instance_store.save(&instance).await?;
                    self.execute_activity(instance_id, &next).await?;
                } else {
                    // 工作流完成
                    instance.status = WorkflowStatus::Completed;
                    instance.current_activity = None;
                    self.instance_store.save(&instance).await?;

                    self.event_publisher.publish(WorkflowEvent::Completed {
                        instance_id: instance_id.to_string(),
                        output,
                    }).await?;
                }
            }
            Err(e) => {
                // 处理失败
                if let Some(exec) = instance.history.last_mut() {
                    exec.status = ActivityStatus::Failed;
                    exec.finished_at = Some(Instant::now());
                    exec.error = Some(format!("{:?}", e));
                }

                // 检查是否需要补偿
                if self.should_compensate(&instance) {
                    self.compensate(&mut instance).await?;
                } else {
                    instance.status = WorkflowStatus::Failed;
                }

                self.instance_store.save(&instance).await?;
            }
        }

        Ok(())
    }

    fn prepare_input(
        &self,
        context: &WorkflowContext,
        bindings: &HashMap<String, String>,
    ) -> serde_json::Value {
        let mut input = serde_json::Map::new();

        for (param, source) in bindings {
            let value = if source.starts_with("input.") {
                // 从工作流输入获取
                context.input.pointer(&source[6..].replace('.', "/")).cloned()
            } else if source.starts_with("var.") {
                // 从变量获取
                context.variables.get(&source[4..]).cloned()
            } else {
                Some(serde_json::Value::String(source.clone()))
            };

            if let Some(v) = value {
                input.insert(param.clone(), v);
            }
        }

        serde_json::Value::Object(input)
    }

    fn find_next_activity(
        &self,
        definition: &WorkflowDefinition,
        current_id: &str,
        _output: &serde_json::Value,
    ) -> Option<String> {
        definition.transitions.iter()
            .find(|t| t.from == current_id)
            .map(|t| t.to.clone())
    }

    fn should_compensate(&self, instance: &WorkflowInstance) -> bool {
        // 有成功的活动需要补偿
        instance.history.iter().any(|h| h.status == ActivityStatus::Completed)
    }

    async fn compensate(&self, instance: &mut WorkflowInstance) -> Result<(), WorkflowError> {
        // 倒序补偿
        for execution in instance.history.iter_mut().rev() {
            if execution.status == ActivityStatus::Completed {
                execution.status = ActivityStatus::Compensating;

                // 获取执行器并补偿
                let definition = self.definition_store.get(&instance.definition_id).await
                    .ok_or(WorkflowError::DefinitionNotFound)?;

                if let Some(activity_def) = definition.activities.iter().find(|a| a.id == execution.activity_id) {
                    if let Some(executor) = self.activity_executors.get(&activity_def.activity_type) {
                        if let Err(e) = executor.compensate(&execution.input).await {
                            tracing::error!("Compensation failed: {:?}", e);
                        } else {
                            execution.status = ActivityStatus::Compensated;
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum WorkflowError {
    DefinitionNotFound,
    InstanceNotFound,
    ActivityNotFound,
    ExecutorNotFound,
    EmptyWorkflow,
    StorageError(String),
    ExecutionError(String),
}

#[derive(Debug)]
pub enum ActivityError {
    ExecutionFailed(String),
    InvalidInput(String),
    Timeout,
}

#[derive(Debug)]
pub enum WorkflowEvent {
    Completed { instance_id: String, output: serde_json::Value },
    Failed { instance_id: String, error: String },
    ActivityStarted { instance_id: String, activity_id: String },
    ActivityCompleted { instance_id: String, activity_id: String },
}
```

### 10.2 分布式锁

**基于 Redis 的锁：**

```rust
/// Redis 分布式锁
///
/// 使用 SET key value NX EX 实现

pub struct RedisDistributedLock {
    redis: redis::aio::MultiplexedConnection,

    /// 锁的 key 前缀
    key_prefix: String,

    /// 锁的持有标识（通常是 UUID）
    identifier: String,
}

impl RedisDistributedLock {
    pub async fn new(redis_url: &str, key_prefix: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        let redis = client.get_multiplexed_async_connection().await?;

        Ok(Self {
            redis,
            key_prefix: key_prefix.to_string(),
            identifier: uuid::Uuid::new_v4().to_string(),
        })
    }

    /// 尝试获取锁
    pub async fn try_acquire(
        &mut self,
        resource: &str,
        ttl: Duration,
    ) -> Result<Option<LockGuard>, LockError> {
        let key = format!("{}:{}", self.key_prefix, resource);

        // SET key value NX EX ttl
        let result: Option<String> = redis::cmd("SET")
            .arg(&key)
            .arg(&self.identifier)
            .arg("NX")  // 只有 key 不存在时才设置
            .arg("EX")  // 设置过期时间
            .arg(ttl.as_secs())
            .query_async(&mut self.redis)
            .await?;

        if result.is_some() {
            Ok(Some(LockGuard {
                redis: self.redis.clone(),
                key,
                identifier: self.identifier.clone(),
            }))
        } else {
            Ok(None)
        }
    }

    /// 阻塞式获取锁
    pub async fn acquire(
        &mut self,
        resource: &str,
        ttl: Duration,
        timeout: Duration,
    ) -> Result<LockGuard, LockError> {
        let deadline = Instant::now() + timeout;
        let retry_interval = Duration::from_millis(100);

        loop {
            if let Some(guard) = self.try_acquire(resource, ttl).await? {
                return Ok(guard);
            }

            if Instant::now() >= deadline {
                return Err(LockError::Timeout);
            }

            tokio::time::sleep(retry_interval).await;
        }
    }
}

/// 锁守卫（RAII 自动释放）
pub struct LockGuard {
    redis: redis::aio::MultiplexedConnection,
    key: String,
    identifier: String,
}

impl LockGuard {
    /// 手动释放锁
    pub async fn release(mut self) -> Result<(), LockError> {
        self.unlock().await
    }

    /// 续约（Watchdog 模式）
    pub async fn extend(&mut self, ttl: Duration) -> Result<(), LockError> {
        // 检查锁是否仍由自己持有，然后延长过期时间
        let script = redis::Script::new(r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("expire", KEYS[1], ARGV[2])
            else
                return 0
            end
        "#");

        let result: i32 = script
            .key(&self.key)
            .arg(&self.identifier)
            .arg(ttl.as_secs())
            .invoke_async(&mut self.redis)
            .await?;

        if result == 1 {
            Ok(())
        } else {
            Err(LockError::LockLost)
        }
    }

    async fn unlock(&mut self) -> Result<(), LockError> {
        // 使用 Lua 脚本确保原子性
        let script = redis::Script::new(r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("del", KEYS[1])
            else
                return 0
            end
        "#");

        script.key(&self.key)
            .arg(&self.identifier)
            .invoke_async(&mut self.redis)
            .await?;

        Ok(())
    }
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        // 在 drop 中尝试释放锁
        // 注意：同步的 drop 中不能直接调用 async
        // 实际实现可能需要使用 tokio::spawn 或通道
    }
}

/// 带自动续约的锁
pub struct AutoRenewingLock {
    inner: RedisDistributedLock,
    renew_interval: Duration,
}

impl AutoRenewingLock {
    pub async fn acquire_with_watchdog(
        &mut self,
        resource: &str,
        ttl: Duration,
    ) -> Result<AutoRenewLockGuard, LockError> {
        let guard = self.inner.acquire(resource, ttl, Duration::from_secs(10)).await?;

        // 启动续约任务
        let (stop_tx, mut stop_rx) = tokio::sync::mpsc::channel(1);
        let guard_clone = LockGuard {
            redis: guard.redis.clone(),
            key: guard.key.clone(),
            identifier: guard.identifier.clone(),
        };
        let renew_interval = self.renew_interval;

        let renew_handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(renew_interval);

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        let mut guard = LockGuard {
                            redis: guard_clone.redis.clone(),
                            key: guard_clone.key.clone(),
                            identifier: guard_clone.identifier.clone(),
                        };
                        if let Err(e) = guard.extend(ttl).await {
                            tracing::error!("Lock renew failed: {:?}", e);
                            break;
                        }
                    }
                    _ = stop_rx.recv() => {
                        break;
                    }
                }
            }
        });

        Ok(AutoRenewLockGuard {
            inner: guard,
            stop_tx,
            renew_handle,
        })
    }
}

pub struct AutoRenewLockGuard {
    inner: LockGuard,
    stop_tx: tokio::sync::mpsc::Sender<()>,
    renew_handle: tokio::task::JoinHandle<()>,
}

impl AutoRenewLockGuard {
    pub async fn release(self) -> Result<(), LockError> {
        // 停止续约
        let _ = self.stop_tx.send(()).await;
        self.renew_handle.abort();

        // 释放锁
        let mut inner = self.inner;
        inner.unlock().await
    }
}

#[derive(Debug)]
pub enum LockError {
    RedisError(redis::RedisError),
    Timeout,
    LockLost,
}

impl From<redis::RedisError> for LockError {
    fn from(e: redis::RedisError) -> Self {
        LockError::RedisError(e)
    }
}
```

**基于 ZooKeeper 的锁：**

```rust
/// ZooKeeper 分布式锁
///
/// 使用临时顺序节点实现

pub struct ZkDistributedLock {
    zk: zookeeper::ZooKeeper,
    root_path: String,
    session_id: i64,
}

impl ZkDistributedLock {
    pub async fn new(connect_string: &str, root_path: &str) -> Result<Self, ZkError> {
        let zk = zookeeper::ZooKeeper::connect(connect_string, Duration::from_secs(15), |event| {
            tracing::info!("ZK event: {:?}", event);
        }).await?;

        // 确保根节点存在
        if zk.exists(root_path, false).await?.is_none() {
            zk.create(
                root_path,
                vec![],
                zookeeper::Acl::open_unsafe(),
                zookeeper::CreateMode::Persistent,
            ).await.ok();
        }

        let session_id = zk.session().0;

        Ok(Self { zk, root_path: root_path.to_string(), session_id })
    }

    /// 获取锁
    pub async fn acquire(&self, lock_name: &str, timeout: Duration) -> Result<ZkLockGuard, LockError> {
        let lock_path = format!("{}/{}", self.root_path, lock_name);

        // 确保锁目录存在
        if self.zk.exists(&lock_path, false).await?.is_none() {
            self.zk.create(
                &lock_path,
                vec![],
                zookeeper::Acl::open_unsafe(),
                zookeeper::CreateMode::Persistent,
            ).await.ok();
        }

        // 创建临时顺序节点
        let node_path = self.zk.create(
            &format!("{}/lock-", lock_path),
            vec![],
            zookeeper::Acl::open_unsafe(),
            zookeeper::CreateMode::EphemeralSequential,
        ).await?;

        let node_name = node_path.split('/').last().unwrap().to_string();

        // 尝试获取锁
        let deadline = Instant::now() + timeout;

        loop {
            // 获取所有子节点
            let children = self.zk.get_children(&lock_path, false).await?;
            let mut sorted: Vec<_> = children.iter().cloned().collect();
            sorted.sort();

            let my_index = sorted.iter().position(|n| n == &node_name)
                .ok_or(LockError::NodeLost)?;

            if my_index == 0 {
                // 我是第一个，获取锁成功
                return Ok(ZkLockGuard {
                    zk: self.zk.clone(),
                    node_path,
                });
            }

            // 监听前一个节点
            let prev_node = &sorted[my_index - 1];
            let prev_path = format!("{}/{}", lock_path, prev_node);

            let (tx, mut rx) = tokio::sync::mpsc::channel(1);
            let exists = self.zk.exists_w(&prev_path, move |event| {
                let _ = tx.try_send(event);
            }).await?;

            if exists.is_none() {
                // 前一个节点已删除，重试
                continue;
            }

            // 等待前一个节点删除或超时
            let wait_result = tokio::time::timeout(
                deadline.saturating_duration_since(Instant::now()),
                rx.recv()
            ).await;

            if wait_result.is_err() {
                // 超时，删除自己的节点
                self.zk.delete(&node_path, None).await.ok();
                return Err(LockError::Timeout);
            }
        }
    }
}

pub struct ZkLockGuard {
    zk: zookeeper::ZooKeeper,
    node_path: String,
}

impl ZkLockGuard {
    pub async fn release(self) -> Result<(), LockError> {
        self.zk.delete(&self.node_path, None).await?;
        Ok(())
    }
}

#[derive(Debug)]
pub enum ZkError {
    ConnectionError,
    OperationError(String),
}
```

**基于 etcd 的锁：**

```rust
/// etcd 分布式锁
///
/// 使用租约（lease）和事务实现

pub struct EtcdDistributedLock {
    client: etcd_client::Client,
    lease_ttl: i64,
}

impl EtcdDistributedLock {
    pub async fn new(endpoints: &[&str], lease_ttl: i64) -> Result<Self, etcd_client::Error> {
        let client = etcd_client::Client::connect(endpoints, None).await?;
        Ok(Self { client, lease_ttl })
    }

    /// 获取锁
    pub async fn acquire(&mut self, lock_name: &str) -> Result<EtcdLockGuard, LockError> {
        // 创建租约
        let lease = self.client.lease_grant(self.lease_ttl, None).await?;
        let lease_id = lease.id();

        let key = format!("/locks/{}", lock_name);
        let value = uuid::Uuid::new_v4().to_string();

        // 尝试获取锁（使用事务确保原子性）
        let txn = etcd_client::Txn::new()
            .when([
                etcd_client::Compare::version(&key, etcd_client::CompareOp::Equal, 0),
            ])
            .and_then([
                etcd_client::TxnOp::put(&key, &value, Some(etcd_client::PutOptions::new().with_lease(lease_id))),
            ])
            .or_else([]);

        let txn_response = self.client.txn(txn).await?;

        if txn_response.succeeded() {
            // 启动 keep alive
            let (mut keeper, mut stream) = self.client.lease_keep_alive(lease_id).await?;

            tokio::spawn(async move {
                loop {
                    tokio::time::sleep(Duration::from_secs(5)).await;
                    if keeper.keep_alive().await.is_err() {
                        break;
                    }
                }
            });

            Ok(EtcdLockGuard {
                client: self.client.clone(),
                key,
                lease_id,
            })
        } else {
            // 释放租约
            self.client.lease_revoke(lease_id).await.ok();
            Err(LockError::LockExists)
        }
    }
}

pub struct EtcdLockGuard {
    client: etcd_client::Client,
    key: String,
    lease_id: i64,
}

impl EtcdLockGuard {
    pub async fn release(mut self) -> Result<(), LockError> {
        // 删除 key
        self.client.delete(&self.key, None).await?;

        // 撤销租约
        self.client.lease_revoke(self.lease_id).await?;

        Ok(())
    }
}

#[derive(Debug)]
pub enum LockError {
    EtcdError(etcd_client::Error),
    LockExists,
    LockLost,
    Timeout,
    NodeLost,
}

impl From<etcd_client::Error> for LockError {
    fn from(e: etcd_client::Error) -> Self {
        LockError::EtcdError(e)
    }
}
```

**锁续期语义：**

```rust
/// 锁续约管理器
///
/// 自动续约以防止锁过期

pub struct LockRenewalManager {
    /// 续约间隔（应小于锁 TTL 的 1/3）
    renewal_interval: Duration,

    /// 续约中的锁
    renewing_locks: Arc<RwLock<HashMap<String, RenewalHandle>>>,
}

struct RenewalHandle {
    stop_tx: tokio::sync::mpsc::Sender<()>,
    task_handle: tokio::task::JoinHandle<()>,
}

impl LockRenewalManager {
    pub fn new(renewal_interval: Duration) -> Self {
        Self {
            renewal_interval,
            renewing_locks: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 开始续约
    pub async fn start_renewal<L: RenewableLock>(&self, lock: L, key: String)
    where
        L: Send + 'static,
    {
        let (stop_tx, mut stop_rx) = tokio::sync::mpsc::channel(1);
        let interval = self.renewal_interval;
        let locks = self.renewing_locks.clone();

        let task_handle = tokio::spawn(async move {
            let mut ticker = tokio::time::interval(interval);

            loop {
                tokio::select! {
                    _ = ticker.tick() => {
                        if let Err(e) = lock.renew().await {
                            tracing::error!("Lock renewal failed: {:?}", e);
                            break;
                        }
                    }
                    _ = stop_rx.recv() => {
                        break;
                    }
                }
            }

            // 从管理中移除
            locks.write().await.remove(&key);
        });

        let handle = RenewalHandle { stop_tx, task_handle };
        self.renewing_locks.write().await.insert(key, handle);
    }

    /// 停止续约
    pub async fn stop_renewal(&self, key: &str) {
        if let Some(handle) = self.renewing_locks.write().await.remove(key) {
            let _ = handle.stop_tx.send(()).await;
            handle.task_handle.abort();
        }
    }
}

#[async_trait]
pub trait RenewableLock: Send + Sync {
    async fn renew(&self) -> Result<(), RenewalError>;
}

#[derive(Debug)]
pub enum RenewalError {
    LockExpired,
    ConnectionError,
    Unknown,
}
```
