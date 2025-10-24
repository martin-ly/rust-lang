# Kafka 与 Pingora 集成实战指南

> **适用版本**: Rust 1.75+ (推荐 1.90+)  
> **更新日期**: 2025-10-24  
> **难度级别**: 中级到高级

本指南详细介绍如何在 Rust 中使用 Kafka 进行消息队列处理，以及使用 Pingora 构建高性能代理服务。

---

## 📊 目录

- [Kafka 与 Pingora 集成实战指南](#kafka-与-pingora-集成实战指南)
  - [📊 目录](#-目录)
  - [Kafka 完整实战](#kafka-完整实战)
    - [核心概念](#核心概念)
    - [快速开始](#快速开始)
    - [生产者详解](#生产者详解)
    - [消费者详解](#消费者详解)
    - [事务与幂等性](#事务与幂等性)
    - [性能优化](#性能优化)
    - [安全配置](#安全配置)
  - [Pingora 完整实战](#pingora-完整实战)
    - [架构原理](#架构原理)
    - [反向代理实现](#反向代理实现)
    - [负载均衡](#负载均衡)
    - [中间件开发](#中间件开发)
    - [](#)
  - [Pingora MVP 路线图（建议）](#pingora-mvp-路线图建议)
  - [常见问题与排查](#常见问题与排查)

---

## Kafka 完整实战

### 核心概念

**Kafka 架构基础**:

Kafka 是一个分布式流处理平台，由以下核心组件构成：

1. **Broker**: Kafka 服务器节点，存储消息
2. **Topic**: 消息主题，逻辑上的消息分类
3. **Partition**: Topic 的物理分区，实现并行处理
4. **Producer**: 消息生产者，发送消息到 Topic
5. **Consumer**: 消息消费者，从 Topic 读取消息
6. **Consumer Group**: 消费者组，实现负载均衡和故障转移

**分区与副本**:

```text
Topic: orders (3 partitions, replication-factor: 3)

Partition 0: [Leader: Broker-1] [Follower: Broker-2, Broker-3]
Partition 1: [Leader: Broker-2] [Follower: Broker-1, Broker-3]
Partition 2: [Leader: Broker-3] [Follower: Broker-1, Broker-2]
```

**消息顺序性保证**:

- 同一分区内的消息严格有序
- 跨分区无顺序保证
- 使用分区键 (partition key) 将相关消息路由到同一分区

---

### 快速开始

**环境准备**:

```bash
# Docker 启动 Kafka (包含 Zookeeper)
docker run -d --name zookeeper -p 2181:2181 zookeeper:3.8
docker run -d --name kafka -p 9092:9092 \
  -e KAFKA_ZOOKEEPER_CONNECT=host.docker.internal:2181 \
  -e KAFKA_ADVERTISED_LISTENERS=PLAINTEXT://localhost:9092 \
  -e KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR=1 \
  confluentinc/cp-kafka:7.5.0

# 创建测试 Topic
docker exec kafka kafka-topics --create \
  --topic test-topic \
  --bootstrap-server localhost:9092 \
  --partitions 3 \
  --replication-factor 1
```

**依赖配置**:

```toml
[dependencies]
rdkafka = { version = "0.36", features = ["cmake-build"] }
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
anyhow = "1"
tracing = "0.1"
```

**最简单的生产者**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use std::time::Duration;

async fn simple_producer() -> anyhow::Result<()> {
    // 创建生产者
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .create()?;

    // 发送消息
    let delivery_status = producer
        .send(
            FutureRecord::to("test-topic")
                .payload("Hello Kafka from Rust!")
                .key("key-1"),
            Duration::from_secs(0),
        )
        .await;

    match delivery_status {
        Ok(delivery) => println!("消息已发送: {:?}", delivery),
        Err((e, _)) => eprintln!("发送失败: {:?}", e),
    }

    Ok(())
}
```

**最简单的消费者**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;

async fn simple_consumer() -> anyhow::Result<()> {
    // 创建消费者
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "test-group")
        .set("auto.offset.reset", "earliest")
        .create()?;

    // 订阅 Topic
    consumer.subscribe(&["test-topic"])?;

    // 消费消息
    loop {
        match consumer.recv().await {
            Ok(message) => {
                let payload = match message.payload_view::<str>() {
                    Some(Ok(s)) => s,
                    Some(Err(_)) => "<invalid utf-8>",
                    None => "<empty>",
                };
                println!("收到消息: key={:?}, payload={}", message.key(), payload);
            }
            Err(e) => eprintln!("消费错误: {:?}", e),
        }
    }
}
```

---

### 生产者详解

**生产者配置最佳实践**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};

fn create_optimized_producer() -> anyhow::Result<FutureProducer> {
    let producer: FutureProducer = ClientConfig::new()
        // 基础配置
        .set("bootstrap.servers", "localhost:9092")
        .set("client.id", "rust-producer-01")
        
        // 可靠性配置
        .set("enable.idempotence", "true")  // 幂等性生产者
        .set("acks", "all")                  // 等待所有副本确认
        .set("retries", "10")                // 重试次数
        .set("max.in.flight.requests.per.connection", "5")
        
        // 性能配置
        .set("compression.type", "zstd")     // 压缩 (lz4/zstd/snappy)
        .set("batch.size", "32768")          // 批量大小 32KB
        .set("linger.ms", "10")              // 延迟发送 10ms
        .set("buffer.memory", "67108864")    // 缓冲区 64MB
        
        // 超时配置
        .set("request.timeout.ms", "30000")  // 请求超时 30s
        .set("message.timeout.ms", "300000") // 消息超时 5min
        
        .create()?;

    Ok(producer)
}
```

**批量发送与性能优化**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use std::time::Duration;
use tokio::time::Instant;

async fn batch_send_example(producer: &FutureProducer) -> anyhow::Result<()> {
    let start = Instant::now();
    let batch_size = 10000;
    
    // 并发发送（利用内部批处理）
    let mut handles = vec![];
    
    for i in 0..batch_size {
        let key = format!("key-{}", i);
        let value = format!("message-{}", i);
        
        let handle = producer.send(
            FutureRecord::to("test-topic")
                .key(&key)
                .payload(&value)
                .partition(i % 3), // 手动指定分区
            Duration::from_secs(0),
        );
        
        handles.push(handle);
    }
    
    // 等待所有消息发送完成
    for (i, handle) in handles.into_iter().enumerate() {
        match handle.await {
            Ok(_) => {},
            Err((e, _)) => eprintln!("消息 {} 发送失败: {:?}", i, e),
        }
    }
    
    let elapsed = start.elapsed();
    let throughput = batch_size as f64 / elapsed.as_secs_f64();
    println!("发送 {} 条消息，耗时 {:?}，吞吐量: {:.0} msg/s", 
             batch_size, elapsed, throughput);
    
    Ok(())
}
```

**自定义分区策略**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord, Partitioner};
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

// 使用一致性哈希进行分区
fn partition_by_user_id(user_id: &str, partition_count: i32) -> i32 {
    let mut hasher = DefaultHasher::new();
    user_id.hash(&mut hasher);
    (hasher.finish() % partition_count as u64) as i32
}

async fn send_with_custom_partition(
    producer: &FutureProducer,
    user_id: &str,
    message: &str,
) -> anyhow::Result<()> {
    let partition = partition_by_user_id(user_id, 3);
    
    producer.send(
        FutureRecord::to("user-events")
            .key(user_id)
            .payload(message)
            .partition(partition),
        Duration::from_secs(0),
    ).await
    .map_err(|(e, _)| e)?;
    
    Ok(())
}
```

**错误处理与重试**:

```rust
use rdkafka::error::KafkaError;
use std::time::Duration;
use tokio::time::sleep;

async fn send_with_retry(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
    max_retries: u32,
) -> anyhow::Result<()> {
    let mut retry_count = 0;
    let mut delay_ms = 100;
    
    loop {
        match producer.send(
            FutureRecord::to(topic)
                .key(key)
                .payload(payload),
            Duration::from_secs(5),
        ).await {
            Ok(_) => {
                if retry_count > 0 {
                    println!("重试 {} 次后成功", retry_count);
                }
                return Ok(());
            }
            Err((e, _)) => {
                retry_count += 1;
                if retry_count >= max_retries {
                    return Err(anyhow::anyhow!("发送失败，已重试 {} 次: {:?}", 
                                               retry_count, e));
                }
                
                println!("发送失败，{} ms 后重试 ({}/{}): {:?}", 
                        delay_ms, retry_count, max_retries, e);
                sleep(Duration::from_millis(delay_ms)).await;
                delay_ms = (delay_ms * 2).min(5000); // 指数退避，最大5秒
            }
        }
    }
}
```

---

### 消费者详解

**消费者配置最佳实践**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::StreamConsumer;

fn create_optimized_consumer(group_id: &str) -> anyhow::Result<StreamConsumer> {
    let consumer: StreamConsumer = ClientConfig::new()
        // 基础配置
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", group_id)
        .set("client.id", "rust-consumer-01")
        
        // 偏移量管理
        .set("enable.auto.commit", "false")  // 手动提交偏移量
        .set("auto.offset.reset", "earliest") // earliest/latest/none
        
        // 性能配置
        .set("fetch.min.bytes", "10240")     // 最小拉取 10KB
        .set("fetch.max.wait.ms", "500")     // 最大等待 500ms
        .set("max.partition.fetch.bytes", "1048576") // 单分区最大 1MB
        
        // 会话与心跳
        .set("session.timeout.ms", "10000")  // 会话超时 10s
        .set("heartbeat.interval.ms", "3000") // 心跳间隔 3s
        .set("max.poll.interval.ms", "300000") // 最大轮询间隔 5min
        
        .create()?;

    Ok(consumer)
}
```

**手动提交偏移量**:

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;
use rdkafka::TopicPartitionList;

async fn consume_with_manual_commit(consumer: StreamConsumer) -> anyhow::Result<()> {
    consumer.subscribe(&["orders"])?;
    
    let mut message_count = 0;
    let commit_interval = 100; // 每100条消息提交一次
    
    loop {
        match consumer.recv().await {
            Ok(message) => {
                // 处理消息
                process_message(&message)?;
                
                message_count += 1;
                
                // 定期提交偏移量
                if message_count % commit_interval == 0 {
                    consumer.commit_message(&message, rdkafka::consumer::CommitMode::Async)?;
                    println!("已提交偏移量: partition={}, offset={}", 
                            message.partition(), message.offset());
                }
            }
            Err(e) => {
                eprintln!("消费错误: {:?}", e);
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        }
    }
}

fn process_message(message: &rdkafka::message::BorrowedMessage) -> anyhow::Result<()> {
    let payload = message.payload_view::<str>()
        .ok_or(anyhow::anyhow!("空消息"))?
        .map_err(|_| anyhow::anyhow!("UTF-8 解析失败"))?;
    
    println!("处理消息: {}", payload);
    
    // 业务逻辑处理
    // ...
    
    Ok(())
}
```

**并发消费模式**:

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::Message;
use tokio::sync::Semaphore;
use std::sync::Arc;

async fn concurrent_consumer(
    consumer: StreamConsumer,
    concurrency: usize,
) -> anyhow::Result<()> {
    consumer.subscribe(&["orders"])?;
    
    let semaphore = Arc::new(Semaphore::new(concurrency));
    
    loop {
        match consumer.recv().await {
            Ok(message) => {
                let permit = semaphore.clone().acquire_owned().await?;
                let payload = message.payload().unwrap().to_vec();
                
                // 并发处理消息
                tokio::spawn(async move {
                    if let Err(e) = process_message_async(&payload).await {
                        eprintln!("处理失败: {:?}", e);
                    }
                    drop(permit); // 释放信号量
                });
            }
            Err(e) => {
                eprintln!("消费错误: {:?}", e);
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        }
    }
}

async fn process_message_async(payload: &[u8]) -> anyhow::Result<()> {
    // 模拟异步处理
    tokio::time::sleep(Duration::from_millis(100)).await;
    println!("处理消息: {} bytes", payload.len());
    Ok(())
}
```

---

### 事务与幂等性

**幂等性生产者**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};

async fn idempotent_producer_example() -> anyhow::Result<()> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("enable.idempotence", "true")  // 启用幂等性
        .set("acks", "all")
        .set("max.in.flight.requests.per.connection", "5")
        .create()?;
    
    // 即使网络抖动导致重试，也不会产生重复消息
    for i in 0..1000 {
        producer.send(
            FutureRecord::to("orders")
                .key(&format!("order-{}", i))
                .payload(&format!("amount:{}", i * 100)),
            Duration::from_secs(5),
        ).await.map_err(|(e, _)| e)?;
    }
    
    println!("所有消息已发送（无重复）");
    Ok(())
}
```

**事务性生产者（Exactly-Once 语义）**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord, Transaction};

async fn transactional_producer_example() -> anyhow::Result<()> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("transactional.id", "my-transactional-id-001")
        .set("enable.idempotence", "true")
        .create()?;
    
    // 初始化事务
    producer.init_transactions(Duration::from_secs(30))?;
    
    // 开始事务
    producer.begin_transaction()?;
    
    match send_batch(&producer).await {
        Ok(_) => {
            // 提交事务
            producer.commit_transaction(Duration::from_secs(30))?;
            println!("事务提交成功");
        }
        Err(e) => {
            // 回滚事务
            producer.abort_transaction(Duration::from_secs(30))?;
            eprintln!("事务回滚: {:?}", e);
        }
    }
    
    Ok(())
}

async fn send_batch(producer: &FutureProducer) -> anyhow::Result<()> {
    for i in 0..10 {
        producer.send(
            FutureRecord::to("orders")
                .key(&format!("order-{}", i))
                .payload(&format!("amount:{}", i * 100)),
            Duration::from_secs(5),
        ).await.map_err(|(e, _)| e)?;
    }
    Ok(())
}
```

---

### 性能优化

**生产者性能调优**:

```rust
// 高吞吐量配置
let high_throughput_producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("enable.idempotence", "true")
    .set("acks", "1")  // 只等待 leader 确认，降低延迟
    .set("compression.type", "lz4")  // lz4 压缩速度快
    .set("batch.size", "524288")  // 增大批量 512KB
    .set("linger.ms", "100")  // 增加等待时间，提升批处理
    .set("buffer.memory", "134217728")  // 缓冲区 128MB
    .create()?;

// 低延迟配置
let low_latency_producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("acks", "1")
    .set("compression.type", "none")  // 不压缩
    .set("linger.ms", "0")  // 立即发送
    .set("batch.size", "16384")  // 小批量
    .create()?;
```

**消费者性能调优**:

```rust
// 高吞吐量消费者
let high_throughput_consumer: StreamConsumer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("group.id", "high-throughput-group")
    .set("fetch.min.bytes", "102400")  // 最小 100KB
    .set("fetch.max.wait.ms", "1000")  // 等待 1s
    .set("max.partition.fetch.bytes", "10485760")  // 单分区 10MB
    .create()?;
```

**性能监控指标**:

```rust
use rdkafka::statistics::Statistics;

// 启用统计信息
let producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("statistics.interval.ms", "5000")  // 每5秒统计一次
    .create()?;

// 在实际应用中，需要实现统计回调来收集这些指标
// - msg_cnt: 发送的消息数
// - msg_size: 消息总大小
// - tx: 发送字节数
// - txmsgs: 发送消息数
// - queue: 队列中的消息数
```

---

### 安全配置

**TLS/SSL 配置**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::FutureProducer;

async fn create_secure_producer() -> anyhow::Result<FutureProducer> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "kafka.example.com:9093")
        .set("security.protocol", "SSL")
        
        // CA 证书
        .set("ssl.ca.location", "/path/to/ca-cert.pem")
        
        // 客户端证书（双向 TLS）
        .set("ssl.certificate.location", "/path/to/client-cert.pem")
        .set("ssl.key.location", "/path/to/client-key.pem")
        .set("ssl.key.password", "key-password")
        
        .create()?;
    
    Ok(producer)
}
```

**SASL 认证**:

```rust
// SASL/PLAIN
let sasl_plain_producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "kafka.example.com:9093")
    .set("security.protocol", "SASL_SSL")
    .set("sasl.mechanisms", "PLAIN")
    .set("sasl.username", "your-username")
    .set("sasl.password", "your-password")
    .set("ssl.ca.location", "/path/to/ca-cert.pem")
    .create()?;

// SASL/SCRAM-SHA-256
let sasl_scram_producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "kafka.example.com:9093")
    .set("security.protocol", "SASL_SSL")
    .set("sasl.mechanisms", "SCRAM-SHA-256")
    .set("sasl.username", "your-username")
    .set("sasl.password", "your-password")
    .create()?;
```

---

## Pingora 完整实战

### 架构原理

**Pingora 简介**:

Pingora 是 Cloudflare 开源的高性能 HTTP 代理框架，用 Rust 编写，具有以下特点：

- **零拷贝**: 最小化内存分配和拷贝
- **异步架构**: 基于 Tokio 的完全异步
- **模块化设计**: 可插拔的中间件系统
- **高性能**: 处理百万级并发连接

**核心组件**:

1. **Server**: HTTP 服务器，监听端口
2. **Proxy**: 代理逻辑，处理请求转发
3. **Upstream**: 上游服务器管理
4. **LoadBalancer**: 负载均衡器
5. **HealthCheck**: 健康检查

---

### 反向代理实现

**最简单的反向代理**:

```rust
use pingora::prelude::*;
use async_trait::async_trait;

pub struct MyProxy {
    upstream: String,
}

#[async_trait]
impl ProxyHttp for MyProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream.parse()?,
            false,  // TLS
            "".to_string(),
        ));
        Ok(peer)
    }
}

#[tokio::main]
async fn main() {
    let mut server = Server::new(None).unwrap();
    server.bootstrap();
    
    let proxy = MyProxy {
        upstream: "127.0.0.1:8080".to_string(),
    };
    
    let mut service = HttpProxy::new(proxy, None);
    service.add_tcp("0.0.0.0:6188");
    
    server.add_service(service);
    server.run_forever();
}
```

**带路径路由的反向代理**:

```rust
use pingora::prelude::*;
use async_trait::async_trait;

pub struct RoutingProxy;

#[async_trait]
impl ProxyHttp for RoutingProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let path = session.req_header().uri.path();
        
        let upstream = if path.starts_with("/api") {
            "127.0.0.1:8080"  // API 服务
        } else if path.starts_with("/static") {
            "127.0.0.1:8081"  // 静态资源服务
        } else {
            "127.0.0.1:8082"  // 默认服务
        };
        
        let peer = Box::new(HttpPeer::new(
            upstream.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<bool> {
        // 添加自定义 Header
        session
            .req_header_mut()
            .insert_header("X-Proxy", "Pingora")?;
        
        Ok(false)
    }
}
```

---

### 负载均衡

**轮询 (Round Robin) 负载均衡**:

```rust
use pingora::lb::{LoadBalancer, RoundRobin, Backend};
use pingora::prelude::*;
use async_trait::async_trait;
use std::sync::Arc;

pub struct LoadBalancedProxy {
    lb: Arc<LoadBalancer<RoundRobin>>,
}

impl LoadBalancedProxy {
    fn new() -> Self {
        let upstreams = vec![
            Backend::new("127.0.0.1:8080").unwrap(),
            Backend::new("127.0.0.1:8081").unwrap(),
            Backend::new("127.0.0.1:8082").unwrap(),
        ];
        
        let backends = Arc::new(LoadBalancer::from_backends(upstreams));
        
        Self { lb: backends }
    }
}

#[async_trait]
impl ProxyHttp for LoadBalancedProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let upstream = self.lb
            .select(b"", 256)  // 选择一个后端
            .unwrap();
        
        let peer = Box::new(HttpPeer::new(
            upstream.addr,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

**健康检查**:

```rust
use pingora::protocols::l4::socket::SocketAddr;
use pingora::lb::{Backend, health_check};
use std::time::Duration;

async fn setup_health_checks(backends: Vec<Backend>) {
    let check_freq = Duration::from_secs(10);
    
    for backend in backends {
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(check_freq).await;
                
                match health_check::http_health_check(&backend.addr, "/health").await {
                    Ok(true) => {
                        println!("后端 {} 健康", backend.addr);
                        // 标记为健康
                    }
                    _ => {
                        println!("后端 {} 不健康", backend.addr);
                        // 标记为不健康，从负载均衡中移除
                    }
                }
            }
        });
    }
}
```

---

### 中间件开发

**限流中间件**:

```rust
use pingora::prelude::*;
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

pub struct RateLimitMiddleware {
    // IP -> (请求数, 窗口开始时间)
    counters: Arc<Mutex<HashMap<String, (u32, Instant)>>>,
    max_requests: u32,
    window: Duration,
}

impl RateLimitMiddleware {
    fn new(max_requests: u32, window: Duration) -> Self {
        Self {
            counters: Arc::new(Mutex::new(HashMap::new())),
            max_requests,
            window,
        }
    }
    
    fn check_rate_limit(&self, client_ip: &str) -> bool {
        let mut counters = self.counters.lock().unwrap();
        let now = Instant::now();
        
        let entry = counters.entry(client_ip.to_string())
            .or_insert((0, now));
        
        // 检查窗口是否过期
        if now.duration_since(entry.1) > self.window {
            entry.0 = 0;
            entry.1 = now;
        }
        
        entry.0 += 1;
        entry.0 <= self.max_requests
    }
}

#[async_trait]
impl ProxyHttp for RateLimitMiddleware {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<bool> {
        let client_ip = session.client_addr()
            .map(|addr| addr.to_string())
            .unwrap_or_else(|| "unknown".to_string());
        
        if !self.check_rate_limit(&client_ip) {
            // 返回 429 Too Many Requests
            let resp = ResponseHeader::build(429, None)?;
            session.write_response_header(Box::new(resp)).await?;
            return Ok(true);  // 中断请求
        }
        
        Ok(false)  // 继续处理
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            "127.0.0.1:8080".parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

**熔断中间件**:

```rust
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

pub struct CircuitBreaker {
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    last_failure_time: Arc<AtomicU64>,
    
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    fn new(failure_threshold: u32, success_threshold: u32, timeout: Duration) -> Self {
        Self {
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
            last_failure_time: Arc::new(AtomicU64::new(0)),
            failure_threshold,
            success_threshold,
            timeout,
        }
    }
    
    fn is_open(&self) -> bool {
        let failures = self.failure_count.load(Ordering::Relaxed);
        if failures < self.failure_threshold {
            return false;
        }
        
        let last_fail = self.last_failure_time.load(Ordering::Relaxed);
        let now = Instant::now().duration_since(Instant::now()).as_secs();
        
        now - last_fail < self.timeout.as_secs()
    }
    
    fn record_success(&self) {
        self.success_count.fetch_add(1, Ordering::Relaxed);
        
        if self.success_count.load(Ordering::Relaxed) >= self.success_threshold {
            // 关闭熔断器
            self.failure_count.store(0, Ordering::Relaxed);
            self.success_count.store(0, Ordering::Relaxed);
        }
    }
    
    fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        let now = Instant::now().duration_since(Instant::now()).as_secs();
        self.last_failure_time.store(now, Ordering::Relaxed);
    }
}
```

---

###

## Pingora MVP 路线图（建议）

- 阶段 1：最小反代
  - 监听地址、静态上游、基础超时（连接/请求/上游）

- 阶段 2：中间件与路由
  - 可插拔中间件：限流、重试、熔断、Tracing
  - 路由：基于前缀/Host/权重；健康检查

- 阶段 3：TLS 与安全
  - 终止 TLS（SNI）、上游 TLS、ACL
  - 指标：QPS/P95/P99、上游可用率

## 常见问题与排查

- Kafka 无法连接：
  - 检查 `bootstrap.servers` 可达性与安全配置；查看 broker 日志
  - Windows 下确认 `librdkafka` 安装与动态库路径（`PATH`）
- 消费无消息：
  - 检查 `group.id`、`auto.offset.reset`，以及主题/分区权限
- Pingora 502/超时：
  - 检查上游可达性与超时设置；查看 CPU 与连接数限制

> 当你提供明确的 MVP 需求（主题数/分区、SASL/TLS、位点策略、代理路由规则等），我将据此优先实现并提供端到端示例。
