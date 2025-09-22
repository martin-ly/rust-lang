//! 消息队列演示程序
//!
//! 展示Kafka和NATS消息队列的使用方法

use std::collections::HashMap;
use std::time::Duration;
use tracing::{info, error};

use c13_microservice::{
    messaging::{
        KafkaManager, KafkaProducerConfig, KafkaConsumerConfig, Acks, Compression,
        NatsManager, NatsConfig,
        Message, MessageHandler,
    },
};

/// 示例消息处理器
struct DemoMessageHandler {
    name: String,
}

impl DemoMessageHandler {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl MessageHandler for DemoMessageHandler {
    fn handle(&self, message: Message) -> Result<(), Box<dyn std::error::Error>> {
        info!("[{}] 收到消息: ID={}, 主题={}, 大小={} bytes", 
              self.name, message.id, message.topic, message.payload.len());
        
        // 模拟消息处理
        std::thread::sleep(Duration::from_millis(100));
        
        info!("[{}] 消息处理完成", self.name);
        Ok(())
    }
}

/// Kafka演示
async fn demo_kafka() -> std::result::Result<(), Box<dyn std::error::Error>> {
    info!("=== Kafka 消息队列演示 ===");
    
    // 创建Kafka管理器
    let mut kafka_manager = KafkaManager::new();
    
    // 配置生产者
    let producer_config = KafkaProducerConfig {
        brokers: vec!["localhost:9092".to_string()],
        client_id: Some("demo-producer".to_string()),
        acks: Acks::All,
        retries: 3,
        batch_size: 16384,
        linger: Duration::from_millis(5),
        compression: Compression::Gzip,
    };
    
    // 配置消费者
    let consumer_config = KafkaConsumerConfig {
        brokers: vec!["localhost:9092".to_string()],
        group_id: "demo-consumer-group".to_string(),
        client_id: Some("demo-consumer".to_string()),
        ..Default::default()
    };
    
    // 添加组件
    kafka_manager.add_producer(producer_config);
    kafka_manager.add_consumer(consumer_config);
    kafka_manager.add_admin(vec!["localhost:9092".to_string()]);
    
    // 连接所有组件
    kafka_manager.connect_all().await?;
    
    // 创建主题
    kafka_manager.admin.as_ref().unwrap()
        .create_topic("demo-topic", 3, 1).await?;
    
    // 发布消息
    let messages = vec![
        (Some(b"key1".to_vec()), b"Hello Kafka 1".to_vec(), None::<HashMap<String, Vec<u8>>>),
        (Some(b"key2".to_vec()), b"Hello Kafka 2".to_vec(), None::<HashMap<String, Vec<u8>>>),
        (Some(b"key3".to_vec()), b"Hello Kafka 3".to_vec(), None::<HashMap<String, Vec<u8>>>),
    ];
    
    let mut headers = HashMap::new();
    headers.insert("content-type".to_string(), b"application/json".to_vec());
    
    for (key, payload, _) in messages {
        kafka_manager.publish_message("demo-topic", key.as_deref(), &payload, Some(headers.clone())).await?;
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    info!("Kafka消息发布完成");
    
    // 列出主题
    let topics = kafka_manager.admin.as_ref().unwrap().list_topics().await?;
    info!("Kafka主题列表: {:?}", topics);
    
    Ok(())
}

/// NATS演示
async fn demo_nats() -> std::result::Result<(), Box<dyn std::error::Error>> {
    info!("=== NATS 消息队列演示 ===");
    
    // 创建NATS管理器
    let mut nats_manager = NatsManager::new();
    
    // 配置NATS客户端
    let nats_config = NatsConfig {
        url: "nats://localhost:4222".to_string(),
        name: Some("demo-client".to_string()),
        ..Default::default()
    };
    
    // 添加客户端
    nats_manager.add_client(nats_config);
    
    // 连接
    nats_manager.connect_all().await?;
    
    // 发布消息
    let payloads = vec![
        b"Hello NATS 1".to_vec(),
        b"Hello NATS 2".to_vec(),
        b"Hello NATS 3".to_vec(),
    ];
    
    for (i, payload) in payloads.iter().enumerate() {
        let subject = format!("demo.subject.{}", i);
        nats_manager.publish_message(&subject, payload, None).await?;
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    info!("NATS消息发布完成");
    
    // 发送请求-响应消息
    let request_payload = b"request data";
    let response = nats_manager.send_request("demo.request", request_payload, Some(Duration::from_secs(5))).await?;
    info!("收到NATS响应: {} bytes", response.len());
    
    // 订阅消息
    let handler = DemoMessageHandler::new("NATS订阅者".to_string());
    let _subscription = nats_manager.subscribe_topic("demo.subject.*", handler).await?;
    
    // 获取统计信息
    if let Some(stats) = nats_manager.get_stats() {
        info!("NATS统计信息: 入站消息={}, 出站消息={}, 订阅数={}", 
              stats.in_msgs, stats.out_msgs, stats.subscriptions);
    }
    
    Ok(())
}

/// 性能测试
async fn performance_test() -> std::result::Result<(), Box<dyn std::error::Error>> {
    info!("=== Kafka性能测试 ===");
    
    let mut kafka_manager = KafkaManager::new();
    
    let producer_config = KafkaProducerConfig {
        brokers: vec!["localhost:9092".to_string()],
        ..Default::default()
    };
    
    kafka_manager.add_producer(producer_config);
    kafka_manager.connect_all().await?;
    
    let message_count = 100;
    let payload_size = 1024; // 1KB
    let payload = vec![0u8; payload_size];
    
    // 测试发布性能
    let start = std::time::Instant::now();
    
    for i in 0..message_count {
        let topic = format!("perf.test.{}", i);
        if let Err(e) = kafka_manager.publish_message(&topic, Some(b"key"), &payload, None).await {
            error!("发布消息失败: {}", e);
        }
        
        if i % 10 == 0 {
            info!("已发布 {} 条消息", i);
        }
    }
    
    let duration = start.elapsed();
    let throughput = message_count as f64 / duration.as_secs_f64();
    
    info!("性能测试结果:");
    info!("  消息数量: {}", message_count);
    info!("  消息大小: {} bytes", payload_size);
    info!("  总耗时: {:?}", duration);
    info!("  吞吐量: {:.2} 消息/秒", throughput);
    info!("  带宽: {:.2} MB/s", (message_count * payload_size) as f64 / duration.as_secs_f64() / 1024.0 / 1024.0);
    
    Ok(())
}

#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    info!("开始消息队列演示");
    
    // 运行各种演示
    if let Err(e) = demo_kafka().await {
        error!("Kafka演示失败: {}", e);
    }
    
    if let Err(e) = demo_nats().await {
        error!("NATS演示失败: {}", e);
    }
    
    if let Err(e) = performance_test().await {
        error!("性能测试失败: {}", e);
    }
    
    info!("消息队列演示完成");
    Ok(())
}