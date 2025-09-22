//! 简单的消息队列测试

use tracing::{info, error};

use c13_microservice::messaging::{
    KafkaManager, KafkaProducerConfig, Acks, Compression,
    Message, MessageHandler,
};

#[allow(dead_code)]
struct TestHandler;

impl MessageHandler for TestHandler {
    fn handle(&self, message: Message) -> Result<(), Box<dyn std::error::Error>> {
        println!("收到消息: {:?}", message);
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("开始简单消息队列测试");
    info!("开始简单消息队列测试");
    
    // 创建Kafka管理器
    let mut kafka_manager = KafkaManager::new();
    
    let producer_config = KafkaProducerConfig {
        brokers: vec!["localhost:9092".to_string()],
        client_id: Some("test-producer".to_string()),
        acks: Acks::All,
        retries: 3,
        batch_size: 16384,
        linger: std::time::Duration::from_millis(5),
        compression: Compression::None,
    };
    
    kafka_manager.add_producer(producer_config);
    
    // 连接
    match kafka_manager.connect_all().await {
        Ok(_) => {
            println!("Kafka连接成功");
            info!("Kafka连接成功");
        }
        Err(e) => {
            println!("Kafka连接失败: {}", e);
            error!("Kafka连接失败: {}", e);
            return Ok(());
        }
    }
    
    // 发布消息
    let payload = b"Hello World";
    match kafka_manager.publish_message("test-topic", Some(b"key"), payload, None).await {
        Ok(_) => {
            println!("消息发布成功");
            info!("消息发布成功");
        }
        Err(e) => {
            println!("消息发布失败: {}", e);
            error!("消息发布失败: {}", e);
        }
    }
    
    println!("测试完成");
    info!("测试完成");
    Ok(())
}
