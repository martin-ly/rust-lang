//! 高级消息队列示例
//!
//! 展示如何使用多种消息队列系统进行消息发布和订阅。

use c13_microservice::messaging::{Message, MessageHandler, MessageQueueManager};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{error, info, warn};

/// 用户事件消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserEvent {
    pub event_type: String,
    pub user_id: String,
    pub data: HashMap<String, String>,
    pub timestamp: u64,
}

impl UserEvent {
    pub fn new(event_type: String, user_id: String) -> Self {
        Self {
            event_type,
            user_id,
            data: HashMap::new(),
            timestamp: c13_microservice::utils::current_timestamp_secs(),
        }
    }

    pub fn with_data(mut self, key: String, value: String) -> Self {
        self.data.insert(key, value);
        self
    }
}

/// 用户事件处理器
pub struct UserEventHandler {
    pub name: String,
}

#[async_trait::async_trait]
impl MessageHandler for UserEventHandler {
    fn handle(&self, message: Message) -> Result<(), Box<dyn std::error::Error>> {
        info!(
            "[{}] 处理消息: ID={}, Topic={}",
            self.name, message.id, message.topic
        );

        // 解析消息内容
        if let Ok(user_event) = serde_json::from_slice::<UserEvent>(&message.payload) {
            info!("[{}] 用户事件: {:?}", self.name, user_event);

            // 根据事件类型处理
            match user_event.event_type.as_str() {
                "user_created" => {
                    info!("[{}] 处理用户创建事件: {}", self.name, user_event.user_id);
                }
                "user_updated" => {
                    info!("[{}] 处理用户更新事件: {}", self.name, user_event.user_id);
                }
                "user_deleted" => {
                    info!("[{}] 处理用户删除事件: {}", self.name, user_event.user_id);
                }
                _ => {
                    warn!("[{}] 未知事件类型: {}", self.name, user_event.event_type);
                }
            }
        } else {
            warn!("[{}] 无法解析消息内容", self.name);
        }

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动高级消息队列示例");

    // 创建消息队列管理器
    let mut mq_manager = MessageQueueManager::new();

    // 添加不同的消息队列
    mq_manager.add_redis("redis://localhost:6379".to_string());
    mq_manager.add_rabbitmq("amqp://localhost:5672".to_string());
    mq_manager.add_kafka(vec!["localhost:9092".to_string()]);

    // 连接所有消息队列
    info!("连接消息队列...");
    mq_manager.connect_all().await?;

    // 创建用户事件
    let user_events = vec![
        UserEvent::new("user_created".to_string(), "user_001".to_string())
            .with_data("name".to_string(), "张三".to_string())
            .with_data("email".to_string(), "zhangsan@example.com".to_string()),
        UserEvent::new("user_updated".to_string(), "user_001".to_string())
            .with_data("name".to_string(), "张三（更新）".to_string()),
        UserEvent::new("user_deleted".to_string(), "user_001".to_string()),
    ];

    // 发布消息到所有队列
    for (i, event) in user_events.iter().enumerate() {
        let payload = serde_json::to_vec(event)?;
        let message = Message::new("user_events".to_string(), payload)
            .with_header("event_id".to_string(), format!("event_{}", i))
            .with_header("source".to_string(), "microservice".to_string());

        info!("发布消息 {} 到所有队列", message.id);

        // 发布到所有消息队列
        mq_manager
            .publish_to_all(&message.topic, &message.payload)
            .await?;

        // 模拟处理延迟
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }

    // 创建消息处理器
    let handler1 = UserEventHandler {
        name: "处理器1".to_string(),
    };
    let handler2 = UserEventHandler {
        name: "处理器2".to_string(),
    };

    info!("创建消息处理器完成");

    // 模拟消息处理
    info!("模拟消息处理...");
    for (i, event) in user_events.iter().enumerate() {
        let payload = serde_json::to_vec(event)?;
        let message = Message::new("user_events".to_string(), payload)
            .with_header("event_id".to_string(), format!("event_{}", i));

        // 使用不同的处理器处理消息
        let handler = if i % 2 == 0 { &handler1 } else { &handler2 };
        if let Err(e) = handler.handle(message) {
            error!("消息处理失败: {}", e);
        }

        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    }

    info!("高级消息队列示例完成");
    Ok(())
}
