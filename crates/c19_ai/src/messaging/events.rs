//! 消息事件模块
//! 
//! 定义消息系统的事件类型

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 消息系统事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Event {
    /// 队列创建事件
    QueueCreated {
        queue_id: String,
        queue_name: String,
        created_at: DateTime<Utc>,
    },
    /// 队列删除事件
    QueueDeleted {
        queue_id: String,
        queue_name: String,
        deleted_at: DateTime<Utc>,
    },
    /// 消息发布事件
    MessagePublished {
        message_id: String,
        queue_id: String,
        published_at: DateTime<Utc>,
    },
    /// 消息处理事件
    MessageProcessed {
        message_id: String,
        queue_id: String,
        processed_at: DateTime<Utc>,
        success: bool,
        error: Option<String>,
    },
    /// 订阅创建事件
    SubscriptionCreated {
        subscription_id: String,
        queue_id: String,
        consumer_id: String,
        created_at: DateTime<Utc>,
    },
    /// 订阅取消事件
    SubscriptionCancelled {
        subscription_id: String,
        queue_id: String,
        cancelled_at: DateTime<Utc>,
    },
    /// 消费者连接事件
    ConsumerConnected {
        consumer_id: String,
        queue_id: String,
        connected_at: DateTime<Utc>,
    },
    /// 消费者断开连接事件
    ConsumerDisconnected {
        consumer_id: String,
        queue_id: String,
        disconnected_at: DateTime<Utc>,
    },
    /// 生产者连接事件
    ProducerConnected {
        producer_id: String,
        queue_id: String,
        connected_at: DateTime<Utc>,
    },
    /// 生产者断开连接事件
    ProducerDisconnected {
        producer_id: String,
        queue_id: String,
        disconnected_at: DateTime<Utc>,
    },
    /// 错误事件
    Error {
        error_type: String,
        error_message: String,
        occurred_at: DateTime<Utc>,
        context: Option<serde_json::Value>,
    },
}

impl Event {
    /// 获取事件类型
    pub fn event_type(&self) -> &'static str {
        match self {
            Event::QueueCreated { .. } => "queue_created",
            Event::QueueDeleted { .. } => "queue_deleted",
            Event::MessagePublished { .. } => "message_published",
            Event::MessageProcessed { .. } => "message_processed",
            Event::SubscriptionCreated { .. } => "subscription_created",
            Event::SubscriptionCancelled { .. } => "subscription_cancelled",
            Event::ConsumerConnected { .. } => "consumer_connected",
            Event::ConsumerDisconnected { .. } => "consumer_disconnected",
            Event::ProducerConnected { .. } => "producer_connected",
            Event::ProducerDisconnected { .. } => "producer_disconnected",
            Event::Error { .. } => "error",
        }
    }

    /// 获取事件时间戳
    pub fn timestamp(&self) -> DateTime<Utc> {
        match self {
            Event::QueueCreated { created_at, .. } => *created_at,
            Event::QueueDeleted { deleted_at, .. } => *deleted_at,
            Event::MessagePublished { published_at, .. } => *published_at,
            Event::MessageProcessed { processed_at, .. } => *processed_at,
            Event::SubscriptionCreated { created_at, .. } => *created_at,
            Event::SubscriptionCancelled { cancelled_at, .. } => *cancelled_at,
            Event::ConsumerConnected { connected_at, .. } => *connected_at,
            Event::ConsumerDisconnected { disconnected_at, .. } => *disconnected_at,
            Event::ProducerConnected { connected_at, .. } => *connected_at,
            Event::ProducerDisconnected { disconnected_at, .. } => *disconnected_at,
            Event::Error { occurred_at, .. } => *occurred_at,
        }
    }

    /// 序列化为JSON
    pub fn to_json(&self) -> anyhow::Result<String> {
        Ok(serde_json::to_string(self)?)
    }

    /// 从JSON反序列化
    pub fn from_json(json: &str) -> anyhow::Result<Self> {
        Ok(serde_json::from_str(json)?)
    }
}