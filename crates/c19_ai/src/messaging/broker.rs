//! 消息代理模块
//! 
//! 提供消息路由和分发功能

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

use super::manager::{Message, MessagePriority};

/// 消息代理
#[derive(Debug)]
pub struct MessageBroker {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    routes: Arc<RwLock<HashMap<String, Vec<String>>>>, // topic -> queue_names
    message_count: Arc<RwLock<u64>>,
    error_count: Arc<RwLock<u64>>,
}

impl MessageBroker {
    /// 创建新的消息代理
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            routes: Arc::new(RwLock::new(HashMap::new())),
            message_count: Arc::new(RwLock::new(0)),
            error_count: Arc::new(RwLock::new(0)),
        }
    }

    /// 添加路由规则
    pub async fn add_route(&self, topic: String, queue_name: String) {
        let mut routes = self.routes.write().await;
        routes.entry(topic).or_insert_with(Vec::new).push(queue_name);
    }

    /// 移除路由规则
    pub async fn remove_route(&self, topic: &str, queue_name: &str) {
        let mut routes = self.routes.write().await;
        if let Some(queues) = routes.get_mut(topic) {
            queues.retain(|q| q != queue_name);
            if queues.is_empty() {
                routes.remove(topic);
            }
        }
    }

    /// 获取路由
    pub async fn get_routes(&self, topic: &str) -> Vec<String> {
        let routes = self.routes.read().await;
        routes.get(topic).cloned().unwrap_or_default()
    }

    /// 路由消息
    pub async fn route_message(&self, message: Message) -> anyhow::Result<Vec<String>> {
        let routes = self.routes.read().await;
        let queue_names = routes.get(&message.topic).cloned().unwrap_or_default();

        if queue_names.is_empty() {
            tracing::warn!("No routes found for topic: {}", message.topic);
            return Ok(Vec::new());
        }

        // TODO: 实现实际的消息路由逻辑
        tracing::info!("Routing message {} to {} queues", message.id, queue_names.len());

        // 更新消息计数
        {
            let mut count = self.message_count.write().await;
            *count += 1;
        }

        Ok(queue_names)
    }

    /// 获取消息计数
    pub async fn get_message_count(&self) -> u64 {
        let count = self.message_count.read().await;
        *count
    }

    /// 获取错误计数
    pub async fn get_error_count(&self) -> u64 {
        let count = self.error_count.write().await;
        *count
    }

    /// 获取所有路由
    pub async fn get_all_routes(&self) -> HashMap<String, Vec<String>> {
        let routes = self.routes.read().await;
        routes.clone()
    }
}