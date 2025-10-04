/// 观察者模式 (Observer Pattern)
///
/// 定义对象间的一对多依赖关系，当一个对象状态改变时，所有依赖它的对象都会得到通知并自动更新
///
/// # 应用场景
///
/// - 系统状态变更通知
/// - 事件驱动架构
/// - 实时监控和告警
/// - 日志聚合和分发

use crate::prelude::*;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// 观察者 trait
#[async_trait::async_trait]
pub trait Observer: Send + Sync {
    /// 接收事件通知
    async fn on_event(&self, event: &Event) -> Result<()>;
    
    /// 观察者ID
    fn id(&self) -> &str;
    
    /// 观察者优先级（数字越小优先级越高）
    fn priority(&self) -> u32 {
        100
    }
}

/// 主题/被观察者 trait
#[async_trait::async_trait]
pub trait Subject: Send + Sync {
    /// 添加观察者
    async fn attach(&self, observer: Arc<dyn Observer>) -> Result<()>;
    
    /// 移除观察者
    async fn detach(&self, observer_id: &str) -> Result<()>;
    
    /// 通知所有观察者
    async fn notify(&self, event: &Event) -> Result<()>;
}

/// 事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    /// 事件ID
    pub id: String,
    /// 事件类型
    pub event_type: EventType,
    /// 事件源
    pub source: String,
    /// 事件数据
    pub data: serde_json::Value,
    /// 事件时间戳
    pub timestamp: u64,
    /// 事件严重性
    pub severity: EventSeverity,
}

/// 事件类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum EventType {
    /// 系统状态变更
    StateChange,
    /// 错误事件
    Error,
    /// 警告事件
    Warning,
    /// 性能指标
    Metric,
    /// 健康检查
    HealthCheck,
    /// 配置变更
    ConfigChange,
    /// 服务启动
    ServiceStart,
    /// 服务停止
    ServiceStop,
    /// 自定义事件
    Custom(String),
}

/// 事件严重性
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum EventSeverity {
    /// 调试
    Debug,
    /// 信息
    Info,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 严重
    Critical,
}

impl Event {
    /// 创建新事件
    pub fn new(
        event_type: EventType,
        source: impl Into<String>,
        data: serde_json::Value,
    ) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            event_type,
            source: source.into(),
            data,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            severity: EventSeverity::Info,
        }
    }
    
    /// 设置严重性
    pub fn with_severity(mut self, severity: EventSeverity) -> Self {
        self.severity = severity;
        self
    }
}

/// 事件总线 - 实现 Subject trait
pub struct EventBus {
    /// 观察者列表
    observers: Arc<RwLock<HashMap<String, Arc<dyn Observer>>>>,
    /// 事件类型订阅
    subscriptions: Arc<RwLock<HashMap<EventType, Vec<String>>>>,
    /// 事件历史（可选）
    history: Arc<RwLock<Vec<Event>>>,
    /// 最大历史记录数
    max_history: usize,
}

impl EventBus {
    /// 创建新的事件总线
    pub fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(HashMap::new())),
            subscriptions: Arc::new(RwLock::new(HashMap::new())),
            history: Arc::new(RwLock::new(Vec::new())),
            max_history: 1000,
        }
    }
    
    /// 设置最大历史记录数
    pub fn with_max_history(mut self, max: usize) -> Self {
        self.max_history = max;
        self
    }
    
    /// 订阅特定事件类型
    pub async fn subscribe(
        &self,
        observer: Arc<dyn Observer>,
        event_types: Vec<EventType>,
    ) -> Result<()> {
        let observer_id = observer.id().to_string();
        
        // 添加观察者
        {
            let mut observers = self.observers.write().await;
            observers.insert(observer_id.clone(), observer);
        }
        
        // 添加订阅
        {
            let mut subs = self.subscriptions.write().await;
            for event_type in event_types {
                subs.entry(event_type)
                    .or_insert_with(Vec::new)
                    .push(observer_id.clone());
            }
        }
        
        Ok(())
    }
    
    /// 取消订阅
    pub async fn unsubscribe(&self, observer_id: &str) -> Result<()> {
        // 移除观察者
        {
            let mut observers = self.observers.write().await;
            observers.remove(observer_id);
        }
        
        // 移除订阅
        {
            let mut subs = self.subscriptions.write().await;
            for subscribers in subs.values_mut() {
                subscribers.retain(|id| id != observer_id);
            }
        }
        
        Ok(())
    }
    
    /// 发布事件
    pub async fn publish(&self, event: Event) -> Result<()> {
        // 保存到历史
        {
            let mut history = self.history.write().await;
            history.push(event.clone());
            if history.len() > self.max_history {
                history.remove(0);
            }
        }
        
        // 通知订阅者
        self.notify(&event).await
    }
    
    /// 获取事件历史
    pub async fn get_history(&self) -> Vec<Event> {
        self.history.read().await.clone()
    }
    
    /// 清空历史
    pub async fn clear_history(&self) {
        self.history.write().await.clear();
    }
}

impl Default for EventBus {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Subject for EventBus {
    async fn attach(&self, observer: Arc<dyn Observer>) -> Result<()> {
        let observer_id = observer.id().to_string();
        let mut observers = self.observers.write().await;
        observers.insert(observer_id, observer);
        Ok(())
    }
    
    async fn detach(&self, observer_id: &str) -> Result<()> {
        self.unsubscribe(observer_id).await
    }
    
    async fn notify(&self, event: &Event) -> Result<()> {
        // 获取订阅了此事件类型的观察者
        let subscriber_ids = {
            let subs = self.subscriptions.read().await;
            subs.get(&event.event_type)
                .map(|ids| ids.clone())
                .unwrap_or_default()
        };
        
        // 获取观察者并按优先级排序
        let mut observers_with_priority = Vec::new();
        {
            let observers = self.observers.read().await;
            for id in subscriber_ids {
                if let Some(observer) = observers.get(&id) {
                    observers_with_priority.push((observer.priority(), observer.clone()));
                }
            }
        }
        observers_with_priority.sort_by_key(|(priority, _)| *priority);
        
        // 通知观察者
        for (_, observer) in observers_with_priority {
            if let Err(e) = observer.on_event(event).await {
                // 记录错误但继续通知其他观察者
                eprintln!("Observer {} failed to handle event: {}", observer.id(), e);
            }
        }
        
        Ok(())
    }
}

/// 简单的日志观察者示例
pub struct LogObserver {
    id: String,
    priority: u32,
}

impl LogObserver {
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            priority: 100,
        }
    }
    
    pub fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }
}

#[async_trait::async_trait]
impl Observer for LogObserver {
    async fn on_event(&self, event: &Event) -> Result<()> {
        println!(
            "[{}] {} event from {}: {:?}",
            self.id, 
            format!("{:?}", event.event_type),
            event.source,
            event.data
        );
        Ok(())
    }
    
    fn id(&self) -> &str {
        &self.id
    }
    
    fn priority(&self) -> u32 {
        self.priority
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_event_bus() {
        let bus = EventBus::new();
        let observer = Arc::new(LogObserver::new("test-observer"));
        
        bus.subscribe(observer, vec![EventType::StateChange]).await.unwrap();
        
        let event = Event::new(
            EventType::StateChange,
            "test-service",
            serde_json::json!({"state": "running"}),
        );
        
        bus.publish(event).await.unwrap();
        
        let history = bus.get_history().await;
        assert_eq!(history.len(), 1);
    }
    
    #[tokio::test]
    async fn test_observer_priority() {
        let bus = EventBus::new();
        
        let high_priority = Arc::new(LogObserver::new("high").with_priority(1));
        let low_priority = Arc::new(LogObserver::new("low").with_priority(100));
        
        bus.subscribe(low_priority, vec![EventType::Metric]).await.unwrap();
        bus.subscribe(high_priority, vec![EventType::Metric]).await.unwrap();
        
        let event = Event::new(
            EventType::Metric,
            "test",
            serde_json::json!({"value": 42}),
        );
        
        bus.publish(event).await.unwrap();
    }
}

