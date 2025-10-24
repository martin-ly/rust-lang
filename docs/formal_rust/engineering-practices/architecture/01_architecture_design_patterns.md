# 🏗️ Rust架构设计模式最佳实践


## 📊 目录

- [📚 目录](#目录)
- [概述](#概述)
- [1. 分层架构模式](#1-分层架构模式)
  - [1.1 经典分层架构 (Classic Layered Architecture)](#11-经典分层架构-classic-layered-architecture)
  - [1.2 六边形架构 (Hexagonal Architecture)](#12-六边形架构-hexagonal-architecture)
- [2. 微服务架构模式](#2-微服务架构模式)
  - [2.1 微服务通信模式 (Microservice Communication Pattern)](#21-微服务通信模式-microservice-communication-pattern)
  - [2.2 服务网格模式 (Service Mesh Pattern)](#22-服务网格模式-service-mesh-pattern)
- [3. 事件驱动架构模式](#3-事件驱动架构模式)
  - [3.1 事件溯源模式 (Event Sourcing Pattern)](#31-事件溯源模式-event-sourcing-pattern)
- [4. 测试和验证](#4-测试和验证)
- [5. 最佳实践总结](#5-最佳实践总结)
  - [5.1 架构设计原则](#51-架构设计原则)
  - [5.2 架构考虑](#52-架构考虑)
  - [5.3 技术选择](#53-技术选择)


## 📚 目录

- [🏗️ Rust架构设计模式最佳实践](#️-rust架构设计模式最佳实践)
  - [📚 目录](#-目录)
  - [概述](#概述)
  - [1. 分层架构模式](#1-分层架构模式)
    - [1.1 经典分层架构 (Classic Layered Architecture)](#11-经典分层架构-classic-layered-architecture)
    - [1.2 六边形架构 (Hexagonal Architecture)](#12-六边形架构-hexagonal-architecture)
  - [2. 微服务架构模式](#2-微服务架构模式)
    - [2.1 微服务通信模式 (Microservice Communication Pattern)](#21-微服务通信模式-microservice-communication-pattern)
    - [2.2 服务网格模式 (Service Mesh Pattern)](#22-服务网格模式-service-mesh-pattern)
  - [3. 事件驱动架构模式](#3-事件驱动架构模式)
    - [3.1 事件溯源模式 (Event Sourcing Pattern)](#31-事件溯源模式-event-sourcing-pattern)
  - [4. 测试和验证](#4-测试和验证)
  - [5. 最佳实践总结](#5-最佳实践总结)
    - [5.1 架构设计原则](#51-架构设计原则)
    - [5.2 架构考虑](#52-架构考虑)
    - [5.3 技术选择](#53-技术选择)

## 概述

本文档基于MIT 6.172、Stanford CS110、CMU 15-410、UC Berkeley CS61C等著名大学软件架构课程的标准，详细分析Rust架构设计的各种模式和实践技巧。

## 1. 分层架构模式

### 1.1 经典分层架构 (Classic Layered Architecture)

```rust
// MIT 6.172风格：经典分层架构
// src/lib.rs
pub mod presentation;    // 表示层：用户界面和API
pub mod application;     // 应用层：业务逻辑和用例
pub mod domain;          // 领域层：核心业务模型
pub mod infrastructure;  // 基础设施层：外部依赖

// 领域实体示例
// src/domain/entities/user.rs
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: UserId,
    pub name: String,
    pub email: Email,
    pub status: UserStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserId(Uuid);

impl UserId {
    pub fn new() -> Self {
        UserId(Uuid::new_v4())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Email(String);

impl Email {
    pub fn new(email: String) -> Result<Self, String> {
        if email.contains('@') {
            Ok(Email(email))
        } else {
            Err("Invalid email format".to_string())
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UserStatus {
    Active,
    Inactive,
    Suspended,
}

// 领域服务示例
// src/domain/domain_services/user_service.rs
pub trait UserDomainService {
    fn validate_user_registration(&self, user: &User) -> Result<(), String>;
    fn calculate_user_score(&self, user: &User) -> u32;
}

pub struct UserDomainServiceImpl;

impl UserDomainService for UserDomainServiceImpl {
    fn validate_user_registration(&self, user: &User) -> Result<(), String> {
        if user.name.is_empty() {
            return Err("User name cannot be empty".to_string());
        }
        
        if user.name.len() < 2 {
            return Err("User name must be at least 2 characters".to_string());
        }
        
        Ok(())
    }

    fn calculate_user_score(&self, user: &User) -> u32 {
        let mut score = 0;
        
        match user.status {
            UserStatus::Active => score += 100,
            UserStatus::Inactive => score += 50,
            UserStatus::Suspended => score += 0,
        }
        
        if user.email.0.ends_with(".edu") {
            score += 20;
        }
        
        score
    }
}
```

### 1.2 六边形架构 (Hexagonal Architecture)

```rust
// Stanford CS110风格：六边形架构
// src/lib.rs
pub mod domain;          // 核心领域
pub mod ports;           // 端口定义
pub mod adapters;        // 适配器实现

// 端口定义
// src/ports/mod.rs
pub mod input_ports;     // 输入端口
pub mod output_ports;    // 输出端口

// 输入端口
// src/ports/input_ports.rs
pub trait UserInputPort {
    fn create_user(&self, name: String, email: String) -> Result<User, String>;
    fn get_user(&self, id: UserId) -> Result<Option<User>, String>;
    fn update_user(&self, user: User) -> Result<User, String>;
    fn delete_user(&self, id: UserId) -> Result<(), String>;
}

// 输出端口
// src/ports/output_ports.rs
pub trait UserRepository {
    fn save(&self, user: User) -> Result<User, String>;
    fn find_by_id(&self, id: UserId) -> Result<Option<User>, String>;
    fn find_by_email(&self, email: &Email) -> Result<Option<User>, String>;
    fn delete(&self, id: UserId) -> Result<(), String>;
}

pub trait EmailService {
    fn send_welcome_email(&self, user: &User) -> Result<(), String>;
    fn send_password_reset(&self, email: &Email) -> Result<(), String>;
}

// 应用服务实现
// src/application/user_service.rs
pub struct UserService {
    user_repository: Box<dyn UserRepository>,
    email_service: Box<dyn EmailService>,
    domain_service: Box<dyn UserDomainService>,
}

impl UserService {
    pub fn new(
        user_repository: Box<dyn UserRepository>,
        email_service: Box<dyn EmailService>,
        domain_service: Box<dyn UserDomainService>,
    ) -> Self {
        UserService {
            user_repository,
            email_service,
            domain_service,
        }
    }
}

impl UserInputPort for UserService {
    fn create_user(&self, name: String, email: String) -> Result<User, String> {
        let email = Email::new(email)?;
        let user = User {
            id: UserId::new(),
            name,
            email,
            status: UserStatus::Active,
        };

        // 领域验证
        self.domain_service.validate_user_registration(&user)?;

        // 保存用户
        let saved_user = self.user_repository.save(user)?;

        // 发送欢迎邮件
        self.email_service.send_welcome_email(&saved_user)?;

        Ok(saved_user)
    }

    fn get_user(&self, id: UserId) -> Result<Option<User>, String> {
        self.user_repository.find_by_id(id)
    }

    fn update_user(&self, user: User) -> Result<User, String> {
        self.user_repository.save(user)
    }

    fn delete_user(&self, id: UserId) -> Result<(), String> {
        self.user_repository.delete(id)
    }
}
```

## 2. 微服务架构模式

### 2.1 微服务通信模式 (Microservice Communication Pattern)

```rust
// CMU 15-410风格：微服务通信
// src/lib.rs
pub mod services;        // 微服务集合
pub mod communication;   // 服务间通信
pub mod discovery;       // 服务发现
pub mod configuration;   // 配置管理

// 服务间通信
// src/communication/mod.rs
pub mod http_client;
pub mod grpc_client;
pub mod message_broker;

// HTTP客户端
// src/communication/http_client.rs
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::Duration;

pub struct HttpClient {
    client: Client,
    base_url: String,
}

impl HttpClient {
    pub fn new(base_url: String) -> Self {
        let client = Client::builder()
            .timeout(Duration::from_secs(30))
            .build()
            .unwrap();

        HttpClient { client, base_url }
    }

    pub async fn get<T>(&self, path: &str) -> Result<T, Box<dyn std::error::Error>>
    where
        T: for<'de> Deserialize<'de>,
    {
        let url = format!("{}{}", self.base_url, path);
        let response = self.client.get(&url).send().await?;
        let data = response.json::<T>().await?;
        Ok(data)
    }

    pub async fn post<T, U>(&self, path: &str, data: &T) -> Result<U, Box<dyn std::error::Error>>
    where
        T: Serialize,
        U: for<'de> Deserialize<'de>,
    {
        let url = format!("{}{}", self.base_url, path);
        let response = self.client.post(&url).json(data).send().await?;
        let result = response.json::<U>().await?;
        Ok(result)
    }
}

// 消息代理
// src/communication/message_broker.rs
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub topic: String,
    pub payload: serde_json::Value,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

pub struct MessageBroker {
    sender: mpsc::Sender<Message>,
    receiver: mpsc::Receiver<Message>,
}

impl MessageBroker {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel(1000);
        MessageBroker { sender, receiver }
    }

    pub async fn publish(&self, topic: String, payload: serde_json::Value) -> Result<(), String> {
        let message = Message {
            id: uuid::Uuid::new_v4().to_string(),
            topic,
            payload,
            timestamp: chrono::Utc::now(),
        };

        self.sender.send(message).await.map_err(|e| e.to_string())
    }

    pub async fn subscribe(&mut self, topic: &str) -> Option<Message> {
        while let Some(message) = self.receiver.recv().await {
            if message.topic == topic {
                return Some(message);
            }
        }
        None
    }
}
```

### 2.2 服务网格模式 (Service Mesh Pattern)

```rust
// UC Berkeley CS61C风格：服务网格
// src/service_mesh/mod.rs
pub mod proxy;
pub mod sidecar;
pub mod traffic_management;
pub mod observability;

// 代理实现
// src/service_mesh/proxy.rs
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct ServiceProxy {
    routes: Arc<RwLock<HashMap<String, String>>>,
    circuit_breakers: Arc<RwLock<HashMap<String, CircuitBreaker>>>,
    metrics: Arc<RwLock<MetricsCollector>>,
}

impl ServiceProxy {
    pub fn new() -> Self {
        ServiceProxy {
            routes: Arc::new(RwLock::new(HashMap::new())),
            circuit_breakers: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(MetricsCollector::new())),
        }
    }

    pub async fn route_request(&self, service_name: &str, request: &str) -> Result<String, String> {
        // 检查熔断器状态
        let circuit_breaker = self.circuit_breakers.read().await;
        if let Some(cb) = circuit_breaker.get(service_name) {
            if cb.is_open() {
                return Err("Circuit breaker is open".to_string());
            }
        }
        drop(circuit_breaker);

        // 获取路由
        let routes = self.routes.read().await;
        let target_url = routes.get(service_name)
            .ok_or_else(|| format!("Service {} not found", service_name))?;
        drop(routes);

        // 记录指标
        let mut metrics = self.metrics.write().await;
        metrics.record_request(service_name);

        // 转发请求
        let client = reqwest::Client::new();
        let response = client.post(target_url)
            .body(request.to_string())
            .send()
            .await
            .map_err(|e| e.to_string())?;

        let response_text = response.text().await.map_err(|e| e.to_string())?;
        
        // 更新指标
        metrics.record_response(service_name, response.status().is_success());

        Ok(response_text)
    }
}

// 熔断器
pub struct CircuitBreaker {
    failure_count: u32,
    threshold: u32,
    state: CircuitBreakerState,
    last_failure_time: Option<std::time::Instant>,
}

#[derive(Debug, Clone)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub fn new(threshold: u32) -> Self {
        CircuitBreaker {
            failure_count: 0,
            threshold,
            state: CircuitBreakerState::Closed,
            last_failure_time: None,
        }
    }

    pub fn is_open(&self) -> bool {
        matches!(self.state, CircuitBreakerState::Open)
    }

    pub fn record_success(&mut self) {
        self.failure_count = 0;
        self.state = CircuitBreakerState::Closed;
    }

    pub fn record_failure(&mut self) {
        self.failure_count += 1;
        self.last_failure_time = Some(std::time::Instant::now());

        if self.failure_count >= self.threshold {
            self.state = CircuitBreakerState::Open;
        }
    }
}

// 指标收集器
pub struct MetricsCollector {
    request_counts: HashMap<String, u64>,
    success_counts: HashMap<String, u64>,
    failure_counts: HashMap<String, u64>,
}

impl MetricsCollector {
    pub fn new() -> Self {
        MetricsCollector {
            request_counts: HashMap::new(),
            success_counts: HashMap::new(),
            failure_counts: HashMap::new(),
        }
    }

    pub fn record_request(&mut self, service: &str) {
        *self.request_counts.entry(service.to_string()).or_insert(0) += 1;
    }

    pub fn record_response(&mut self, service: &str, success: bool) {
        if success {
            *self.success_counts.entry(service.to_string()).or_insert(0) += 1;
        } else {
            *self.failure_counts.entry(service.to_string()).or_insert(0) += 1;
        }
    }

    pub fn get_metrics(&self) -> ServiceMetrics {
        ServiceMetrics {
            request_counts: self.request_counts.clone(),
            success_counts: self.success_counts.clone(),
            failure_counts: self.failure_counts.clone(),
        }
    }
}

pub struct ServiceMetrics {
    pub request_counts: HashMap<String, u64>,
    pub success_counts: HashMap<String, u64>,
    pub failure_counts: HashMap<String, u64>,
}
```

## 3. 事件驱动架构模式

### 3.1 事件溯源模式 (Event Sourcing Pattern)

```rust
// MIT 6.172风格：事件溯源
// src/event_sourcing/mod.rs
pub mod events;
pub mod aggregates;
pub mod event_store;
pub mod projections;

// 事件定义
// src/event_sourcing/events.rs
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainEvent {
    pub id: String,
    pub aggregate_id: String,
    pub event_type: String,
    pub version: u64,
    pub timestamp: DateTime<Utc>,
    pub data: serde_json::Value,
}

impl DomainEvent {
    pub fn new(
        aggregate_id: String,
        event_type: String,
        version: u64,
        data: serde_json::Value,
    ) -> Self {
        DomainEvent {
            id: uuid::Uuid::new_v4().to_string(),
            aggregate_id,
            event_type,
            version,
            timestamp: Utc::now(),
            data,
        }
    }
}

// 聚合根
// src/event_sourcing/aggregates.rs
pub trait Aggregate {
    fn id(&self) -> &str;
    fn version(&self) -> u64;
    fn apply_event(&mut self, event: &DomainEvent);
    fn uncommitted_events(&self) -> Vec<DomainEvent>;
    fn mark_events_as_committed(&mut self);
}

// 用户聚合根
pub struct UserAggregate {
    id: String,
    version: u64,
    name: String,
    email: String,
    status: UserStatus,
    uncommitted_events: Vec<DomainEvent>,
}

impl UserAggregate {
    pub fn new(id: String, name: String, email: String) -> Self {
        let mut aggregate = UserAggregate {
            id,
            version: 0,
            name,
            email,
            status: UserStatus::Active,
            uncommitted_events: Vec::new(),
        };

        // 创建用户事件
        let event = DomainEvent::new(
            aggregate.id.clone(),
            "UserCreated".to_string(),
            aggregate.version + 1,
            serde_json::json!({
                "name": aggregate.name,
                "email": aggregate.email
            }),
        );

        aggregate.apply_event(&event);
        aggregate.uncommitted_events.push(event);

        aggregate
    }

    pub fn change_name(&mut self, new_name: String) {
        let event = DomainEvent::new(
            self.id.clone(),
            "UserNameChanged".to_string(),
            self.version + 1,
            serde_json::json!({
                "old_name": self.name.clone(),
                "new_name": new_name.clone()
            }),
        );

        self.apply_event(&event);
        self.uncommitted_events.push(event);
    }

    pub fn deactivate(&mut self) {
        let event = DomainEvent::new(
            self.id.clone(),
            "UserDeactivated".to_string(),
            self.version + 1,
            serde_json::json!({}),
        );

        self.apply_event(&event);
        self.uncommitted_events.push(event);
    }
}

impl Aggregate for UserAggregate {
    fn id(&self) -> &str {
        &self.id
    }

    fn version(&self) -> u64 {
        self.version
    }

    fn apply_event(&mut self, event: &DomainEvent) {
        match event.event_type.as_str() {
            "UserCreated" => {
                self.name = event.data["name"].as_str().unwrap().to_string();
                self.email = event.data["email"].as_str().unwrap().to_string();
                self.status = UserStatus::Active;
            }
            "UserNameChanged" => {
                self.name = event.data["new_name"].as_str().unwrap().to_string();
            }
            "UserDeactivated" => {
                self.status = UserStatus::Inactive;
            }
            _ => {}
        }
        self.version = event.version;
    }

    fn uncommitted_events(&self) -> Vec<DomainEvent> {
        self.uncommitted_events.clone()
    }

    fn mark_events_as_committed(&mut self) {
        self.uncommitted_events.clear();
    }
}

// 事件存储
// src/event_sourcing/event_store.rs
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

pub trait EventStore {
    fn save_events(&self, aggregate_id: &str, events: Vec<DomainEvent>) -> Result<(), String>;
    fn get_events(&self, aggregate_id: &str) -> Result<Vec<DomainEvent>, String>;
}

pub struct InMemoryEventStore {
    events: Arc<RwLock<HashMap<String, Vec<DomainEvent>>>>,
}

impl InMemoryEventStore {
    pub fn new() -> Self {
        InMemoryEventStore {
            events: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl EventStore for InMemoryEventStore {
    fn save_events(&self, aggregate_id: &str, events: Vec<DomainEvent>) -> Result<(), String> {
        let mut store = self.events.write().unwrap();
        let aggregate_events = store.entry(aggregate_id.to_string()).or_insert_with(Vec::new);
        aggregate_events.extend(events);
        Ok(())
    }

    fn get_events(&self, aggregate_id: &str) -> Result<Vec<DomainEvent>, String> {
        let store = self.events.read().unwrap();
        Ok(store.get(aggregate_id).cloned().unwrap_or_default())
    }
}
```

## 4. 测试和验证

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio::test;

    #[test]
    fn test_user_aggregate() {
        let mut user = UserAggregate::new(
            "user-1".to_string(),
            "John Doe".to_string(),
            "john@example.com".to_string(),
        );

        assert_eq!(user.id(), "user-1");
        assert_eq!(user.name, "John Doe");
        assert_eq!(user.status, UserStatus::Active);

        user.change_name("Jane Doe".to_string());
        assert_eq!(user.name, "Jane Doe");

        user.deactivate();
        assert_eq!(user.status, UserStatus::Inactive);
    }

    #[test]
    fn test_event_store() {
        let event_store = InMemoryEventStore::new();
        let events = vec![
            DomainEvent::new(
                "user-1".to_string(),
                "UserCreated".to_string(),
                1,
                serde_json::json!({"name": "John"}),
            ),
        ];

        event_store.save_events("user-1", events.clone()).unwrap();
        let retrieved_events = event_store.get_events("user-1").unwrap();
        assert_eq!(retrieved_events.len(), 1);
    }

    #[tokio::test]
    async fn test_service_proxy() {
        let proxy = ServiceProxy::new();
        
        // 添加路由
        {
            let mut routes = proxy.routes.write().await;
            routes.insert("user-service".to_string(), "http://localhost:8081".to_string());
        }

        // 测试路由
        let result = proxy.route_request("user-service", "test request").await;
        // 由于没有实际的服务运行，这里会失败，但测试了路由逻辑
        assert!(result.is_err());
    }
}
```

## 5. 最佳实践总结

### 5.1 架构设计原则

1. **单一职责**: 每个组件只负责一个特定的功能
2. **开闭原则**: 对扩展开放，对修改关闭
3. **依赖倒置**: 依赖抽象而非具体实现
4. **接口隔离**: 客户端不应依赖它不需要的接口
5. **里氏替换**: 子类应该能够替换父类

### 5.2 架构考虑

1. **可扩展性**: 设计支持水平扩展的架构
2. **可维护性**: 清晰的模块边界和依赖关系
3. **可测试性**: 支持单元测试和集成测试
4. **性能**: 考虑性能瓶颈和优化策略
5. **安全性**: 实现适当的安全措施

### 5.3 技术选择

1. **通信协议**: 选择合适的服务间通信协议
2. **数据存储**: 根据需求选择合适的数据存储方案
3. **消息队列**: 使用消息队列实现异步通信
4. **监控和日志**: 建立完善的监控和日志系统
5. **配置管理**: 实现灵活的配置管理机制

这些架构设计模式和实践基于国际一流大学的软件架构课程标准，为构建可扩展、可维护的Rust应用程序提供了全面的架构指导。
