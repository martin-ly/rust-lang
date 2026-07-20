//! 服务通信案例
//! 
//! 本模块演示微服务间的各种通信模式，包括同步通信、异步通信、流式通信等。
//! 
//! 理论映射：
//! - 同步通信: Sync(s_i, s_j) = Request(s_i) → Response(s_j)
//! - 异步通信: Async(s_i, s_j) = Event(s_i) → Handler(s_j)
//! - 流式通信: Stream(s_i, s_j) = DataFlow(s_i) → Processor(s_j)

use actix_web::{web, App, HttpServer, HttpResponse, Responder};
use axum::{routing::post, Json, Router};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// 同步通信模式
/// 
/// 理论映射：Sync(s_i, s_j) = Request(s_i) → Response(s_j)
pub struct SynchronousCommunication {
    client: reqwest::Client,
}

impl SynchronousCommunication {
    pub fn new() -> Self {
        Self {
            client: reqwest::Client::new(),
        }
    }
    
    /// HTTP REST API 同步通信
    pub async fn http_request(&self, url: &str) -> Result<String, reqwest::Error> {
        let response = self.client.get(url).send().await?;
        let body = response.text().await?;
        Ok(body)
    }
    
    /// gRPC 同步通信
    pub async fn grpc_request(&self, service_url: &str, request: &str) -> Result<String, String> {
        // 模拟 gRPC 请求
        sleep(Duration::from_millis(50)).await;
        
        // 在实际应用中，这里会使用 tonic 或其他 gRPC 客户端
        Ok(format!("gRPC response from {}: {}", service_url, request))
    }
    
    /// 服务间同步调用
    pub async fn service_call(&self, from_service: &str, to_service: &str, data: &str) -> Result<String, String> {
        println!("同步调用: {} → {}", from_service, to_service);
        
        // 模拟网络延迟
        sleep(Duration::from_millis(30)).await;
        
        // 模拟服务处理
        let response = format!("Response from {} to {}: processed {}", to_service, from_service, data);
        Ok(response)
    }
}

/// 异步通信模式
/// 
/// 理论映射：Async(s_i, s_j) = Event(s_i) → Handler(s_j)
pub struct AsynchronousCommunication {
    event_bus: Arc<Mutex<HashMap<String, Vec<Box<dyn EventHandler + Send + Sync>>>>>,
    message_queue: Arc<Mutex<Vec<Message>>>,
}

/// 事件处理器特质
pub trait EventHandler {
    fn handle_event(&self, event: &Event) -> Result<(), String>;
}

/// 事件结构
#[derive(Clone, Serialize, Deserialize)]
pub struct Event {
    pub id: String,
    pub event_type: String,
    pub source_service: String,
    pub target_service: String,
    pub data: serde_json::Value,
    pub timestamp: String,
}

/// 消息结构
#[derive(Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub queue_name: String,
    pub data: serde_json::Value,
    pub timestamp: String,
}

impl AsynchronousCommunication {
    pub fn new() -> Self {
        Self {
            event_bus: Arc::new(Mutex::new(HashMap::new())),
            message_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    /// 发布事件
    pub async fn publish_event(&self, event: Event) -> Result<(), String> {
        println!("发布事件: {} → {}", event.source_service, event.target_service);
        
        let mut event_bus = self.event_bus.lock().unwrap();
        let handlers = event_bus.entry(event.target_service.clone()).or_insert_with(Vec::new);
        
        // 异步处理事件
        for handler in handlers.iter() {
            if let Err(e) = handler.handle_event(&event) {
                println!("事件处理失败: {}", e);
            }
        }
        
        Ok(())
    }
    
    /// 订阅事件
    pub async fn subscribe_event(&self, service_name: &str, handler: Box<dyn EventHandler + Send + Sync>) {
        let mut event_bus = self.event_bus.lock().unwrap();
        let handlers = event_bus.entry(service_name.to_string()).or_insert_with(Vec::new);
        handlers.push(handler);
    }
    
    /// 发送消息到队列
    pub async fn send_message(&self, queue_name: &str, data: serde_json::Value) -> Result<(), String> {
        let message = Message {
            id: uuid::Uuid::new_v4().to_string(),
            queue_name: queue_name.to_string(),
            data,
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        
        let mut queue = self.message_queue.lock().unwrap();
        queue.push(message);
        
        println!("消息已发送到队列: {}", queue_name);
        Ok(())
    }
    
    /// 从队列接收消息
    pub async fn receive_message(&self, queue_name: &str) -> Option<Message> {
        let mut queue = self.message_queue.lock().unwrap();
        
        if let Some(index) = queue.iter().position(|msg| msg.queue_name == queue_name) {
            let message = queue.remove(index);
            println!("从队列接收消息: {}", queue_name);
            Some(message)
        } else {
            None
        }
    }
}

/// 流式通信模式
/// 
/// 理论映射：Stream(s_i, s_j) = DataFlow(s_i) → Processor(s_j)
pub struct StreamingCommunication {
    data_streams: Arc<Mutex<HashMap<String, Vec<DataChunk>>>>,
}

/// 数据块结构
#[derive(Clone, Serialize, Deserialize)]
pub struct DataChunk {
    pub id: String,
    pub stream_id: String,
    pub data: Vec<u8>,
    pub sequence_number: u64,
    pub timestamp: String,
}

impl StreamingCommunication {
    pub fn new() -> Self {
        Self {
            data_streams: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    /// 创建数据流
    pub async fn create_stream(&self, stream_id: &str) -> Result<(), String> {
        let mut streams = self.data_streams.lock().unwrap();
        streams.insert(stream_id.to_string(), Vec::new());
        println!("创建数据流: {}", stream_id);
        Ok(())
    }
    
    /// 发送数据块
    pub async fn send_chunk(&self, stream_id: &str, data: Vec<u8>) -> Result<(), String> {
        let chunk = DataChunk {
            id: uuid::Uuid::new_v4().to_string(),
            stream_id: stream_id.to_string(),
            data,
            sequence_number: chrono::Utc::now().timestamp() as u64,
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        
        let mut streams = self.data_streams.lock().unwrap();
        if let Some(stream) = streams.get_mut(stream_id) {
            stream.push(chunk);
            println!("发送数据块到流: {}", stream_id);
            Ok(())
        } else {
            Err("Stream not found".to_string())
        }
    }
    
    /// 接收数据块
    pub async fn receive_chunk(&self, stream_id: &str) -> Option<DataChunk> {
        let mut streams = self.data_streams.lock().unwrap();
        
        if let Some(stream) = streams.get_mut(stream_id) {
            stream.pop()
        } else {
            None
        }
    }
    
    /// 实时数据流处理
    pub async fn process_stream(&self, stream_id: &str, processor: impl Fn(&DataChunk) -> Result<(), String>) {
        println!("开始处理数据流: {}", stream_id);
        
        loop {
            if let Some(chunk) = self.receive_chunk(stream_id).await {
                if let Err(e) = processor(&chunk) {
                    println!("数据块处理失败: {}", e);
                }
            } else {
                sleep(Duration::from_millis(100)).await;
            }
        }
    }
}

/// 混合通信模式
/// 
/// 结合同步、异步和流式通信
pub struct HybridCommunication {
    sync_comm: SynchronousCommunication,
    async_comm: AsynchronousCommunication,
    stream_comm: StreamingCommunication,
}

impl HybridCommunication {
    pub fn new() -> Self {
        Self {
            sync_comm: SynchronousCommunication::new(),
            async_comm: AsynchronousCommunication::new(),
            stream_comm: StreamingCommunication::new(),
        }
    }
    
    /// 混合通信示例：订单处理流程
    pub async fn process_order_workflow(&self, order_data: &str) -> Result<String, String> {
        println!("开始订单处理工作流");
        
        // 1. 同步调用：验证用户
        let user_validation = self.sync_comm.service_call("OrderService", "UserService", order_data).await?;
        println!("用户验证结果: {}", user_validation);
        
        // 2. 异步事件：通知库存服务
        let inventory_event = Event {
            id: uuid::Uuid::new_v4().to_string(),
            event_type: "ORDER_CREATED".to_string(),
            source_service: "OrderService".to_string(),
            target_service: "InventoryService".to_string(),
            data: serde_json::json!({"order_data": order_data}),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        self.async_comm.publish_event(inventory_event).await?;
        
        // 3. 消息队列：发送支付请求
        let payment_message = serde_json::json!({
            "order_id": "12345",
            "amount": 100.0,
            "currency": "USD"
        });
        self.async_comm.send_message("payment_queue", payment_message).await?;
        
        // 4. 流式通信：实时订单状态更新
        self.stream_comm.create_stream("order_status_stream").await?;
        let status_data = format!("Order {} status: PROCESSING", "12345").into_bytes();
        self.stream_comm.send_chunk("order_status_stream", status_data).await?;
        
        Ok("订单处理工作流完成".to_string())
    }
}

/// 具体的事件处理器实现
pub struct UserEventHandler;

impl EventHandler for UserEventHandler {
    fn handle_event(&self, event: &Event) -> Result<(), String> {
        println!("用户服务处理事件: {} - {}", event.event_type, event.id);
        Ok(())
    }
}

pub struct InventoryEventHandler;

impl EventHandler for InventoryEventHandler {
    fn handle_event(&self, event: &Event) -> Result<(), String> {
        println!("库存服务处理事件: {} - {}", event.event_type, event.id);
        Ok(())
    }
}

pub struct PaymentEventHandler;

impl EventHandler for PaymentEventHandler {
    fn handle_event(&self, event: &Event) -> Result<(), String> {
        println!("支付服务处理事件: {} - {}", event.event_type, event.id);
        Ok(())
    }
}

/// HTTP路由处理
pub async fn sync_api_call() -> impl Responder {
    let sync_comm = SynchronousCommunication::new();
    
    match sync_comm.service_call("Client", "UserService", "get_user_123").await {
        Ok(response) => HttpResponse::Ok().json(response),
        Err(e) => HttpResponse::InternalServerError().json(e),
    }
}

pub async fn async_event_publish(event: web::Json<Event>) -> impl Responder {
    let async_comm = AsynchronousCommunication::new();
    
    match async_comm.publish_event(event.into_inner()).await {
        Ok(_) => HttpResponse::Ok().json("Event published successfully"),
        Err(e) => HttpResponse::InternalServerError().json(e),
    }
}

pub async fn stream_data() -> impl Responder {
    let stream_comm = StreamingCommunication::new();
    
    match stream_comm.create_stream("test_stream").await {
        Ok(_) => HttpResponse::Ok().json("Stream created successfully"),
        Err(e) => HttpResponse::InternalServerError().json(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试同步通信
    #[tokio::test]
    async fn test_synchronous_communication() {
        let sync_comm = SynchronousCommunication::new();
        
        // 测试HTTP请求
        let result = sync_comm.http_request("https://httpbin.org/get").await;
        assert!(result.is_ok());
        
        // 测试gRPC请求
        let result = sync_comm.grpc_request("user-service:50051", "get_user").await;
        assert!(result.is_ok());
        
        // 测试服务间调用
        let result = sync_comm.service_call("OrderService", "UserService", "user_data").await;
        assert!(result.is_ok());
        assert!(result.unwrap().contains("Response from UserService"));
    }

    /// 测试异步通信
    #[tokio::test]
    async fn test_asynchronous_communication() {
        let async_comm = AsynchronousCommunication::new();
        
        // 订阅事件
        async_comm.subscribe_event("UserService", Box::new(UserEventHandler)).await;
        async_comm.subscribe_event("InventoryService", Box::new(InventoryEventHandler)).await;
        
        // 发布事件
        let event = Event {
            id: "test_event_1".to_string(),
            event_type: "USER_CREATED".to_string(),
            source_service: "AuthService".to_string(),
            target_service: "UserService".to_string(),
            data: serde_json::json!({"user_id": "123"}),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        
        let result = async_comm.publish_event(event).await;
        assert!(result.is_ok());
        
        // 测试消息队列
        let message_data = serde_json::json!({"order_id": "456", "amount": 50.0});
        let result = async_comm.send_message("order_queue", message_data).await;
        assert!(result.is_ok());
        
        let received_message = async_comm.receive_message("order_queue").await;
        assert!(received_message.is_some());
    }

    /// 测试流式通信
    #[tokio::test]
    async fn test_streaming_communication() {
        let stream_comm = StreamingCommunication::new();
        
        // 创建流
        let result = stream_comm.create_stream("test_stream").await;
        assert!(result.is_ok());
        
        // 发送数据块
        let data = b"Hello, streaming world!".to_vec();
        let result = stream_comm.send_chunk("test_stream", data.clone()).await;
        assert!(result.is_ok());
        
        // 接收数据块
        let received_chunk = stream_comm.receive_chunk("test_stream").await;
        assert!(received_chunk.is_some());
        assert_eq!(received_chunk.unwrap().data, data);
    }

    /// 测试混合通信
    #[tokio::test]
    async fn test_hybrid_communication() {
        let hybrid_comm = HybridCommunication::new();
        
        // 测试混合工作流
        let result = hybrid_comm.process_order_workflow("order_data_123").await;
        assert!(result.is_ok());
        assert!(result.unwrap().contains("订单处理工作流完成"));
    }
}

/// 示例用法
pub async fn run_examples() {
    println!("=== 服务通信案例 ===");
    
    // 1. 同步通信示例
    println!("\n1. 同步通信示例:");
    let sync_comm = SynchronousCommunication::new();
    
    match sync_comm.service_call("OrderService", "UserService", "get_user_123").await {
        Ok(response) => println!("  同步调用结果: {}", response),
        Err(e) => println!("  同步调用失败: {}", e),
    }
    
    // 2. 异步通信示例
    println!("\n2. 异步通信示例:");
    let async_comm = AsynchronousCommunication::new();
    
    // 订阅事件处理器
    async_comm.subscribe_event("UserService", Box::new(UserEventHandler)).await;
    async_comm.subscribe_event("InventoryService", Box::new(InventoryEventHandler)).await;
    async_comm.subscribe_event("PaymentService", Box::new(PaymentEventHandler)).await;
    
    // 发布事件
    let event = Event {
        id: uuid::Uuid::new_v4().to_string(),
        event_type: "ORDER_CREATED".to_string(),
        source_service: "OrderService".to_string(),
        target_service: "InventoryService".to_string(),
        data: serde_json::json!({
            "order_id": "12345",
            "items": [{"product_id": 1, "quantity": 2}]
        }),
        timestamp: chrono::Utc::now().to_rfc3339(),
    };
    
    match async_comm.publish_event(event).await {
        Ok(_) => println!("  事件发布成功"),
        Err(e) => println!("  事件发布失败: {}", e),
    }
    
    // 发送消息到队列
    let message_data = serde_json::json!({
        "payment_id": "pay_123",
        "amount": 100.0,
        "currency": "USD"
    });
    
    match async_comm.send_message("payment_queue", message_data).await {
        Ok(_) => println!("  消息发送成功"),
        Err(e) => println!("  消息发送失败: {}", e),
    }
    
    // 3. 流式通信示例
    println!("\n3. 流式通信示例:");
    let stream_comm = StreamingCommunication::new();
    
    match stream_comm.create_stream("order_status_stream").await {
        Ok(_) => println!("  数据流创建成功"),
        Err(e) => println!("  数据流创建失败: {}", e),
    }
    
    // 发送多个数据块
    for i in 1..=5 {
        let data = format!("Order status update #{}: PROCESSING", i).into_bytes();
        match stream_comm.send_chunk("order_status_stream", data).await {
            Ok(_) => println!("  数据块 {} 发送成功", i),
            Err(e) => println!("  数据块 {} 发送失败: {}", i, e),
        }
    }
    
    // 4. 混合通信示例
    println!("\n4. 混合通信示例:");
    let hybrid_comm = HybridCommunication::new();
    
    match hybrid_comm.process_order_workflow("complete_order_data").await {
        Ok(result) => println!("  混合工作流结果: {}", result),
        Err(e) => println!("  混合工作流失败: {}", e),
    }
    
    // 5. 性能对比
    println!("\n5. 通信模式性能对比:");
    
    // 同步通信性能
    let start = std::time::Instant::now();
    for _ in 0..10 {
        let _ = sync_comm.service_call("ServiceA", "ServiceB", "test_data").await;
    }
    let sync_duration = start.elapsed();
    println!("  同步通信 (10次): {:?}", sync_duration);
    
    // 异步通信性能
    let start = std::time::Instant::now();
    for i in 0..10 {
        let event = Event {
            id: format!("event_{}", i),
            event_type: "TEST_EVENT".to_string(),
            source_service: "ServiceA".to_string(),
            target_service: "ServiceB".to_string(),
            data: serde_json::json!({"test": "data"}),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        let _ = async_comm.publish_event(event).await;
    }
    let async_duration = start.elapsed();
    println!("  异步通信 (10次): {:?}", async_duration);
    
    // 流式通信性能
    let start = std::time::Instant::now();
    for i in 0..10 {
        let data = format!("stream_data_{}", i).into_bytes();
        let _ = stream_comm.send_chunk("test_stream", data).await;
    }
    let stream_duration = start.elapsed();
    println!("  流式通信 (10次): {:?}", stream_duration);
} 