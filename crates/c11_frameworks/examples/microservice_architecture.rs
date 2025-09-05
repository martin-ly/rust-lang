//! 微服务架构示例
//! 
//! 展示Rust微服务架构的高级特性，包括：
//! - 服务发现与注册
//! - 负载均衡
//! - 熔断器模式
//! - 分布式追踪
//! - 配置中心
//! - 消息队列集成

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Mutex};
use tokio::time::timeout;
use uuid::Uuid;
use tracing::{info, warn, error, instrument};

/// 服务注册中心
#[derive(Debug, Clone)]
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
}

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub health_check_url: String,
    pub metadata: HashMap<String, String>,
    pub last_heartbeat: Instant,
    pub status: ServiceStatus,
}

/// 服务状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ServiceStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 服务发现客户端
#[derive(Debug, Clone)]
pub struct ServiceDiscovery {
    registry: ServiceRegistry,
    load_balancer: LoadBalancer,
}

/// 负载均衡器
#[derive(Debug, Clone)]
pub struct LoadBalancer {
    strategy: LoadBalanceStrategy,
}

/// 负载均衡策略
#[derive(Debug, Clone)]
pub enum LoadBalanceStrategy {
    RoundRobin,
    Random,
    LeastConnections,
    WeightedRoundRobin,
}

/// 熔断器
#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    failure_threshold: u32,
    timeout: Duration,
    state: Arc<Mutex<CircuitState>>,
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,    // 正常状态
    Open,      // 熔断状态
    HalfOpen,  // 半开状态
}

/// 分布式追踪上下文
#[derive(Debug, Clone)]
pub struct TraceContext {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub baggage: HashMap<String, String>,
}

/// 配置中心
#[derive(Debug, Clone)]
pub struct ConfigCenter {
    configs: Arc<RwLock<HashMap<String, serde_json::Value>>>,
}

/// 消息队列客户端
#[derive(Debug, Clone)]
pub struct MessageQueue {
    producers: Arc<RwLock<HashMap<String, MessageProducer>>>,
    consumers: Arc<RwLock<HashMap<String, MessageConsumer>>>,
}

/// 消息生产者
#[derive(Debug, Clone)]
pub struct MessageProducer {
    pub topic: String,
    pub config: ProducerConfig,
}

/// 消息消费者
#[derive(Debug, Clone)]
pub struct MessageConsumer {
    pub topic: String,
    pub group_id: String,
    pub config: ConsumerConfig,
}

/// 生产者配置
#[derive(Debug, Clone)]
pub struct ProducerConfig {
    pub batch_size: usize,
    pub timeout: Duration,
    pub retry_count: u32,
}

/// 消费者配置
#[derive(Debug, Clone)]
pub struct ConsumerConfig {
    pub auto_commit: bool,
    pub max_poll_records: usize,
    pub session_timeout: Duration,
}

/// 用户服务
#[derive(Debug, Clone)]
pub struct UserService {
    pub service_id: String,
    pub discovery: ServiceDiscovery,
    pub circuit_breaker: CircuitBreaker,
    pub config_center: ConfigCenter,
    pub message_queue: MessageQueue,
}

/// 订单服务
#[derive(Debug, Clone)]
pub struct OrderService {
    pub service_id: String,
    pub discovery: ServiceDiscovery,
    pub circuit_breaker: CircuitBreaker,
    pub config_center: ConfigCenter,
    pub message_queue: MessageQueue,
}

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

/// 订单模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: String,
    pub user_id: String,
    pub items: Vec<OrderItem>,
    pub total_amount: f64,
    pub status: OrderStatus,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

/// 订单项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: String,
    pub quantity: u32,
    pub price: f64,
}

/// 订单状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

/// 服务间通信请求
#[derive(Debug, Serialize, Deserialize)]
pub struct ServiceRequest {
    pub service_name: String,
    pub endpoint: String,
    pub method: String,
    pub headers: HashMap<String, String>,
    pub body: Option<serde_json::Value>,
    pub timeout: Option<Duration>,
}

/// 服务间通信响应
#[derive(Debug, Serialize, Deserialize)]
pub struct ServiceResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: Option<serde_json::Value>,
    pub duration: Duration,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 注册服务实例
    pub async fn register(&self, instance: ServiceInstance) -> Result<(), String> {
        let mut services = self.services.write().await;
        services
            .entry(instance.name.clone())
            .or_insert_with(Vec::new)
            .push(instance);
        Ok(())
    }
    
    /// 注销服务实例
    pub async fn deregister(&self, service_name: &str, instance_id: &str) -> Result<(), String> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            instances.retain(|instance| instance.id != instance_id);
            if instances.is_empty() {
                services.remove(service_name);
            }
        }
        Ok(())
    }
    
    /// 发现服务实例
    pub async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>, String> {
        let services = self.services.read().await;
        Ok(services.get(service_name).cloned().unwrap_or_default())
    }
    
    /// 健康检查
    pub async fn health_check(&self, service_name: &str) -> Result<Vec<ServiceInstance>, String> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            for instance in instances.iter_mut() {
                // 模拟健康检查
                let is_healthy = self.check_instance_health(&instance).await;
                instance.status = if is_healthy {
                    ServiceStatus::Healthy
                } else {
                    ServiceStatus::Unhealthy
                };
                instance.last_heartbeat = Instant::now();
            }
            
            // 过滤掉不健康的实例
            instances.retain(|instance| instance.status == ServiceStatus::Healthy);
        }
        
        Ok(services.get(service_name).cloned().unwrap_or_default())
    }
    
    /// 检查实例健康状态
    async fn check_instance_health(&self, instance: &ServiceInstance) -> bool {
        // 模拟健康检查逻辑
        // 在实际应用中，这里会发送HTTP请求到health_check_url
        tokio::time::sleep(Duration::from_millis(10)).await;
        true // 简化实现，总是返回健康
    }
}

impl ServiceDiscovery {
    pub fn new(registry: ServiceRegistry) -> Self {
        Self {
            registry,
            load_balancer: LoadBalancer {
                strategy: LoadBalanceStrategy::RoundRobin,
            },
        }
    }
    
    /// 调用远程服务
    #[instrument(skip(self))]
    pub async fn call_service(
        &self,
        service_name: &str,
        endpoint: &str,
        method: &str,
        body: Option<serde_json::Value>,
    ) -> Result<ServiceResponse, String> {
        // 发现服务实例
        let instances = self.registry.discover(service_name).await?;
        if instances.is_empty() {
            return Err(format!("服务 {} 没有可用实例", service_name));
        }
        
        // 负载均衡选择实例
        let instance = self.load_balancer.select_instance(&instances)?;
        
        // 构建请求URL
        let url = format!("http://{}:{}{}", instance.address, instance.port, endpoint);
        
        // 发送HTTP请求
        let start = Instant::now();
        let response = self.send_http_request(&url, method, body).await?;
        let duration = start.elapsed();
        
        Ok(ServiceResponse {
            status_code: response.status_code,
            headers: response.headers,
            body: response.body,
            duration,
        })
    }
    
    /// 发送HTTP请求
    async fn send_http_request(
        &self,
        url: &str,
        method: &str,
        body: Option<serde_json::Value>,
    ) -> Result<ServiceResponse, String> {
        // 模拟HTTP请求
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        Ok(ServiceResponse {
            status_code: 200,
            headers: HashMap::new(),
            body: Some(serde_json::json!({"message": "success"})),
            duration: Duration::from_millis(50),
        })
    }
}

impl LoadBalancer {
    /// 选择服务实例
    pub fn select_instance(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, String> {
        if instances.is_empty() {
            return Err("没有可用的服务实例".to_string());
        }
        
        match self.strategy {
            LoadBalanceStrategy::RoundRobin => {
                // 简化实现，随机选择
                let index = fastrand::usize(..instances.len());
                Ok(instances[index].clone())
            }
            LoadBalanceStrategy::Random => {
                let index = fastrand::usize(..instances.len());
                Ok(instances[index].clone())
            }
            LoadBalanceStrategy::LeastConnections => {
                // 简化实现，选择第一个
                Ok(instances[0].clone())
            }
            LoadBalanceStrategy::WeightedRoundRobin => {
                // 简化实现，随机选择
                let index = fastrand::usize(..instances.len());
                Ok(instances[index].clone())
            }
        }
    }
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, timeout: Duration) -> Self {
        Self {
            failure_threshold,
            timeout,
            state: Arc::new(Mutex::new(CircuitState::Closed)),
        }
    }
    
    /// 执行操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T, String>
    where
        F: std::future::Future<Output = Result<T, String>>,
    {
        let state = self.state.lock().await;
        
        match *state {
            CircuitState::Open => {
                return Err("熔断器开启，拒绝请求".to_string());
            }
            CircuitState::HalfOpen => {
                // 半开状态，允许一个请求通过
                drop(state);
                let result = timeout(self.timeout, operation).await;
                match result {
                    Ok(Ok(value)) => {
                        // 成功，关闭熔断器
                        let mut state = self.state.lock().await;
                        *state = CircuitState::Closed;
                        Ok(value)
                    }
                    Ok(Err(e)) | Err(_) => {
                        // 失败，重新开启熔断器
                        let mut state = self.state.lock().await;
                        *state = CircuitState::Open;
                        Err(e)
                    }
                }
            }
            CircuitState::Closed => {
                drop(state);
                let result = timeout(self.timeout, operation).await;
                match result {
                    Ok(Ok(value)) => Ok(value),
                    Ok(Err(e)) => {
                        // 失败，增加失败计数
                        // 简化实现，直接开启熔断器
                        let mut state = self.state.lock().await;
                        *state = CircuitState::Open;
                        Err(e)
                    }
                    Err(_) => {
                        // 超时
                        let mut state = self.state.lock().await;
                        *state = CircuitState::Open;
                        Err("请求超时".to_string())
                    }
                }
            }
        }
    }
}

impl ConfigCenter {
    pub fn new() -> Self {
        Self {
            configs: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 获取配置
    pub async fn get_config(&self, key: &str) -> Option<serde_json::Value> {
        let configs = self.configs.read().await;
        configs.get(key).cloned()
    }
    
    /// 设置配置
    pub async fn set_config(&self, key: String, value: serde_json::Value) {
        let mut configs = self.configs.write().await;
        configs.insert(key, value);
    }
    
    /// 监听配置变化
    pub async fn watch_config(&self, key: &str) -> tokio::sync::watch::Receiver<Option<serde_json::Value>> {
        let (tx, rx) = tokio::sync::watch::channel(self.get_config(key).await);
        
        // 简化实现，在实际应用中会监听配置变化事件
        tokio::spawn({
            let configs = self.configs.clone();
            let key = key.to_string();
            async move {
                loop {
                    tokio::time::sleep(Duration::from_secs(10)).await;
                    let value = {
                        let configs = configs.read().await;
                        configs.get(&key).cloned()
                    };
                    let _ = tx.send(value);
                }
            }
        });
        
        rx
    }
}

impl MessageQueue {
    pub fn new() -> Self {
        Self {
            producers: Arc::new(RwLock::new(HashMap::new())),
            consumers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 创建生产者
    pub async fn create_producer(&self, topic: String, config: ProducerConfig) {
        let producer = MessageProducer { topic: topic.clone(), config };
        let mut producers = self.producers.write().await;
        producers.insert(topic, producer);
    }
    
    /// 创建消费者
    pub async fn create_consumer(&self, topic: String, group_id: String, config: ConsumerConfig) {
        let consumer = MessageConsumer { topic: topic.clone(), group_id, config };
        let mut consumers = self.consumers.write().await;
        consumers.insert(topic, consumer);
    }
    
    /// 发送消息
    pub async fn send_message(&self, topic: &str, message: serde_json::Value) -> Result<(), String> {
        let producers = self.producers.read().await;
        if let Some(_producer) = producers.get(topic) {
            // 模拟发送消息
            info!("发送消息到主题 {}: {:?}", topic, message);
            Ok(())
        } else {
            Err(format!("主题 {} 没有生产者", topic))
        }
    }
    
    /// 消费消息
    pub async fn consume_message(&self, topic: &str) -> Result<Option<serde_json::Value>, String> {
        let consumers = self.consumers.read().await;
        if let Some(_consumer) = consumers.get(topic) {
            // 模拟消费消息
            Ok(Some(serde_json::json!({"message": "test message"})))
        } else {
            Err(format!("主题 {} 没有消费者", topic))
        }
    }
}

impl UserService {
    pub fn new(
        service_id: String,
        discovery: ServiceDiscovery,
        circuit_breaker: CircuitBreaker,
        config_center: ConfigCenter,
        message_queue: MessageQueue,
    ) -> Self {
        Self {
            service_id,
            discovery,
            circuit_breaker,
            config_center,
            message_queue,
        }
    }
    
    /// 获取用户信息
    pub async fn get_user(&self, user_id: &str) -> Result<User, String> {
        // 模拟从数据库获取用户
        Ok(User {
            id: user_id.to_string(),
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
            created_at: chrono::Utc::now(),
        })
    }
    
    /// 创建用户
    pub async fn create_user(&self, name: String, email: String) -> Result<User, String> {
        let user = User {
            id: Uuid::new_v4().to_string(),
            name,
            email,
            created_at: chrono::Utc::now(),
        };
        
        // 发送用户创建事件
        self.message_queue
            .send_message("user.created", serde_json::to_value(&user).unwrap())
            .await?;
        
        Ok(user)
    }
}

impl OrderService {
    pub fn new(
        service_id: String,
        discovery: ServiceDiscovery,
        circuit_breaker: CircuitBreaker,
        config_center: ConfigCenter,
        message_queue: MessageQueue,
    ) -> Self {
        Self {
            service_id,
            discovery,
            circuit_breaker,
            config_center,
            message_queue,
        }
    }
    
    /// 创建订单
    pub async fn create_order(&self, user_id: String, items: Vec<OrderItem>) -> Result<Order, String> {
        // 验证用户是否存在
        let user_response = self.discovery
            .call_service("user-service", &format!("/users/{}", user_id), "GET", None)
            .await?;
        
        if user_response.status_code != 200 {
            return Err("用户不存在".to_string());
        }
        
        let total_amount = items.iter().map(|item| item.price * item.quantity as f64).sum();
        
        let order = Order {
            id: Uuid::new_v4().to_string(),
            user_id,
            items,
            total_amount,
            status: OrderStatus::Pending,
            created_at: chrono::Utc::now(),
        };
        
        // 发送订单创建事件
        self.message_queue
            .send_message("order.created", serde_json::to_value(&order).unwrap())
            .await?;
        
        Ok(order)
    }
    
    /// 更新订单状态
    pub async fn update_order_status(&self, order_id: String, status: OrderStatus) -> Result<(), String> {
        // 模拟更新订单状态
        info!("更新订单 {} 状态为 {:?}", order_id, status);
        
        // 发送订单状态更新事件
        self.message_queue
            .send_message("order.status.updated", serde_json::json!({
                "order_id": order_id,
                "status": status
            }))
            .await?;
        
        Ok(())
    }
}

/// 微服务应用状态
#[derive(Clone)]
pub struct MicroserviceApp {
    pub registry: ServiceRegistry,
    pub user_service: UserService,
    pub order_service: OrderService,
    pub config_center: ConfigCenter,
    pub message_queue: MessageQueue,
}

/// 创建微服务应用
async fn create_microservice_app() -> MicroserviceApp {
    let registry = ServiceRegistry::new();
    let discovery = ServiceDiscovery::new(registry.clone());
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(10));
    let config_center = ConfigCenter::new();
    let message_queue = MessageQueue::new();
    
    // 初始化配置
    config_center.set_config("database.url".to_string(), serde_json::json!("postgresql://localhost/microservice")).await;
    config_center.set_config("redis.url".to_string(), serde_json::json!("redis://localhost:6379")).await;
    
    // 创建消息队列生产者和消费者
    message_queue.create_producer("user.created".to_string(), ProducerConfig {
        batch_size: 100,
        timeout: Duration::from_secs(5),
        retry_count: 3,
    }).await;
    
    message_queue.create_consumer("order.created".to_string(), "order-service".to_string(), ConsumerConfig {
        auto_commit: true,
        max_poll_records: 100,
        session_timeout: Duration::from_secs(30),
    }).await;
    
    let user_service = UserService::new(
        "user-service-1".to_string(),
        discovery.clone(),
        circuit_breaker.clone(),
        config_center.clone(),
        message_queue.clone(),
    );
    
    let order_service = OrderService::new(
        "order-service-1".to_string(),
        discovery,
        circuit_breaker,
        config_center.clone(),
        message_queue.clone(),
    );
    
    MicroserviceApp {
        registry,
        user_service,
        order_service,
        config_center,
        message_queue,
    }
}

/// 用户服务路由
async fn user_routes(app: MicroserviceApp) -> Router {
    Router::new()
        .route("/users/:id", get(get_user_handler))
        .route("/users", post(create_user_handler))
        .with_state(app)
}

/// 订单服务路由
async fn order_routes(app: MicroserviceApp) -> Router {
    Router::new()
        .route("/orders", post(create_order_handler))
        .route("/orders/:id/status", post(update_order_status_handler))
        .with_state(app)
}

/// 获取用户处理器
async fn get_user_handler(
    State(app): State<MicroserviceApp>,
    Path(user_id): Path<String>,
) -> Result<Json<User>, (StatusCode, String)> {
    match app.user_service.get_user(&user_id).await {
        Ok(user) => Ok(Json(user)),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, e)),
    }
}

/// 创建用户处理器
async fn create_user_handler(
    State(app): State<MicroserviceApp>,
    Json(payload): Json<serde_json::Value>,
) -> Result<Json<User>, (StatusCode, String)> {
    let name = payload["name"].as_str().unwrap_or("").to_string();
    let email = payload["email"].as_str().unwrap_or("").to_string();
    
    match app.user_service.create_user(name, email).await {
        Ok(user) => Ok(Json(user)),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, e)),
    }
}

/// 创建订单处理器
async fn create_order_handler(
    State(app): State<MicroserviceApp>,
    Json(payload): Json<serde_json::Value>,
) -> Result<Json<Order>, (StatusCode, String)> {
    let user_id = payload["user_id"].as_str().unwrap_or("").to_string();
    let items = payload["items"].as_array().unwrap_or(&vec![]);
    
    let order_items: Vec<OrderItem> = items.iter()
        .filter_map(|item| {
            Some(OrderItem {
                product_id: item["product_id"].as_str()?.to_string(),
                quantity: item["quantity"].as_u64()? as u32,
                price: item["price"].as_f64()?,
            })
        })
        .collect();
    
    match app.order_service.create_order(user_id, order_items).await {
        Ok(order) => Ok(Json(order)),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, e)),
    }
}

/// 更新订单状态处理器
async fn update_order_status_handler(
    State(app): State<MicroserviceApp>,
    Path(order_id): Path<String>,
    Json(payload): Json<serde_json::Value>,
) -> Result<StatusCode, (StatusCode, String)> {
    let status_str = payload["status"].as_str().unwrap_or("Pending");
    let status = match status_str {
        "Pending" => OrderStatus::Pending,
        "Confirmed" => OrderStatus::Confirmed,
        "Shipped" => OrderStatus::Shipped,
        "Delivered" => OrderStatus::Delivered,
        "Cancelled" => OrderStatus::Cancelled,
        _ => return Err((StatusCode::BAD_REQUEST, "无效的订单状态".to_string())),
    };
    
    match app.order_service.update_order_status(order_id, status).await {
        Ok(_) => Ok(StatusCode::OK),
        Err(e) => Err((StatusCode::INTERNAL_SERVER_ERROR, e)),
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    // 创建微服务应用
    let app = create_microservice_app().await;
    
    // 注册服务实例
    let user_service_instance = ServiceInstance {
        id: "user-service-1".to_string(),
        name: "user-service".to_string(),
        address: "127.0.0.1".to_string(),
        port: 3001,
        health_check_url: "http://127.0.0.1:3001/health".to_string(),
        metadata: HashMap::new(),
        last_heartbeat: Instant::now(),
        status: ServiceStatus::Healthy,
    };
    
    let order_service_instance = ServiceInstance {
        id: "order-service-1".to_string(),
        name: "order-service".to_string(),
        address: "127.0.0.1".to_string(),
        port: 3002,
        health_check_url: "http://127.0.0.1:3002/health".to_string(),
        metadata: HashMap::new(),
        last_heartbeat: Instant::now(),
        status: ServiceStatus::Healthy,
    };
    
    app.registry.register(user_service_instance).await?;
    app.registry.register(order_service_instance).await?;
    
    // 创建路由
    let user_router = user_routes(app.clone()).await;
    let order_router = order_routes(app.clone()).await;
    
    // 启动用户服务
    let user_listener = tokio::net::TcpListener::bind("127.0.0.1:3001").await?;
    info!("用户服务启动在 http://127.0.0.1:3001");
    
    tokio::spawn(async move {
        axum::serve(user_listener, user_router).await.unwrap();
    });
    
    // 启动订单服务
    let order_listener = tokio::net::TcpListener::bind("127.0.0.1:3002").await?;
    info!("订单服务启动在 http://127.0.0.1:3002");
    
    axum::serve(order_listener, order_router).await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_service_registry() {
        let registry = ServiceRegistry::new();
        
        let instance = ServiceInstance {
            id: "test-1".to_string(),
            name: "test-service".to_string(),
            address: "127.0.0.1".to_string(),
            port: 8080,
            health_check_url: "http://127.0.0.1:8080/health".to_string(),
            metadata: HashMap::new(),
            last_heartbeat: Instant::now(),
            status: ServiceStatus::Healthy,
        };
        
        registry.register(instance).await.unwrap();
        
        let instances = registry.discover("test-service").await.unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].id, "test-1");
    }
    
    #[tokio::test]
    async fn test_circuit_breaker() {
        let circuit_breaker = CircuitBreaker::new(3, Duration::from_millis(100));
        
        // 测试成功操作
        let result = circuit_breaker.execute(async { Ok("success") }).await;
        assert_eq!(result, Ok("success"));
        
        // 测试失败操作
        let result = circuit_breaker.execute(async { Err("failure".to_string()) }).await;
        assert!(result.is_err());
    }
    
    #[tokio::test]
    async fn test_config_center() {
        let config_center = ConfigCenter::new();
        
        config_center.set_config("test.key".to_string(), serde_json::json!("test.value")).await;
        
        let value = config_center.get_config("test.key").await;
        assert_eq!(value, Some(serde_json::json!("test.value")));
    }
    
    #[tokio::test]
    async fn test_message_queue() {
        let message_queue = MessageQueue::new();
        
        message_queue.create_producer("test-topic".to_string(), ProducerConfig {
            batch_size: 10,
            timeout: Duration::from_secs(5),
            retry_count: 3,
        }).await;
        
        let result = message_queue.send_message("test-topic", serde_json::json!("test message")).await;
        assert!(result.is_ok());
    }
}
