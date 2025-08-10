//! 基础微服务案例
//! 
//! 本模块演示微服务系统的基础实现，包括服务定义、通信、发现等。
//! 
//! 理论映射：
//! - 微服务系统: MS = (S, C, D, O, M)
//! - 服务接口: Service_i = (Interface_i, Implementation_i, Contract_i)
//! - 服务组合: Composition(S_1, S_2, ..., S_k) = ○_{i=1}^{k} S_i
//! - 分布式一致性: Consistency(S) = ∀s_i, s_j ∈ S. State(s_i) ≡ State(s_j)

use actix_web::{web, App, HttpServer, HttpResponse, Responder};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::time::{sleep, Duration};

/// 用户服务
/// 
/// 理论映射：s_i ∈ S (服务集合)
pub struct UserService {
    users: Arc<Mutex<HashMap<u32, User>>>,
}

/// 用户数据结构
#[derive(Clone, Serialize, Deserialize)]
pub struct User {
    pub id: u32,
    pub name: String,
    pub email: String,
    pub created_at: String,
}

impl UserService {
    pub fn new() -> Self {
        let mut users = HashMap::new();
        users.insert(1, User {
            id: 1,
            name: "John Doe".to_string(),
            email: "john@example.com".to_string(),
            created_at: "2025-01-01".to_string(),
        });
        users.insert(2, User {
            id: 2,
            name: "Jane Smith".to_string(),
            email: "jane@example.com".to_string(),
            created_at: "2025-01-02".to_string(),
        });
        
        Self {
            users: Arc::new(Mutex::new(users)),
        }
    }
    
    /// 获取用户信息
    /// 
    /// 理论映射：Interface_i (服务接口)
    pub async fn get_user(&self, user_id: u32) -> Option<User> {
        // 模拟网络延迟
        sleep(Duration::from_millis(10)).await;
        
        let users = self.users.lock().unwrap();
        users.get(&user_id).cloned()
    }
    
    /// 创建用户
    pub async fn create_user(&self, user: User) -> Result<User, String> {
        let mut users = self.users.lock().unwrap();
        
        if users.contains_key(&user.id) {
            return Err("User already exists".to_string());
        }
        
        users.insert(user.id, user.clone());
        Ok(user)
    }
    
    /// 更新用户
    pub async fn update_user(&self, user_id: u32, user: User) -> Result<User, String> {
        let mut users = self.users.lock().unwrap();
        
        if !users.contains_key(&user_id) {
            return Err("User not found".to_string());
        }
        
        users.insert(user_id, user.clone());
        Ok(user)
    }
    
    /// 删除用户
    pub async fn delete_user(&self, user_id: u32) -> Result<(), String> {
        let mut users = self.users.lock().unwrap();
        
        if !users.contains_key(&user_id) {
            return Err("User not found".to_string());
        }
        
        users.remove(&user_id);
        Ok(())
    }
}

/// 订单服务
/// 
/// 理论映射：s_j ∈ S (服务集合)
pub struct OrderService {
    orders: Arc<Mutex<HashMap<u32, Order>>>,
}

/// 订单数据结构
#[derive(Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: u32,
    pub user_id: u32,
    pub items: Vec<OrderItem>,
    pub total: f64,
    pub status: OrderStatus,
    pub created_at: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: u32,
    pub quantity: u32,
    pub price: f64,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

impl OrderService {
    pub fn new() -> Self {
        let mut orders = HashMap::new();
        orders.insert(1, Order {
            id: 1,
            user_id: 1,
            items: vec![
                OrderItem { product_id: 1, quantity: 2, price: 29.99 },
                OrderItem { product_id: 2, quantity: 1, price: 49.99 },
            ],
            total: 109.97,
            status: OrderStatus::Confirmed,
            created_at: "2025-01-01".to_string(),
        });
        
        Self {
            orders: Arc::new(Mutex::new(orders)),
        }
    }
    
    /// 获取订单信息
    pub async fn get_order(&self, order_id: u32) -> Option<Order> {
        sleep(Duration::from_millis(15)).await;
        
        let orders = self.orders.lock().unwrap();
        orders.get(&order_id).cloned()
    }
    
    /// 创建订单
    pub async fn create_order(&self, order: Order) -> Result<Order, String> {
        let mut orders = self.orders.lock().unwrap();
        
        if orders.contains_key(&order.id) {
            return Err("Order already exists".to_string());
        }
        
        orders.insert(order.id, order.clone());
        Ok(order)
    }
    
    /// 更新订单状态
    pub async fn update_order_status(&self, order_id: u32, status: OrderStatus) -> Result<Order, String> {
        let mut orders = self.orders.lock().unwrap();
        
        if let Some(order) = orders.get_mut(&order_id) {
            order.status = status;
            Ok(order.clone())
        } else {
            Err("Order not found".to_string())
        }
    }
}

/// 支付服务
/// 
/// 理论映射：s_k ∈ S (服务集合)
pub struct PaymentService {
    payments: Arc<Mutex<HashMap<u32, Payment>>>,
}

/// 支付数据结构
#[derive(Clone, Serialize, Deserialize)]
pub struct Payment {
    pub id: u32,
    pub order_id: u32,
    pub amount: f64,
    pub method: PaymentMethod,
    pub status: PaymentStatus,
    pub created_at: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum PaymentMethod {
    CreditCard,
    DebitCard,
    PayPal,
    BankTransfer,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum PaymentStatus {
    Pending,
    Processing,
    Completed,
    Failed,
    Refunded,
}

impl PaymentService {
    pub fn new() -> Self {
        let mut payments = HashMap::new();
        payments.insert(1, Payment {
            id: 1,
            order_id: 1,
            amount: 109.97,
            method: PaymentMethod::CreditCard,
            status: PaymentStatus::Completed,
            created_at: "2025-01-01".to_string(),
        });
        
        Self {
            payments: Arc::new(Mutex::new(payments)),
        }
    }
    
    /// 处理支付
    pub async fn process_payment(&self, payment: Payment) -> Result<Payment, String> {
        sleep(Duration::from_millis(20)).await;
        
        // 模拟支付处理
        let mut payments = self.payments.lock().unwrap();
        
        if payments.contains_key(&payment.id) {
            return Err("Payment already exists".to_string());
        }
        
        // 模拟支付成功率
        let success_rate = 0.95;
        let random = rand::random::<f64>();
        
        let mut processed_payment = payment.clone();
        if random < success_rate {
            processed_payment.status = PaymentStatus::Completed;
        } else {
            processed_payment.status = PaymentStatus::Failed;
        }
        
        payments.insert(processed_payment.id, processed_payment.clone());
        Ok(processed_payment)
    }
    
    /// 获取支付信息
    pub async fn get_payment(&self, payment_id: u32) -> Option<Payment> {
        let payments = self.payments.lock().unwrap();
        payments.get(&payment_id).cloned()
    }
}

/// 服务注册中心
/// 
/// 理论映射：D (服务发现机制)
pub struct ServiceRegistry {
    services: Arc<Mutex<HashMap<String, ServiceInfo>>>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct ServiceInfo {
    pub name: String,
    pub url: String,
    pub health: ServiceHealth,
    pub last_heartbeat: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum ServiceHealth {
    Healthy,
    Unhealthy,
    Unknown,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    /// 注册服务
    /// 
    /// 理论映射：Register(S) (服务注册)
    pub async fn register_service(&self, name: String, url: String) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        
        let service_info = ServiceInfo {
            name: name.clone(),
            url,
            health: ServiceHealth::Healthy,
            last_heartbeat: chrono::Utc::now().to_rfc3339(),
        };
        
        services.insert(name, service_info);
        Ok(())
    }
    
    /// 发现服务
    /// 
    /// 理论映射：Lookup(S) (服务查找)
    pub async fn discover_service(&self, name: &str) -> Option<ServiceInfo> {
        let services = self.services.lock().unwrap();
        services.get(name).cloned()
    }
    
    /// 获取所有服务
    pub async fn get_all_services(&self) -> Vec<ServiceInfo> {
        let services = self.services.lock().unwrap();
        services.values().cloned().collect()
    }
    
    /// 更新服务健康状态
    pub async fn update_health(&self, name: &str, health: ServiceHealth) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        
        if let Some(service_info) = services.get_mut(name) {
            service_info.health = health;
            service_info.last_heartbeat = chrono::Utc::now().to_rfc3339();
            Ok(())
        } else {
            Err("Service not found".to_string())
        }
    }
}

/// 微服务系统
/// 
/// 理论映射：MS = (S, C, D, O, M)
pub struct MicroserviceSystem {
    pub user_service: UserService,
    pub order_service: OrderService,
    pub payment_service: PaymentService,
    pub registry: ServiceRegistry,
}

impl MicroserviceSystem {
    pub fn new() -> Self {
        Self {
            user_service: UserService::new(),
            order_service: OrderService::new(),
            payment_service: PaymentService::new(),
            registry: ServiceRegistry::new(),
        }
    }
    
    /// 初始化系统
    pub async fn initialize(&self) -> Result<(), String> {
        // 注册所有服务
        self.registry.register_service(
            "user-service".to_string(),
            "http://localhost:8081".to_string(),
        ).await?;
        
        self.registry.register_service(
            "order-service".to_string(),
            "http://localhost:8082".to_string(),
        ).await?;
        
        self.registry.register_service(
            "payment-service".to_string(),
            "http://localhost:8083".to_string(),
        ).await?;
        
        Ok(())
    }
    
    /// 创建完整订单流程
    /// 
    /// 理论映射：Composition(S_1, S_2, ..., S_k) = ○_{i=1}^{k} S_i
    pub async fn create_complete_order(
        &self,
        user_id: u32,
        items: Vec<OrderItem>,
    ) -> Result<CompleteOrder, String> {
        // 1. 验证用户
        let user = self.user_service.get_user(user_id).await
            .ok_or("User not found")?;
        
        // 2. 创建订单
        let order_id = rand::random::<u32>();
        let total = items.iter().map(|item| item.price * item.quantity as f64).sum();
        
        let order = Order {
            id: order_id,
            user_id,
            items,
            total,
            status: OrderStatus::Pending,
            created_at: chrono::Utc::now().to_rfc3339(),
        };
        
        let created_order = self.order_service.create_order(order).await?;
        
        // 3. 处理支付
        let payment = Payment {
            id: rand::random::<u32>(),
            order_id,
            amount: total,
            method: PaymentMethod::CreditCard,
            status: PaymentStatus::Pending,
            created_at: chrono::Utc::now().to_rfc3339(),
        };
        
        let processed_payment = self.payment_service.process_payment(payment).await?;
        
        // 4. 更新订单状态
        let final_order = if processed_payment.status == PaymentStatus::Completed {
            self.order_service.update_order_status(order_id, OrderStatus::Confirmed).await?
        } else {
            self.order_service.update_order_status(order_id, OrderStatus::Cancelled).await?
        };
        
        Ok(CompleteOrder {
            user,
            order: final_order,
            payment: processed_payment,
        })
    }
}

/// 完整订单信息
#[derive(Serialize, Deserialize)]
pub struct CompleteOrder {
    pub user: User,
    pub order: Order,
    pub payment: Payment,
}

/// HTTP路由处理
pub async fn get_user(path: web::Path<u32>) -> impl Responder {
    let user_id = path.into_inner();
    let user_service = UserService::new();
    
    match user_service.get_user(user_id).await {
        Some(user) => HttpResponse::Ok().json(user),
        None => HttpResponse::NotFound().json("User not found"),
    }
}

pub async fn create_user(user: web::Json<User>) -> impl Responder {
    let user_service = UserService::new();
    
    match user_service.create_user(user.into_inner()).await {
        Ok(user) => HttpResponse::Created().json(user),
        Err(e) => HttpResponse::BadRequest().json(e),
    }
}

pub async fn get_order(path: web::Path<u32>) -> impl Responder {
    let order_id = path.into_inner();
    let order_service = OrderService::new();
    
    match order_service.get_order(order_id).await {
        Some(order) => HttpResponse::Ok().json(order),
        None => HttpResponse::NotFound().json("Order not found"),
    }
}

pub async fn create_order(order: web::Json<Order>) -> impl Responder {
    let order_service = OrderService::new();
    
    match order_service.create_order(order.into_inner()).await {
        Ok(order) => HttpResponse::Created().json(order),
        Err(e) => HttpResponse::BadRequest().json(e),
    }
}

pub async fn process_payment(payment: web::Json<Payment>) -> impl Responder {
    let payment_service = PaymentService::new();
    
    match payment_service.process_payment(payment.into_inner()).await {
        Ok(payment) => HttpResponse::Ok().json(payment),
        Err(e) => HttpResponse::BadRequest().json(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试用户服务
    #[tokio::test]
    async fn test_user_service() {
        let user_service = UserService::new();
        
        // 测试获取用户
        let user = user_service.get_user(1).await;
        assert!(user.is_some());
        assert_eq!(user.unwrap().name, "John Doe");
        
        // 测试创建用户
        let new_user = User {
            id: 3,
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
            created_at: "2025-01-03".to_string(),
        };
        
        let result = user_service.create_user(new_user.clone()).await;
        assert!(result.is_ok());
        
        // 测试获取新创建的用户
        let retrieved_user = user_service.get_user(3).await;
        assert!(retrieved_user.is_some());
        assert_eq!(retrieved_user.unwrap().name, "Test User");
    }

    /// 测试订单服务
    #[tokio::test]
    async fn test_order_service() {
        let order_service = OrderService::new();
        
        // 测试获取订单
        let order = order_service.get_order(1).await;
        assert!(order.is_some());
        assert_eq!(order.unwrap().user_id, 1);
        
        // 测试创建订单
        let new_order = Order {
            id: 2,
            user_id: 2,
            items: vec![
                OrderItem { product_id: 3, quantity: 1, price: 19.99 },
            ],
            total: 19.99,
            status: OrderStatus::Pending,
            created_at: "2025-01-03".to_string(),
        };
        
        let result = order_service.create_order(new_order.clone()).await;
        assert!(result.is_ok());
        
        // 测试更新订单状态
        let updated_order = order_service.update_order_status(2, OrderStatus::Confirmed).await;
        assert!(updated_order.is_ok());
        assert!(matches!(updated_order.unwrap().status, OrderStatus::Confirmed));
    }

    /// 测试支付服务
    #[tokio::test]
    async fn test_payment_service() {
        let payment_service = PaymentService::new();
        
        // 测试处理支付
        let payment = Payment {
            id: 2,
            order_id: 2,
            amount: 29.99,
            method: PaymentMethod::CreditCard,
            status: PaymentStatus::Pending,
            created_at: "2025-01-03".to_string(),
        };
        
        let result = payment_service.process_payment(payment).await;
        assert!(result.is_ok());
        
        let processed_payment = result.unwrap();
        assert!(matches!(processed_payment.status, PaymentStatus::Completed | PaymentStatus::Failed));
    }

    /// 测试服务注册中心
    #[tokio::test]
    async fn test_service_registry() {
        let registry = ServiceRegistry::new();
        
        // 测试注册服务
        let result = registry.register_service(
            "test-service".to_string(),
            "http://localhost:8080".to_string(),
        ).await;
        assert!(result.is_ok());
        
        // 测试发现服务
        let service_info = registry.discover_service("test-service").await;
        assert!(service_info.is_some());
        assert_eq!(service_info.unwrap().name, "test-service");
        
        // 测试更新健康状态
        let result = registry.update_health("test-service", ServiceHealth::Unhealthy).await;
        assert!(result.is_ok());
        
        let service_info = registry.discover_service("test-service").await;
        assert!(matches!(service_info.unwrap().health, ServiceHealth::Unhealthy));
    }

    /// 测试完整微服务系统
    #[tokio::test]
    async fn test_microservice_system() {
        let system = MicroserviceSystem::new();
        
        // 初始化系统
        let result = system.initialize().await;
        assert!(result.is_ok());
        
        // 测试创建完整订单
        let items = vec![
            OrderItem { product_id: 1, quantity: 2, price: 29.99 },
        ];
        
        let result = system.create_complete_order(1, items).await;
        assert!(result.is_ok());
        
        let complete_order = result.unwrap();
        assert_eq!(complete_order.user.id, 1);
        assert!(matches!(complete_order.order.status, OrderStatus::Confirmed | OrderStatus::Cancelled));
        assert!(matches!(complete_order.payment.status, PaymentStatus::Completed | PaymentStatus::Failed));
    }
}

/// 示例用法
pub async fn run_examples() {
    println!("=== 基础微服务案例 ===");
    
    // 创建微服务系统
    let system = MicroserviceSystem::new();
    
    // 初始化系统
    match system.initialize().await {
        Ok(_) => println!("系统初始化成功"),
        Err(e) => println!("系统初始化失败: {}", e),
    }
    
    // 测试用户服务
    println!("\n1. 测试用户服务:");
    let user = system.user_service.get_user(1).await;
    match user {
        Some(user) => println!("  用户: {} ({})", user.name, user.email),
        None => println!("  用户未找到"),
    }
    
    // 测试订单服务
    println!("\n2. 测试订单服务:");
    let order = system.order_service.get_order(1).await;
    match order {
        Some(order) => println!("  订单: ID={}, 总金额=${:.2}", order.id, order.total),
        None => println!("  订单未找到"),
    }
    
    // 测试支付服务
    println!("\n3. 测试支付服务:");
    let payment = Payment {
        id: rand::random::<u32>(),
        order_id: 1,
        amount: 100.0,
        method: PaymentMethod::CreditCard,
        status: PaymentStatus::Pending,
        created_at: chrono::Utc::now().to_rfc3339(),
    };
    
    match system.payment_service.process_payment(payment).await {
        Ok(payment) => println!("  支付处理成功: {:?}", payment.status),
        Err(e) => println!("  支付处理失败: {}", e),
    }
    
    // 测试完整订单流程
    println!("\n4. 测试完整订单流程:");
    let items = vec![
        OrderItem { product_id: 1, quantity: 1, price: 29.99 },
        OrderItem { product_id: 2, quantity: 2, price: 19.99 },
    ];
    
    match system.create_complete_order(1, items).await {
        Ok(complete_order) => {
            println!("  完整订单创建成功:");
            println!("    用户: {}", complete_order.user.name);
            println!("    订单: ID={}, 总金额=${:.2}", complete_order.order.id, complete_order.order.total);
            println!("    支付: {:?}", complete_order.payment.status);
        }
        Err(e) => println!("  完整订单创建失败: {}", e),
    }
    
    // 显示服务注册信息
    println!("\n5. 服务注册信息:");
    let services = system.registry.get_all_services().await;
    for service in services {
        println!("  {}: {} ({:?})", service.name, service.url, service.health);
    }
} 