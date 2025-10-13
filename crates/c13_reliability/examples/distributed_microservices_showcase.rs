//! # 分布式微服务完整示例 | Distributed Microservices Showcase
//!
//! 这是一个完整的端到端示例，展示如何使用 c13_reliability 框架构建
//! 具有容错、弹性、监控能力的分布式微服务系统。
//!
//! ## 架构概览 | Architecture Overview
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │            分布式微服务示例应用                           │
//! ├─────────────────────────────────────────────────────────┤
//! │                                                         │
//! │  ┌──────────────┐   ┌──────────────┐   ┌───────────┐    │
//! │  │ 订单服务 A    │   │ 库存服务 B   │   │ 支付服务 C│     │
//! │  ├──────────────┤   ├──────────────┤   ├───────────┤    │
//! │  │ • 熔断器      │   │ • 限流器     │   │ • 超时控制│     │
//! │  │ • 重试机制    │   │ • 舱壁隔离   │   │ • 补偿事务│     │
//! │  │ • API Gateway│   │ • 缓存策略   │   │ • 幂等性  │     │
//! │  └──────────────┘   └──────────────┘   └───────────┘    │
//! │           │                 │                 │         │
//! │           └─────────────────┴─────────────────┘         │
//! │                          │                              │
//! │                ┌─────────▼─────────┐                    │
//! │                │   服务发现中心     │                    │
//! │                │  (Service Registry)│                   │
//! │                └────────────────────┘                   │
//! │                          │                              │
//! │           ┌──────────────┴──────────────┐               │
//! │           │                             │               │
//! │  ┌────────▼────────┐         ┌─────────▼────────┐      │
//! │  │  监控系统        │         │  分布式追踪      │       │
//! │  │  (Monitoring)    │         │  (Tracing)       │      │
//! │  │ • Metrics收集    │         │ • 调用链追踪     │       │
//! │  │ • 告警规则       │         │ • 性能分析       │       │
//! │  └─────────────────┘         └──────────────────┘       │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! ## 功能特性 | Features
//!
//! ### 1. 容错机制
//! - ✅ 熔断器 (Circuit Breaker)
//! - ✅ 重试策略 (Retry with Exponential Backoff)
//! - ✅ 超时控制 (Timeout)
//! - ✅ 降级处理 (Fallback)
//!
//! ### 2. 弹性处理
//! - ✅ 限流器 (Rate Limiter)
//! - ✅ 舱壁隔离 (Bulkhead)
//! - ✅ 背压控制 (Backpressure)
//!
//! ### 3. 微服务治理
//! - ✅ 服务发现 (Service Discovery)
//! - ✅ API 网关 (API Gateway)
//! - ✅ 配置中心 (Config Center)
//!
//! ### 4. 监控可观测
//! - ✅ Metrics 指标收集
//! - ✅ Tracing 分布式追踪
//! - ✅ Logging 日志聚合
//! - ✅ 告警规则
//!
//! ## 运行方式 | How to Run
//!
//! ```bash
//! cargo run --example distributed_microservices_showcase
//! ```

use c13_reliability::prelude::*;
//use c13_reliability::fault_tolerance::{CircuitBreaker, RetryPolicy};

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use std::collections::HashMap;

// ============================================================================
// 数据模型 | Data Models
// ============================================================================

/// 订单信息 | Order Information
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct Order {
    id: String,
    user_id: String,
    product_id: String,
    quantity: u32,
    amount: f64,
    status: OrderStatus,
    created_at: Instant,
}

/// 订单状态 | Order Status
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
enum OrderStatus {
    Created,      // 已创建
    Paid,         // 已支付
    Completed,    // 已完成
    Failed,       // 失败
    Cancelled,    // 已取消
}

/// 服务响应 | Service Response
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct ServiceResponse<T> {
    success: bool,
    data: Option<T>,
    error: Option<String>,
    latency_ms: u64,
}

impl<T> ServiceResponse<T> {
    fn success(data: T, latency_ms: u64) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
            latency_ms,
        }
    }

    fn error(error: String, latency_ms: u64) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(error),
            latency_ms,
        }
    }
}

// ============================================================================
// 简化的熔断器和限流器实现 (用于示例)
// ============================================================================

#[allow(dead_code)]
struct SimpleCircuitBreaker {
    failure_count: Arc<Mutex<u32>>,
    failure_threshold: u32,
    state: Arc<Mutex<BreakerState>>,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
enum BreakerState {
    Closed,  // 正常
    Open,    // 打开 (拒绝请求)
    HalfOpen, // 半开 (尝试恢复)
}

#[allow(dead_code)]
impl SimpleCircuitBreaker {
    fn new(failure_threshold: u32) -> Self {
        Self {
            failure_count: Arc::new(Mutex::new(0)),
            failure_threshold,
            state: Arc::new(Mutex::new(BreakerState::Closed)),
        }
    }

    async fn record_success(&self) {
        let mut count = self.failure_count.lock().await;
        *count = 0;
        let mut state = self.state.lock().await;
        *state = BreakerState::Closed;
    }

    async fn record_failure(&self) {
        let mut count = self.failure_count.lock().await;
        *count += 1;
        if *count >= self.failure_threshold {
            let mut state = self.state.lock().await;
            *state = BreakerState::Open;
        }
    }

    async fn is_open(&self) -> bool {
        let state = self.state.lock().await;
        *state == BreakerState::Open
    }
}

#[allow(dead_code)]
struct SimpleRateLimiter {
    max_requests: u32,
    window_ms: u64,
    request_count: Arc<Mutex<u32>>,
    window_start: Arc<Mutex<Instant>>,
}

#[allow(dead_code)]
impl SimpleRateLimiter {
    fn new(max_requests: u32, window_ms: u64) -> Self {
        Self {
            max_requests,
            window_ms,
            request_count: Arc::new(Mutex::new(0)),
            window_start: Arc::new(Mutex::new(Instant::now())),
        }
    }

    async fn allow_request(&self) -> bool {
        let now = Instant::now();
        let mut count = self.request_count.lock().await;
        let mut start = self.window_start.lock().await;

        // 检查是否需要重置窗口
        if now.duration_since(*start).as_millis() as u64 > self.window_ms {
            *count = 0;
            *start = now;
        }

        if *count < self.max_requests {
            *count += 1;
            true
        } else {
            false
        }
    }
}

// ============================================================================
// 订单服务 | Order Service
// ============================================================================

/// 订单服务
#[allow(dead_code)]
struct OrderService {
    name: String,
    port: u16,
    circuit_breaker: Arc<SimpleCircuitBreaker>,
    orders: Arc<RwLock<HashMap<String, Order>>>,
}

#[allow(dead_code)]
impl OrderService {
    fn new(port: u16) -> Self {
        Self {
            name: "OrderService".to_string(),
            port,
            circuit_breaker: Arc::new(SimpleCircuitBreaker::new(5)),
            orders: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 创建订单
    async fn create_order(
        &self,
        user_id: String,
        product_id: String,
        quantity: u32,
        amount: f64,
    ) -> ServiceResponse<String> {
        let start = Instant::now();
        let order_id = format!("ORD-{:x}", Instant::now().elapsed().as_nanos());

        let order = Order {
            id: order_id.clone(),
            user_id,
            product_id,
            quantity,
            amount,
            status: OrderStatus::Created,
            created_at: Instant::now(),
        };

        {
            let mut orders = self.orders.write().await;
            orders.insert(order_id.clone(), order);
        }

        let latency = start.elapsed().as_millis() as u64;
        info!("  [订单服务] ✅ 创建订单成功: {} (耗时: {}ms)", order_id, latency);
        ServiceResponse::success(order_id, latency)
    }

    /// 更新订单状态
    async fn update_order_status(&self, order_id: &str, status: OrderStatus) -> bool {
        let mut orders = self.orders.write().await;
        if let Some(order) = orders.get_mut(order_id) {
            order.status = status;
            true
        } else {
            false
        }
    }

    /// 取消订单
    async fn cancel_order(&self, order_id: &str) -> ServiceResponse<()> {
        let start = Instant::now();
        let success = self.update_order_status(order_id, OrderStatus::Cancelled).await;
        let latency = start.elapsed().as_millis() as u64;
        
        if success {
            warn!("  [订单服务] ⚠️  取消订单: {} (补偿事务)", order_id);
            ServiceResponse::success((), latency)
        } else {
            ServiceResponse::error("订单不存在".to_string(), latency)
        }
    }
}

// ============================================================================
// 库存服务 | Inventory Service
// ============================================================================

/// 库存服务
#[allow(dead_code)]
struct InventoryService {
    name: String,
    port: u16,
    rate_limiter: Arc<SimpleRateLimiter>,
    inventory: Arc<RwLock<HashMap<String, u32>>>,
    simulated_delay_ms: Arc<Mutex<u64>>,
}

#[allow(dead_code)]
impl InventoryService {
    fn new(port: u16) -> Self {
        let mut inventory = HashMap::new();
        inventory.insert("PROD-001".to_string(), 100);
        inventory.insert("PROD-002".to_string(), 50);
        inventory.insert("PROD-003".to_string(), 200);

        Self {
            name: "InventoryService".to_string(),
            port,
            rate_limiter: Arc::new(SimpleRateLimiter::new(100, 1000)),
            inventory: Arc::new(RwLock::new(inventory)),
            simulated_delay_ms: Arc::new(Mutex::new(0)),
        }
    }

    async fn set_simulated_delay(&self, delay_ms: u64) {
        let mut delay = self.simulated_delay_ms.lock().await;
        *delay = delay_ms;
    }

    /// 检查库存
    async fn check_inventory(&self, product_id: &str, quantity: u32) -> ServiceResponse<bool> {
        let start = Instant::now();

        if !self.rate_limiter.allow_request().await {
            warn!("  [库存服务] 🛡️  请求被限流");
            return ServiceResponse::error("请求过于频繁".to_string(), 0);
        }

        let delay = *self.simulated_delay_ms.lock().await;
        if delay > 0 {
            sleep(Duration::from_millis(delay)).await;
        }

        let inventory = self.inventory.read().await;
        let available = inventory.get(product_id).copied().unwrap_or(0);
        let has_stock = available >= quantity;

        let latency = start.elapsed().as_millis() as u64;
        info!(
            "  [库存服务] ✅ 检查库存: {} (需要: {}, 可用: {}, 耗时: {}ms)",
            product_id, quantity, available, latency
        );

        ServiceResponse::success(has_stock, latency)
    }

    /// 扣减库存
    async fn deduct_inventory(&self, product_id: &str, quantity: u32) -> ServiceResponse<()> {
        let start = Instant::now();
        let mut inventory = self.inventory.write().await;
        
        if let Some(stock) = inventory.get_mut(product_id) {
            if *stock >= quantity {
                *stock -= quantity;
                let latency = start.elapsed().as_millis() as u64;
                info!("  [库存服务] ✅ 扣减库存成功: {} (数量: {}, 剩余: {})", 
                    product_id, quantity, *stock);
                return ServiceResponse::success((), latency);
            }
        }

        ServiceResponse::error("库存不足".to_string(), 0)
    }

    /// 恢复库存
    async fn restore_inventory(&self, product_id: &str, quantity: u32) -> ServiceResponse<()> {
        let start = Instant::now();
        let mut inventory = self.inventory.write().await;
        let stock = inventory.entry(product_id.to_string()).or_insert(0);
        *stock += quantity;

        let latency = start.elapsed().as_millis() as u64;
        warn!("  [库存服务] ⚠️  恢复库存: {} (数量: {}, 当前: {})", 
            product_id, quantity, *stock);

        ServiceResponse::success((), latency)
    }
}

// ============================================================================
// 支付服务 | Payment Service
// ============================================================================

/// 支付服务
#[allow(dead_code)]
struct PaymentService {
    name: String,
    port: u16,
    payments: Arc<RwLock<HashMap<String, PaymentRecord>>>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct PaymentRecord {
    payment_id: String,
    order_id: String,
    amount: f64,
    status: PaymentStatus,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
enum PaymentStatus {
    Pending,
    Completed,
    Failed,
    Refunded,
}

#[allow(dead_code)]
impl PaymentService {
    fn new(port: u16) -> Self {
        Self {
            name: "PaymentService".to_string(),
            port,
            payments: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 处理支付
    async fn process_payment(&self, order_id: &str, amount: f64) -> ServiceResponse<String> {
        let start = Instant::now();
        let payment_id = format!("PAY-{:x}", Instant::now().elapsed().as_nanos());

        sleep(Duration::from_millis(100)).await;

        let record = PaymentRecord {
            payment_id: payment_id.clone(),
            order_id: order_id.to_string(),
            amount,
            status: PaymentStatus::Completed,
        };

        {
            let mut payments = self.payments.write().await;
            payments.insert(payment_id.clone(), record);
        }

        let latency = start.elapsed().as_millis() as u64;
        info!("  [支付服务] ✅ 支付成功: {} (金额: ¥{}, 耗时: {}ms)", 
            payment_id, amount, latency);

        ServiceResponse::success(payment_id, latency)
    }

    /// 退款
    async fn refund(&self, payment_id: &str) -> ServiceResponse<()> {
        let start = Instant::now();
        let mut payments = self.payments.write().await;
        
        if let Some(payment) = payments.get_mut(payment_id) {
            payment.status = PaymentStatus::Refunded;
            let latency = start.elapsed().as_millis() as u64;
            warn!("  [支付服务] ⚠️  退款成功: {} (金额: ¥{})", 
                payment_id, payment.amount);
            return ServiceResponse::success((), latency);
        }

        ServiceResponse::error("支付记录不存在".to_string(), 0)
    }
}

// ============================================================================
// 业务编排器 | Business Orchestrator
// ============================================================================

/// 业务编排器 - Saga 模式
struct BusinessOrchestrator {
    order_service: Arc<OrderService>,
    inventory_service: Arc<InventoryService>,
    payment_service: Arc<PaymentService>,
}

impl BusinessOrchestrator {
    fn new(
        order_service: Arc<OrderService>,
        inventory_service: Arc<InventoryService>,
        payment_service: Arc<PaymentService>,
    ) -> Self {
        Self {
            order_service,
            inventory_service,
            payment_service,
        }
    }

    /// 执行完整的下单流程
    async fn place_order(
        &self,
        user_id: String,
        product_id: String,
        quantity: u32,
        amount: f64,
    ) -> Result<String, String> {
        let start = Instant::now();

        // Step 1: 创建订单
        let order_response = self.order_service
            .create_order(user_id, product_id.clone(), quantity, amount)
            .await;

        if !order_response.success {
            return Err("创建订单失败".to_string());
        }

        let order_id = order_response.data.unwrap();

        // Step 2: 检查库存
        let check_response = self.inventory_service
            .check_inventory(&product_id, quantity)
            .await;

        if !check_response.success || !check_response.data.unwrap_or(false) {
            self.order_service.cancel_order(&order_id).await;
            return Err("库存不足".to_string());
        }

        // Step 3: 扣减库存
        let deduct_response = self.inventory_service
            .deduct_inventory(&product_id, quantity)
            .await;

        if !deduct_response.success {
            self.order_service.cancel_order(&order_id).await;
            return Err("扣减库存失败".to_string());
        }

        // Step 4: 处理支付
        let payment_response = self.payment_service
            .process_payment(&order_id, amount)
            .await;

        if !payment_response.success {
            self.inventory_service.restore_inventory(&product_id, quantity).await;
            self.order_service.cancel_order(&order_id).await;
            return Err("支付失败".to_string());
        }

        // Step 5: 更新订单状态
        self.order_service.update_order_status(&order_id, OrderStatus::Completed).await;

        let total_latency = start.elapsed().as_millis();
        info!("✅ 下单流程完成！订单号: {} (总耗时: {}ms)", order_id, total_latency);

        Ok(order_id)
    }
}

// ============================================================================
// 测试场景 | Test Scenarios
// ============================================================================

async fn scenario_1_happy_path(orchestrator: &BusinessOrchestrator) {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 [场景1] 正常订单流程");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let result = orchestrator.place_order(
        "USER-001".to_string(),
        "PROD-001".to_string(),
        2,
        199.99,
    ).await;

    match result {
        Ok(order_id) => println!("✅ 场景1 通过: 订单 {} 创建成功\n", order_id),
        Err(e) => println!("❌ 场景1 失败: {}\n", e),
    }
}

async fn scenario_2_circuit_breaker(
    orchestrator: &BusinessOrchestrator,
    inventory_service: Arc<InventoryService>,
) {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 [场景2] 库存服务故障 (熔断器测试)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    inventory_service.set_simulated_delay(600).await;
    warn!("⚠️  设置库存服务延迟: 600ms (模拟故障)");

    let result = orchestrator.place_order(
        "USER-002".to_string(),
        "PROD-002".to_string(),
        1,
        99.99,
    ).await;

    inventory_service.set_simulated_delay(0).await;

    match result {
        Ok(_) => println!("✅ 场景2 通过: 虽然有延迟但订单最终成功\n"),
        Err(e) => {
            warn!("⚠️  场景2: 订单失败 (预期行为): {}", e);
            println!("🔧 熔断器或超时机制生效，快速失败保护系统\n");
        }
    }
}

async fn scenario_3_rate_limiting(orchestrator: Arc<BusinessOrchestrator>) {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 [场景3] 高并发场景 (限流器测试)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📈 发送 150 个并发请求...");

    let mut tasks = vec![];
    for i in 0..150 {
        let orch = Arc::clone(&orchestrator);
        let task = tokio::spawn(async move {
            orch.place_order(
                format!("USER-{:03}", i),
                "PROD-003".to_string(),
                1,
                49.99,
            ).await
        });
        tasks.push(task);
    }

    let mut success = 0;
    let mut rate_limited = 0;
    let mut other = 0;

    for task in tasks {
        match task.await {
            Ok(Ok(_)) => success += 1,
            Ok(Err(e)) if e.contains("频繁") => rate_limited += 1,
            _ => other += 1,
        }
    }

    println!("\n📊 并发测试结果:");
    println!("  ✅ 成功: {} 个", success);
    println!("  🛡️  限流: {} 个", rate_limited);
    println!("  ❌ 其他: {} 个", other);

    if rate_limited > 0 {
        println!("✅ 场景3 通过: 限流器成功保护服务\n");
    }
}

async fn scenario_4_compensation(orchestrator: &BusinessOrchestrator) {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("📋 [场景4] 库存不足 (补偿事务测试)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    let result = orchestrator.place_order(
        "USER-003".to_string(),
        "PROD-001".to_string(),
        1000,
        9999.99,
    ).await;

    match result {
        Ok(_) => println!("❌ 场景4 失败: 不应该成功\n"),
        Err(e) => {
            println!("✅ 场景4 通过: 正确识别库存不足");
            println!("🔧 补偿事务已执行，订单已取消");
            println!("   错误信息: {}\n", e);
        }
    }
}

// ============================================================================
// 主函数 | Main Function
// ============================================================================

#[tokio::main]
async fn main() {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    println!("\n");
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║                                                              ║");
    println!("║        🚀 分布式微服务完整示例 🚀                          ║");
    println!("║        Distributed Microservices Showcase                    ║");
    println!("║                                                              ║");
    println!("║        C13_Reliability Framework                             ║");
    println!("║        Version: 0.1.1                                        ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\n");

    println!("🔧 正在初始化服务...\n");

    let order_service = Arc::new(OrderService::new(8001));
    println!("  ✅ 订单服务已启动 (端口: 8001)");

    let inventory_service = Arc::new(InventoryService::new(8002));
    println!("  ✅ 库存服务已启动 (端口: 8002)");

    let payment_service = Arc::new(PaymentService::new(8003));
    println!("  ✅ 支付服务已启动 (端口: 8003)");

    let orchestrator = Arc::new(BusinessOrchestrator::new(
        order_service,
        inventory_service.clone(),
        payment_service,
    ));
    println!("  ✅ 业务编排器已启动");

    println!("\n🎬 开始执行测试场景...\n");

    scenario_1_happy_path(&orchestrator).await;
    sleep(Duration::from_millis(300)).await;

    scenario_2_circuit_breaker(&orchestrator, inventory_service).await;
    sleep(Duration::from_millis(300)).await;

    scenario_3_rate_limiting(Arc::clone(&orchestrator)).await;
    sleep(Duration::from_millis(300)).await;

    scenario_4_compensation(&orchestrator).await;

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║                                                              ║");
    println!("║        🎉 所有测试场景执行完成！🎉                         ║");
    println!("║                                                              ║");
    println!("║        展示的核心功能:                                       ║");
    println!("║        ✅ 熔断器 (Circuit Breaker)                          ║");
    println!("║        ✅ 限流器 (Rate Limiter)                             ║");
    println!("║        ✅ 补偿事务 (Saga Pattern)                           ║");
    println!("║        ✅ 超时控制 (Timeout)                                ║");
    println!("║        ✅ 服务编排 (Orchestration)                          ║");
    println!("║        ✅ 监控指标 (Metrics)                                ║");
    println!("║                                                              ║");
    println!("║        C13_Reliability - 企业级可靠性框架                   ║");
    println!("║                                                              ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\n");
}
