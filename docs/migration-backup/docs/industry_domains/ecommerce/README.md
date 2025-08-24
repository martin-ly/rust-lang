# 电子商务 - Rust架构指南

## 概述

电子商务领域需要处理高并发交易、实时库存管理、个性化推荐、支付处理等复杂业务场景。Rust的高性能和内存安全特性使其成为构建电商平台的理想选择。本指南涵盖在线商城、支付系统、库存管理、推荐引擎等核心领域。

## Rust架构选型

### 核心技术栈

#### 电商框架

- **Web框架**: `actix-web`, `axum`, `rocket`, `warp`
- **数据库**: `diesel`, `sqlx`, `seaorm`, `redis-rs`
- **搜索引擎**: `elasticsearch-rs`, `meilisearch-rs`
- **消息队列**: `kafka-rust`, `rabbitmq-rs`, `redis-streams`

#### 支付和金融

- **支付处理**: `stripe-rs`, `paypal-rs`, `alipay-rs`
- **加密**: `ring`, `rustls`, `aes-gcm`
- **合规**: `pci-dss-rs`, `gdpr-rs`
- **风控**: `fraud-detection-rs`, `risk-assessment`

#### 推荐和AI

- **推荐系统**: `collaborative-filtering`, `content-based-rs`
- **机器学习**: `tch-rs`, `burn`, `candle`
- **数据分析**: `polars`, `ndarray`, `statrs`
- **实时处理**: `flink-rust`, `kafka-streams`

### 架构模式

#### 微服务电商架构

```rust
use actix_web::{web, App, HttpServer, middleware};
use serde::{Deserialize, Serialize};

#[derive(Clone)]
pub struct ECommerceMicroservices {
    user_service: UserService,
    product_service: ProductService,
    order_service: OrderService,
    payment_service: PaymentService,
    inventory_service: InventoryService,
    recommendation_service: RecommendationService,
    notification_service: NotificationService,
}

impl ECommerceMicroservices {
    pub async fn start_services(&self) -> Result<(), ServiceError> {
        // 启动用户服务
        let user_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(user_routes())
        })
        .bind("127.0.0.1:8081")?
        .run();

        // 启动产品服务
        let product_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(product_routes())
        })
        .bind("127.0.0.1:8082")?
        .run();

        // 启动订单服务
        let order_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(order_routes())
        })
        .bind("127.0.0.1:8083")?
        .run();

        // 启动支付服务
        let payment_server = HttpServer::new(|| {
            App::new()
                .wrap(middleware::Logger::default())
                .wrap(middleware::Cors::default())
                .service(payment_routes())
        })
        .bind("127.0.0.1:8084")?
        .run();

        // 并行运行所有服务
        tokio::try_join!(user_server, product_server, order_server, payment_server)?;
        Ok(())
    }
}

#[derive(Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub email: String,
    pub username: String,
    pub profile: UserProfile,
    pub preferences: UserPreferences,
    pub addresses: Vec<Address>,
    pub payment_methods: Vec<PaymentMethod>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub struct UserProfile {
    pub first_name: String,
    pub last_name: String,
    pub phone: Option<String>,
    pub date_of_birth: Option<Date<Utc>>,
    pub avatar_url: Option<String>,
    pub language: String,
    pub currency: String,
}

#[derive(Serialize, Deserialize)]
pub struct Product {
    pub id: String,
    pub name: String,
    pub description: String,
    pub category: Category,
    pub brand: String,
    pub sku: String,
    pub price: Money,
    pub sale_price: Option<Money>,
    pub inventory: InventoryInfo,
    pub images: Vec<ProductImage>,
    pub attributes: HashMap<String, String>,
    pub variants: Vec<ProductVariant>,
    pub status: ProductStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}
```

#### 事件驱动电商架构

```rust
use tokio::sync::broadcast;
use serde::{Deserialize, Serialize};

#[derive(Clone, Serialize, Deserialize)]
pub struct ECommerceEvent {
    pub id: String,
    pub event_type: ECommerceEventType,
    pub user_id: Option<String>,
    pub data: serde_json::Value,
    pub timestamp: DateTime<Utc>,
    pub correlation_id: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub enum ECommerceEventType {
    UserRegistered,
    UserLoggedIn,
    ProductViewed,
    ProductAddedToCart,
    ProductRemovedFromCart,
    OrderCreated,
    OrderPaid,
    OrderShipped,
    OrderDelivered,
    PaymentProcessed,
    PaymentFailed,
    InventoryUpdated,
    PriceChanged,
}

pub struct EventDrivenECommerce {
    event_bus: EventBus,
    event_handlers: HashMap<ECommerceEventType, Vec<Box<dyn EventHandler>>>,
    saga_orchestrator: SagaOrchestrator,
    notification_service: NotificationService,
}

impl EventDrivenECommerce {
    pub async fn process_event(&self, event: ECommerceEvent) -> Result<(), EventError> {
        // 1. 发布事件到事件总线
        self.event_bus.publish(event.clone()).await?;
        
        // 2. 处理事件
        if let Some(handlers) = self.event_handlers.get(&event.event_type) {
            for handler in handlers {
                handler.handle(&event).await?;
            }
        }
        
        // 3. 处理分布式事务
        if self.requires_saga(&event.event_type) {
            self.saga_orchestrator.process_saga(&event).await?;
        }
        
        // 4. 发送通知
        if self.requires_notification(&event.event_type) {
            self.notification_service.send_notification(&event).await?;
        }
        
        Ok(())
    }
    
    pub async fn subscribe_to_events(
        &mut self,
        event_type: ECommerceEventType,
        handler: Box<dyn EventHandler>,
    ) {
        self.event_handlers
            .entry(event_type)
            .or_insert_with(Vec::new)
            .push(handler);
    }
}
```

## 业务领域概念建模

### 核心领域模型

#### 订单管理系统

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: String,
    pub user_id: String,
    pub order_number: String,
    pub items: Vec<OrderItem>,
    pub status: OrderStatus,
    pub payment_info: PaymentInfo,
    pub shipping_info: ShippingInfo,
    pub billing_info: BillingInfo,
    pub totals: OrderTotals,
    pub notes: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub id: String,
    pub product_id: String,
    pub variant_id: Option<String>,
    pub quantity: u32,
    pub unit_price: Money,
    pub total_price: Money,
    pub discount: Money,
    pub tax: Money,
    pub attributes: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
    Refunded,
    Returned,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaymentInfo {
    pub payment_method: PaymentMethod,
    pub transaction_id: Option<String>,
    pub status: PaymentStatus,
    pub amount: Money,
    pub currency: String,
    pub processed_at: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShippingInfo {
    pub address: Address,
    pub method: ShippingMethod,
    pub cost: Money,
    pub tracking_number: Option<String>,
    pub estimated_delivery: Option<DateTime<Utc>>,
    pub actual_delivery: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderTotals {
    pub subtotal: Money,
    pub tax: Money,
    pub shipping: Money,
    pub discount: Money,
    pub total: Money,
}
```

#### 库存管理系统

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Inventory {
    pub id: String,
    pub product_id: String,
    pub variant_id: Option<String>,
    pub warehouse_id: String,
    pub quantity: u32,
    pub reserved_quantity: u32,
    pub available_quantity: u32,
    pub low_stock_threshold: u32,
    pub reorder_point: u32,
    pub reorder_quantity: u32,
    pub last_updated: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InventoryTransaction {
    pub id: String,
    pub inventory_id: String,
    pub transaction_type: InventoryTransactionType,
    pub quantity: i32,
    pub reason: String,
    pub reference_id: Option<String>,
    pub notes: Option<String>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InventoryTransactionType {
    Purchase,
    Sale,
    Return,
    Adjustment,
    Transfer,
    Damage,
    Expiry,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Warehouse {
    pub id: String,
    pub name: String,
    pub address: Address,
    pub contact_info: ContactInfo,
    pub operating_hours: OperatingHours,
    pub capacity: WarehouseCapacity,
    pub status: WarehouseStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WarehouseCapacity {
    pub total_space: f64,
    pub used_space: f64,
    pub available_space: f64,
    pub unit: String,
}
```

#### 推荐系统

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecommendationEngine {
    pub id: String,
    pub name: String,
    pub algorithm: RecommendationAlgorithm,
    pub parameters: HashMap<String, f64>,
    pub status: EngineStatus,
    pub performance_metrics: PerformanceMetrics,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecommendationAlgorithm {
    CollaborativeFiltering,
    ContentBased,
    Hybrid,
    MatrixFactorization,
    DeepLearning,
    ContextualBandit,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Recommendation {
    pub id: String,
    pub user_id: String,
    pub product_id: String,
    pub score: f64,
    pub reason: String,
    pub algorithm: String,
    pub context: RecommendationContext,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RecommendationContext {
    pub session_id: Option<String>,
    pub category: Option<String>,
    pub price_range: Option<PriceRange>,
    pub user_segment: Option<String>,
    pub time_of_day: Option<u8>,
    pub day_of_week: Option<u8>,
    pub device_type: Option<String>,
    pub location: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserBehavior {
    pub user_id: String,
    pub behavior_type: BehaviorType,
    pub product_id: Option<String>,
    pub category_id: Option<String>,
    pub session_id: Option<String>,
    pub timestamp: DateTime<Utc>,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BehaviorType {
    View,
    AddToCart,
    RemoveFromCart,
    Purchase,
    Wishlist,
    Search,
    Click,
    Scroll,
}
```

## 数据建模

### 电商数据存储

#### 分布式缓存系统

```rust
use redis::AsyncCommands;
use std::collections::HashMap;

pub struct DistributedCache {
    redis_client: redis::Client,
    cache_config: CacheConfig,
    cache_stats: CacheStats,
}

impl DistributedCache {
    pub async fn new(redis_url: &str, config: CacheConfig) -> Result<Self, CacheError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(Self {
            redis_client: client,
            cache_config: config,
            cache_stats: CacheStats::new(),
        })
    }
    
    pub async fn get_product(&self, product_id: &str) -> Result<Option<Product>, CacheError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("product:{}", product_id);
        
        let result: Option<String> = conn.get(&key).await?;
        
        if let Some(data) = result {
            let product: Product = serde_json::from_str(&data)?;
            self.cache_stats.record_hit();
            Ok(Some(product))
        } else {
            self.cache_stats.record_miss();
            Ok(None)
        }
    }
    
    pub async fn set_product(&self, product: &Product, ttl: Option<Duration>) -> Result<(), CacheError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("product:{}", product.id);
        let data = serde_json::to_string(product)?;
        
        if let Some(ttl) = ttl {
            conn.set_ex(&key, data, ttl.as_secs() as usize).await?;
        } else {
            conn.set(&key, data).await?;
        }
        
        Ok(())
    }
    
    pub async fn get_user_cart(&self, user_id: &str) -> Result<Option<ShoppingCart>, CacheError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("cart:{}", user_id);
        
        let result: Option<String> = conn.get(&key).await?;
        
        if let Some(data) = result {
            let cart: ShoppingCart = serde_json::from_str(&data)?;
            Ok(Some(cart))
        } else {
            Ok(None)
        }
    }
    
    pub async fn update_cart(&self, user_id: &str, cart: &ShoppingCart) -> Result<(), CacheError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("cart:{}", user_id);
        let data = serde_json::to_string(cart)?;
        
        // 购物车数据设置较长的TTL
        conn.set_ex(&key, data, 24 * 60 * 60).await?; // 24小时
        
        Ok(())
    }
    
    pub async fn invalidate_product(&self, product_id: &str) -> Result<(), CacheError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("product:{}", product_id);
        
        conn.del(&key).await?;
        
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub default_ttl: Duration,
    pub max_memory: usize,
    pub eviction_policy: EvictionPolicy,
    pub compression_enabled: bool,
}

#[derive(Debug, Clone)]
pub enum EvictionPolicy {
    LRU,
    LFU,
    TTL,
    Random,
}
```

#### 搜索引擎集成

```rust
use elasticsearch::{Elasticsearch, SearchParts};
use serde_json::json;

pub struct ProductSearchEngine {
    elastic_client: Elasticsearch,
    search_config: SearchConfig,
}

impl ProductSearchEngine {
    pub async fn new(elastic_url: &str, config: SearchConfig) -> Result<Self, SearchError> {
        let client = Elasticsearch::new(elastic_url)?;
        
        Ok(Self {
            elastic_client: client,
            search_config: config,
        })
    }
    
    pub async fn index_product(&self, product: &Product) -> Result<(), SearchError> {
        let response = self.elastic_client
            .index(elasticsearch::IndexParts::Index("products"))
            .body(json!({
                "id": product.id,
                "name": product.name,
                "description": product.description,
                "category": product.category.name,
                "brand": product.brand,
                "price": product.price.amount,
                "currency": product.price.currency,
                "attributes": product.attributes,
                "tags": self.extract_tags(product),
                "created_at": product.created_at,
                "updated_at": product.updated_at,
            }))
            .send()
            .await?;
        
        if !response.status_code().is_success() {
            return Err(SearchError::IndexingFailed);
        }
        
        Ok(())
    }
    
    pub async fn search_products(&self, query: &SearchQuery) -> Result<SearchResult, SearchError> {
        let search_body = self.build_search_query(query).await?;
        
        let response = self.elastic_client
            .search(SearchParts::Index(&["products"]))
            .body(search_body)
            .send()
            .await?;
        
        let body: serde_json::Value = response.json().await?;
        
        // 解析搜索结果
        let hits = body["hits"]["hits"].as_array().unwrap();
        let mut products = Vec::new();
        
        for hit in hits {
            let source = &hit["_source"];
            let product: Product = serde_json::from_value(source.clone())?;
            products.push(product);
        }
        
        let total = body["hits"]["total"]["value"].as_u64().unwrap_or(0);
        
        Ok(SearchResult {
            products,
            total,
            took: body["took"].as_u64().unwrap_or(0),
            aggregations: self.parse_aggregations(&body).await?,
        })
    }
    
    async fn build_search_query(&self, query: &SearchQuery) -> Result<serde_json::Value, SearchError> {
        let mut search_body = json!({
            "query": {
                "bool": {
                    "must": [],
                    "filter": [],
                    "should": []
                }
            },
            "sort": [],
            "aggs": {},
            "size": query.limit.unwrap_or(20),
            "from": query.offset.unwrap_or(0)
        });
        
        // 添加文本搜索
        if !query.text.is_empty() {
            let text_query = json!({
                "multi_match": {
                    "query": query.text,
                    "fields": ["name^3", "description^2", "brand", "category"],
                    "type": "best_fields",
                    "fuzziness": "AUTO"
                }
            });
            search_body["query"]["bool"]["must"].as_array_mut().unwrap().push(text_query);
        }
        
        // 添加价格过滤
        if let Some(price_range) = &query.price_range {
            let price_filter = json!({
                "range": {
                    "price": {
                        "gte": price_range.min,
                        "lte": price_range.max
                    }
                }
            });
            search_body["query"]["bool"]["filter"].as_array_mut().unwrap().push(price_filter);
        }
        
        // 添加分类过滤
        if !query.categories.is_empty() {
            let category_filter = json!({
                "terms": {
                    "category": query.categories
                }
            });
            search_body["query"]["bool"]["filter"].as_array_mut().unwrap().push(category_filter);
        }
        
        // 添加排序
        if let Some(sort_field) = &query.sort_by {
            let sort = json!({
                sort_field: {
                    "order": query.sort_order.as_deref().unwrap_or("desc")
                }
            });
            search_body["sort"].as_array_mut().unwrap().push(sort);
        }
        
        Ok(search_body)
    }
}
```

## 流程建模

### 电商业务流程

#### 订单处理流程

```rust
pub struct OrderProcessingWorkflow {
    order_service: OrderService,
    inventory_service: InventoryService,
    payment_service: PaymentService,
    shipping_service: ShippingService,
    notification_service: NotificationService,
}

impl OrderProcessingWorkflow {
    pub async fn process_order(&self, order_request: OrderRequest) -> Result<OrderResult, WorkflowError> {
        let mut workflow_state = WorkflowState::new();
        
        // 1. 验证订单
        let validated_order = self.order_service.validate_order(&order_request).await?;
        workflow_state.add_step("order_validation", StepStatus::Completed);
        
        // 2. 检查库存
        let inventory_check = self.inventory_service.check_availability(&validated_order).await?;
        if !inventory_check.available {
            return Err(WorkflowError::InsufficientInventory(inventory_check.unavailable_items));
        }
        workflow_state.add_step("inventory_check", StepStatus::Completed);
        
        // 3. 预留库存
        let inventory_reservation = self.inventory_service.reserve_inventory(&validated_order).await?;
        workflow_state.add_step("inventory_reservation", StepStatus::Completed);
        
        // 4. 创建订单
        let order = self.order_service.create_order(&validated_order).await?;
        workflow_state.add_step("order_creation", StepStatus::Completed);
        
        // 5. 处理支付
        let payment_result = self.payment_service.process_payment(&order).await?;
        if !payment_result.success {
            // 释放库存
            self.inventory_service.release_reservation(&inventory_reservation).await?;
            return Err(WorkflowError::PaymentFailed(payment_result.error_message));
        }
        workflow_state.add_step("payment_processing", StepStatus::Completed);
        
        // 6. 确认订单
        let confirmed_order = self.order_service.confirm_order(&order).await?;
        workflow_state.add_step("order_confirmation", StepStatus::Completed);
        
        // 7. 安排发货
        let shipping_arrangement = self.shipping_service.arrange_shipping(&confirmed_order).await?;
        workflow_state.add_step("shipping_arrangement", StepStatus::Completed);
        
        // 8. 发送通知
        self.notification_service.send_order_confirmation(&confirmed_order).await?;
        workflow_state.add_step("notification_sent", StepStatus::Completed);
        
        Ok(OrderResult {
            order: confirmed_order,
            payment_result,
            shipping_arrangement,
            workflow_state,
        })
    }
}
```

#### 支付处理流程

```rust
pub struct PaymentProcessingWorkflow {
    payment_gateway: PaymentGateway,
    fraud_detection: FraudDetection,
    risk_assessment: RiskAssessment,
    compliance_checker: ComplianceChecker,
}

impl PaymentProcessingWorkflow {
    pub async fn process_payment(&self, payment_request: PaymentRequest) -> Result<PaymentResult, PaymentError> {
        let mut workflow_state = WorkflowState::new();
        
        // 1. 验证支付信息
        let validated_payment = self.validate_payment_info(&payment_request).await?;
        workflow_state.add_step("payment_validation", StepStatus::Completed);
        
        // 2. 欺诈检测
        let fraud_check = self.fraud_detection.check_transaction(&validated_payment).await?;
        if fraud_check.risk_score > 0.8 {
            return Err(PaymentError::HighFraudRisk(fraud_check.reason));
        }
        workflow_state.add_step("fraud_detection", StepStatus::Completed);
        
        // 3. 风险评估
        let risk_assessment = self.risk_assessment.assess_risk(&validated_payment).await?;
        if risk_assessment.risk_level == RiskLevel::High {
            // 需要额外验证
            let additional_verification = self.perform_additional_verification(&validated_payment).await?;
            if !additional_verification.verified {
                return Err(PaymentError::VerificationFailed);
            }
        }
        workflow_state.add_step("risk_assessment", StepStatus::Completed);
        
        // 4. 合规检查
        let compliance_check = self.compliance_checker.check_compliance(&validated_payment).await?;
        if !compliance_check.compliant {
            return Err(PaymentError::ComplianceViolation(compliance_check.violations));
        }
        workflow_state.add_step("compliance_check", StepStatus::Completed);
        
        // 5. 处理支付
        let payment_result = self.payment_gateway.process_payment(&validated_payment).await?;
        workflow_state.add_step("payment_processing", StepStatus::Completed);
        
        // 6. 记录交易
        let transaction_record = self.record_transaction(&payment_result).await?;
        workflow_state.add_step("transaction_recording", StepStatus::Completed);
        
        Ok(PaymentResult {
            transaction_id: payment_result.transaction_id,
            status: payment_result.status,
            amount: payment_result.amount,
            currency: payment_result.currency,
            processing_fee: payment_result.processing_fee,
            transaction_record,
            workflow_state,
        })
    }
    
    async fn validate_payment_info(&self, request: &PaymentRequest) -> Result<ValidatedPayment, ValidationError> {
        let mut validation_result = ValidatedPayment::new();
        
        // 验证金额
        if request.amount <= 0.0 {
            return Err(ValidationError::InvalidAmount);
        }
        
        // 验证货币
        if !self.is_valid_currency(&request.currency) {
            return Err(ValidationError::InvalidCurrency);
        }
        
        // 验证支付方式
        match &request.payment_method {
            PaymentMethod::CreditCard(card) => {
                if !self.validate_credit_card(card).await? {
                    return Err(ValidationError::InvalidCreditCard);
                }
            }
            PaymentMethod::BankTransfer(transfer) => {
                if !self.validate_bank_transfer(transfer).await? {
                    return Err(ValidationError::InvalidBankTransfer);
                }
            }
            PaymentMethod::DigitalWallet(wallet) => {
                if !self.validate_digital_wallet(wallet).await? {
                    return Err(ValidationError::InvalidDigitalWallet);
                }
            }
        }
        
        validation_result.payment_request = request.clone();
        Ok(validation_result)
    }
}
```

## 组件建模

### 核心电商组件

#### 购物车系统

```rust
use std::collections::HashMap;
use tokio::sync::RwLock;

pub struct ShoppingCartSystem {
    cart_store: Arc<RwLock<HashMap<String, ShoppingCart>>>,
    product_service: ProductService,
    pricing_engine: PricingEngine,
    inventory_checker: InventoryChecker,
}

impl ShoppingCartSystem {
    pub async fn add_to_cart(&self, user_id: &str, item: CartItem) -> Result<ShoppingCart, CartError> {
        let mut carts = self.cart_store.write().await;
        
        // 获取或创建购物车
        let cart = carts.entry(user_id.to_string()).or_insert_with(|| ShoppingCart {
            user_id: user_id.to_string(),
            items: HashMap::new(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        });
        
        // 验证产品
        let product = self.product_service.get_product(&item.product_id).await?;
        if product.status != ProductStatus::Active {
            return Err(CartError::ProductNotAvailable);
        }
        
        // 检查库存
        let inventory_check = self.inventory_checker.check_availability(&item.product_id, item.quantity).await?;
        if !inventory_check.available {
            return Err(CartError::InsufficientInventory);
        }
        
        // 计算价格
        let pricing = self.pricing_engine.calculate_price(&product, &item).await?;
        
        // 更新购物车
        let cart_item = CartItem {
            product_id: item.product_id,
            variant_id: item.variant_id,
            quantity: item.quantity,
            unit_price: pricing.unit_price,
            total_price: pricing.total_price,
            discount: pricing.discount,
            added_at: Utc::now(),
        };
        
        cart.items.insert(item.product_id.clone(), cart_item);
        cart.updated_at = Utc::now();
        
        // 重新计算购物车总计
        self.recalculate_cart_totals(cart).await?;
        
        Ok(cart.clone())
    }
    
    pub async fn remove_from_cart(&self, user_id: &str, product_id: &str) -> Result<ShoppingCart, CartError> {
        let mut carts = self.cart_store.write().await;
        
        if let Some(cart) = carts.get_mut(user_id) {
            cart.items.remove(product_id);
            cart.updated_at = Utc::now();
            
            // 重新计算购物车总计
            self.recalculate_cart_totals(cart).await?;
            
            Ok(cart.clone())
        } else {
            Err(CartError::CartNotFound)
        }
    }
    
    pub async fn update_quantity(&self, user_id: &str, product_id: &str, quantity: u32) -> Result<ShoppingCart, CartError> {
        let mut carts = self.cart_store.write().await;
        
        if let Some(cart) = carts.get_mut(user_id) {
            if let Some(item) = cart.items.get_mut(product_id) {
                if quantity == 0 {
                    cart.items.remove(product_id);
                } else {
                    // 检查库存
                    let inventory_check = self.inventory_checker.check_availability(product_id, quantity).await?;
                    if !inventory_check.available {
                        return Err(CartError::InsufficientInventory);
                    }
                    
                    // 更新数量
                    item.quantity = quantity;
                    item.total_price = item.unit_price * quantity as f64;
                }
                
                cart.updated_at = Utc::now();
                
                // 重新计算购物车总计
                self.recalculate_cart_totals(cart).await?;
                
                Ok(cart.clone())
            } else {
                Err(CartError::ItemNotFound)
            }
        } else {
            Err(CartError::CartNotFound)
        }
    }
    
    async fn recalculate_cart_totals(&self, cart: &mut ShoppingCart) -> Result<(), CartError> {
        let mut subtotal = 0.0;
        let mut total_discount = 0.0;
        
        for item in cart.items.values() {
            subtotal += item.total_price;
            total_discount += item.discount;
        }
        
        // 应用购物车级别的折扣
        let cart_discount = self.pricing_engine.calculate_cart_discount(subtotal).await?;
        total_discount += cart_discount;
        
        cart.subtotal = subtotal;
        cart.total_discount = total_discount;
        cart.total = subtotal - total_discount;
        
        Ok(())
    }
}
```

#### 推荐引擎

```rust
use std::collections::HashMap;

pub struct RecommendationEngine {
    collaborative_filter: CollaborativeFilter,
    content_based_filter: ContentBasedFilter,
    hybrid_recommender: HybridRecommender,
    user_behavior_analyzer: UserBehaviorAnalyzer,
}

impl RecommendationEngine {
    pub async fn generate_recommendations(&self, user_id: &str, context: &RecommendationContext) -> Result<Vec<Recommendation>, RecommendationError> {
        // 1. 分析用户行为
        let user_behavior = self.user_behavior_analyzer.analyze_behavior(user_id).await?;
        
        // 2. 协同过滤推荐
        let collaborative_recs = self.collaborative_filter.recommend(user_id, &user_behavior).await?;
        
        // 3. 基于内容的推荐
        let content_recs = self.content_based_filter.recommend(user_id, &user_behavior).await?;
        
        // 4. 混合推荐
        let hybrid_recs = self.hybrid_recommender.combine_recommendations(
            &collaborative_recs,
            &content_recs,
            context,
        ).await?;
        
        // 5. 排序和过滤
        let final_recommendations = self.rank_and_filter_recommendations(&hybrid_recs, context).await?;
        
        Ok(final_recommendations)
    }
    
    pub async fn update_user_preferences(&self, user_id: &str, interaction: &UserInteraction) -> Result<(), RecommendationError> {
        // 1. 更新用户行为模型
        self.user_behavior_analyzer.update_model(user_id, interaction).await?;
        
        // 2. 更新协同过滤模型
        self.collaborative_filter.update_model(user_id, interaction).await?;
        
        // 3. 更新内容过滤模型
        self.content_based_filter.update_model(user_id, interaction).await?;
        
        // 4. 重新训练混合模型
        self.hybrid_recommender.retrain_model().await?;
        
        Ok(())
    }
}

pub struct CollaborativeFilter {
    user_item_matrix: UserItemMatrix,
    similarity_calculator: SimilarityCalculator,
}

impl CollaborativeFilter {
    pub async fn recommend(&self, user_id: &str, behavior: &UserBehavior) -> Result<Vec<Recommendation>, RecommendationError> {
        // 1. 找到相似用户
        let similar_users = self.find_similar_users(user_id, behavior).await?;
        
        // 2. 获取相似用户的偏好
        let user_preferences = self.get_user_preferences(&similar_users).await?;
        
        // 3. 计算推荐分数
        let recommendations = self.calculate_recommendation_scores(user_id, &user_preferences).await?;
        
        Ok(recommendations)
    }
    
    async fn find_similar_users(&self, user_id: &str, behavior: &UserBehavior) -> Result<Vec<SimilarUser>, RecommendationError> {
        let user_vector = self.user_item_matrix.get_user_vector(user_id).await?;
        let mut similarities = Vec::new();
        
        for other_user_id in self.user_item_matrix.get_all_users().await? {
            if other_user_id != user_id {
                let other_vector = self.user_item_matrix.get_user_vector(&other_user_id).await?;
                let similarity = self.similarity_calculator.calculate_cosine_similarity(&user_vector, &other_vector);
                
                similarities.push(SimilarUser {
                    user_id: other_user_id,
                    similarity,
                });
            }
        }
        
        // 排序并返回最相似的用户
        similarities.sort_by(|a, b| b.similarity.partial_cmp(&a.similarity).unwrap());
        similarities.truncate(10); // 返回前10个最相似的用户
        
        Ok(similarities)
    }
}
```

## 运维运营

### 电商平台监控

#### 业务指标监控

```rust
use prometheus::{Counter, Histogram, Gauge};
use std::sync::Arc;

#[derive(Clone)]
pub struct ECommerceMetrics {
    active_users: Gauge,
    orders_created: Counter,
    orders_completed: Counter,
    revenue_total: Counter,
    cart_abandonment_rate: Gauge,
    conversion_rate: Gauge,
    average_order_value: Gauge,
    payment_success_rate: Gauge,
    inventory_alerts: Counter,
    search_queries: Counter,
}

impl ECommerceMetrics {
    pub fn new() -> Self {
        let active_users = Gauge::new(
            "active_users",
            "Number of currently active users"
        ).unwrap();
        
        let orders_created = Counter::new(
            "orders_created_total",
            "Total number of orders created"
        ).unwrap();
        
        let orders_completed = Counter::new(
            "orders_completed_total",
            "Total number of orders completed"
        ).unwrap();
        
        let revenue_total = Counter::new(
            "revenue_total",
            "Total revenue generated"
        ).unwrap();
        
        let cart_abandonment_rate = Gauge::new(
            "cart_abandonment_rate",
            "Cart abandonment rate percentage"
        ).unwrap();
        
        let conversion_rate = Gauge::new(
            "conversion_rate",
            "Conversion rate percentage"
        ).unwrap();
        
        let average_order_value = Gauge::new(
            "average_order_value",
            "Average order value"
        ).unwrap();
        
        let payment_success_rate = Gauge::new(
            "payment_success_rate",
            "Payment success rate percentage"
        ).unwrap();
        
        let inventory_alerts = Counter::new(
            "inventory_alerts_total",
            "Total number of inventory alerts"
        ).unwrap();
        
        let search_queries = Counter::new(
            "search_queries_total",
            "Total number of search queries"
        ).unwrap();
        
        Self {
            active_users,
            orders_created,
            orders_completed,
            revenue_total,
            cart_abandonment_rate,
            conversion_rate,
            average_order_value,
            payment_success_rate,
            inventory_alerts,
            search_queries,
        }
    }
    
    pub fn record_active_user(&self) {
        self.active_users.inc();
    }
    
    pub fn record_user_logout(&self) {
        self.active_users.dec();
    }
    
    pub fn record_order_created(&self) {
        self.orders_created.inc();
    }
    
    pub fn record_order_completed(&self) {
        self.orders_completed.inc();
    }
    
    pub fn record_revenue(&self, amount: f64) {
        self.revenue_total.inc_by(amount);
    }
    
    pub fn set_cart_abandonment_rate(&self, rate: f64) {
        self.cart_abandonment_rate.set(rate);
    }
    
    pub fn set_conversion_rate(&self, rate: f64) {
        self.conversion_rate.set(rate);
    }
    
    pub fn set_average_order_value(&self, value: f64) {
        self.average_order_value.set(value);
    }
    
    pub fn set_payment_success_rate(&self, rate: f64) {
        self.payment_success_rate.set(rate);
    }
    
    pub fn record_inventory_alert(&self) {
        self.inventory_alerts.inc();
    }
    
    pub fn record_search_query(&self) {
        self.search_queries.inc();
    }
}
```

#### 性能监控

```rust
pub struct PerformanceMonitor {
    response_time_tracker: ResponseTimeTracker,
    throughput_monitor: ThroughputMonitor,
    error_rate_tracker: ErrorRateTracker,
    resource_monitor: ResourceMonitor,
}

impl PerformanceMonitor {
    pub async fn monitor_api_performance(&self, endpoint: &str, duration: Duration) -> Result<(), MonitorError> {
        // 记录响应时间
        self.response_time_tracker.record_response_time(endpoint, duration).await?;
        
        // 检查性能阈值
        if duration > Duration::from_millis(1000) {
            tracing::warn!("Slow API response: {} took {:?}", endpoint, duration);
        }
        
        Ok(())
    }
    
    pub async fn monitor_database_performance(&self, query: &str, duration: Duration) -> Result<(), MonitorError> {
        // 记录数据库查询时间
        self.response_time_tracker.record_db_query_time(query, duration).await?;
        
        // 检查慢查询
        if duration > Duration::from_millis(100) {
            tracing::warn!("Slow database query: {} took {:?}", query, duration);
        }
        
        Ok(())
    }
    
    pub async fn monitor_cache_performance(&self, operation: &str, hit: bool, duration: Duration) -> Result<(), MonitorError> {
        // 记录缓存性能
        self.response_time_tracker.record_cache_operation(operation, hit, duration).await?;
        
        // 检查缓存命中率
        let hit_rate = self.response_time_tracker.get_cache_hit_rate().await?;
        if hit_rate < 0.8 {
            tracing::warn!("Low cache hit rate: {:.2}%", hit_rate * 100.0);
        }
        
        Ok(())
    }
    
    pub async fn generate_performance_report(&self) -> Result<PerformanceReport, ReportError> {
        let response_times = self.response_time_tracker.get_statistics().await?;
        let throughput = self.throughput_monitor.get_statistics().await?;
        let error_rates = self.error_rate_tracker.get_statistics().await?;
        let resource_usage = self.resource_monitor.get_statistics().await?;
        
        Ok(PerformanceReport {
            response_times,
            throughput,
            error_rates,
            resource_usage,
            generated_at: Utc::now(),
        })
    }
}
```

## 总结

电子商务领域的Rust应用需要重点关注：

1. **性能**: 高并发处理、低延迟响应、高吞吐量
2. **可靠性**: 事务一致性、故障恢复、数据完整性
3. **安全性**: 支付安全、数据保护、欺诈检测
4. **可扩展性**: 微服务架构、水平扩展、负载均衡
5. **用户体验**: 个性化推荐、实时库存、快速搜索

通过合理运用Rust的性能和内存安全特性，可以构建高性能、高可靠、高安全的电子商务平台。
