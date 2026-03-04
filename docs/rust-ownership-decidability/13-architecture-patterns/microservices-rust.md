# 微服务架构模式 (Rust实现)

> 使用Rust构建高可靠、高性能的微服务系统

---

## 目录

- [微服务架构模式 (Rust实现)](#微服务架构模式-rust实现)
  - [目录](#目录)
  - [1. 服务边界设计](#1-服务边界设计)
    - [1.1 领域驱动边界](#11-领域驱动边界)
    - [1.2 服务契约](#12-服务契约)
  - [2. 通信模式](#2-通信模式)
    - [2.1 同步通信（gRPC）](#21-同步通信grpc)
    - [2.2 异步通信（消息队列）](#22-异步通信消息队列)
    - [2.3 事件总线模式](#23-事件总线模式)
  - [3. 服务发现与负载均衡](#3-服务发现与负载均衡)
    - [3.1 Consul集成](#31-consul集成)
    - [3.2 客户端负载均衡](#32-客户端负载均衡)
  - [4. 容错模式](#4-容错模式)
    - [4.1 断路器模式](#41-断路器模式)
    - [4.2 重试模式](#42-重试模式)
    - [4.3 舱壁隔离](#43-舱壁隔离)
  - [5. 数据一致性](#5-数据一致性)
    - [5.1 Saga模式](#51-saga模式)
    - [5.2 CQRS模式](#52-cqrs模式)
  - [6. 可观测性](#6-可观测性)
    - [6.1 分布式追踪](#61-分布式追踪)
    - [6.2 指标收集](#62-指标收集)
  - [7. 部署策略](#7-部署策略)
    - [7.1 容器化](#71-容器化)
    - [7.2 Kubernetes配置](#72-kubernetes配置)
  - [8. 完整示例](#8-完整示例)
    - [8.1 服务启动](#81-服务启动)
  - [总结](#总结)

---

## 1. 服务边界设计

### 1.1 领域驱动边界

```rust
// 订单服务领域
mod order_service {
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// 服务作为所有权边界
    pub struct OrderService {
        // 数据库连接池 - 共享所有权
        db: Arc<DatabasePool>,
        // 事件总线发布者
        event_bus: EventPublisher,
        // 缓存 - 内部可变性
        cache: Arc<RwLock<Cache<Order>>>,
        // 配置 - 只读
        config: Arc<ServiceConfig>,
    }

    impl OrderService {
        pub fn new(
            db: Arc<DatabasePool>,
            event_bus: EventPublisher,
            config: Arc<ServiceConfig>,
        ) -> Self {
            Self {
                db,
                event_bus,
                cache: Arc::new(RwLock::new(Cache::new())),
                config,
            }
        }

        /// 创建订单 - 所有权转移确保数据一致性
        pub async fn create_order(
            &self,
            cmd: CreateOrderCommand
        ) -> Result<OrderId, OrderError> {
            // 验证命令（借用）
            cmd.validate()?;

            // 创建订单（所有权转移）
            let order = Order::new(cmd)?;
            let id = order.id();

            // 保存到数据库
            let mut tx = self.db.begin().await?;
            tx.save(&order).await?;

            // 发布事件（借用）
            self.event_bus.publish(
                OrderCreated::from(&order)
            ).await?;

            // 更新缓存
            self.cache.write().await.insert(id, order);

            tx.commit().await?;
            Ok(id)
        }

        /// 查询订单 - 借用语义
        pub async fn get_order(&self, id: OrderId) -> Option<Order> {
            // 先查缓存（共享借用）
            if let Some(order) = self.cache.read().await.get(&id) {
                return Some(order.clone());
            }

            // 查数据库
            let order = self.db.query::<Order>(id).await.ok()?;

            // 回填缓存
            self.cache.write().await.insert(id, order.clone());

            Some(order)
        }
    }
}
```

### 1.2 服务契约

```rust
/// 服务接口定义（gRPC/HTTP）
#[async_trait]
pub trait OrderService {
    async fn create_order(
        &self,
        request: CreateOrderRequest,
    ) -> Result<CreateOrderResponse, ServiceError>;

    async fn get_order(
        &self,
        request: GetOrderRequest,
    ) -> Result<GetOrderResponse, ServiceError>;

    async fn cancel_order(
        &self,
        request: CancelOrderRequest,
    ) -> Result<CancelOrderResponse, ServiceError>;
}

/// 事件契约
#[derive(Serialize, Deserialize, Clone)]
pub struct OrderCreated {
    pub order_id: OrderId,
    pub customer_id: CustomerId,
    pub items: Vec<LineItem>,
    pub total_amount: Money,
    pub created_at: DateTime<Utc>,
}

impl Event for OrderCreated {
    const TOPIC: &'static str = "orders.created";
    const VERSION: u32 = 1;
}
```

---

## 2. 通信模式

### 2.1 同步通信（gRPC）

```rust
/// gRPC服务实现
pub struct OrderGrpcService {
    inner: Arc<order_service::OrderService>,
}

#[tonic::async_trait]
impl OrderService for OrderGrpcService {
    async fn create_order(
        &self,
        request: Request<CreateOrderRequest>,
    ) -> Result<Response<CreateOrderResponse>, Status> {
        let cmd = CreateOrderCommand::from(request.into_inner());

        match self.inner.create_order(cmd).await {
            Ok(id) => Ok(Response::new(CreateOrderResponse {
                order_id: id.to_string(),
                status: "created".into(),
            })),
            Err(e) => Err(Status::invalid_argument(e.to_string())),
        }
    }
}

/// 连接池管理
pub struct GrpcConnectionPool<T> {
    endpoints: Vec<Endpoint>,
    connections: Arc<RwLock<Vec<T>>>,
    load_balancer: Arc<dyn LoadBalancer>,
}

impl<T: Clone> GrpcConnectionPool<T> {
    /// 获取连接 - 负载均衡
    pub async fn acquire(&self) -> Option<PooledConnection<T>> {
        let idx = self.load_balancer.select(&self.endpoints);
        let conns = self.connections.read().await;
        conns.get(idx).cloned().map(|conn| {
            PooledConnection {
                conn,
                pool: self.connections.clone(),
                idx,
            }
        })
    }
}
```

### 2.2 异步通信（消息队列）

```rust
/// Kafka生产者
pub struct KafkaEventPublisher {
    producer: Arc<RwLock<FutureProducer>>,
    topic_prefix: String,
}

impl EventPublisher for KafkaEventPublisher {
    async fn publish<E: Event>(&self, event: E) -> Result<(), PublishError> {
        let payload = serde_json::to_vec(&event)?;
        let topic = format!("{}.{}", self.topic_prefix, E::TOPIC);

        let record = FutureRecord::to(&topic)
            .payload(&payload)
            .key(&event.key());

        self.producer.read().await
            .send(record, Duration::from_secs(5))
            .await
            .map_err(|e| PublishError::from(e.0))?;

        Ok(())
    }
}

/// 消费者组
pub struct KafkaConsumerGroup {
    consumers: Vec<StreamConsumer>,
    handlers: Arc<HashMap<String, Box<dyn EventHandler>>>,
}

impl KafkaConsumerGroup {
    pub async fn run(&self) {
        let mut futures = vec![];

        for consumer in &self.consumers {
            let handlers = self.handlers.clone();
            let fut = async move {
                loop {
                    match consumer.recv().await {
                        Ok(msg) => {
                            let topic = msg.topic();
                            if let Some(handler) = handlers.get(topic) {
                                if let Err(e) = handler.handle(msg.payload()).await {
                                    log::error!("Handler error: {}", e);
                                    // 根据策略重试或死信队列
                                }
                            }
                        }
                        Err(e) => {
                            log::error!("Consumer error: {}", e);
                        }
                    }
                }
            };
            futures.push(fut);
        }

        futures::future::join_all(futures).await;
    }
}
```

### 2.3 事件总线模式

```rust
/// 内存事件总线（服务内通信）
pub struct InMemoryEventBus {
    subscribers: Arc<RwLock<HashMap<String, Vec<Box<dyn EventSubscriber>>>>>,
}

impl InMemoryEventBus {
    pub async fn subscribe(
        &self,
        event_type: &str,
        subscriber: Box<dyn EventSubscriber>,
    ) {
        self.subscribers
            .write()
            .await
            .entry(event_type.to_string())
            .or_default()
            .push(subscriber);
    }

    pub async fn publish<E: Event + Clone>(&self, event: E) {
        let subs = self.subscribers.read().await;
        if let Some(handlers) = subs.get(E::TOPIC) {
            for handler in handlers {
                // 并发处理所有订阅者
                let evt = event.clone();
                tokio::spawn(async move {
                    if let Err(e) = handler.handle(evt).await {
                        log::error!("Event handler error: {}", e);
                    }
                });
            }
        }
    }
}
```

---

## 3. 服务发现与负载均衡

### 3.1 Consul集成

```rust
/// 服务注册
pub struct ConsulRegistry {
    client: ConsulClient,
    service_id: String,
    health_check: HealthChecker,
}

impl ConsulRegistry {
    pub async fn register(&self, config: ServiceConfig) -> Result<(), RegistryError> {
        let registration = AgentServiceRegistration {
            name: config.name,
            id: self.service_id.clone(),
            address: config.host,
            port: config.port,
            check: Some(AgentServiceCheck {
                http: Some(format!("http://{}:{}/health", config.host, config.port)),
                interval: Some("10s".into()),
                timeout: Some("5s".into()),
                ..Default::default()
            }),
            ..Default::default()
        };

        self.client.register_service(&registration).await?;
        Ok(())
    }

    /// 服务发现
    pub async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>, RegistryError> {
        let services = self.client
            .health_service(service_name, true, None)
            .await?;

        Ok(services.into_iter()
            .map(|s| ServiceInstance {
                id: s.service.id,
                address: s.service.address,
                port: s.service.port,
                metadata: s.service.meta,
            })
            .collect())
    }
}
```

### 3.2 客户端负载均衡

```rust
/// 负载均衡策略
pub trait LoadBalancer: Send + Sync {
    fn select(&self, instances: &[ServiceInstance]) -> usize;
}

/// 轮询
pub struct RoundRobin {
    counter: AtomicUsize,
}

impl LoadBalancer for RoundRobin {
    fn select(&self, instances: &[ServiceInstance]) -> usize {
        let idx = self.counter.fetch_add(1, Ordering::SeqCst);
        idx % instances.len()
    }
}

/// 加权随机
pub struct WeightedRandom {
    rng: Arc<Mutex<StdRng>>,
}

impl LoadBalancer for WeightedRandom {
    fn select(&self, instances: &[ServiceInstance]) -> usize {
        let weights: Vec<u32> = instances.iter()
            .map(|i| i.metadata.get("weight")
                .and_then(|w| w.parse().ok())
                .unwrap_or(1))
            .collect();

        let total: u32 = weights.iter().sum();
        let mut rng = self.rng.lock().unwrap();
        let random = rng.gen_range(0..total);

        let mut cumulative = 0;
        for (i, w) in weights.iter().enumerate() {
            cumulative += w;
            if random < cumulative {
                return i;
            }
        }
        0
    }
}
```

---

## 4. 容错模式

### 4.1 断路器模式

```rust
/// 断路器状态机
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常
    Open,        // 熔断
    HalfOpen,    // 试探
}

pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_count: Arc<AtomicUsize>,
    success_count: Arc<AtomicUsize>,
    config: CircuitConfig,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
}

impl CircuitBreaker {
    pub async fn call<F, Fut, T, E>(&self, op: F) -> Result<T, CircuitError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        // 检查状态
        match *self.state.read().await {
            CircuitState::Open => {
                // 检查是否到达半开时间
                let should_try = self.last_failure_time.read().await
                    .map(|t| Instant::now().duration_since(t) > self.config.timeout)
                    .unwrap_or(false);

                if should_try {
                    *self.state.write().await = CircuitState::HalfOpen;
                    self.success_count.store(0, Ordering::SeqCst);
                } else {
                    return Err(CircuitError::Open);
                }
            }
            _ => {}
        }

        // 执行操作
        match op().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitError::Inner(e))
            }
        }
    }

    async fn on_success(&self) {
        match *self.state.read().await {
            CircuitState::HalfOpen => {
                let count = self.success_count.fetch_add(1, Ordering::SeqCst) + 1;
                if count >= self.config.success_threshold {
                    *self.state.write().await = CircuitState::Closed;
                    self.failure_count.store(0, Ordering::SeqCst);
                }
            }
            CircuitState::Closed => {
                self.failure_count.store(0, Ordering::SeqCst);
            }
            _ => {}
        }
    }

    async fn on_failure(&self) {
        let count = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;

        match *self.state.read().await {
            CircuitState::HalfOpen | CircuitState::Closed
                if count >= self.config.failure_threshold =>
            {
                *self.state.write().await = CircuitState::Open;
                *self.last_failure_time.write().await = Some(Instant::now());
            }
            _ => {}
        }
    }
}
```

### 4.2 重试模式

```rust
/// 重试策略
pub struct RetryPolicy {
    max_attempts: u32,
    base_delay: Duration,
    max_delay: Duration,
    backoff_multiplier: f64,
    retryable_errors: Vec<ErrorKind>,
}

impl RetryPolicy {
    pub async fn execute<F, Fut, T>(&self, mut operation: F) -> Result<T, RetryError>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T, Error>>,
    {
        let mut attempts = 0;
        let mut delay = self.base_delay;

        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) if !self.is_retryable(&e) => return Err(RetryError::Fatal(e)),
                Err(e) => {
                    attempts += 1;
                    if attempts >= self.max_attempts {
                        return Err(RetryError::Exhausted(e));
                    }

                    log::warn!("Attempt {} failed, retrying in {:?}", attempts, delay);
                    tokio::time::sleep(delay).await;

                    // 指数退避
                    delay = std::cmp::min(
                        Duration::from_secs_f64(delay.as_secs_f64() * self.backoff_multiplier),
                        self.max_delay
                    );
                }
            }
        }
    }
}
```

### 4.3 舱壁隔离

```rust
/// 舱壁模式 - 限制资源使用
pub struct Bulkhead {
    semaphore: Arc<Semaphore>,
    queue_size: Arc<AtomicUsize>,
    max_queue: usize,
}

impl Bulkhead {
    pub fn new(max_concurrent: usize, max_queue: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            queue_size: Arc::new(AtomicUsize::new(0)),
            max_queue,
        }
    }

    pub async fn execute<F, Fut, T>(&self, op: F) -> Result<T, BulkheadError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        // 检查队列
        if self.queue_size.fetch_add(1, Ordering::SeqCst) >= self.max_queue {
            self.queue_size.fetch_sub(1, Ordering::SeqCst);
            return Err(BulkheadError::QueueFull);
        }

        // 获取许可
        let _permit = self.semaphore.acquire().await
            .map_err(|_| BulkheadError::Closed)?;

        self.queue_size.fetch_sub(1, Ordering::SeqCst);

        // 执行
        Ok(op().await)
    }
}
```

---

## 5. 数据一致性

### 5.1 Saga模式

```rust
/// Saga编排器
pub struct SagaOrchestrator {
    steps: Vec<Box<dyn SagaStep>>,
    compensations: Vec<Box<dyn Compensation>>,
}

impl SagaOrchestrator {
    pub async fn execute(&mut self, ctx: &SagaContext) -> Result<(), SagaError> {
        let completed = Arc::new(Mutex::new(Vec::new()));

        for (i, step) in self.steps.iter().enumerate() {
            match step.execute(ctx).await {
                Ok(_) => {
                    completed.lock().await.push(i);
                }
                Err(e) => {
                    log::error!("Saga step {} failed: {}", i, e);
                    // 补偿已完成的步骤
                    self.compensate(&completed, ctx).await;
                    return Err(SagaError::StepFailed(i, e));
                }
            }
        }

        Ok(())
    }

    async fn compensate(&self, completed: &[usize], ctx: &SagaContext) {
        for &i in completed.iter().rev() {
            if let Err(e) = self.compensations[i].compensate(ctx).await {
                log::error!("Compensation {} failed: {}", i, e);
                // 记录到人工干预队列
            }
        }
    }
}

/// 订单创建Saga
pub struct CreateOrderSaga {
    order_service: Arc<OrderService>,
    inventory_service: Arc<InventoryService>,
    payment_service: Arc<PaymentService>,
}

impl CreateOrderSaga {
    pub async fn execute(&self, cmd: CreateOrderCommand) -> Result<OrderId, SagaError> {
        // Step 1: 创建订单（草稿）
        let order_id = self.order_service.create_draft(&cmd).await?;

        // Step 2: 扣减库存
        if let Err(e) = self.inventory_service.reserve(&cmd.items).await {
            // 补偿：删除订单
            self.order_service.cancel(order_id).await.ok();
            return Err(SagaError::InventoryFailed(e));
        }

        // Step 3: 处理支付
        if let Err(e) = self.payment_service.charge(cmd.payment_info).await {
            // 补偿：释放库存
            self.inventory_service.release(&cmd.items).await.ok();
            self.order_service.cancel(order_id).await.ok();
            return Err(SagaError::PaymentFailed(e));
        }

        // Step 4: 确认订单
        self.order_service.confirm(order_id).await?;

        Ok(order_id)
    }
}
```

### 5.2 CQRS模式

```rust
/// 命令端
pub struct OrderCommandHandler {
    event_store: Arc<EventStore>,
    projection_writer: ProjectionWriter,
}

impl OrderCommandHandler {
    pub async fn handle_create(
        &self,
        cmd: CreateOrderCommand,
    ) -> Result<(), CommandError> {
        // 加载聚合
        let mut order = Order::load(cmd.order_id, &self.event_store).await?;

        // 执行命令
        let events = order.create(cmd)?;

        // 存储事件
        self.event_store.append(&events).await?;

        // 更新投影（异步）
        for event in events {
            self.projection_writer.apply(event).await?;
        }

        Ok(())
    }
}

/// 查询端
pub struct OrderQueryHandler {
    projection_reader: ProjectionReader,
    cache: Arc<RwLock<Cache>>,
}

impl OrderQueryHandler {
    pub async fn get_order(&self, id: OrderId) -> Option<OrderView> {
        // 先查缓存
        if let Some(cached) = self.cache.read().await.get(&id) {
            return Some(cached.clone());
        }

        // 查投影数据库
        let view = self.projection_reader.get_order(id).await.ok()?;

        // 回填缓存
        self.cache.write().await.insert(id, view.clone());

        Some(view)
    }

    pub async fn search_orders(&self, query: OrderQuery) -> Vec<OrderSummary> {
        // 只读查询，可以直接访问投影
        self.projection_reader.search(query).await
    }
}
```

---

## 6. 可观测性

### 6.1 分布式追踪

```rust
/// OpenTelemetry集成
pub struct TracedService {
    tracer: Tracer,
}

impl TracedService {
    pub async fn handle_request(&self, req: Request) -> Response {
        let span = self.tracer
            .span_builder("handle_request")
            .with_kind(SpanKind::Server)
            .start(&self.tracer);

        let cx = Context::current_with_span(span);

        // 在上下文中执行
        async {
            // 数据库查询
            let db_span = self.tracer
                .span_builder("db_query")
                .start(&self.tracer);
            let result = self.db.query().await;
            db_span.end();

            // 下游调用
            let client_span = self.tracer
                .span_builder("downstream_call")
                .start(&self.tracer);
            let response = self.call_downstream().await;
            client_span.end();

            response
        }
        .with_context(cx)
        .await
    }
}
```

### 6.2 指标收集

```rust
/// Prometheus指标
lazy_static! {
    static ref REQUEST_COUNT: CounterVec = register_counter_vec!(
        "http_requests_total",
        "Total HTTP requests",
        &["method", "endpoint", "status"]
    ).unwrap();

    static ref REQUEST_DURATION: HistogramVec = register_histogram_vec!(
        "http_request_duration_seconds",
        "Request duration",
        &["method", "endpoint"],
        exponential_buckets(0.001, 2.0, 15).unwrap()
    ).unwrap();
}

pub async fn metrics_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let path = req.uri().path().to_string();

    let response = next.run(req).await;

    let duration = start.elapsed();
    let status = response.status().as_u16().to_string();

    REQUEST_COUNT
        .with_label_values(&[&method.to_string(), &path, &status])
        .inc();

    REQUEST_DURATION
        .with_label_values(&[&method.to_string(), &path])
        .observe(duration.as_secs_f64());

    response
}
```

---

## 7. 部署策略

### 7.1 容器化

```dockerfile
# Dockerfile
FROM rust:1.93-alpine AS builder
WORKDIR /app
COPY . .
RUN cargo build --release

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/target/release/order-service .
EXPOSE 8080
CMD ["./order-service"]
```

### 7.2 Kubernetes配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-service
  template:
    metadata:
      labels:
        app: order-service
    spec:
      containers:
      - name: order-service
        image: order-service:latest
        ports:
        - containerPort: 8080
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 3
---
apiVersion: v1
kind: Service
metadata:
  name: order-service
spec:
  selector:
    app: order-service
  ports:
  - port: 80
    targetPort: 8080
  type: ClusterIP
```

---

## 8. 完整示例

### 8.1 服务启动

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化追踪
    init_tracing()?;

    // 加载配置
    let config = load_config()?;

    // 创建数据库连接池
    let db_pool = Arc::new(create_db_pool(&config.database).await?);

    // 创建事件总线
    let event_bus = Arc::new(KafkaEventPublisher::new(&config.kafka).await?);

    // 创建服务
    let order_service = Arc::new(OrderService::new(
        db_pool.clone(),
        event_bus.clone(),
        Arc::new(config.service),
    ));

    // 创建断路器
    let circuit_breaker = Arc::new(CircuitBreaker::new(CircuitConfig {
        failure_threshold: 5,
        success_threshold: 3,
        timeout: Duration::from_secs(30),
    }));

    // 启动gRPC服务
    let grpc_addr = format!("0.0.0.0:{}", config.grpc_port).parse()?;
    let grpc_service = OrderGrpcService::new(order_service.clone());

    tokio::spawn(async move {
        Server::builder()
            .add_service(OrderServiceServer::new(grpc_service))
            .serve(grpc_addr)
            .await
            .unwrap();
    });

    // 启动HTTP服务
    let http_addr = format!("0.0.0.0:{}", config.http_port).parse()?;
    let app = create_router(order_service, circuit_breaker);

    log::info!("Starting HTTP server on {}", http_addr);
    axum::Server::bind(&http_addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}
```

---

## 总结

Rust的所有权模型在微服务架构中的优势：

1. **资源安全**: 编译期防止资源泄漏
2. **并发安全**: 无数据竞争， fearless concurrency
3. **故障隔离**: 类型系统保证错误处理
4. **性能**: 零成本抽象，低延迟高吞吐

通过合理的架构设计和Rust的类型系统，可以构建出既安全又高效的微服务系统。
