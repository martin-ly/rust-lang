# 软件设计模型综合分析

## 目录

- [软件设计模型综合分析](#软件设计模型综合分析)
  - [目录](#目录)
  - [概述](#概述)
  - [程序设计范式](#程序设计范式)
    - [函数式编程 (Functional Programming)](#函数式编程-functional-programming)
    - [面向对象编程 (Object-Oriented Programming)](#面向对象编程-object-oriented-programming)
    - [反应式编程 (Reactive Programming)](#反应式编程-reactive-programming)
    - [数据流编程 (Dataflow Programming)](#数据流编程-dataflow-programming)
  - [架构设计模式](#架构设计模式)
    - [分层架构 (Layered Architecture)](#分层架构-layered-architecture)
    - [六边形架构 (Hexagonal Architecture)](#六边形架构-hexagonal-architecture)
    - [事件驱动架构 (Event-Driven Architecture)](#事件驱动架构-event-driven-architecture)
    - [CQRS (Command Query Responsibility Segregation)](#cqrs-command-query-responsibility-segregation)
    - [微服务架构 (Microservices Architecture)](#微服务架构-microservices-architecture)
    - [管道过滤器 (Pipe-and-Filter)](#管道过滤器-pipe-and-filter)
    - [P2P架构 (Peer-to-Peer)](#p2p架构-peer-to-peer)
  - [架构模式等价性分析](#架构模式等价性分析)
    - [分层架构 ↔ 六边形架构](#分层架构--六边形架构)
    - [事件驱动 ↔ 消息队列](#事件驱动--消息队列)
    - [CQRS ↔ 事件溯源](#cqrs--事件溯源)
    - [微服务 ↔ SOA](#微服务--soa)
  - [架构模式转换](#架构模式转换)
    - [单体 → 微服务](#单体--微服务)
    - [同步 → 异步](#同步--异步)
    - [分层 → 六边形](#分层--六边形)
    - [传统架构 → 事件驱动](#传统架构--事件驱动)
  - [设计原则与模式](#设计原则与模式)
    - [SOLID原则](#solid原则)
    - [设计模式分类](#设计模式分类)
  - [Rust中的设计模式实现](#rust中的设计模式实现)
    - [Builder模式](#builder模式)
    - [Strategy模式](#strategy模式)
    - [Observer模式](#observer模式)
    - [Decorator模式](#decorator模式)
  - [范式组合与混合模式](#范式组合与混合模式)
  - [实战案例](#实战案例)
    - [案例1: Web应用架构演进](#案例1-web应用架构演进)
    - [案例2: 分布式系统设计](#案例2-分布式系统设计)
    - [案例3: 高性能计算系统](#案例3-高性能计算系统)
  - [架构评估与权衡](#架构评估与权衡)
  - [最佳实践](#最佳实践)
  - [总结](#总结)
  - [参考文献](#参考文献)

## 概述

软件设计模型是构建高质量软件系统的理论基础。本文档全面分析了程序设计范式、架构设计模式、它们之间的等价性关系和转换方法,并展示如何在Rust 1.90中优雅地实现这些模式。

**核心主题**:

- 程序设计范式的理论与实践
- 架构设计模式的分类与应用
- 模式间的等价性与转换
- Rust语言的独特优势

## 程序设计范式

### 函数式编程 (Functional Programming)

**核心概念**:

- 不可变数据
- 纯函数
- 高阶函数
- 函数组合
- 惰性求值

**Rust实现**:

```rust
use c12_model::*;

// 不可变数据结构
let list = ImmutableList::new()
    .cons(1)
    .cons(2)
    .cons(3);

// 高阶函数
fn map<A, B>(list: ImmutableList<A>, f: impl Fn(A) -> B) -> ImmutableList<B> {
    // 函数式映射实现
    todo!()
}

// Functor实例
let functor = Functor::new(42);
let mapped = functor.fmap(|x| x * 2);

// Monad实例
let monad = Monad::new(10);
let result = monad.bind(|x| Monad::new(x + 5))
                  .bind(|x| Monad::new(x * 2));
```

**特点**:

- ✅ 引用透明
- ✅ 无副作用
- ✅ 易于测试
- ✅ 并行友好
- ⚠️ 学习曲线陡峭

### 面向对象编程 (Object-Oriented Programming)

**核心概念**:

- 封装
- 继承(组合)
- 多态

**Rust实现**:

```rust
// 使用trait实现多态
trait Account {
    fn deposit(&mut self, amount: f64);
    fn withdraw(&mut self, amount: f64) -> Result<(), String>;
    fn balance(&self) -> f64;
}

struct BankAccount {
    balance: f64,
}

impl Account for BankAccount {
    fn deposit(&mut self, amount: f64) {
        self.balance += amount;
    }
    
    fn withdraw(&mut self, amount: f64) -> Result<(), String> {
        if self.balance >= amount {
            self.balance -= amount;
            Ok(())
        } else {
            Err("Insufficient funds".to_string())
        }
    }
    
    fn balance(&self) -> f64 {
        self.balance
    }
}

// Observer模式
use c12_model::*;

let mut subject = Subject::new();
let observer1 = Box::new(ConcreteObserver::new("Observer1"));
let observer2 = Box::new(ConcreteObserver::new("Observer2"));

subject.attach(observer1);
subject.attach(observer2);
subject.notify("Event occurred");
```

**特点**:

- ✅ 模块化
- ✅ 代码复用
- ✅ 易于维护
- ⚠️ 可能过度设计

### 反应式编程 (Reactive Programming)

**核心概念**:

- 数据流
- 变化传播
- 背压控制
- 操作符组合

**Rust实现**:

```rust
use c12_model::*;

// 创建反应式流
let stream = ReactiveStream::new();

// 添加操作符
let processed = stream
    .map(|x| x * 2)
    .filter(|x| x > 10)
    .take(100);

// 订阅
let subscriber = ReactiveSubscriber::new(|value| {
    println!("Received: {}", value);
});

processed.subscribe(subscriber);
```

**特点**:

- ✅ 异步处理
- ✅ 背压控制
- ✅ 声明式
- ⚠️ 调试困难

### 数据流编程 (Dataflow Programming)

**核心概念**:

- 数据流图
- 数据驱动执行
- 并行执行
- 管道组合

**Rust实现**:

```rust
use c12_model::*;

// 创建数据流图
let mut graph = DataflowGraph::new();

// 添加节点
let node1 = graph.add_node("source");
let node2 = graph.add_node("transform");
let node3 = graph.add_node("sink");

// 连接节点
graph.connect(node1, node2);
graph.connect(node2, node3);

// 执行数据流
graph.execute(input_data);
```

**特点**:

- ✅ 自然并行
- ✅ 可视化强
- ✅ 易于优化
- ⚠️ 状态管理复杂

## 架构设计模式

### 分层架构 (Layered Architecture)

**结构**:

```text
┌─────────────────────┐
│  Presentation Layer │  (UI, API)
├─────────────────────┤
│   Business Layer    │  (业务逻辑)
├─────────────────────┤
│ Persistence Layer   │  (数据访问)
├─────────────────────┤
│   Database Layer    │  (数据存储)
└─────────────────────┘
```

**Rust实现**:

```rust
// 表现层
mod presentation {
    pub struct ApiController {
        business: super::business::BusinessService,
    }
    
    impl ApiController {
        pub fn handle_request(&self, req: Request) -> Response {
            let result = self.business.process(req.data);
            Response::from(result)
        }
    }
}

// 业务层
mod business {
    pub struct BusinessService {
        repository: super::persistence::Repository,
    }
    
    impl BusinessService {
        pub fn process(&self, data: Data) -> Result<Output> {
            // 业务逻辑
            let validated = self.validate(data)?;
            self.repository.save(validated)
        }
        
        fn validate(&self, data: Data) -> Result<ValidatedData> {
            // 验证逻辑
            Ok(ValidatedData::from(data))
        }
    }
}

// 持久层
mod persistence {
    pub struct Repository {
        db: Database,
    }
    
    impl Repository {
        pub fn save(&self, data: ValidatedData) -> Result<Output> {
            self.db.execute("INSERT INTO ...", data)
        }
        
        pub fn find(&self, id: Id) -> Result<Output> {
            self.db.query("SELECT * FROM ...", id)
        }
    }
}
```

**优势**:

- ✅ 关注点分离
- ✅ 易于理解
- ✅ 团队协作友好
- ⚠️ 可能出现上下层紧耦合

### 六边形架构 (Hexagonal Architecture)

**结构**:

```text
        ┌─────────────┐
        │  Adapters   │
        │  (HTTP API) │
        └──────┬──────┘
               │
        ┌──────▼──────┐
        │    Ports    │
        │ (Interface) │
        └──────┬──────┘
               │
    ┌──────────▼──────────┐
    │   Domain Logic      │
    │   (Core Business)   │
    └──────────┬──────────┘
               │
        ┌──────▼──────┐
        │    Ports    │
        └──────┬──────┘
               │
        ┌──────▼──────┐
        │  Adapters   │
        │ (Database)  │
        └─────────────┘
```

**Rust实现**:

```rust
use c12_model::*;

// 核心领域
struct CoreDomain {
    // 业务逻辑
}

// 端口(trait)
trait RepositoryPort {
    fn save(&self, data: Data) -> Result<()>;
    fn find(&self, id: Id) -> Result<Data>;
}

trait NotificationPort {
    fn send(&self, message: String) -> Result<()>;
}

// 适配器
struct PostgresAdapter {
    connection: PgConnection,
}

impl RepositoryPort for PostgresAdapter {
    fn save(&self, data: Data) -> Result<()> {
        // PostgreSQL特定实现
        Ok(())
    }
    
    fn find(&self, id: Id) -> Result<Data> {
        // PostgreSQL特定实现
        Ok(Data::default())
    }
}

struct EmailAdapter;

impl NotificationPort for EmailAdapter {
    fn send(&self, message: String) -> Result<()> {
        // SMTP发送
        Ok(())
    }
}
```

**优势**:

- ✅ 核心业务独立
- ✅ 易于测试
- ✅ 技术栈可替换
- ⚠️ 初期设计复杂

### 事件驱动架构 (Event-Driven Architecture)

**结构**:

```text
Producer → [Event Bus] → Consumer1
                      → Consumer2
                      → Consumer3
```

**Rust实现**:

```rust
use c12_model::*;

// 事件定义
#[derive(Debug, Clone, Serialize, Deserialize)]
enum DomainEvent {
    UserCreated { user_id: String, email: String },
    OrderPlaced { order_id: String, amount: f64 },
    PaymentProcessed { payment_id: String },
}

// 事件总线
let mut event_bus = EventBus::new();

// 注册处理器
event_bus.subscribe(|event| {
    match event {
        DomainEvent::UserCreated { user_id, email } => {
            println!("发送欢迎邮件给: {}", email);
        }
        _ => {}
    }
});

event_bus.subscribe(|event| {
    match event {
        DomainEvent::OrderPlaced { order_id, .. } => {
            println!("处理订单: {}", order_id);
        }
        _ => {}
    }
});

// 发布事件
event_bus.publish(DomainEvent::UserCreated {
    user_id: "123".to_string(),
    email: "user@example.com".to_string(),
});
```

**优势**:

- ✅ 松耦合
- ✅ 可扩展性强
- ✅ 异步处理
- ⚠️ 调试复杂
- ⚠️ 事件顺序问题

### CQRS (Command Query Responsibility Segregation)

**结构**:

```text
Command (写) → [Command Bus] → Write Model → Event Store
                                                  │
                                                  ▼
Query (读) ← [Query Bus] ← Read Model ← Event Projection
```

**Rust实现**:

```rust
use c12_model::*;

// 命令
#[derive(Debug)]
enum Command {
    CreateUser { name: String, email: String },
    UpdateUser { id: String, name: String },
}

// 查询
#[derive(Debug)]
enum Query {
    GetUser { id: String },
    ListUsers,
}

// CQRS模型
let mut cqrs = CQRSModel::new();

// 命令总线
let command_bus = CommandBus::new();
command_bus.dispatch(Command::CreateUser {
    name: "Alice".to_string(),
    email: "alice@example.com".to_string(),
})?;

// 查询总线
let query_bus = QueryBus::new();
let user = query_bus.execute(Query::GetUser {
    id: "123".to_string(),
})?;
```

**优势**:

- ✅ 读写分离
- ✅ 性能优化
- ✅ 独立扩展
- ⚠️ 最终一致性
- ⚠️ 复杂度增加

### 微服务架构 (Microservices Architecture)

**结构**:

```text
[API Gateway]
      │
      ├─→ [User Service]    → [User DB]
      ├─→ [Order Service]   → [Order DB]
      ├─→ [Payment Service] → [Payment DB]
      └─→ [Notification]
```

**Rust实现**:

```rust
// 用户微服务
mod user_service {
    pub struct UserService {
        db: Database,
    }
    
    impl UserService {
        pub async fn create_user(&self, req: CreateUserRequest) -> Result<User> {
            // 创建用户逻辑
            let user = User::new(req.name, req.email);
            self.db.save(&user).await?;
            
            // 发布事件
            self.publish_event(UserCreated { id: user.id }).await?;
            
            Ok(user)
        }
    }
}

// 订单微服务
mod order_service {
    pub struct OrderService {
        db: Database,
        user_client: UserServiceClient,  // 跨服务调用
    }
    
    impl OrderService {
        pub async fn create_order(&self, req: CreateOrderRequest) -> Result<Order> {
            // 验证用户(跨服务调用)
            let user = self.user_client.get_user(req.user_id).await?;
            
            // 创建订单
            let order = Order::new(user.id, req.items);
            self.db.save(&order).await?;
            
            Ok(order)
        }
    }
}
```

**优势**:

- ✅ 独立部署
- ✅ 技术栈灵活
- ✅ 故障隔离
- ⚠️ 分布式复杂性
- ⚠️ 数据一致性挑战

### 管道过滤器 (Pipe-and-Filter)

**结构**:

```text
Input → [Filter1] → [Filter2] → [Filter3] → Output
```

**Rust实现**:

```rust
use c12_model::*;

// 过滤器trait
trait Filter {
    fn process(&self, input: Data) -> Data;
}

// 具体过滤器
struct ValidateFilter;
impl Filter for ValidateFilter {
    fn process(&self, input: Data) -> Data {
        // 验证逻辑
        input
    }
}

struct TransformFilter;
impl Filter for TransformFilter {
    fn process(&self, input: Data) -> Data {
        // 转换逻辑
        input.transform()
    }
}

// 管道
let mut pipeline = PipelineArchitecture::new();
pipeline.add_filter(Box::new(ValidateFilter));
pipeline.add_filter(Box::new(TransformFilter));

let output = pipeline.execute(input)?;
```

**优势**:

- ✅ 组件可复用
- ✅ 易于扩展
- ✅ 并行执行
- ⚠️ 性能开销
- ⚠️ 状态传递复杂

### P2P架构 (Peer-to-Peer)

**结构**:

```text
Peer1 ←→ Peer2
  ↕        ↕
Peer4 ←→ Peer3
```

**Rust实现**:

```rust
use c12_model::*;

// P2P网络
let mut network = P2PNetwork::new(P2PTopology::FullMesh);

// 添加对等节点
let peer1 = Peer::new("peer1", "127.0.0.1:8001");
let peer2 = Peer::new("peer2", "127.0.0.1:8002");
let peer3 = Peer::new("peer3", "127.0.0.1:8003");

network.add_peer(peer1)?;
network.add_peer(peer2)?;
network.add_peer(peer3)?;

// 广播消息
network.broadcast("Hello, P2P!".to_string())?;

// 发送给特定节点
network.send_to("peer2", "Direct message".to_string())?;
```

**优势**:

- ✅ 无中心故障点
- ✅ 可扩展性强
- ✅ 负载分散
- ⚠️ 一致性难保证
- ⚠️ 安全性挑战

## 架构模式等价性分析

### 分层架构 ↔ 六边形架构

**映射关系**:

```text
分层架构                六边形架构
─────────────────────────────────
Presentation Layer  ↔  Inbound Adapter
Business Layer      ↔  Core Domain
Persistence Layer   ↔  Outbound Adapter
Database            ↔  External System
```

**转换规则**:

1. 层间接口 → 端口(Port)
2. 层实现 → 适配器(Adapter)
3. 依赖注入 → 端口注入

**代码示例**:

```rust
// 分层架构
struct BusinessLayer {
    persistence: PersistenceLayer,  // 直接依赖
}

// 转换为六边形架构
trait RepositoryPort {  // 定义端口
    fn save(&self, data: Data) -> Result<()>;
}

struct BusinessDomain<R: RepositoryPort> {
    repository: R,  // 依赖抽象
}
```

### 事件驱动 ↔ 消息队列

**等价性**:

- 事件总线 ≈ 消息队列
- 事件发布 ≈ 消息发送
- 事件订阅 ≈ 消息消费

**实现**:

```rust
// 事件驱动
event_bus.publish(OrderPlaced { order_id: "123" });

// 等价的消息队列
message_queue.send(Message {
    topic: "order.placed",
    payload: json!({"order_id": "123"}),
});
```

### CQRS ↔ 事件溯源

**组合关系**:

```text
CQRS + Event Sourcing = 强大的架构组合

Command → Event Store (写)
            ↓
        Event Stream
            ↓
Query ← Projection (读)
```

**实现**:

```rust
// CQRS + Event Sourcing
let event_store = EventStore::new();

// 命令处理
command_bus.handle(CreateOrder { .. }, |cmd| {
    let event = OrderCreated { .. };
    event_store.append(event)?;  // 存储事件
    Ok(())
});

// 查询通过投影
let projection = OrderProjection::new(&event_store);
let order = projection.get_order(order_id)?;
```

### 微服务 ↔ SOA

**对比**:

| 特性 | 微服务 | SOA |
|------|--------|-----|
| 服务粒度 | 细 | 粗 |
| 通信 | REST/gRPC | ESB/SOAP |
| 数据 | 每服务独立DB | 共享DB |
| 部署 | 独立 | 集中 |
| 治理 | 去中心化 | 中心化 |

**演进**:

```rust
// SOA风格(粗粒度)
struct MonolithService {
    user_module: UserModule,
    order_module: OrderModule,
    payment_module: PaymentModule,
}

// 微服务风格(细粒度)
struct UserMicroservice { /* 独立服务 */ }
struct OrderMicroservice { /* 独立服务 */ }
struct PaymentMicroservice { /* 独立服务 */ }
```

## 架构模式转换

### 单体 → 微服务

**迁移步骤**:

1. **识别边界**: 按业务能力划分
2. **提取模块**: 使用Strangler Fig模式
3. **建立接口**: API Gateway
4. **数据分离**: 每个服务独立数据库
5. **渐进迁移**: 一次迁移一个服务

**示例**:

```rust
// 阶段1: 单体应用
struct Monolith {
    users: UserModule,
    orders: OrderModule,
    payments: PaymentModule,
}

// 阶段2: 提取第一个微服务
struct MonolithWithUserService {
    user_service: UserServiceClient,  // 已迁移
    orders: OrderModule,               // 待迁移
    payments: PaymentModule,           // 待迁移
}

// 阶段3: 完全微服务化
// UserService独立部署
// OrderService独立部署
// PaymentService独立部署
```

### 同步 → 异步

**转换模式**:

```rust
// 同步调用
fn process_order(order: Order) -> Result<Receipt> {
    let user = user_service.get_user(order.user_id)?;
    let payment = payment_service.charge(order.amount)?;
    Ok(Receipt::new(user, payment))
}

// 转换为异步(基于事件)
async fn process_order_async(order: Order) -> Result<()> {
    // 发布命令
    command_bus.publish(ProcessOrder {
        order_id: order.id,
    }).await?;
    
    // 异步处理
    // 1. UserService处理验证
    // 2. PaymentService处理支付
    // 3. ReceiptService生成收据
    
    Ok(())  // 立即返回
}
```

### 分层 → 六边形

**重构步骤**:

```rust
// Step 1: 提取接口(端口)
trait UserRepository {
    fn find(&self, id: UserId) -> Result<User>;
    fn save(&self, user: User) -> Result<()>;
}

// Step 2: 实现适配器
struct PostgresUserRepository {
    pool: PgPool,
}

impl UserRepository for PostgresUserRepository {
    fn find(&self, id: UserId) -> Result<User> {
        // PostgreSQL特定实现
        todo!()
    }
    
    fn save(&self, user: User) -> Result<()> {
        // PostgreSQL特定实现
        todo!()
    }
}

// Step 3: 核心业务依赖抽象
struct UserService<R: UserRepository> {
    repository: R,
}

impl<R: UserRepository> UserService<R> {
    fn register_user(&self, email: String) -> Result<User> {
        let user = User::new(email);
        self.repository.save(user)?;
        Ok(user)
    }
}
```

### 传统架构 → 事件驱动

**转换**:

```rust
// 传统方式(紧耦合)
fn create_user(name: String, email: String) -> Result<User> {
    let user = User::new(name, email);
    db.save(&user)?;
    
    // 直接调用其他服务
    email_service.send_welcome_email(&user)?;
    analytics_service.track_signup(&user)?;
    
    Ok(user)
}

// 事件驱动(松耦合)
fn create_user_event_driven(name: String, email: String) -> Result<User> {
    let user = User::new(name, email);
    db.save(&user)?;
    
    // 发布事件
    event_bus.publish(UserCreated {
        user_id: user.id,
        email: user.email.clone(),
    })?;
    
    // 其他服务监听事件自行处理
    
    Ok(user)
}
```

## 设计原则与模式

### SOLID原则

**1. Single Responsibility Principle (单一职责)**:

```rust
// ❌ 违反SRP
struct UserService {
    fn create_user(&self) { /* ... */ }
    fn send_email(&self) { /* ... */ }  // 不应该在这里
    fn log(&self) { /* ... */ }          // 不应该在这里
}

// ✅ 遵循SRP
struct UserService {
    email_service: EmailService,
    logger: Logger,
    
    fn create_user(&self) { /* ... */ }
}
```

**2. Open/Closed Principle (开放封闭)**:

```rust
// 使用trait扩展功能
trait PaymentMethod {
    fn process(&self, amount: f64) -> Result<()>;
}

struct CreditCardPayment;
impl PaymentMethod for CreditCardPayment {
    fn process(&self, amount: f64) -> Result<()> {
        // 信用卡支付
        Ok(())
    }
}

struct AlipayPayment;
impl PaymentMethod for AlipayPayment {
    fn process(&self, amount: f64) -> Result<()> {
        // 支付宝支付
        Ok(())
    }
}

// 新增支付方式无需修改现有代码
```

**3. Liskov Substitution Principle (里氏替换)**:

```rust
trait Shape {
    fn area(&self) -> f64;
}

struct Rectangle { width: f64, height: f64 }
struct Circle { radius: f64 }

impl Shape for Rectangle {
    fn area(&self) -> f64 { self.width * self.height }
}

impl Shape for Circle {
    fn area(&self) -> f64 { std::f64::consts::PI * self.radius * self.radius }
}

// 任何Shape都可以替换
fn print_area(shape: &dyn Shape) {
    println!("Area: {}", shape.area());
}
```

**4. Interface Segregation Principle (接口隔离)**:

```rust
// ❌ 胖接口
trait Worker {
    fn work(&self);
    fn eat(&self);
    fn sleep(&self);
}

// ✅ 接口隔离
trait Workable {
    fn work(&self);
}

trait Eatable {
    fn eat(&self);
}

trait Sleepable {
    fn sleep(&self);
}

// 机器人只需要实现Workable
struct Robot;
impl Workable for Robot {
    fn work(&self) { /* ... */ }
}
```

**5. Dependency Inversion Principle (依赖倒置)**:

```rust
// 高层模块依赖抽象
trait MessageSender {
    fn send(&self, msg: String) -> Result<()>;
}

struct NotificationService<S: MessageSender> {
    sender: S,  // 依赖抽象
}

// 低层模块实现抽象
struct EmailSender;
impl MessageSender for EmailSender {
    fn send(&self, msg: String) -> Result<()> {
        // 发送邮件
        Ok(())
    }
}

struct SmsSender;
impl MessageSender for SmsSender {
    fn send(&self, msg: String) -> Result<()> {
        // 发送短信
        Ok(())
    }
}
```

### 设计模式分类

**创建型模式**:

- Builder: 复杂对象构建
- Factory: 对象创建
- Singleton: 唯一实例
- Prototype: 对象克隆

**结构型模式**:

- Adapter: 接口适配
- Decorator: 功能增强
- Proxy: 代理访问
- Composite: 树形结构

**行为型模式**:

- Strategy: 算法切换
- Observer: 事件通知
- Command: 命令封装
- Iterator: 遍历访问

## Rust中的设计模式实现

### Builder模式

```rust
struct Server {
    host: String,
    port: u16,
    timeout: Duration,
    max_connections: usize,
}

struct ServerBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<Duration>,
    max_connections: Option<usize>,
}

impl ServerBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: None,
            timeout: None,
            max_connections: None,
        }
    }
    
    fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }
    
    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    fn max_connections(mut self, max: usize) -> Self {
        self.max_connections = Some(max);
        self
    }
    
    fn build(self) -> Result<Server> {
        Ok(Server {
            host: self.host.ok_or("host is required")?,
            port: self.port.unwrap_or(8080),
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            max_connections: self.max_connections.unwrap_or(1000),
        })
    }
}

// 使用
let server = ServerBuilder::new()
    .host("localhost")
    .port(3000)
    .timeout(Duration::from_secs(60))
    .build()?;
```

### Strategy模式

```rust
trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
}

struct GzipCompression;
impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // Gzip压缩
        vec![]
    }
}

struct ZstdCompression;
impl CompressionStrategy for ZstdCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // Zstd压缩
        vec![]
    }
}

struct Compressor<S: CompressionStrategy> {
    strategy: S,
}

impl<S: CompressionStrategy> Compressor<S> {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }
}

// 使用
let gzip_compressor = Compressor { strategy: GzipCompression };
let compressed = gzip_compressor.compress(data);
```

### Observer模式

```rust
use c12_model::*;

// 已在c12_model中实现
let mut subject = Subject::new();

let observer1 = Box::new(ConcreteObserver::new("Logger"));
let observer2 = Box::new(ConcreteObserver::new("EmailSender"));

subject.attach(observer1);
subject.attach(observer2);

subject.notify("Important event occurred!");
```

### Decorator模式

```rust
trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

struct SimpleCoffee;
impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 { 2.0 }
    fn description(&self) -> String { "Simple coffee".to_string() }
}

struct MilkDecorator<C: Coffee> {
    coffee: C,
}

impl<C: Coffee> Coffee for MilkDecorator<C> {
    fn cost(&self) -> f64 { self.coffee.cost() + 0.5 }
    fn description(&self) -> String {
        format!("{}, milk", self.coffee.description())
    }
}

struct SugarDecorator<C: Coffee> {
    coffee: C,
}

impl<C: Coffee> Coffee for SugarDecorator<C> {
    fn cost(&self) -> f64 { self.coffee.cost() + 0.2 }
    fn description(&self) -> String {
        format!("{}, sugar", self.coffee.description())
    }
}

// 使用
let coffee = SimpleCoffee;
let coffee = MilkDecorator { coffee };
let coffee = SugarDecorator { coffee };

println!("{}: ${}", coffee.description(), coffee.cost());
// 输出: Simple coffee, milk, sugar: $2.7
```

## 范式组合与混合模式

**Rust的多范式特性**:

```rust
// 函数式 + 面向对象 + 并发
use rayon::prelude::*;

trait Processor {  // OOP: trait多态
    fn process(&self, data: Data) -> Result;
}

fn process_batch<P: Processor + Sync>(
    processor: &P,
    items: Vec<Data>,
) -> Vec<Result> {
    items.par_iter()  // 并发: 并行迭代
        .map(|item| processor.process(item.clone()))  // FP: map
        .collect()  // FP: collect
}
```

**反应式 + 事件驱动**:

```rust
use c12_model::*;

// 反应式流 + 事件总线
let stream = ReactiveStream::new();
let event_bus = EventBus::new();

stream
    .filter(|x| x > threshold)
    .map(|x| DomainEvent::from(x))
    .subscribe(|event| {
        event_bus.publish(event);
    });
```

## 实战案例

### 案例1: Web应用架构演进

**阶段1: 单体应用**:

```rust
struct MonolithApp {
    router: Router,
    db: Database,
}

impl MonolithApp {
    fn handle_request(&self, req: Request) -> Response {
        match req.path {
            "/users" => self.handle_users(req),
            "/orders" => self.handle_orders(req),
            "/payments" => self.handle_payments(req),
            _ => Response::not_found(),
        }
    }
}
```

**阶段2: 分层架构**:

```rust
struct LayeredApp {
    presentation: ApiController,
    business: BusinessService,
    persistence: Repository,
}
```

**阶段3: 六边形架构**:

```rust
struct HexagonalApp<R: RepositoryPort, N: NotificationPort> {
    core: DomainService,
    repository: R,
    notifier: N,
}
```

**阶段4: 微服务**:

```rust
// 拆分为独立服务
struct UserService { /* ... */ }
struct OrderService { /* ... */ }
struct PaymentService { /* ... */ }
```

### 案例2: 分布式系统设计

**组合模式**:

```rust
use c12_model::*;

// CQRS + Event Sourcing + Microservices
struct DistributedSystem {
    // 命令端(写)
    command_service: CommandService,
    event_store: EventStore,
    
    // 查询端(读)
    query_service: QueryService,
    read_db: ReadDatabase,
    
    // 分布式共识
    raft: RaftProtocol,
    
    // 服务网格
    service_mesh: ServiceMesh,
}
```

### 案例3: 高性能计算系统

**数据流 + 并行模型**:

```rust
use c12_model::*;

// 数据流图 + 任务并行
let mut dataflow = DataflowGraph::new();
let parallel_executor = TaskParallelExecutor::new(num_cpus::get());

// 构建计算管道
let stage1 = dataflow.add_node("load");
let stage2 = dataflow.add_node("transform");
let stage3 = dataflow.add_node("aggregate");

dataflow.connect(stage1, stage2);
dataflow.connect(stage2, stage3);

// 并行执行
parallel_executor.execute(dataflow)?;
```

## 架构评估与权衡

**评估维度**:

| 维度 | 单体 | 分层 | 六边形 | 微服务 | 事件驱动 |
|------|------|------|--------|--------|---------|
| 复杂度 | 低 | 中 | 中 | 高 | 高 |
| 可测试性 | 中 | 中 | 高 | 高 | 中 |
| 可扩展性 | 低 | 中 | 中 | 高 | 高 |
| 性能 | 高 | 高 | 高 | 中 | 中 |
| 部署难度 | 低 | 低 | 低 | 高 | 中 |
| 团队规模 | 小 | 中 | 中 | 大 | 中 |

**选择决策树**:

```text
项目规模?
├─ 小型 (<10K LOC)
│  └─→ 单体 或 分层架构
├─ 中型 (10K-100K LOC)
│  └─→ 分层 或 六边形架构
└─ 大型 (>100K LOC)
   ├─ 单团队 → 模块化单体 + 六边形
   └─ 多团队 → 微服务架构
```

## 最佳实践

1. **从简单开始**: 不要过早微服务化
2. **边界清晰**: 明确定义模块/服务边界
3. **依赖管理**: 使用依赖注入和接口抽象
4. **测试优先**: 架构设计应便于测试
5. **渐进演进**: 支持架构平滑演进
6. **文档齐全**: 记录架构决策(ADR)
7. **性能监控**: 建立可观测性体系
8. **安全第一**: 架构层面考虑安全

**Rust特定最佳实践**:

```rust
// 1. 使用newtype模式增强类型安全
struct UserId(String);
struct OrderId(String);

// 2. 利用trait做抽象
trait Repository<T> {
    fn find(&self, id: &str) -> Result<T>;
    fn save(&self, entity: &T) -> Result<()>;
}

// 3. 使用Result处理错误
fn process() -> Result<Output, Error> {
    let data = load()?;
    let validated = validate(data)?;
    Ok(transform(validated))
}

// 4. 利用所有权避免数据竞争
struct Service {
    state: Arc<RwLock<State>>,
}
```

## 总结

软件设计模型提供了构建高质量系统的理论框架:

**核心洞察**:

1. **没有银弹**: 每种架构都有权衡
2. **渐进演进**: 随需求演化架构
3. **模式组合**: 混合使用多种模式
4. **Rust优势**: 类型安全 + 零成本抽象 + 并发安全

**关键能力**:

- ✅ 理解各种架构模式的本质
- ✅ 分析模式间的等价性和转换
- ✅ 根据场景选择合适的模式
- ✅ 在Rust中优雅地实现模式

**未来方向**:

- Serverless架构
- Function-as-a-Service (FaaS)
- Edge Computing
- WebAssembly模块化

## 参考文献

1. Martin Fowler. "Patterns of Enterprise Application Architecture". 2002
2. Eric Evans. "Domain-Driven Design". 2003
3. Gregor Hohpe, Bobby Woolf. "Enterprise Integration Patterns". 2003
4. Sam Newman. "Building Microservices". 2015
5. Mark Richards, Neal Ford. "Fundamentals of Software Architecture". 2020
6. [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
7. [The Rust Programming Language](https://doc.rust-lang.org/book/)
