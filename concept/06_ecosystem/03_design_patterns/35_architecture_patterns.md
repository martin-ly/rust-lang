> **内容分级**: [专家级]
> **代码状态**: ✅ 含可编译示例
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
# Architecture Patterns（架构设计模式）
>
> **EN**: Design Patterns
> **Summary**: Design Patterns. Guide to 35 Architecture Patterns.
>
> **受众**: [进阶]
> **Bloom 层级**: L4-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: C×Cre — 分析系统架构层级与依赖关系设计
> **前置依赖**: [泛型（Generics）](../../02_intermediate/01_generics/02_generics.md) · [Trait](../../02_intermediate/00_traits/01_traits.md) · [生命周期（Lifetimes）](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · 设计模式
> **后置延伸**: [CQRS & Event Sourcing](33_cqrs_event_sourcing.md) · [微服务架构模式](31_microservice_patterns.md) · [事件驱动架构](32_event_driven_architecture.md)
>
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **前置概念**: N/A
---

> **来源**: [Hexagonal Architecture — Alistair Cockburn](https://alistair.cockburn.us/hexagonal-architecture/) ·
> [Onion Architecture — Jeffrey Palermo](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken --> ·
> [Clean Architecture — Robert C. Martin](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) ·
> [Martin Fowler — Enterprise Architecture Patterns](https://martinfowler.com/books/eaa.html) ·
> [Serverless Architectures — AWS](https://aws.amazon.com/serverless/) ·
> [AWS Lambda Best Practices](https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html)
> [来源: [Fowler — EAA](https://martinfowler.com/books/eaa.html)] ·
> [来源: [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/)]
> **后置概念**: [Future Roadmap](../../07_future/05_roadmaps/24_roadmap.md)
> **前置依赖**: [Type Theory](../../04_formal/00_type_theory/02_type_theory.md)
> **前置依赖**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

## 📑 目录

- [Architecture Patterns（架构设计模式）](#architecture-patterns架构设计模式)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 分层架构（Layered Architecture）](#11-分层架构layered-architecture)
    - [1.2 六边形架构 / 端口与适配器（Hexagonal / Ports \& Adapters）](#12-六边形架构--端口与适配器hexagonal--ports--adapters)
    - [1.3 洋葱架构（Onion Architecture）](#13-洋葱架构onion-architecture)
    - [1.4 整洁架构（Clean Architecture）](#14-整洁架构clean-architecture)
    - [1.5 Serverless / FaaS（无服务器/函数即服务）](#15-serverless--faas无服务器函数即服务)
  - [二、概念属性矩阵](#二概念属性矩阵)
  - [三、分层架构](#三分层架构)
    - [3.1 经典四层模型](#31-经典四层模型)
    - [3.2 依赖规则](#32-依赖规则)
  - [四、六边形架构](#四六边形架构)
    - [4.1 端口（Ports）](#41-端口ports)
    - [4.2 适配器（Adapters）](#42-适配器adapters)
    - [4.3 Rust 实现](#43-rust-实现)
  - [五、洋葱架构](#五洋葱架构)
    - [5.1 层次结构](#51-层次结构)
    - [5.2 依赖方向](#52-依赖方向)
  - [六、整洁架构](#六整洁架构)
    - [6.1 同心圆模型](#61-同心圆模型)
    - [6.2 依赖规则](#62-依赖规则)
    - [6.3 与六边形/洋葱的关系](#63-与六边形洋葱的关系)
  - [七、Serverless / FaaS](#七serverless--faas)
    - [7.1 架构特征](#71-架构特征)
    - [7.2 Rust 在 Serverless 中的实践](#72-rust-在-serverless-中的实践)
    - [7.3 冷启动与性能优化](#73-冷启动与性能优化)
  - [八、对比矩阵](#八对比矩阵)
    - [8.1 架构模式决策矩阵](#81-架构模式决策矩阵)
    - [8.2 架构模式适用场景](#82-架构模式适用场景)
  - [九、反命题与边界](#九反命题与边界)
    - [9.1 反命题树](#91-反命题树)
    - [9.2 边界极限](#92-边界极限)
  - [十、边界测试](#十边界测试)
    - [10.1 边界测试：适配器绕过端口直接依赖核心（编译错误）](#101-边界测试适配器绕过端口直接依赖核心编译错误)
    - [10.2 边界测试：跨层依赖导致循环依赖（编译错误）](#102-边界测试跨层依赖导致循环依赖编译错误)
    - [10.3 边界测试：Serverless 超时导致状态不一致（运行时错误）](#103-边界测试serverless-超时导致状态不一致运行时错误)
  - [相关概念文件](#相关概念文件)
    - [补充定理链](#补充定理链)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Rust 中常用的分层架构（Layered Architecture）如何划分？（理解层）](#测验-1rust-中常用的分层架构layered-architecture如何划分理解层)
    - [测验 2：六边形架构（Hexagonal Architecture / Ports and Adapters）在 Rust 中如何体现？（理解层）](#测验-2六边形架构hexagonal-architecture--ports-and-adapters在-rust-中如何体现理解层)
    - [测验 3：Rust 的强类型系统对洋葱架构（Onion Architecture）有什么天然支持？（理解层）](#测验-3rust-的强类型系统对洋葱架构onion-architecture有什么天然支持理解层)
    - [测验 4：什么是"依赖倒置原则"（DIP）？Rust 的 trait 如何帮助实现它？（理解层）](#测验-4什么是依赖倒置原则diprust-的-trait-如何帮助实现它理解层)
    - [测验 5：在 Rust 中，为什么 Repository 模式比直接在 Service 中调用 SQL 更受推荐？（理解层）](#测验-5在-rust-中为什么-repository-模式比直接在-service-中调用-sql-更受推荐理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [十一、架构演进与对比（crates 迁移）](#十一架构演进与对比crates-迁移)
    - [架构演进路径](#架构演进路径)
      - [单体 → 分布式演进](#单体--分布式演进)
      - [架构决策因子](#架构决策因子)
    - [架构模式对比](#架构模式对比)

**变更日志**:

- v1.0 (2026-05-25): 初始创建——分层/六边形/洋葱/整洁/Serverless 架构模式对比，含 Rust 实现骨架与边界测试

---

## 一、权威定义（Definition）
>

### 1.1 分层架构（Layered Architecture）
>
> **[Martin Fowler — Enterprise Application Architecture](https://martinfowler.com/books/eaa.html)** 分层架构将系统组织为水平层级，每一层提供特定的抽象级别，并且只依赖于其下方的层。这是企业应用中最常见的架构模式。

```text
┌─────────────────────┐
│   Presentation      │  ← 用户界面、HTTP 路由、API 序列化
├─────────────────────┤
│   Application       │  ← 用例编排、事务边界、DTO 转换
├─────────────────────┤
│   Domain            │  ← 业务规则、实体、值对象、领域服务
├─────────────────────┤
│   Infrastructure    │  ← 数据库、消息队列、外部 API 客户端
└─────────────────────┘
         ↓ 依赖方向（上层依赖下层）
```

> **来源**: [Fowler — EAA](https://martinfowler.com/books/eaa.html) · [Evans — DDD](https://www.amazon.com/Domain-Driven-Design-Tackling-Complexity-Software/dp/0321125215)
> [来源: [Palermo — Onion](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken -->] · [来源: [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)]

### 1.2 六边形架构 / 端口与适配器（Hexagonal / Ports & Adapters）
>
> **[Alistair Cockburn — Hexagonal Architecture](https://alistair.cockburn.us/hexagonal-architecture/)** 六边形架构（又称端口与适配器）将应用程序置于中心，外部世界通过**端口**（抽象接口）与应用程序交互，具体的技术实现通过**适配器**连接端口。目标是让应用程序独立于框架、UI 和数据库。

```text
         ┌───────────────┐
         │   Web UI      │
         └───────┬───────┘
                 │ HTTP
         ┌───────▼───────┐
         │  Web Adapter  │
         └───────┬───────┘
                 │
    ┌────────────┼────────────┐
    │  ┌─────────┴─────────┐  │
    │  │   Application     │  │  ← 核心：业务逻辑
    │  │  (Inside)         │  │     不依赖任何外部技术
    │  │                   │  │
    │  │  ┌─────────────┐  │  │
    │  │  │   Domain    │  │  │
    │  │  │  (Ports)    │  │  │
    │  │  └─────────────┘  │  │
    │  └───────────────────┘  │
    └────────────┬────────────┘
                 │
         ┌───────▼───────┐
         │  DB Adapter   │
         └───────┬───────┘
                 │ SQL
         ┌───────▼───────┐
         │   PostgreSQL  │
         └───────────────┘
```

> **来源**: [Cockburn — Hexagonal Architecture](https://alistair.cockburn.us/hexagonal-architecture/) · [Cockburn — Ports & Adapters Pattern](https://alistair.cockburn.us/hexagonal-architecture/)
> [来源: [AWS — Serverless](https://aws.amazon.com/serverless/)] · [来源: [Evans — DDD](https://www.amazon.com/Domain-Driven-Design-Tackling-Complexity-Software/dp/0321125215)]

### 1.3 洋葱架构（Onion Architecture）
>
> **[Jeffrey Palermo — Onion Architecture](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken -->** 洋葱架构是分层架构的演进，核心思想是**领域模型位于最内层**，所有依赖都指向中心。外层定义接口，内层实现接口——与经典分层架构的依赖方向完全相反。

```text
         ┌───────────────┐
         │   UI / API    │  ← 最外层：具体技术
         │   Tests       │
         ├───────────────┤
         │  Application  │  ← 用例层
         │  Services     │
         ├───────────────┤
         │   Domain      │  ← 领域服务
         │   Services    │
         ├───────────────┤
         │   Domain      │  ← 最内层：实体、值对象
         │   Model       │     零外部依赖
         └───────────────┘
              ↑ 依赖方向（全部指向中心）
```

> **来源**: [Palermo — Onion Architecture](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken --> · [Palermo — Onion Architecture Part 3](https://jeffreypalermo.com/blog/the-onion-architecture-part-3/)

### 1.4 整洁架构（Clean Architecture）
>
> **[Robert C. Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)** 整洁架构是六边形架构和洋葱架构的进一步抽象和规范化。核心原则：**依赖关系只能向内指向更抽象、更稳定的层**。外层是机制（Mechanisms），内层是策略（Policies）。

```text
         ┌───────────────┐
         │   Frameworks  │  ← 外层: UI, Database, Web, External Interfaces
         │   Drivers     │     (最易变)
         ├───────────────┤
         │   Interface   │  ← 接口适配器
         │   Adapters    │
         ├───────────────┤
         │  Application  │  ← 用例层
         │  Business     │     (相对稳定)
         │  Rules        │
         ├───────────────┤
         │   Enterprise  │  ← 最内层: Entities
         │   Business    │     (最稳定，零依赖)
         │   Rules       │
         └───────────────┘
              ↑ 依赖规则 (Dependency Rule)
```

> **来源**: [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) · [Martin — Clean Architecture Book](https://www.amazon.com/Clean-Architecture-Craftsmans-Software-Structure/dp/0134494164)

### 1.5 Serverless / FaaS（无服务器/函数即服务）
>
> **[AWS — Serverless Architectures](https://aws.amazon.com/serverless/)** Serverless 是一种云计算执行模型，云提供商动态管理计算资源的分配。函数即服务（FaaS）是 Serverless 的核心组件，开发者上传代码函数，平台在事件触发时自动执行。

```text
传统架构:         Serverless 架构:
┌──────────┐      ┌──────────┐
│  Client  │      │  Client  │
└────┬─────┘      └────┬─────┘
     │ HTTP              │ HTTP
┌────▼─────┐      ┌─────▼────┐
│  Server  │      │ API Gateway │
│ (always  │      └─────┬────┘
│  running)│            │ trigger
└────┬─────┘      ┌─────▼────┐
     │ SQL        │ Lambda   │  ← 按需执行
┌────▼─────┐      │ Function │     冷启动 / 热复用
│ Database │      └─────┬────┘
└──────────┘            │
                   ┌────▼─────┐
                   │ Database │
                   └──────────┘
```

> **来源**: [AWS — Serverless](https://aws.amazon.com/serverless/) · [Azure Functions](https://docs.microsoft.com/en-us/azure/azure-functions/) · [Google Cloud Functions](https://cloud.google.com/functions)

---

## 二、概念属性矩阵

| **维度** | **分层架构** | **六边形架构** | **洋葱架构** | **整洁架构** | **Serverless** |
|:---|:---|:---|:---|:---|:---|
| **核心思想** | 水平抽象层级 | 端口/适配器隔离 | 领域在中心 | 依赖向内 | 事件驱动、按需执行 |
| **依赖方向** | 上层 → 下层 | 外部 → 内部 | 外层 → 内层 | 外层 → 内层 | 无（函数无状态）|
| **领域位置** | 中间层 | 六边形中心 | 最内层 | 最内层（Entities）| 函数内 |
| **框架耦合** | 高（基础设施在最底层）| 低 | 低 | 低 | 极高（平台锁定）|
| **可测试性** | 中（需模拟下层）| 高（直接测试核心）| 高 | 高 | 中（本地模拟困难）|
| **Rust 适配性** | 良好 | 优秀（Trait 即端口）| 优秀 | 优秀 | 良好（cargo-lambda）|
| **主要来源** | Fowler EAA | Cockburn | Palermo | Martin | AWS / Azure / GCP |

> **来源**: [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/) · [Palermo — Onion](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken --> · [Martin — Clean](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) · [AWS — Serverless](https://aws.amazon.com/serverless/)

---

## 三、分层架构

### 3.1 经典四层模型
>

```rust,ignore
// 分层架构在 Rust 中的模块组织
//
// order-service/
// ├── src/
// │   ├── main.rs              # 入口：组装各层
// │   ├── presentation/        # 表示层：HTTP 路由、JSON 序列化
// │   │   ├── mod.rs
// │   │   ├── routes.rs
// │   │   └── dto.rs
// │   ├── application/         # 应用层：用例编排、事务
// │   │   ├── mod.rs
// │   │   ├── commands.rs
// │   │   └── queries.rs
// │   ├── domain/              # 领域层：业务规则、实体
// │   │   ├── mod.rs
// │   │   ├── order.rs
// │   │   ├── customer.rs
// │   │   └── repository.rs    # 仓储接口（trait）
// │   └── infrastructure/      # 基础设施层：具体实现
// │       ├── mod.rs
// │       ├── persistence.rs   # PostgreSQL 实现
// │       └── messaging.rs     # Kafka 实现

// domain/repository.rs — 领域层只定义接口，不依赖具体技术
use uuid::Uuid;

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
pub trait OrderRepository: Send + Sync {
    async fn find_by_id(&self, id: Uuid) -> Option<Order>;
    async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
    async fn delete(&self, id: Uuid) -> Result<(), RepositoryError>;
}

// domain/order.rs — 纯业务逻辑，零外部依赖
#[derive(Debug, Clone)]
pub struct Order {
    id: Uuid,
    customer_id: Uuid,
    items: Vec<OrderItem>,
    status: OrderStatus,
}

impl Order {
    pub fn add_item(&mut self, item: OrderItem) -> Result<(), DomainError> {
        if self.status != OrderStatus::Pending {
            return Err(DomainError::CannotModifySubmittedOrder);
        }
        self.items.push(item);
        Ok(())
    }

    pub fn submit(&mut self) -> Result<(), DomainError> {
        if self.items.is_empty() {
            return Err(DomainError::EmptyOrder);
        }
        self.status = OrderStatus::Submitted;
        Ok(())
    }
}
```

> **来源**: [来源: [Fowler — EAA](https://martinfowler.com/books/eaa.html)]

### 3.2 依赖规则
>

```text
分层架构的依赖规则（Fowler）:
  Presentation  ──depends on──→ Application
  Application   ──depends on──→ Domain
  Domain        ──depends on──→ Infrastructure  ❌ 违反依赖规则！

正确方向:
  Presentation  ──depends on──→ Application
  Application   ──depends on──→ Domain
  Infrastructure──depends on──→ Domain  ✅ Domain 不依赖 Infrastructure

Rust 实现: 通过 Cargo workspace 的依赖约束强制分层
  # Cargo.toml (domain crate)
  [dependencies]
  # 零外部依赖（仅标准库 + uuid + chrono 等纯工具库）

  # Cargo.toml (infrastructure crate)
  [dependencies]
  domain = { path = "../domain" }  # 基础设施依赖领域
  sqlx = "0.7"
  tokio = "1"
```

> **来源**: [Fowler — EAA](https://martinfowler.com/books/eaa.html) · [Evans — DDD](https://www.amazon.com/Domain-Driven-Design-Tackling-Complexity-Software/dp/0321125215)

---

## 四、六边形架构

### 4.1 端口（Ports）
>

端口是应用程序与外部世界交互的**抽象接口**。在 Rust 中，端口就是 `trait`。

```rust,ignore
// 驱动端口（Driving Ports）—— 外部调用应用程序
// 对应: Web API, CLI, 消息消费者

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
pub trait OrderService {
    async fn place_order(&self, cmd: PlaceOrderCommand) -> Result<Uuid, OrderError>;
    async fn get_order(&self, id: Uuid) -> Option<OrderDto>;
    async fn cancel_order(&self, id: Uuid) -> Result<(), OrderError>;
}

// 被驱动端口（Driven Ports）—— 应用程序调用外部
// 对应: 数据库、消息队列、外部 API

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
pub trait OrderRepository {
    async fn find_by_id(&self, id: Uuid) -> Option<Order>;
    async fn save(&self, order: &Order) -> Result<(), RepositoryError>;
}

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
pub trait EventPublisher {
    async fn publish(&self, event: DomainEvent) -> Result<(), PublishError>;
}

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
pub trait PaymentGateway {
    async fn charge(&self, amount: f64, currency: &str) -> Result<PaymentResult, PaymentError>;
}
```

> **来源**: [来源: [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/)]

### 4.2 适配器（Adapters）
>

适配器是端口的**具体实现**，将外部技术框架适配到应用程序的抽象接口。

```rust
// 驱动适配器：HTTP API（外部 → 应用程序）
pub struct HttpOrderAdapter<OS: OrderService> {
    order_service: OS,
}

impl<OS: OrderService> HttpOrderAdapter<OS> {
    pub async fn create_order_handler(
        State(state): State<Arc<Self>>,
        Json(cmd): Json<PlaceOrderCommand>,
    ) -> Result<Json<OrderResponse>, StatusCode> {
        match state.order_service.place_order(cmd).await {
            Ok(id) => Ok(Json(OrderResponse { order_id: id })),
            Err(OrderError::InvalidInput(msg)) => {
                Err(StatusCode::BAD_REQUEST)
            }
            Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
        }
    }
}

// 被驱动适配器：PostgreSQL 实现（应用程序 → 外部）
pub struct PostgresOrderRepository {
    pool: PgPool,
}

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
impl OrderRepository for PostgresOrderRepository {
    async fn find_by_id(&self, id: Uuid) -> Option<Order> {
        sqlx::query_as::<_, OrderRow>("SELECT * FROM orders WHERE id = $1")
            .bind(id)
            .fetch_optional(&self.pool).await.ok()?
            .map(|row| row.into())
    }

    async fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        sqlx::query(
            "INSERT INTO orders (id, customer_id, status, total) VALUES ($1, $2, $3, $4) ON CONFLICT (id) DO UPDATE SET status = $3, total = $4"
        )
        .bind(order.id).bind(order.customer_id).bind(order.status.as_str()).bind(order.total())
        .execute(&self.pool).await?;
        Ok(())
    }
}

// 被驱动适配器：Kafka 事件发布（应用程序 → 外部）
pub struct KafkaEventPublisher {
    producer: FutureProducer,
    topic: String,
}

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
impl EventPublisher for KafkaEventPublisher {
    async fn publish(&self, event: DomainEvent) -> Result<(), PublishError> {
        let payload = serde_json::to_string(&event)?;
        self.producer.send(
            FutureRecord::to(&self.topic)
                .payload(&payload)
                .key(&event.aggregate_id().to_string()),
            Duration::from_secs(5),
        ).await?;
        Ok(())
    }
}
```

> **来源**: [来源: [Cockburn — Ports & Adapters](https://alistair.cockburn.us/hexagonal-architecture/)]

### 4.3 Rust 实现
>

```rust
// main.rs — 六边形架构的组装（Composition Root）
#[tokio::main]
async fn main() {
    // 1. 创建被驱动适配器（基础设施）
    let db_pool = PgPool::connect(&env::var("DATABASE_URL").unwrap()).await.unwrap();
    let kafka_producer = create_kafka_producer();

    let order_repo = Arc::new(PostgresOrderRepository::new(db_pool));
    let event_pub = Arc::new(KafkaEventPublisher::new(kafka_producer, "order-events".to_string()));
    let payment_gateway = Arc::new(StripePaymentGateway::new(env::var("STRIPE_KEY").unwrap()));

    // 2. 创建应用程序核心（注入端口实现）
    let order_service = Arc::new(OrderServiceImpl::new(
        order_repo.clone(),
        event_pub.clone(),
        payment_gateway.clone(),
    ));

    // 3. 创建驱动适配器（注入应用程序核心）
    let http_adapter = Arc::new(HttpOrderAdapter::new(order_service.clone()));

    // 4. 启动 HTTP 服务器
    let app = Router::new()
        .route("/orders", post(HttpOrderAdapter::create_order_handler))
        .route("/orders/:id", get(HttpOrderAdapter::get_order_handler))
        .layer(Extension(http_adapter));

    axum::serve(TcpListener::bind("0.0.0.0:3000").await.unwrap(), app).await.unwrap();
}
```

> **关键洞察**: Rust 的 `trait` 系统是六边形架构的**理想实现**：
>
> - 端口 = `trait`（抽象接口）
> - 适配器 = `impl Trait for Struct`（具体实现）
> - 依赖注入 = 泛型（Generics）参数或 `Arc<dyn Trait>`（动态分发）
> - 编译器强制依赖规则 = `cargo` 的模块（Module）可见性和 workspace 依赖约束
>
> **来源**: [Cockburn — Hexagonal Architecture](https://alistair.cockburn.us/hexagonal-architecture/) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/))

---

## 五、洋葱架构

### 5.1 层次结构
>

洋葱架构是分层架构的**依赖反转**版本。核心规则：**所有依赖都指向中心**。

```text
洋葱架构层次（Palermo）:

Layer 1 — Domain Model（最内层）
  ├── Entities（实体）: Order, Customer, Product
  ├── Value Objects（值对象）: Money, Address, OrderItem
  └── Domain Events（领域事件）: OrderPlaced, PaymentReceived
  依赖: 无（纯 Rust 数据结构）

Layer 2 — Domain Services
  ├── OrderDomainService: 跨越多个实体的业务规则
  └── PricingService: 复杂的定价逻辑
  依赖: Layer 1

Layer 3 — Application Services
  ├── OrderApplicationService: 用例编排
  └── DTOs: 应用层数据传输对象
  依赖: Layer 1, Layer 2

Layer 4 — Infrastructure（最外层）
  ├── Repositories: PostgreSQLRepository, RedisRepository
  ├── Controllers: HTTP handlers, gRPC services
  └── External Services: PaymentGateway, EmailService
  依赖: Layer 1, Layer 2, Layer 3
```

```rust,ignore
// Layer 1: Domain Model — 零外部依赖
// src/domain/model.rs
#[derive(Debug, Clone)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
}

impl Order {
    pub fn total(&self) -> Money {
        self.items.iter().map(|i| i.price * i.quantity).sum()
    }
    // ... 纯业务逻辑，无 async，无外部调用
}

// Layer 2: Domain Services
// src/domain/services.rs
pub struct PricingService;

impl PricingService {
    pub fn calculate_discount(order: &Order, customer: &Customer) -> Money {
        if customer.is_vip() && order.total() > Money::from(100.0) {
            order.total() * 0.1  // VIP 10% 折扣
        } else {
            Money::zero()
        }
    }
}

// Layer 3: Application Services
// src/application/services.rs
pub struct OrderApplicationService<R: OrderRepository, P: PaymentGateway> {
    repo: R,
    payment: P,
}

impl<R: OrderRepository, P: PaymentGateway> OrderApplicationService<R, P> {
    pub async fn place_order(&self, cmd: PlaceOrderCommand) -> Result<OrderId, ApplicationError> {
        let mut order = Order::new(cmd.customer_id);
        for item in cmd.items {
            order.add_item(item)?;
        }

        self.payment.charge(order.total(), "USD").await?;
        self.repo.save(&order).await?;

        Ok(order.id)
    }
}

// Layer 4: Infrastructure — 具体技术实现
// src/infrastructure/repositories.rs
pub struct PostgresOrderRepository { pool: PgPool }

// 注意：Axum 0.8+ 使用原生 AFIT，不再需要 #[async_trait]
impl OrderRepository for PostgresOrderRepository {
    async fn save(&self, order: &Order) -> Result<(), RepositoryError> {
        // PostgreSQL 具体实现（示意）
        sqlx::query("INSERT INTO orders (id, total) VALUES ($1, $2)")
            .bind(&order.id)
            .bind(order.total)
            .execute(&self.pool)
            .await
            .map_err(RepositoryError::from)?;
        Ok(())
    }
}
```

> **来源**: [来源: [Palermo — Onion](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken -->]

### 5.2 依赖方向
>

```text
洋葱架构 vs 经典分层架构的依赖方向对比:

经典分层:              洋葱架构:
  Presentation           UI/API (外层)
       ↓                      ↓
  Application          Application (中层)
       ↓                      ↓
     Domain             Domain Services
       ↓                      ↓
  Infrastructure        Domain Model (内层)

关键区别:
  - 经典分层: Domain 依赖 Infrastructure（通过接口间接依赖）
  - 洋葱架构: Infrastructure 依赖 Domain（依赖倒置）
  - 洋葱架构的 Domain Model 是真正的"零依赖"核心
```

> **来源**: [Palermo — Onion Architecture](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken --> · [Palermo — Onion Architecture Part 3](https://jeffreypalermo.com/blog/the-onion-architecture-part-3/)

---

## 六、整洁架构

### 6.1 同心圆模型
>

整洁架构将系统组织为**同心圆**，每一层代表不同的抽象级别：

```text
同心圆层次（Martin）:

Enterprise Business Rules（最内层）
  └── Entities: 跨应用共享的核心业务对象
      例: User, Account, Transaction
      特征: 可独立存在，不依赖任何框架

Application Business Rules
  └── Use Cases: 特定应用的用例编排
      例: TransferMoney, CreateOrder
      特征: 编排 Entities 完成业务流程

Interface Adapters
  ├── Presenters: 数据格式化（JSON/XML/HTML）
  ├── Controllers: HTTP/gRPC 请求处理
  └── Gateways: 数据库/外部 API 的抽象接口

Frameworks & Drivers（最外层）
  ├── Web Framework: axum, actix-web, rocket
  ├── Database: sqlx, diesel, sea-orm
  ├── External APIs: reqwest, tonic
  └── UI: CLI, Web, Mobile
```

> **来源**: [来源: [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)]

### 6.2 依赖规则
>
> **[Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)** 依赖规则：源代码依赖只能**向内**指向更高层次的抽象。内层不知道外层的任何信息。

```rust
// ❌ 违反依赖规则: Entity 依赖外部框架
// src/entities/order.rs
use sqlx::FromRow;  // ❌ 错误！Entity 不应依赖数据库框架

#[derive(FromRow)]  // ❌ 错误！
pub struct Order {
    pub id: Uuid,
    pub total: f64,
}

// ✅ 正确: Entity 是纯数据结构
// src/entities/order.rs
pub struct Order {
    pub id: OrderId,
    pub total: Money,
    pub items: Vec<OrderItem>,
}

// 外部框架的使用仅限于外层（Interface Adapters / Infrastructure）
// src/adapters/persistence/order_mapper.rs
use sqlx::FromRow;
use crate::entities::Order;

#[derive(FromRow)]
pub struct OrderRow {
    pub id: Uuid,
    pub total: f64,
}

impl From<OrderRow> for Order {
    fn from(row: OrderRow) -> Self {
        Order { /* 转换逻辑 */ }
    }
}
```

> **来源**: [来源: [Martin — Clean Architecture Book](https://www.amazon.com/Clean-Architecture-Craftsmans-Software-Structure/dp/0134494164)]

### 6.3 与六边形/洋葱的关系
>

```text
架构演进关系:

分层架构 (Fowler, 2002)
    │
    ├── 问题: Domain 依赖 Infrastructure（通过接口）
    │
    ▼
六边形架构 (Cockburn, 2005)
    │   改进: 明确区分 Ports（接口）和 Adapters（实现）
    │   核心: 应用程序独立于技术框架
    │
    ▼
洋葱架构 (Palermo, 2008)
    │   改进: 依赖方向反转（全部指向中心）
    │   核心: Domain Model 是真正的零依赖核心
    │
    ▼
整洁架构 (Martin, 2012)
    │   改进: 规范化术语和层次
    │   核心: Entities → Use Cases → Interface Adapters → Frameworks
    │
    └── 共同原则: 依赖倒置（Dependency Inversion Principle）

Rust 实现共性: 所有四种架构都可以用 Rust 的 trait + 模块系统实现
  - 端口/接口 = trait
  - 依赖注入 = 泛型或 Arc<dyn Trait>
  - 编译器保证 = cargo workspace 依赖约束
```

> **来源**: [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) · [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/) · [Palermo — Onion](https://jeffreypalermo.com/blog/the-onion-architecture-part-1/) <!-- link: known-broken -->

---

## 七、Serverless / FaaS

### 7.1 架构特征
>

| **特征** | **传统架构** | **Serverless (FaaS)** |
|:---|:---|:---|
| **执行模型** | 常驻进程 | 事件触发、按需执行 |
| **计费模式** | 按资源/时间 | 按请求数 + 执行时间 |
| **状态管理** | 内存/本地存储 | 无状态（外部存储）|
| **扩展** | 手动/自动 | 自动（由平台管理）|
| **冷启动** | 无 | 有（首次调用延迟）|
| **执行时长限制** | 无限制 | 有限制（通常 15min）|
| **Rust 支持** | 原生 | cargo-lambda, serverless framework |

> **来源**: [来源: [AWS — Serverless](https://aws.amazon.com/serverless/)]

### 7.2 Rust 在 Serverless 中的实践
>

```rust
// AWS Lambda with Rust (cargo-lambda)
// Cargo.toml:
// [dependencies]
// lambda_runtime = "0.11"
// serde = { version = "1", features = ["derive"] }
// tokio = { version = "1", features = ["macros"] }
// aws-sdk-dynamodb = "1"

use lambda_runtime::{service_fn, LambdaEvent, Error};
use serde_json::{json, Value};

#[derive(Debug, serde::Deserialize)]
struct OrderRequest {
    customer_id: String,
    items: Vec<OrderItemRequest>,
}

#[derive(Debug, serde::Deserialize)]
struct OrderItemRequest {
    product_id: String,
    quantity: i32,
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    // Lambda 运行时入口：每个请求调用一次 handler
    let func = service_fn(handler);
    lambda_runtime::run(func).await?;
    Ok(())
}

async fn handler(event: LambdaEvent<OrderRequest>) -> Result<Value, Error> {
    let request = event.payload;

    // 无状态: 每次调用都需要重新初始化客户端
    let config = aws_config::load_from_env().await;
    let dynamodb = aws_sdk_dynamodb::Client::new(&config);

    // 生成订单 ID
    let order_id = uuid::Uuid::new_v4().to_string();

    // 写入 DynamoDB
    dynamodb.put_item()
        .table_name("orders")
        .item("order_id", AttributeValue::S(order_id.clone()))
        .item("customer_id", AttributeValue::S(request.customer_id))
        .item("status", AttributeValue::S("PENDING".to_string()))
        .item("created_at", AttributeValue::S(chrono::Utc::now().to_rfc3339()))
        .send().await?;

    Ok(json!({
        "order_id": order_id,
        "status": "created"
    }))
}
```

> **来源**: [来源: [cargo-lambda](https://www.cargo-lambda.info/)]

### 7.3 冷启动与性能优化
>

```text
Serverless 冷启动的组成（Rust on AWS Lambda）:

1. 初始化阶段（Init Phase）
   ├── 下载容器镜像: ~50-200ms（首次调用）
   ├── 运行时启动: ~10-30ms（Rust 二进制极小，启动快）
   ├── 初始化代码执行: 取决于代码复杂度
   └── 总计: ~100-500ms（Rust 通常 < 200ms）

2. 调用阶段（Invoke Phase）
   ├── 热启动: ~1-5ms（复用已初始化的执行环境）
   └── 冷启动: 包含初始化阶段

Rust 的冷启动优势:
  - 无 GC，启动即运行
  - 静态链接二进制小（~5-15MB vs Node.js ~50MB+）
  - 内存占用低（~10-50MB vs Java ~200MB+）
  - AWS Lambda 的 Rust runtime 优化：graviton2 架构上冷启动 < 50ms
```

```rust
// 冷启动优化：预初始化共享客户端
use std::sync::Arc;
use once_cell::sync::Lazy;

// 使用全局懒加载初始化（在 Init Phase 完成）
static DYNAMODB_CLIENT: Lazy<Arc<aws_sdk_dynamodb::Client>> = Lazy::new(|| {
    let rt = tokio::runtime::Runtime::new().unwrap();
    let config = rt.block_on(aws_config::load_from_env());
    Arc::new(aws_sdk_dynamodb::Client::new(&config))
});

async fn optimized_handler(event: LambdaEvent<OrderRequest>) -> Result<Value, Error> {
    // 复用已初始化的客户端，跳过初始化开销
    let client = DYNAMODB_CLIENT.clone();
    // ... 处理逻辑
    Ok(json!({ "status": "ok" }))
}
```

> **来源**: [AWS Lambda — Rust Runtime](https://github.com/awslabs/aws-lambda-rust-runtime) · [cargo-lambda](https://www.cargo-lambda.info/) · [AWS Lambda Best Practices](https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html) · [Serverless Rust](https://www.serverless.com/plugins/serverless-rust)

---

## 八、对比矩阵

### 8.1 架构模式决策矩阵
>

| **评估维度** | **分层** | **六边形** | **洋葱** | **整洁** | **Serverless** |
|:---|:---|:---|:---|:---|:---|
| **团队规模** | 小-中 | 中-大 | 中-大 | 中-大 | 小-中 |
| **系统复杂度** | 低-中 | 中-高 | 中-高 | 高 | 低-中 |
| **领域复杂度** | 低 | 高 | 高 | 高 | 低 |
| **可测试性** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **技术替换灵活性** | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ |
| **学习曲线** | 低 | 中 | 中 | 高 | 低 |
| **Rust 实现复杂度** | 低 | 中 | 中 | 中 | 低 |
| **部署灵活性** | 高 | 高 | 高 | 高 | 低（平台锁定）|

> **来源**: [来源: [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/)]

### 8.2 架构模式适用场景
>

```text
决策树:

是否需要水平扩展 / 按需付费？
  ├── 是 → 流量模式是事件驱动/间歇性的？
  │         ├── 是 → Serverless ✅
  │         └── 否 → 传统部署 + 容器编排
  └── 否 → 领域复杂度如何？
            ├── 低（< 10 个核心实体）→ 分层架构 ✅
            ├── 中（10-50 个实体）→ 六边形/洋葱 ✅
            └── 高（> 50 个实体，多边界上下文）→ 整洁架构 ✅

技术栈是否可能频繁变更？
  ├── 是 → 六边形/洋葱/整洁（依赖倒置保护核心）✅
  └── 否 → 分层架构 ✅

是否需要跨平台复用领域逻辑？
  ├── 是 → 整洁架构（Entities 层完全独立）✅
  └── 否 → 六边形/洋葱 ✅
```

> **来源**: [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) · [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/) · [AWS — Serverless](https://aws.amazon.com/serverless/)

---

## 九、反命题与边界

### 9.1 反命题树
>

```text
反命题 1: "六边形/洋葱/整洁架构总是优于分层架构"
├── 前提: 所有系统都需要技术隔离和可测试性
├── 反驳:
│   ├── 简单 CRUD 应用（< 5 个实体，无复杂业务规则）
│   │   └── 分层架构足够，额外抽象增加不必要的认知负荷
│   ├── 原型/MVP 阶段
│   │   └── 需要快速迭代，架构约束成为阻碍
│   └── 微脚本/数据处理任务
│       └── 无领域逻辑，无需端口/适配器抽象
└── 根结论: ❌ 架构选择应匹配复杂度。过度架构（Over-engineering）是反模式。

反命题 2: "Serverless 适用于所有应用场景"
├── 前提: FaaS 的按需执行和自动扩展是普适优势
├── 反驳:
│   ├── 长运行任务（> 15min）→ AWS Lambda 超时限制 ❌
│   ├── 低延迟要求（< 10ms P99）→ 冷启动不可预测 ❌
│   ├── 有状态会话 → 无状态模型需要外部存储，增加延迟 ❌
│   ├── 高频持续流量 → 常驻容器更便宜（无冷启动开销）❌
│   └── 需要特定运行时（如 GPU）→ 平台限制 ❌
└── 根结论: ❌ Serverless 适合事件驱动、间歇性、中等延迟容忍的场景

反命题 3: "架构模式可以完全消除技术债务"
├── 前提: 正确的架构模式保证代码质量
├── 反驳:
│   ├── 架构是框架，不是自动执行器
│   ├── 不遵循依赖规则（如在 Domain 层直接使用 sqlx）→ 架构形同虚设
│   ├── 端口设计不当（过于细粒度或过于粗粒度）→ 反而增加复杂度
│   └── 缺少架构守护（如 ArchUnit 测试）→ 规则被逐渐破坏
└── 根结论: ❌ 架构模式提供结构，但需要纪律和自动化测试来维护
```

> **来源**: [Fowler — Over-Engineering [已失效]]<!-- 原链接: https://martinfowler.com/bliki/OverEngineering.html -->](<https://martinfowler.com/bliki/OverEngineering.html>)

### 9.2 边界极限
>

| **边界** | **现状** | **理论极限** | **工程影响** |
|:---|:---|:---|:---|
| **端口粒度** | 通常 1 聚合 = 1 仓储端口 | 过细导致接口爆炸（> 100 端口）| 需要端口合并策略 |
| **跨层调用深度** | 通常 3-4 层 | 过深导致性能损耗 | 内联关键路径 |
| **Serverless 冷启动** | Rust < 50ms | 理论下限受容器调度限制 | 预热策略/Provisioned Concurrency |
| **架构迁移成本** | 分层 → 六边形: 高 | 完全重写风险 | 渐进式重构（Strangler Fig 模式）|
| **测试金字塔** | 单元:集成:E2E = 70:20:10 | 端口隔离使单元测试占比可提高到 80%+ | 投资回报递减 |

> **来源**: [Fowler — Over-Engineering [已失效]]<!-- 原链接: https://martinfowler.com/bliki/OverEngineering.html --> · [AWS Lambda Limits](https://docs.aws.amazon.com/lambda/latest/dg/gettingstarted-limits.html) · [Martin — Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)

---

## 十、边界测试

### 10.1 边界测试：适配器绕过端口直接依赖核心（编译错误）

```rust,compile_fail
// ❌ 错误：适配器直接依赖领域实现，而非通过端口（trait）
// 这违反了依赖倒置原则，导致核心与技术框架耦合

// infrastructure/postgres_repository.rs
use crate::domain::order::Order;  // ✅ 依赖领域模型（允许）
// use sqlx::PgPool;  // ✅ 基础设施可以依赖外部框架

// ❌ 错误：在领域层直接引入基础设施依赖
// domain/order.rs
use sqlx::FromRow;  // ❌ 编译失败！领域层不应依赖 sqlx

#[derive(FromRow)]  // ❌ 错误！
pub struct Order {
    pub id: uuid::Uuid,
    pub total: f64,
}
```

> **修正**: 在 Rust 中，可以通过 **Cargo workspace 的依赖隔离**强制实现依赖规则：
>
> ```toml
> # domain/Cargo.toml
> [dependencies]
> # 禁止添加 sqlx、tokio、axum 等框架依赖
> uuid = "1"
> chrono = "1"
>
> # infrastructure/Cargo.toml
> [dependencies]
> domain = { path = "../domain" }  # ✅ Infrastructure 依赖 Domain
> sqlx = { version = "0.7", features = ["runtime-tokio", "postgres"] }
> tokio = "1"
> ```
>
> 这样，`domain` crate 无法引入 `sqlx`，编译器会强制阻止违反依赖规则的行为。
>
> **来源**: [Cockburn — Hexagonal](https://alistair.cockburn.us/hexagonal-architecture/) · [Martin — DIP](https://blog.cleancoder.com/uncle-bob/2020/10/18/Solid-Relevance.html)

### 10.2 边界测试：跨层依赖导致循环依赖（编译错误）

```rust,compile_fail
// ❌ 错误：循环依赖 —— Domain 依赖 Application，Application 又依赖 Domain

// domain/mod.rs
pub mod services;
// use crate::application::dto::OrderDto;  // ❌ 编译失败！循环依赖

// application/mod.rs
pub mod dto;
use crate::domain::services::OrderService;  // ✅ Application 依赖 Domain（正确）

// 循环依赖的后果:
// 1. Cargo 编译报错: "cycle detected when computing crate metadata"
// 2. 即使通过 use 语句绕过，逻辑上仍然混乱
// 3. 测试困难：无法独立测试某一层
```

> **修正**: 依赖方向必须是**单向的**（外层 → 内层）。如果 Domain 需要 Application 的数据结构，应该：
>
> 1. 将 DTO 定义在 Domain 层（作为端口的一部分）
> 2. 或者使用**依赖反转**：Domain 定义 trait，Application 实现 trait
>
> ```rust
> // ✅ 正确: Domain 定义接口，Application 提供实现
> // domain/ports.rs
> pub trait OrderNotifier {
>     fn notify_order_created(&self, order_id: Uuid);
> }
>
> // application/services.rs
> use domain::ports::OrderNotifier;
>
> pub struct EmailOrderNotifier;
> impl OrderNotifier for EmailOrderNotifier {
>     fn notify_order_created(&self, order_id: Uuid) {
>         // 发送邮件...
>     }
> }
> ```
>
> **来源**: [Martin — DIP](https://blog.cleancoder.com/uncle-bob/2020/10/18/Solid-Relevance.html) · [Fowler — Dependency Inversion](https://martinfowler.com/articles/dipInTheWild.html)

### 10.3 边界测试：Serverless 超时导致状态不一致（运行时错误）

```rust,ignore
// ❌ 错误：Lambda 函数在数据库操作和消息发布之间超时
use lambda_runtime::{service_fn, LambdaEvent, Error};

async fn risky_handler(event: LambdaEvent<OrderRequest>) -> Result<Value, Error> {
    let dynamodb = aws_sdk_dynamodb::Client::new(&aws_config::load_from_env().await);
    let sqs = aws_sdk_sqs::Client::new(&aws_config::load_from_env().await);

    // 1. 写入 DynamoDB
    dynamodb.put_item()
        .table_name("orders")
        .item("order_id", AttributeValue::S("123".to_string()))
        .send().await?;

    // ⚠️ 危险: 如果 Lambda 在此处超时（> 15min 或内存限制），
    //          则数据库已更新，但 SQS 消息未发送！
    //          下游系统收不到通知，导致数据不一致。

    // 2. 发送 SQS 消息
    sqs.send_message()
        .queue_url("https://sqs...")
        .message_body("order_created")
        .send().await?;

    Ok(json!({ "status": "ok" }))
}
```

> **修正**: Serverless 函数中的**多步操作**需要幂等性和补偿机制：
>
> 1. **幂等性**: 所有操作（DynamoDB Put + SQS Send）都应是幂等的
> 2. **事务性 Outbox**: 使用 DynamoDB 事务将业务数据和事件记录原子写入
> 3. **异步（Async）事件触发**: 使用 DynamoDB Streams 触发 Lambda，而非在函数内直接发消息
>
> ```rust
> / ✅ 正确: 使用 DynamoDB Streams 解耦写入和事件发布
> // DynamoDB Stream → Lambda（事件处理器）→ SQS
> // 这样即使初始 Lambda 超时，DynamoDB Streams 仍能保证事件最终传递
> ```
>
> **来源**: [AWS Lambda — Best Practices](https://docs.aws.amazon.com/lambda/latest/dg/best-practices.html) · [AWS — Lambda Timeouts](https://docs.aws.amazon.com/lambda/latest/dg/configuration-timeout.html) · [DynamoDB Streams](https://docs.aws.amazon.com/amazondynamodb/latest/developerguide/Streams.html)

---

> **补充来源索引**: [来源: [Martin — Clean Architecture Book](https://www.amazon.com/Clean-Architecture-Craftsmans-Software-Structure/dp/0134494164)]
> [来源: [Martin — Clean Architecture Book](https://www.amazon.com/Clean-Architecture-Craftsmans-Software-Structure/dp/0134494164)]
> [来源: [Fowler — Patterns of Enterprise Application Architecture](https://martinfowler.com/eaaCatalog/)]

## 相关概念文件

- [CQRS & Event Sourcing](33_cqrs_event_sourcing.md) — 命令查询分离、事件溯源、Saga
- [微服务架构模式](31_microservice_patterns.md) — 服务发现、熔断、Saga
- [事件驱动架构](32_event_driven_architecture.md) — 发布-订阅、消息队列、Reactive Streams
- [设计模式](02_patterns.md) — GoF 模式、Rust 特有模式（RAII、Typestate）
- [分布式系统](../04_web_and_networking/18_distributed_systems.md) — gRPC、Raft、Actor
- [云原生](../04_web_and_networking/24_cloud_native.md) — Kubernetes、容器化、可观测性
- [公理语义](../../04_formal/03_operational_semantics/20_axiomatic_semantics.md) — Hoare 逻辑、正确性证明

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Standard Library](https://doc.rust-lang.org/std/index.html)
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **过渡**: Architecture Patterns（架构设计模式） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Architecture Patterns（架构设计模式） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Architecture Patterns（架构设计模式） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Architecture Patterns（架构设计模式） 定义 ⟹ 类型安全保证
- **定理**: Architecture Patterns（架构设计模式） 定义 ⟹ 类型安全保证
- **定理**: Architecture Patterns（架构设计模式） 定义 ⟹ 类型安全保证

## 嵌入式测验（Embedded Quiz）

### 测验 1：Rust 中常用的分层架构（Layered Architecture）如何划分？（理解层）

**题目**: Rust 中常用的分层架构（Layered Architecture）如何划分？

<details>
<summary>✅ 答案与解析</summary>

通常分为：表现层（HTTP/gRPC 处理器）、应用层（用例/服务协调）、领域层（核心业务逻辑、实体、值对象）、基础设施层（数据库、外部 API、消息队列）。
</details>

---

### 测验 2：六边形架构（Hexagonal Architecture / Ports and Adapters）在 Rust 中如何体现？（理解层）

**题目**: 六边形架构（Hexagonal Architecture / Ports and Adapters）在 Rust 中如何体现？

<details>
<summary>✅ 答案与解析</summary>

核心业务逻辑通过 trait（端口）定义依赖，具体实现（适配器）在 infrastructure 层。例如 `trait UserRepository` 由 `PostgresUserRepository` 实现，便于测试替换为 mock。
</details>

---

### 测验 3：Rust 的强类型系统对洋葱架构（Onion Architecture）有什么天然支持？（理解层）

**题目**: Rust 的强类型系统（Type System）对洋葱架构（Onion Architecture）有什么天然支持？

<details>
<summary>✅ 答案与解析</summary>

洋葱架构依赖方向指向领域核心。Rust 的模块（Module）系统和可见性（`pub(crate)`、`pub`）可强制分层依赖方向，编译器阻止外层直接绕过内层抽象。
</details>

---

### 测验 4：什么是"依赖倒置原则"（DIP）？Rust 的 trait 如何帮助实现它？（理解层）

**题目**: 什么是"依赖倒置原则"（DIP）？Rust 的 trait 如何帮助实现它？

<details>
<summary>✅ 答案与解析</summary>

高层模块（Module）不应依赖低层模块，两者都应依赖抽象。Rust trait 定义抽象接口，高层通过 `dyn Trait` 或泛型（Generics）参数依赖接口，而非具体实现。
</details>

---

### 测验 5：在 Rust 中，为什么 Repository 模式比直接在 Service 中调用 SQL 更受推荐？（理解层）

**题目**: 在 Rust 中，为什么 Repository 模式比直接在 Service 中调用 SQL 更受推荐？

<details>
<summary>✅ 答案与解析</summary>

Repository 将数据访问逻辑隔离，便于：1) 切换存储后端（Postgres -> Redis）；2) 单元测试 mock；3) 集中处理查询优化和缓存策略。
</details>

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Architecture Patterns（架构设计模式）** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Architecture Patterns（架构设计模式） 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Architecture Patterns（架构设计模式） 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Architecture Patterns（架构设计模式） 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Architecture Patterns（架构设计模式） 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Architecture Patterns（架构设计模式） 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Architecture Patterns（架构设计模式） 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Architecture Patterns（架构设计模式） 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。

## 十一、架构演进与对比（crates 迁移）

### 架构演进路径

#### 单体 → 分布式演进

```text
第一阶段: 单体分层架构
    ↓
    • 适合: MVP、小团队
    • 优点: 简单、易部署
    • 缺点: 扩展性受限

第二阶段: 模块化单体
    ↓
    • 引入: Hexagonal/Clean Architecture
    • 优点: 高内聚、低耦合
    • 缺点: 仍是单一部署单元

第三阶段: 分布式架构
    ↓
    • 微服务 + 事件驱动
    • 优点: 独立部署、水平扩展
    • 缺点: 分布式复杂性

第四阶段: 云原生架构
    ↓
    • Serverless + Service Mesh
    • 优点: 自动伸缩、弹性
    • 缺点: 成本、学习曲线
```

---

#### 架构决策因子

**选择架构的关键因素**:

| 因素           | 单体      | 微服务 | 事件驱动  | CQRS/ES    |
| :--- | :--- | :--- | :--- | :--- || **团队规模**   | 1-10人    | 10+人  | 任意      | 中大型     |
| **业务复杂度** | 低-中     | 高     | 中-高     | 高         |
| **流量规模**   | < 10K QPS | 任意   | > 50K QPS | > 100K QPS |
| **扩展需求**   | 低        | 高     | 高        | 非常高     |
| **开发速度**   | 快        | 慢     | 中        | 慢         |
| **运维成本**   | 低        | 高     | 中-高     | 高         |

---

### 架构模式对比

| 架构模式      | 复杂度     | 可扩展性   | 性能       | 适用场景         |
| :--- | :--- | :--- | :--- | :--- || **分层架构**  | ⭐⭐       | ⭐⭐⭐     | ⭐⭐⭐⭐   | 中小型单体应用   |
| **微服务**    | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐     | 大型分布式系统   |
| **事件驱动**  | ⭐⭐⭐⭐   | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐   | 高并发、异步（Async）场景 |
| **CQRS**      | ⭐⭐⭐⭐   | ⭐⭐⭐⭐   | ⭐⭐⭐⭐⭐ | 读写分离场景     |
| **Hexagonal** | ⭐⭐⭐     | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐   | 高可测试性需求   |

---
