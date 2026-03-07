# 清洁架构 (Clean Architecture)

> **模式类型**: 架构模式
> **难度**: 🟡 中等
> **应用场景**: 复杂业务系统、微服务

---

## 目录

- [清洁架构 (Clean Architecture)](#清洁架构-clean-architecture)
  - [目录](#目录)
  - [核心概念](#核心概念)
  - [原则](#原则)
    - [1. 依赖规则](#1-依赖规则)
    - [2. 抽象在内，实现在外](#2-抽象在内实现在外)
  - [Rust 实现](#rust-实现)
    - [端口与适配器](#端口与适配器)
    - [DI 配置](#di-配置)
  - [领域驱动设计要素](#领域驱动设计要素)
  - [错误处理](#错误处理)
  - [测试](#测试)
  - [对比](#对比)

## 核心概念

清洁架构（洋葱架构）的核心思想：**依赖关系向内指向领域**。

```
         ┌─────────────────┐
         │   外部框架      │  ← Actix, Axum
         │   UI, DB        │
         ├─────────────────┤
         │   接口适配器    │  ← Controllers, Presenters
         ├─────────────────┤
         │   应用业务规则  │  ← Use Cases
         ├─────────────────┤
         │   领域实体      │  ← Enterprise Business Rules
         └─────────────────┘
```

---

## 原则

### 1. 依赖规则

代码依赖只能向内，不能向外。

### 2. 抽象在内，实现在外

领域定义接口（端口），外层提供实现（适配器）。

---

## Rust 实现

### 端口与适配器

```rust
// 领域层 - 定义端口 (trait)
pub trait OrderRepository {
    fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, Error>;
    fn save(&self, order: &Order) -> Result<(), Error>;
}

// 应用层 - 用例
pub struct CreateOrderUseCase<R: OrderRepository> {
    repo: R,
}

impl<R: OrderRepository> CreateOrderUseCase<R> {
    pub fn execute(&self, cmd: CreateOrderCmd) -> Result<Order, Error> {
        let order = Order::new(cmd.customer_id, cmd.items)?;
        self.repo.save(&order)?;
        Ok(order)
    }
}

// 基础设施层 - 适配器实现
pub struct SqliteOrderRepository {
    pool: SqlitePool,
}

impl OrderRepository for SqliteOrderRepository {
    fn find_by_id(&self, id: OrderId) -> Result<Option<Order>, Error> {
        // SQLite 实现
    }

    fn save(&self, order: &Order) -> Result<(), Error> {
        // SQLite 实现
    }
}
```

### DI 配置

```rust
// main.rs
use actix_web::{web, App, HttpServer};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    let repo = SqliteOrderRepository::new("db.sqlite").await;
    let use_case = web::Data::new(CreateOrderUseCase::new(repo));

    HttpServer::new(move || {
        App::new()
            .app_data(use_case.clone())
            .route("/orders", web::post().to(create_order_handler))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

---

## 领域驱动设计要素

```rust
// 实体 (有身份)
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
}

impl Order {
    pub fn new(customer_id: CustomerId, items: Vec<OrderItem>) -> Result<Self, Error> {
        // 不变量检查
        if items.is_empty() {
            return Err(Error::EmptyOrder);
        }

        Ok(Self {
            id: OrderId::generate(),
            customer_id,
            items,
            status: OrderStatus::Pending,
        })
    }

    pub fn confirm(&mut self) -> Result<(), Error> {
        if self.status != OrderStatus::Pending {
            return Err(Error::InvalidState);
        }
        self.status = OrderStatus::Confirmed;
        Ok(())
    }
}

// 值对象 (无身份，不可变)
#[derive(Clone, Debug, PartialEq)]
pub struct Money {
    amount: Decimal,
    currency: Currency,
}

impl Money {
    pub fn add(&self, other: &Money) -> Result<Money, Error> {
        if self.currency != other.currency {
            return Err(Error::CurrencyMismatch);
        }
        Ok(Money {
            amount: self.amount + other.amount,
            currency: self.currency.clone(),
        })
    }
}

// 领域服务 (跨实体的逻辑)
pub struct PricingService;

impl PricingService {
    pub fn calculate_total(items: &[OrderItem]) -> Money {
        items.iter()
            .map(|item| item.price() * item.quantity())
            .fold(Money::zero(), |a, b| a.add(&b).unwrap())
    }
}
```

---

## 错误处理

```rust
// 领域错误
#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("Invalid order state")]
    InvalidState,
    #[error("Empty order")]
    EmptyOrder,
    #[error("Currency mismatch")]
    CurrencyMismatch,
}

// 应用错误
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Domain error: {0}")]
    Domain(#[from] DomainError),
    #[error("Repository error: {0}")]
    Repository(String),
}

// 适配器转换
impl ResponseError for AppError {
    fn status_code(&self) -> StatusCode {
        match self {
            AppError::Domain(_) => StatusCode::BAD_REQUEST,
            AppError::Repository(_) => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}
```

---

## 测试

```rust
// 领域测试 - 纯内存，无依赖
#[test]
fn test_order_creation() {
    let order = Order::new(
        CustomerId::new(),
        vec![OrderItem::new(ProductId::new(), 2, Money::usd(10.0))]
    );
    assert!(order.is_ok());
}

// 用例测试 - 使用 Mock Repository
struct MockOrderRepository {
    saved: RefCell<Vec<Order>>,
}

impl OrderRepository for MockOrderRepository {
    fn save(&self, order: &Order) -> Result<(), Error> {
        self.saved.borrow_mut().push(order.clone());
        Ok(())
    }

    fn find_by_id(&self, _id: OrderId) -> Result<Option<Order>, Error> {
        Ok(None)
    }
}

#[test]
fn test_create_order_use_case() {
    let repo = MockOrderRepository::default();
    let use_case = CreateOrderUseCase::new(repo);

    let result = use_case.execute(CreateOrderCmd {
        customer_id: CustomerId::new(),
        items: vec![/* ... */],
    });

    assert!(result.is_ok());
}
```

---

## 对比

| 特性 | 分层架构 | 清洁架构 |
|-----|---------|---------|
| 依赖方向 | 向下 | 向内 |
| 领域位置 | 中层 | 核心 |
| 灵活性 | 中 | 高 |
| 复杂度 | 中 | 较高 |
| 测试性 | 好 | 优秀 |

---

*文档版本: 1.0.0*
