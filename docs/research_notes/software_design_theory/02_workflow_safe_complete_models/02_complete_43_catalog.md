# 43 种完全模型索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [43 种完全模型索引](#43-种完全模型索引)
  - [目录](#目录)
  - [定义](#定义)
  - [构成方案](#构成方案)
    - [扩展模式（20）](#扩展模式20)
    - [扩展模式简要说明](#扩展模式简要说明)
  - [扩展模式 Rust 代码示例](#扩展模式-rust-代码示例)
    - [Domain Model](#domain-model)
    - [Unit of Work](#unit-of-work)
    - [Data Mapper](#data-mapper)
    - [Value Object](#value-object)
    - [Registry (Service Locator)](#registry-service-locator)
    - [Identity Map](#identity-map)
    - [Service Layer](#service-layer)
    - [Repository](#repository)
    - [DTO](#dto)
    - [Event Sourcing](#event-sourcing)
    - [Specification](#specification)
    - [Table Data Gateway (DAO)](#table-data-gateway-dao)
    - [Active Record](#active-record)
    - [Gateway（外部系统集成）](#gateway外部系统集成)
    - [Model View Controller (MVC)](#model-view-controller-mvc)
    - [Front Controller](#front-controller)
    - [Remote Facade](#remote-facade)
    - [Lazy Load](#lazy-load)
    - [Plugin (Dependency Injection)](#plugin-dependency-injection)
    - [Optimistic Offline Lock](#optimistic-offline-lock)
  - [安全边界](#安全边界)
  - [与 23 安全的关系](#与-23-安全的关系)
  - [与 23 安全的分层关系](#与-23-安全的分层关系)
  - [扩展模式选型](#扩展模式选型)
  - [扩展模式选型决策树](#扩展模式选型决策树)
  - [扩展模式形式化对应（深入）](#扩展模式形式化对应深入)
  - [扩展模式典型场景（实质内容）](#扩展模式典型场景实质内容)
  - [权威来源](#权威来源)

---

## 定义

**43 完全模型** = GoF 23 + 扩展模式（企业/分布式/并发等），包含**需 unsafe** 或**需库支持**的实现路径。

---

## 构成方案

| 来源 | 数量 | 模式 |
| :--- | :--- | :--- |
| **GoF 23** | 23 | 创建型 5、结构型 7、行为型 11 |
| **企业/分布式扩展** | 20 | 见下表 |

### 扩展模式（20）

参考 [Fowler EAA](https://martinfowler.com/eaaCatalog/)、Core J2EE 等权威 catalog，20 项构成如下：

| # | 模式 | 来源 | 分类 | Rust 安全边界 |
| :--- | :--- | :--- | :--- | :--- |
| 1 | Domain Model | Fowler EAA | 业务层 | 纯 Safe |
| 2 | Service Layer | Fowler EAA | 业务层 | 纯 Safe |
| 3 | Repository | Fowler EAA | 数据层 | 纯 Safe |
| 4 | Unit of Work | Fowler EAA | 数据层 | 纯 Safe |
| 5 | Data Mapper | Fowler EAA | 数据层 | 纯 Safe |
| 6 | Table Data Gateway (DAO) | Fowler EAA | 数据层 | 纯 Safe |
| 7 | Active Record | Fowler EAA | 数据层 | 纯 Safe |
| 8 | Gateway | Fowler EAA | 集成层 | 纯 Safe / 需 unsafe（FFI） |
| 9 | Model View Controller | Fowler EAA | 表示层 | 纯 Safe |
| 10 | Front Controller | Fowler EAA | 表示层 | 纯 Safe |
| 11 | Data Transfer Object | Fowler EAA | 分布式 | 纯 Safe |
| 12 | Remote Facade | Fowler EAA | 分布式 | 纯 Safe |
| 13 | Value Object | Fowler EAA | 基础 | 纯 Safe |
| 14 | Registry (Service Locator) | Fowler EAA | 基础 | 纯 Safe |
| 15 | Identity Map | Fowler EAA | 数据层 | 纯 Safe |
| 16 | Lazy Load | Fowler EAA | 数据层 | 纯 Safe |
| 17 | Plugin (Dependency Injection) | Fowler EAA | 基础 | 纯 Safe |
| 18 | Optimistic Offline Lock | Fowler EAA | 并发 | 纯 Safe |
| 19 | Specification | DDD | 业务层 | 纯 Safe |
| 20 | Event Sourcing | DDD/CQRS | 业务层 | 纯 Safe |

### 扩展模式简要说明

| 模式 | 核心意图 | Rust 典型实现 |
| :--- | :--- | :--- |
| Domain Model | 业务逻辑封装为领域对象 | `struct` + 方法、无贫血模型 |
| Service Layer | 用例编排、事务边界 | `struct` + `async fn`、事务封装 |
| Repository | 集合式抽象、持久化隔离 | `trait Repository<T>` + `impl` |
| Unit of Work | 批量提交、一致性 | `struct` 持有待提交实体、`commit()` |
| Data Mapper | ORM 映射层 | `From`/`Into`、serde、diesel/sqlx |
| Table Data Gateway | 表级数据访问 | `struct` 封装 SQL、`async fn` |
| Active Record | 对象即行 | `struct` 持 `Connection`、`save()` |
| Gateway | 外部系统集成 | trait + FFI/HTTP 客户端 |
| Model View Controller | 分离模型/视图/控制器 | `struct` 分层、`axum`/`actix` |
| Front Controller | 单一入口、路由分发 | `Router`、`match` 路径 |
| Data Transfer Object | 跨边界数据传输 | `struct` + serde、无行为 |
| Remote Facade | 粗粒度远程接口 | gRPC/HTTP 服务端 |
| Value Object | 不可变值、相等性 | `#[derive(Clone, PartialEq)]` |
| Registry | 服务定位 | `OnceLock<HashMap>` 或 DI |
| Identity Map | 会话内实体去重 | `HashMap<Id, Arc<T>>` |
| Lazy Load | 延迟加载 | `impl Default`、`Option`、`OnceCell` |
| Plugin | 依赖注入、可替换实现 | `trait` + `Box<dyn Trait>` |
| Optimistic Offline Lock | 乐观并发控制 | `version: u64`、CAS |
| Specification | 业务规则组合 | `trait Spec`、`and`/`or` 组合 |
| Event Sourcing | 事件溯源、审计 | `Vec<Event>`、`fold` 重建状态 |

---

## 扩展模式 Rust 代码示例

### Domain Model

```rust
// 领域模型：业务逻辑封装在领域对象内，非贫血
#[derive(Clone)]
pub struct OrderItem { pub id: u64, pub amount: u64 }

#[derive(PartialEq)]
pub enum OrderStatus { Draft, Submitted, Shipped }

pub struct Order {
    id: u64,
    items: Vec<OrderItem>,
    status: OrderStatus,
}

impl Order {
    pub fn add_item(&mut self, item: OrderItem) -> Result<(), String> {
        if self.status != OrderStatus::Draft {
            return Err("Cannot add to non-draft order".into());
        }
        self.items.push(item);
        Ok(())
    }
    pub fn total(&self) -> u64 {
        self.items.iter().map(|i| i.amount).sum()
    }
}
```

### Unit of Work

```rust
// 批量提交、一致性边界
trait Repository<T> {
    fn save(&mut self, entity: T) -> Result<(), String>;
    fn update(&mut self, entity: T) -> Result<(), String>;
}

pub struct UnitOfWork<T> {
    new_entities: Vec<T>,
    dirty_entities: Vec<T>,
}

impl<T> UnitOfWork<T> {
    pub fn new() -> Self { Self { new_entities: vec![], dirty_entities: vec![] } }
    pub fn register_new(&mut self, entity: T) { self.new_entities.push(entity); }
    pub fn register_dirty(&mut self, entity: T) { self.dirty_entities.push(entity); }
    pub fn commit(&mut self, repo: &mut impl Repository<T>) -> Result<(), String> {
        for e in self.new_entities.drain(..) { repo.save(e)?; }
        for e in self.dirty_entities.drain(..) { repo.update(e)?; }
        Ok(())
    }
}
```

### Data Mapper

```rust
// ORM 映射层：领域 ↔ 持久化；From/Into 实现双向转换
struct UserEntity { id: u64, name: String, email: String }

// 假设 DbRow 为数据库行抽象
impl From<(u64, String, String)> for UserEntity {
    fn from((id, name, email): (u64, String, String)) -> Self {
        Self { id, name, email }
    }
}
impl From<UserEntity> for (u64, String, String) {
    fn from(u: UserEntity) -> Self { (u.id, u.name, u.email) }
}
```

### Value Object

```rust
#[derive(Clone, PartialEq, Eq)]
pub enum Currency { USD, EUR }

#[derive(Clone, PartialEq, Eq)]
pub struct Money {
    amount: u64,
    currency: Currency,
}

impl Money {
    pub fn new(amount: u64, currency: Currency) -> Self { Self { amount, currency } }
    pub fn add(&self, other: &Money) -> Result<Money, String> {
        if self.currency != other.currency { return Err("Currency mismatch".into()); }
        Ok(Money::new(self.amount + other.amount, self.currency.clone()))
    }
}
```

### Registry (Service Locator)

```rust
use std::sync::{OnceLock, Mutex};
use std::collections::HashMap;
use std::any::{TypeId, Any};

type ServiceMap = HashMap<TypeId, Box<dyn Any + Send>>;
static REGISTRY: OnceLock<Mutex<ServiceMap>> = OnceLock::new();

fn register<T: Send + 'static>(service: T) {
    REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
        .lock().unwrap()
        .insert(TypeId::of::<T>(), Box::new(service));
}
// get：需按具体需求设计（返回引用或克隆）；实际项目常用 tioc 等 DI crate
```

### Identity Map

```rust
use std::collections::HashMap;
use std::sync::Arc;

pub struct IdentityMap<T> {
    map: HashMap<u64, Arc<T>>,
}

impl<T> IdentityMap<T> {
    pub fn get_or_load(&mut self, id: u64, load: impl FnOnce(u64) -> T) -> Arc<T> {
        self.map.entry(id).or_insert_with(|| Arc::new(load(id))).clone()
    }
}
```

### Service Layer

```rust
pub struct OrderService {
    repo: Box<dyn Repository<Order>>,
}

impl OrderService {
    pub async fn place_order(&self, req: PlaceOrderRequest) -> Result<OrderId, String> {
        // 用例编排：校验、创建实体、持久化、发事件
        let order = Order::from_request(&req)?;
        self.repo.save(order).map(|_| order.id)
    }
}
// 事务边界：由调用方或框架控制；Rust 用 async/await 或 block_on
```

### Repository

```rust
trait Repository<T> {
    fn find(&self, id: u64) -> Option<T>;
    fn save(&mut self, entity: T) -> Result<(), String>;
}

struct UserRepository { /* 内部持 Connection 等 */ }
impl Repository<User> for UserRepository {
    fn find(&self, id: u64) -> Option<User> { /* ... */ }
    fn save(&mut self, entity: User) -> Result<(), String> { /* ... */ }
}
```

### DTO

```rust
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct UserDto {
    pub id: u64,
    pub name: String,
    pub email: String,
}
// 无行为，仅数据传输；跨边界序列化
```

### Event Sourcing

```rust
#[derive(Clone)]
enum Event { Created { id: u64 }, Updated { name: String } }

struct Aggregate { id: u64, name: String }
impl Aggregate {
    fn from_events(events: &[Event]) -> Self {
        events.iter().fold(
            Self { id: 0, name: String::new() },
            |acc, e| match e {
                Event::Created { id } => Self { id: *id, ..acc },
                Event::Updated { name } => Self { name: name.clone(), ..acc },
            },
        )
    }
}
// 事件日志：Vec<Event> 持久化；重现时 fold 重建状态
```

### Specification

```rust
trait Specification<T> {
    fn is_satisfied_by(&self, candidate: &T) -> bool;
}

struct AndSpec<A, B>(A, B);
impl<T, A: Specification<T>, B: Specification<T>> Specification<T> for AndSpec<A, B> {
    fn is_satisfied_by(&self, c: &T) -> bool {
        self.0.is_satisfied_by(c) && self.1.is_satisfied_by(c)
    }
}
// 业务规则组合：and/or/not；trait 组合优于继承
```

### Table Data Gateway (DAO)

```rust
// 表级数据访问：一张表对应一个 Gateway
pub struct UserGateway {
    // 内部持 Connection 等；实际项目用 sqlx/diesel；Connection 为 trait 抽象
}

impl UserGateway {
    pub async fn find_by_id(&self, id: u64) -> Option<User> { /* ... */ }
    pub async fn insert(&self, user: &User) -> Result<(), String> { /* ... */ }
    pub async fn update(&self, user: &User) -> Result<(), String> { /* ... */ }
    pub async fn delete(&self, id: u64) -> Result<(), String> { /* ... */ }
}
// 表级 API；与 Repository 区别：Repository 为领域抽象，Gateway 为表映射
```

### Active Record

```rust
// 对象即行：领域对象持有数据库连接，自身负责持久化
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub version: u64,  // 乐观锁版本
}

trait Connection {
    fn insert(&mut self, u: &User) -> Result<(), String>;
    fn update(&mut self, u: &User) -> Result<(), String>;
    fn query_one(&self, id: u64) -> Option<User>;
}
impl User {
    pub fn save(&mut self, conn: &mut impl Connection) -> Result<(), String> {
        if self.id == 0 {
            conn.insert(self)?;
        } else {
            conn.update(self)?;
        }
        Ok(())
    }
    pub fn load(conn: &impl Connection, id: u64) -> Option<Self> {
        conn.query_one(id)
    }
}
// 与 DTO 区别：Active Record 有行为；适合简单 CRUD 领域
```

### Gateway（外部系统集成）

```rust
// 外部系统集成：封装 HTTP 客户端、FFI 等
pub trait PaymentGateway: Send + Sync {
    fn charge(&self, amount: u64, token: &str) -> Result<ChargeId, String>;
}

pub struct StripeGateway { /* 持有 HTTP 客户端 */ }
impl PaymentGateway for StripeGateway {
    fn charge(&self, amount: u64, token: &str) -> Result<ChargeId, String> {
        // HTTP 调用 Stripe API
    }
}
// FFI 场景：若需 C 库绑定，内部可能 unsafe；对外仍为 Safe trait
```

### Model View Controller (MVC)

```rust
// 分离模型/视图/控制器；模块分层
mod model {
    pub struct Order { pub id: u64, pub amount: u64 }
}
mod view {
    pub fn render(order: &model::Order) -> String {
        format!("Order #{}: ${}", order.id, order.amount)
    }
}
mod controller {
    use super::model;
    use super::view;
    pub fn handle_request() -> String {
        let order = model::Order { id: 1, amount: 100 };
        view::render(&order)
    }
}
// axum/actix 中：Router 为 Front Controller；Controller 为 handler
```

### Front Controller

```rust
// 单一入口、路由分发
pub struct Router {
    routes: Vec<(String, Box<dyn Fn(&str) -> String>)>,
}

impl Router {
    pub fn route(&self, path: &str) -> String {
        for (prefix, handler) in &self.routes {
            if path.starts_with(prefix) {
                return handler(path);
            }
        }
        "404".to_string()
    }
}
// 与 axum::Router::route().get(...) 对应；match 路径分发
```

### Remote Facade

```rust
// 粗粒度远程接口：减少跨边界调用次数
#[derive(serde::Serialize, serde::Deserialize)]
pub struct OrderBatchRequest {
    pub order_ids: Vec<u64>,
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct OrderBatchResponse {
    pub orders: Vec<OrderDto>,
}

pub async fn handle_order_batch(req: OrderBatchRequest) -> OrderBatchResponse {
    // 一次批量查询替代 N 次远程调用
    let orders = load_orders_batch(&req.order_ids).await;
    OrderBatchResponse { orders: orders.into_iter().map(Into::into).collect() }
}
// gRPC/HTTP 服务端；粗粒度接口减少延迟
```

### Lazy Load

```rust
use std::sync::OnceLock;

// 延迟加载：首次访问时加载
pub struct LazyResource {
    loaded: OnceLock<String>,
}

impl LazyResource {
    pub fn get(&self) -> &String {
        self.loaded.get_or_init(|| expensive_load())
    }
}

fn expensive_load() -> String { "data".to_string() }

// 或 Option + 闭包：load_on_first_access
pub struct Lazy<T> {
    value: Option<T>,
}
impl<T> Lazy<T> {
    pub fn get_or_init<F: FnOnce() -> T>(&mut self, f: F) -> &T {
        if self.value.is_none() { self.value = Some(f()); }
        self.value.as_ref().unwrap()
    }
}
```

### Plugin (Dependency Injection)

```rust
// 依赖注入、可替换实现
pub trait Storage: Send + Sync {
    fn get(&self, key: &str) -> Option<String>;
    fn set(&mut self, key: &str, value: String);
}

pub struct App {
    storage: Box<dyn Storage>,
}

impl App {
    pub fn new(storage: Box<dyn Storage>) -> Self { Self { storage } }
    pub fn run(&mut self) {
        self.storage.set("key", "value".into());
    }
}
// 测试时注入 MockStorage；生产注入 SqlStorage
```

### Optimistic Offline Lock

```rust
// 乐观并发控制：版本号 + CAS
pub struct Entity {
    pub id: u64,
    pub data: String,
    pub version: u64,
}

pub fn update_optimistic(
    repo: &mut impl Repository<Entity>,
    entity: Entity,
) -> Result<(), String> {
    let current = repo.find(entity.id)?;
    if current.version != entity.version {
        return Err("Conflict: entity was modified".into());
    }
    repo.update(Entity { version: entity.version + 1, ..entity })?;
    Ok(())
}
// 或 AtomicU64 compare_exchange；见 [ownership_model](../../formal_methods/ownership_model.md) Def ATOMIC1
```

---

## 安全边界

| 子集 | 安全边界 |
| :--- | :--- |
| GoF 23 | 绝大部分纯 Safe；Singleton 部分实现可需 unsafe |
| 扩展 20 | 绝大部分纯 Safe；Gateway 在 FFI 场景需 unsafe |

---

## 与 23 安全的关系

- 23 安全 ⊆ 43 完全
- 43 完全 = 23 安全 + 扩展 20（Fowler EAA/DDD 权威来源）

---

## 与 23 安全的分层关系

```text
43 完全
├── 23 安全（GoF 纯 Safe 子集）
│   └── 创建型 5、结构型 7、行为型 11
└── 扩展 20（企业/分布式）
    ├── 业务层：Domain Model, Service Layer, Specification, Event Sourcing
    ├── 数据层：Repository, Unit of Work, Data Mapper, Table Data Gateway,
    │          Active Record, Identity Map, Lazy Load
    ├── 表示层：MVC, Front Controller
    ├── 集成层：Gateway
    ├── 分布式：DTO, Remote Facade
    └── 基础：Value Object, Registry, Plugin, Optimistic Offline Lock
```

---

## 扩展模式选型

| 需求 | 推荐模式 |
| :--- | :--- |
| 领域逻辑封装 | Domain Model |
| 用例编排、事务 | Service Layer |
| 持久化抽象 | Repository、Unit of Work |
| 跨边界数据传输 | DTO |
| 外部系统集成 | Gateway |
| 业务规则组合 | Specification |
| 审计、溯源 | Event Sourcing |

---

## 扩展模式选型决策树

```text
企业/分布式需求？
├── 业务层
│   ├── 领域逻辑封装？ → Domain Model
│   ├── 用例编排、事务边界？ → Service Layer
│   ├── 业务规则组合？ → Specification
│   └── 审计、溯源？ → Event Sourcing
├── 数据层
│   ├── 持久化抽象？ → Repository
│   ├── 批量提交一致性？ → Unit of Work
│   ├── ORM 映射？ → Data Mapper
│   ├── 表级访问？ → Table Data Gateway
│   ├── 对象即行？ → Active Record
│   ├── 会话内去重？ → Identity Map
│   └── 延迟加载？ → Lazy Load
├── 表示层
│   ├── 分离模型/视图/控制器？ → MVC
│   └── 单一入口路由？ → Front Controller
├── 集成/分布式
│   ├── 跨边界数据传输？ → DTO
│   ├── 粗粒度远程接口？ → Remote Facade
│   └── 外部系统集成？ → Gateway
└── 基础
    ├── 不可变值、相等性？ → Value Object
    ├── 服务定位？ → Registry
    ├── 依赖注入、可替换？ → Plugin
    └── 乐观并发控制？ → Optimistic Offline Lock
```

---

## 扩展模式形式化对应（深入）

| 模式 | 形式化对应 | 与 23 安全组合 |
| :--- | :--- | :--- |
| Domain Model | 结构体 + 方法；无贫血；见 [ownership_model](../../formal_methods/ownership_model.md) 规则 1–3 | 与 State、Strategy 组合 |
| Service Layer | 模块依赖、trait 组合；见 [03_integration_theory](../../04_compositional_engineering/03_integration_theory.md) IT-T1 | 编排 Repository、Factory |
| Repository | 见 [02_effectiveness_proofs](../../04_compositional_engineering/02_effectiveness_proofs.md) CE-T1；trait 泛型约束 | 可与 Factory Method、Builder 组合 |
| Unit of Work | 批量提交；所有权收集；见 ownership 规则 3 drop 顺序 | 与 Repository、Data Mapper 组合 |
| Data Mapper | `From`/`Into` 转换；所有权转移；见 [ownership_model](../../formal_methods/ownership_model.md) | 与 Repository 组合 |
| Table Data Gateway | 表级 API；`async fn`；见 [async_state_machine](../../formal_methods/async_state_machine.md) | 与 Repository 二选一 |
| Active Record | 对象持 Connection；`save`/`load`；见 ownership 规则 2 | 简单 CRUD；与 DTO 区别：有行为 |
| Gateway | trait + FFI/HTTP；见 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) Def EXTERN1 | 外部集成；FFI 时可能 unsafe |
| MVC | 模块分层；见 [05_boundary_system](../../05_boundary_system/README.md) | 与 Front Controller 组合 |
| Front Controller | `Router`、`match` 路径；见 [03_semantic_boundary_map](03_semantic_boundary_map.md) | 与 MVC 组合 |
| DTO | 结构体 + serde；无行为；所有权转移 | 与 Remote Facade、Gateway 组合 |
| Remote Facade | 粗粒度接口；batch 减少 RPC；见 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) CHAN1 | 与 DTO 组合 |
| Value Object | `Clone`、`PartialEq`；不可变；见 [06_rust_idioms](../../06_rust_idioms.md) Def NW1 | 与 Newtype、DTO 衔接 |
| Registry | `OnceLock<HashMap>`；见 [singleton](../../01_design_patterns_formal/01_creational/singleton.md) | 服务定位；与 Plugin 二选一 |
| Identity Map | `HashMap<Id, Arc<T>>`；见 [ownership_model](../../formal_methods/ownership_model.md) Def ARC1 | 会话内去重 |
| Lazy Load | `OnceLock`、`Option`；见 [proxy](../../01_design_patterns_formal/02_structural/proxy.md) | 延迟加载 |
| Plugin | `trait` + `Box<dyn Trait>`；依赖注入；见 [strategy](../../01_design_patterns_formal/03_behavioral/strategy.md) | 可替换实现 |
| Optimistic Offline Lock | `version: u64`、CAS；见 [ownership_model](../../formal_methods/ownership_model.md) Def ATOMIC1 | 乐观并发 |
| Specification | `trait Spec` + `and`/`or`；组合模式；见 [composite](../../01_design_patterns_formal/02_structural/composite.md) | 业务规则组合 |
| Event Sourcing | `Vec<Event>` + `fold`；无共享可变；见 [ownership_model](../../formal_methods/ownership_model.md) | 与 Command、Memento 概念衔接 |

---

## 扩展模式典型场景（实质内容）

| 模式 | 典型场景 | 实际项目示例 |
| :--- | :--- | :--- |
| Domain Model | 订单、商品、支付；业务规则封装 | 电商订单状态机、库存扣减校验 |
| Service Layer | 用例编排、事务边界 | `place_order`：校验→创建→持久化→发事件 |
| Repository | 持久化抽象、测试可 Mock | `UserRepository`、`OrderRepository` |
| Unit of Work | 批量提交、一致性 | 多实体修改后一次性 `commit` |
| DTO | API 请求/响应、跨服务边界 | REST `UserDto`、gRPC `OrderMessage` |
| Gateway | 支付、短信、邮件 | `StripeGateway`、`SendGridGateway` |
| Event Sourcing | 审计、溯源、CQRS | 订单历史、审计日志、事件重放 |
| Specification | 业务规则组合、查询构建 | `OrderSpec::pending().and(OrderSpec::over(100))` |
| MVC | Web 应用分层 | `axum`/`actix` Router + Handler + 模板 |
| Lazy Load | 关联数据按需加载 | ORM 关联、大对象延迟 |

---

## 权威来源

- [Fowler EAA Catalog](https://martinfowler.com/eaaCatalog/)
- [Core J2EE Patterns](https://corej2eepatterns.com/)
