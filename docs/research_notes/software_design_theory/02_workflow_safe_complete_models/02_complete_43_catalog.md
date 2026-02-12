# 43 种完全模型索引

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 目录

- [43 种完全模型索引](#43-种完全模型索引)
  - [定义](#定义)
  - [构成方案](#构成方案)
  - [扩展模式 Rust 代码示例](#扩展模式-rust-代码示例)
  - [扩展模式选型决策树](#扩展模式选型决策树)
  - [与 23 安全的关系](#与-23-安全的关系)
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
| Repository | 见 [02_effectiveness_proofs](../../04_compositional_engineering/02_effectiveness_proofs.md) CE-T1；trait 泛型约束 | 可与 Factory Method、Builder 组合 |
| Service Layer | 模块依赖、trait 组合；见 [03_integration_theory](../../04_compositional_engineering/03_integration_theory.md) IT-T1 | 编排 Repository、Factory |
| DTO | 结构体 + serde；无行为；所有权转移 | 与 Remote Facade、Gateway 组合 |
| Event Sourcing | `Vec<Event>` + `fold`；无共享可变；见 [ownership_model](../../../formal_methods/ownership_model.md) | 与 Command、Memento 概念衔接 |
| Specification | `trait Spec` + `and`/`or`；组合模式；见 [composite](../../01_design_patterns_formal/02_structural/composite.md) | 业务规则组合 |

---

## 权威来源

- [Fowler EAA Catalog](https://martinfowler.com/eaaCatalog/)
- [Core J2EE Patterns](https://corej2eepatterns.com/)
