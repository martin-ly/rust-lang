> **内容分级**: [专家级]

# 六边形架构在 Rust 中的企业级实践（Hexagonal Architecture in Enterprise）

**EN**: Hexagonal Architecture in Rust — Enterprise Perspective
**Summary**: Scale Cockburn's Ports & Adapters from single crates to enterprise systems, aligning bounded contexts, workspace boundaries, and governance.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从企业架构视角扩展六边形架构：如何将多个 bounded context 的六边形通过共享内核、 anticorruption layer 和开放主机服务组合成企业级系统。
> **前置概念**: [Hexagonal / Ports & Adapters](../03_design_patterns/25_hexagonal_ports_and_adapters.md) · [Enterprise Architecture Frameworks](01_enterprise_architecture_frameworks.md) · [Strategic DDD](05_strategic_domain_driven_design_in_rust.md) · [Comparative Layer README](../../05_comparative/README.md) · [P10-3 Hexagonal / Clean Architecture canonical](../../05_comparative/05_idioms_patterns_architecture/04_architecture/01_hexagonal_clean_architecture.md)
> **后置概念**: [Clean Architecture in Rust](06_clean_architecture_in_rust.md) · [Microservices Patterns in Rust](08_microservices_patterns_in_rust.md)

---

> **来源 / Provenance**:
> [Cockburn 2005 — Hexagonal Architecture](https://alistair.cockburn.us/hexagonal-architecture/) ·
> [Evans 2003 — *Domain-Driven Design*](https://www.oreilly.com/library/view/domain-driven-design-tackling/0321125215/) ·
> [Richardson 2018 — *Microservices Patterns*](https://microservices.io/book) ·
> [ISO/IEC/IEEE 42010:2022](https://www.iso.org/standard/74296.html)

---

## 一、权威定义

**Hexagonal Architecture at Enterprise Scale**: 六边形架构不仅适用于单个服务，也可作为企业系统中每个 bounded context 的内部结构。多个六边形通过以下 DDD 战略模式互联：

- **Partnership（合作关系）**: 两个 context 协同演进。
- **Shared Kernel（共享内核）**: 显式共享一小部分模型。
- **Customer-Supplier（客户-供应商）**: 上游优先满足下游需求。
- **Conformist（遵奉者）**: 下游完全采用上游模型。
- **Anticorruption Layer（防腐层）**: 下游用适配器隔离上游模型。
- **Open Host Service（开放主机服务）**: 上游提供显式协议供多方消费。

> **来源**: [Cockburn 2005](https://alistair.cockburn.us/hexagonal-architecture/) · [Evans 2003](https://www.oreilly.com/library/view/domain-driven-design-tackling/0321125215/)

---

## 二、企业级映射矩阵

| DDD 战略模式 | Rust 结构 | 六边形对应 |
|:---|:---|:---|
| Bounded Context | workspace member crate | 单个六边形 |
| Shared Kernel | 独立 `shared-kernel` crate | 多个六边形共享的端口 |
| Anticorruption Layer | `adapter/legacy.rs` | 外部适配器 |
| Open Host Service | `api/` crate + OpenAPI/gRPC schema | 驱动端口暴露 |
| Customer-Supplier | 下游 `trait` 由上游实现 | 端口契约由上游适配 |

---

## 三、Rust 实现

### 3.1 防腐层适配器

```rust,ignore
// crates/order-context/src/ports.rs
pub trait PricingService {
    async fn price(&self, sku: &Sku) -> Result<Money, PricingError>;
}

// crates/order-context/src/adapters/legacy_pricing_acl.rs
pub struct LegacyPricingAcl { client: legacy::Client }

impl PricingService for LegacyPricingAcl {
    async fn price(&self, sku: &Sku) -> Result<Money, PricingError> {
        let dto = self.client.get_price(&sku.0).await?;
        // 将 legacy DTO 转换为本 context 的 Money 值对象
        Ok(Money::new(dto.cents, dto.currency.parse()?))
    }
}
```

### 3.2 开放主机服务

```rust,ignore
// crates/pricing-context/src/api.rs
use axum::{extract::Path, response::Json};

pub async fn get_price(Path(sku): Path<String>) -> Json<PriceDto> {
    // 由 pricing context 的用例层提供数据
    let price = use_cases::price(&sku).await;
    Json(PriceDto::from(price))
}
```

---

## 四、关系

- **Hexagonal Enterprise ↔ Clean Architecture**: 六边形是服务内部结构；Clean Architecture 是更细粒度的层结构；两者可共存。
- **Hexagonal Enterprise ↔ Microservices**: 每个微服务内部使用六边形；服务间通过 Open Host Service / ACL 通信。
- **Hexagonal Enterprise ↔ TOGAF**: 六边形对应应用架构中的组件；DDD 战略模式对应业务架构中的上下文映射。

---

## 五、反例与边界

### 反例：所有 context 共享同一模型

```rust,ignore
// ❌ 错误：把全局 User 结构体到处复用
pub struct User { id: Uuid, name: String }
```

**修正**: 每个 bounded context 应有自己的 `User` 视图；跨 context 仅共享 ID 类型等最小契约。

### 边界：防腐层成本

ACL 增加映射开销。当上下游模型频繁变化且高度一致时，Conformist 或 Shared Kernel 可能更合适。

## ⚠️ 实测反例（rustc 1.99.1 实编译/实跑，2026-10-19）

本页 3.1 端口写法（`async fn` 直接在 trait 里）与六边形的核心卖点「适配器运行时可替换」在 Rust 里**直接冲突**——本机实编译坐实。

**实测 1：按本页 3.1 原样写 async 端口，用例层 `Box<dyn PricingService>` 注入即 E0038**。端口 trait 照抄本页形态（去 axum 依赖、std 化）：

```rust,compile_fail
pub struct Sku(pub String);
pub struct Money(pub u64);
pub struct PricingError;

pub trait PricingService {
    async fn price(&self, sku: &Sku) -> Result<Money, PricingError>;
}

pub struct LegacyPricingAcl;
impl PricingService for LegacyPricingAcl {
    async fn price(&self, _sku: &Sku) -> Result<Money, PricingError> { Ok(Money(100)) }
}

// 六边形卖点：适配器运行时替换（测试替身/灰度切换）
fn run_case(svc: Box<dyn PricingService>) { let _ = svc; }
fn main() { run_case(Box::new(LegacyPricingAcl)); }
```

rustc 1.99.1 逐字诊断（两处 E0038——Box 与每个构造点各报一次）：

```text
error[E0038]: the trait `PricingService` is not dyn compatible
  --> t29_hex.rs:16:22
   |
16 | fn run_case(svc: Box<dyn PricingService>) { let _ = svc; }
   |                      ^^^^^^^^^^^^^^^^^^ `PricingService` is not dyn compatible
   |
note: for a trait to be dyn compatible it needs to allow building a vtable
  --> t29_hex.rs:7:14
   |
 6 | pub trait PricingService {
   |           -------------- this trait is not dyn compatible...
 7 |     async fn price(&self, sku: &Sku) -> Result<Money, PricingError>;
   |              ^^^^^ ...because method `price` is `async`
   = help: consider moving `price` to another trait
   = help: only type `LegacyPricingAcl` implements `PricingService` within this crate; consider using it directly instead.
```

**实测 2：修复形态实编译实跑通过**——端口改为显式返回 `Pin<Box<dyn Future + Send + 'a>>`（`async_trait` 宏的 std 手工等价），注入恢复：

```rust
use std::pin::Pin;
use std::future::Future;
pub struct Sku(pub String);
pub struct Money(pub u64);
pub struct PricingError;
pub trait PricingService {
    fn price<'a>(&'a self, sku: &'a Sku) -> Pin<Box<dyn Future<Output = Result<Money, PricingError>> + Send + 'a>>;
}
pub struct LegacyPricingAcl;
impl PricingService for LegacyPricingAcl {
    fn price<'a>(&'a self, _sku: &'a Sku) -> Pin<Box<dyn Future<Output = Result<Money, PricingError>> + Send + 'a>> {
        Box::pin(async move { Ok(Money(100)) })
    }
}
fn run_case(svc: Box<dyn PricingService>) { let _ = svc; println!("Box<dyn PricingService> 注入成立"); }
fn main() { run_case(Box::new(LegacyPricingAcl)); }
```

```text
Box<dyn PricingService> 注入成立
```

要点：这不是边角案例而是**六边形 + async 的结构性张力**——端口的可替换性依赖 dyn 兼容，而裸 `async fn` 天生 dyn 不兼容。企业 Rust 六边形实现要么上 `async_trait`/`trait-variant`（引入宏依赖，每次调用堆分配装箱），要么端口放弃 async 签名。诊断里的 `= help: only type LegacyPricingAcl implements ... consider using it directly instead` 还会把团队悄悄推向「直接用具体类型」——那正是六边形要消灭的适配器耦合。与 [`concept/03_advanced/01_async/13_async_trait_object_safety.md`](../03_advanced/01_async/13_async_trait_object_safety.md) 的 dyn 兼容章互为实证入口。

---

## 六、决策树

```mermaid
graph TD
    A[多个 bounded context?] -->|是| B[context 间模型是否一致?]
    B -->|是| C[使用 Shared Kernel]
    B -->|否| D[谁控制上游模型?]
    D -->|我方| E[使用 Customer-Supplier]
    D -->|外部| F[使用 Anticorruption Layer]
    C --> G[每个 context 内部用六边形]
    E --> G
    F --> G
```

---

## 七、思维导图

```mermaid
mindmap
  root((Hexagonal Architecture in Enterprise))
    单服务六边形
      Domain
      Ports
      Adapters
    企业互联
      Shared Kernel
      ACL
      Open Host Service
    Rust 映射
      crate = context
      trait = port
      adapter = ACL
    治理
      上下文映射
      契约版本
      发布边界
```

---

## 八、权威来源索引

- Cockburn, A. "Hexagonal Architecture." 2005. [https://alistair.cockburn.us/hexagonal-architecture/](https://alistair.cockburn.us/hexagonal-architecture/)
- Evans, E. *Domain-Driven Design: Tackling Complexity in the Heart of Software*. Addison-Wesley, 2003.
- Richardson, C. *Microservices Patterns: With examples in Java*. Manning, 2018.
- ISO/IEC/IEEE. *ISO/IEC/IEEE 42010:2022*. 2022.

> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-31 ｜ **状态**: ✅ 新建权威页

## P0 官方来源（P0 Official Rust Authority Sources）

- [The Rust Reference: Traits — doc.rust-lang.org](https://doc.rust-lang.org/reference/items/traits.html)
- [Cargo Workspaces — doc.rust-lang.org](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Asynchronous Programming in Rust — rust-lang.github.io](https://rust-lang.github.io/async-book/)

## 国际化权威来源补充（International Authority Sources）

- <https://dl.acm.org/doi/book/10.5555/186897>
- <https://rust-unofficial.github.io/patterns/>

## 国际化权威来源补充（International Authority Sources）

- <https://blog.rust-lang.org/>

## 生态实证与版本实查锚（2026-10-19，crates.io API 实测）

六边形架构示例栈：tokio **1.53.1**（2.16 亿近期下载）· axum **0.8.9**（1.11 亿近期下载）· tracing **0.1.44**（1.80 亿近期下载）· tower **0.5.3**（1.62 亿近期下载）· sqlx **0.9.0**（3,447 万近期下载）——crates.io API 2026-10-19 实查，https://crates.io/crates/{tokio,axum,tracing,tower,sqlx}。
