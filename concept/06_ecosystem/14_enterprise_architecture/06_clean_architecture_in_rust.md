> **内容分级**: [专家级]

# 整洁架构在 Rust 中的实践（Clean Architecture）

**EN**: Clean Architecture in Rust
**Summary**: Apply Robert C. Martin's Clean Architecture dependency rule to Rust workspaces, using traits for boundaries and crate layers for framework isolation.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 将 Robert C. Martin 的 Clean Architecture 与 Rust 的工程结构（workspace、crate、trait、模块可见性）对齐，明确依赖方向与测试策略。
> **前置概念**: [Enterprise Architecture Frameworks](01_enterprise_architecture_frameworks.md) · [Hexagonal / Ports & Adapters](../03_design_patterns/25_hexagonal_ports_and_adapters.md) · [DDD Tactical Patterns](04_domain_driven_design_in_rust.md) · [Comparative Layer README](../../05_comparative/README.md) · [P10-3 Hexagonal / Clean Architecture canonical](../../05_comparative/05_idioms_patterns_architecture/04_architecture/01_hexagonal_clean_architecture.md)
> **后置概念**: [Microservices Patterns in Rust](08_microservices_patterns_in_rust.md) · [Repository and Unit of Work](../03_design_patterns/24_repository_and_unit_of_work.md)

---

> **来源 / Provenance**:
> [Martin 2017 — *Clean Architecture: A Craftsman's Guide to Software Structure and Design*](https://www.oreilly.com/library/view/clean-architecture-a/9780134494272/) ·
> [Martin 2012 — The Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) ·
> [ISO/IEC/IEEE 42010:2022](https://www.iso.org/standard/74296.html) ·
> [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

## 一、权威定义

**Clean Architecture**: 由 Robert C. Martin 提出，核心规则是**依赖关系向内指向用例与实体**。外层（框架、驱动）依赖内层；内层不依赖外层。典型同心圆分层：

1. **Entities（实体）**: 企业级业务规则。
2. **Use Cases（用例）**: 应用特定的业务规则。
3. **Interface Adapters（接口适配器）**: 将用例数据转换为外层可消费的格式。
4. **Frameworks & Drivers（框架与驱动）**: Web 框架、数据库、UI、外部设备等。

> **来源**: [Martin 2012 — The Clean Architecture](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html) · [Martin 2017](https://www.oreilly.com/library/view/clean-architecture-a/9780134494272/)

---

## 二、Rust Workspace 映射

| Clean Architecture 层 | Rust 结构 | 依赖方向 |
|:---|:---|:---|
| Entities | `crates/entities` 或 `domain/` | 不依赖任何其他 crate |
| Use Cases | `crates/use_cases` | 依赖 entities |
| Interface Adapters | `crates/adapters` | 依赖 use_cases + entities |
| Frameworks & Drivers | `crates/api` / `crates/db` / `crates/cli` | 依赖 adapters + use_cases + entities |

```text
frameworks_and_drivers/
├── api/          # axum/actix-web handlers
├── db/           # sqlx/diesel implementations
└── cli/          # clap commands
interface_adapters/
├── controllers/  # 输入适配器
└── presenters/   # 输出适配器
use_cases/
└── order/        # 用例编排
entities/
└── domain/       # 纯业务规则
```

---

## 三、依赖方向实现

### 3.1 内层 trait 作为边界

```rust,ignore
// crates/entities/src/lib.rs
pub struct Order { /* ... */ }

// crates/use_cases/src/ports.rs
pub trait OrderRepository: Send + Sync {
    async fn by_id(&self, id: &OrderId) -> Option<Order>;
}

// crates/use_cases/src/order_use_case.rs
pub struct PlaceOrderUseCase<R: OrderRepository> {
    repo: R,
}
```

### 3.2 外层适配器实现 trait

```rust,ignore
// crates/db/src/postgres.rs
use entities::Order;
use use_cases::ports::OrderRepository;

pub struct PostgresOrderRepository { pool: PgPool }

impl OrderRepository for PostgresOrderRepository {
    async fn by_id(&self, id: &OrderId) -> Option<Order> { /* ... */ }
}
```

---

## 四、关系

- **Clean Architecture ↔ Hexagonal**: 两者都强调内向依赖；Clean Architecture 明确四层同心圆，Hexagonal 强调端口/适配器。
- **Clean Architecture ↔ DDD**: Entities 层对应 DDD 的聚合与值对象；Use Cases 层对应应用服务。
- **Clean Architecture ↔ Onion Architecture**: 两者是同一思想的不同表述；Onion 更强调领域模型在中心。

---

## 五、反例与边界

### 反例：内层依赖外层框架

```rust,ignore
// ❌ 错误：entities crate 依赖 serde 用于序列化
// crates/entities/Cargo.toml
[dependencies]
serde = { version = "1", features = ["derive"] }
```

**修正**: 序列化属于接口适配器或框架层；实体 crate 应保持最小依赖。需要序列化时，在外层定义 DTO 并做映射。

### 边界：过度分层

对于小型项目，四层 workspace 可能过重。可合并 Entities 与 Use Cases 为一个 `domain` crate，但需保持依赖向内。

## ⚠️ 实测反例（rustc 1.99.1 + cargo 1.99 实编译，2026-10-19）

上面「反例」节声称内层依赖外层框架是错误，但它默认了**有人拦截这种错误**。本机实测的结论更冷酷：**Rust 工具链对「依赖方向向内」这条 Clean Architecture 第一法则零强制**——违规要么全绿，要么以无关的错误码偶然暴露。

**实测 1：crate 内伪分层——内层 mod 调外层 mod，rustc 全绿**。同一 crate 里 `mod` 之间没有任何方向语义：

```rust
mod db { pub fn query(id: u32) -> String { format!("row{id}") } }
mod entities {
    // 号称"内层"，同 crate 内直接调用"外层" db —— rustc 对方向零检查
    pub fn load(id: u32) -> String { crate::db::query(id) }
}
fn main() { println!("单crate伪分层: entities→db 逆向依赖编译全绿: {}", entities::load(1)); }
```

实跑输出（0 错误、0 警告）：

```text
单crate伪分层: entities→db 逆向依赖编译全绿: row1
```

用「一个 crate + 若干 mod」模拟 Clean Architecture 分层的团队，架构法则被违反时**没有任何信号**——这是伪分层的机器定义：结构存在、执法缺席。

**实测 2：真 crate 拆分后，`domain → infra` 逆向 workspace 依赖同样全绿**。`cargo new` 两个 crate，domain（内层）在 Cargo.toml 反向声明 `infra = { path = "../infra" }`：

```text
Checking infra v0.1.0 (...\\s2r3w17\\t28ws2\\infra)
    Checking domain v0.1.0 (...\\s2r3w17\\t28ws2\\domain)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.60s
```

cargo 照单全收，rustc 不产生任何「内层不应依赖外层」的诊断——**分层方向在 Rust 里是文档纪律，不是编译纪律**（对比 Java 世界有 ArchUnit/dependency-checker 类工具；Rust 侧需 cargo deny/arch_guard 级别的外部执法）。

**实测 3：唯一接近硬约束的是 crate 边界本身**。内层 crate 若试图 `use` 未声明依赖的外层 crate，失败以 **E0432** 落地——但诊断语义是「unresolved import」，只说明「你没声明这个依赖」，不说明「这个方向违规」：

```text
error[E0432]: unresolved import `use_cases`
 --> t28_inner.rs:2:5
  |
2 | use use_cases::ports;
  |     ^^^^^^^^^ use of unresolved module or unlinked crate `use_cases`
  |
  = help: you might be missing a crate named `use_cases`
```

结论：Clean Architecture 页的「修正」清单默认了拦截存在；实际上**声明依赖即合法**（实测 2 全绿），拦截必须显式引入工具或 review 流程。把 workspace crate 拆分当作「架构自动生效」的 team 会在实测 1/2 的全绿里腐化方向纪律。

---

## 六、决策树

```mermaid
graph TD
    A[项目生命周期 > 1 年?] -->|是| B[是否需要替换框架/DB?]
    B -->|是| C[采用 Clean Architecture]
    C --> D[Entities crate]
    C --> E[Use Cases crate]
    C --> F[Adapters crate]
    C --> G[Framework/Drivers crate]
    B -->|否| H[采用简单分层 + trait 边界]
```

---

## 七、思维导图

```mermaid
mindmap
  root((Clean Architecture in Rust))
    四层同心圆
      Entities
      Use Cases
      Interface Adapters
      Frameworks & Drivers
    Rust 映射
      crate = 层
      trait = 边界
      workspace = 架构容器
    依赖规则
      向内指向实体
      外层依赖内层
    反例
      实体依赖 serde
      用例调用 HTTP 客户端
```

---

## 八、权威来源索引

- Martin, R. C. "The Clean Architecture." *Clean Coder Blog*, 2012. [https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html](https://blog.cleancoder.com/uncle-bob/2012/08/13/the-clean-architecture.html)
- Martin, R. C. *Clean Architecture: A Craftsman's Guide to Software Structure and Design*. Prentice Hall, 2017.
- ISO/IEC/IEEE. *ISO/IEC/IEEE 42010:2022, Software, systems and enterprise — Architecture description*. 2022.
- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-31 ｜ **状态**: ✅ 新建权威页

## P0 官方来源（P0 Official Rust Authority Sources）

- [Cargo Workspaces — doc.rust-lang.org](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [The Rust Reference: Traits — doc.rust-lang.org](https://doc.rust-lang.org/reference/items/traits.html)
- [The Rust Reference: Modules and Visibility — doc.rust-lang.org](https://doc.rust-lang.org/reference/items/modules.html)

## 国际化权威来源补充（International Authority Sources）

- <https://dl.acm.org/doi/book/10.5555/186897>

## 国际化权威来源补充（International Authority Sources）

- <https://blog.rust-lang.org/>

## 生态实证与版本实查锚（2026-10-19，crates.io API 实测）

Clean Architecture 端口/适配器示例栈：tokio **1.53.1**（2.16 亿近期下载）· axum **0.8.9**（1.11 亿近期下载）· tracing **0.1.44**（1.80 亿近期下载）· tower **0.5.3**（1.62 亿近期下载）· sqlx **0.9.0**（3,447 万近期下载）——crates.io API 2026-10-19 实查，https://crates.io/crates/{tokio,axum,tracing,tower,sqlx}（sqlx 即典型出站端口实现）。
