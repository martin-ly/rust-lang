> **内容分级**: [专家级]
>
> **代码状态**: ✅ 含可编译示例
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
# 模式组合代数：统一坐标系与结构化关联
>
> **EN**: Pattern Composition Algebra
> **Summary**: A unified coordinate system for GoF, concurrency, async, workflow, and distributed patterns, formalizing their compositional, conflicting, and substitutive relationships with Rust examples.
> **受众**: [专家]
> **层级**: L6 生态工程 — 模式组合与架构决策
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: F×Eva — 在统一坐标系中评价模式组合的正确性、一致性（Coherence）与可替代性
> **前置概念**: [Design Patterns](./02_patterns.md) · [Pattern Composition Algebra (v1)](./35_pattern_composition_algebra.md) · [Concurrency Patterns](../03_advanced/10_concurrency_patterns.md) · [Async Patterns](../03_advanced/02_async_patterns.md) · [Type System](../01_foundation/04_type_system.md)
> **后置概念**: [Distributed Systems](./18_distributed_systems.md) · [System Design Principles](./05_system_design_principles.md) · [Semantic Bridge Algorithms Patterns](../00_meta/semantic_bridge_algorithms_patterns.md)
> **主要来源**: [GoF — Design Patterns] · [POSA — Pattern-Oriented Software Architecture] · [Workflow Patterns — van der Aalst] · [Category Theory for Programmers, Bartosz Milewski] · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
>
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) · [Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
---

> **Bloom 层级**: 分析 → 评价 → 创造

## 📑 目录

- [模式组合代数：统一坐标系与结构化关联](#模式组合代数统一坐标系与结构化关联)
  - [一、核心命题](#一核心命题)
  - [二、模式统一坐标系](#二模式统一坐标系)
  - [三、模式关系代数](#三模式关系代数)
  - [四、组合案例分析](#四组合案例分析)
    - [4.1 Observer + Factory + Typestate](#41-observer--factory--typestate)
    - [4.2 Singleton vs 依赖注入](#42-singleton-vs-依赖注入)
    - [4.3 Pipeline + Iterator](#43-pipeline--iterator)
  - [五、模式选择决策表](#五模式选择决策表)
  - [六、反命题与边界分析](#六反命题与边界分析)
  - [七、来源与延伸阅读](#七来源与延伸阅读)

---

## 一、核心命题

> **单独掌握 23 个 GoF 模式、十几个并发/异步（Async）模式或工作流模式，并不足以设计出可维护的系统。**
> **真实系统总是以组合形式使用模式：Observer 负责事件通知，Factory 负责对象创建，Typestate 负责编译期状态约束；Circuit Breaker、Retry、Timeout 组合成弹性调用链；Pipeline、Backpressure、Fan-out 组合成流处理系统。**
> **本文件建立一个统一的模式坐标系，把 GoF 设计模式、并发模式、异步（Async）模式、工作流模式、分布式模式放在同一张地图上，显式刻画它们之间的组合（⊗）、冲突（⊘）、替代（⇄）关系，并给出可执行的 Rust 示例与决策表。**

---

## 二、模式统一坐标系

模式可以按照 **问题域（Problem Domain）** 与 **表达机制（Expression Mechanism）** 两个正交维度进行坐标定位。下表将常见模式统一索引，便于在组合时快速判断它们是否属于同一问题域、是否共享同一 Rust 表达机制。

| 坐标维度 | GoF 设计模式 | 并发模式 | 异步模式 | 工作流模式 | 分布式模式 |
|:---|:---|:---|:---|:---|:---|
| **对象创建** | Factory、Builder、Prototype、Singleton | — | — | — | — |
| **对象结构** | Composite、Decorator、Adapter、Facade | Plugin、Resource Pool | — | — | Gateway、Sidecar |
| **行为/交互** | Observer、Strategy、Command、Visitor、State | Producer-Consumer、Fork-Join、Leader-Follower | Future、Promise、Actor、Reactor | Sequence、Parallel Split、Synchronization、Exclusive Choice、Deferred Choice | Saga、Circuit Breaker、Retry、Timeout、Bulkhead |
| **数据流** | Iterator、Chain of Responsibility | Channel、Queue | Stream、Pipeline | — | Event Sourcing、CQRS |
| **状态/资源** | Typestate、Memento | Lock、Semaphore、RCU | — | Cancel、Compensate | Two-Phase Commit、Saga Compensation |
| **错误/弹性** | — | — | — | Cancel + Compensate | Circuit Breaker、Retry、Timeout、Bulkhead、Saga |

**坐标洞察**：位于同一问题域的模式往往可以**组合**（如 Observer + Typestate 共同管理状态变更通知），而使用同一 Rust 表达机制的模式则常常**冲突**或**替代**（如 Singleton 与依赖注入都试图回答"如何获得依赖"，但前者引入全局可变状态，后者通过显式参数解耦）。

---

## 三、模式关系代数

借鉴范畴论中态射复合的思想，模式之间的结构化关系可以抽象为三种基本运算：

```text
模式关系代数:
  ⊗ 组合 (Composition):  A ⊗ B = A 与 B 同时存在，职责正交，数据/控制流可组合
  ⊘ 冲突 (Conflict):     A ⊘ B = A 与 B 在同一职责点竞争，通常需要显式选择其一
  ⇄ 替代 (Substitution): A ⇄ B = A 与 B 解决同类问题，在不同约束下互换
```

### 3.1 组合 (⊗) 的规则

- **数据不相交原则**：若模式 A 与 B 操作的数据集交集为空或只读共享，则 A ⊗ B 安全。
- **层级分离原则**：结构型模式与行为型模式组合时，通常结构型模式负责"是什么"，行为型模式负责"做什么"。
- **生命周期（Lifetimes）兼容原则**：组合中各模式对资源生命周期的假设必须一致（例如 RAII + Observer 需要确保观察者不会引用（Reference）已释放对象）。

### 3.2 冲突 (⊘) 的典型场景

| 冲突对 | 冲突点 | 裁决建议 |
|:---|:---|:---|
| Singleton ⊗ 依赖注入 | 依赖获取方式：全局隐式 vs 显式参数 | 优先依赖注入；Singleton 仅在进程级唯一资源且无状态时使用 |
| Mutex ⊗ Lock-free | 性能与可预测性 | 低竞争用 Lock-free，高竞争或需要可组合性用 Mutex/Arc<Mutex<_>> |
| goto/裸循环 ⊗ 结构化控制流 | 可读性与可维护性 | Rust 无 `goto`，用 `break 'label`、`match`、`?` 替代 |
| 强一致性（Coherence） ⊗ 最终一致性 | 可用性与延迟 | 根据业务语义选择 Saga/Eventual Consistency 或 2PC |

### 3.3 替代 (⇄) 的决策维度

| 问题 | 候选模式 A | 候选模式 B | 替代条件 |
|:---|:---|:---|:---|
| 获取全局配置 | Singleton | 依赖注入 / 环境参数 | 可测试性要求高时替代为 DI |
| 遍历集合 | Iterator | Visitor | 数据结构稳定且操作多变用 Visitor；操作单一用 Iterator |
| 异步结果传递 | Future/Promise | Callback | 需要组合与错误传播时用 Future |
| 失败恢复 | Retry | Circuit Breaker | 瞬时故障用 Retry；级联故障风险高时用 Circuit Breaker |

---

## 四、组合案例分析

以下三组组合覆盖了"行为+创建+状态"、"全局依赖决策"与"数据流组合"三类典型场景。

### 4.1 Observer + Factory + Typestate

#### 问题定义

构建一个**响应式状态机**：对象在不同状态下接受事件通知，状态转换由类型系统（Type System）在编译期保证，而事件订阅者与具体对象创建逻辑解耦。

#### 模式职责划分

| 模式 | 职责 | Rust 表达 |
|:---|:---|:---|
| **Observer** | 事件订阅与通知 | `trait Observer<Event>` + `Vec<Box<dyn Observer<Event>>>` |
| **Factory** | 根据配置创建对象 | `trait Factory<Config, Product>` |
| **Typestate** | 编译期状态约束 | 泛型（Generics）状态标签 + `PhantomData` |

#### Rust 示例

```rust
use std::marker::PhantomData;

// ===== Typestate 标签 =====
struct Disconnected;
struct Connected;

// 连接在不同状态下拥有不同的可用方法
struct Connection<State> {
    id: u64,
    _marker: PhantomData<State>,
}

impl Connection<Disconnected> {
    fn new(id: u64) -> Self {
        Self { id, _marker: PhantomData }
    }

    fn connect(self) -> Connection<Connected> {
        println!("connection {} established", self.id);
        Connection { id: self.id, _marker: PhantomData }
    }
}

impl Connection<Connected> {
    fn send(&self, msg: &str) {
        println!("send over {}: {}", self.id, msg);
    }

    fn disconnect(self) -> Connection<Disconnected> {
        println!("connection {} closed", self.id);
        Connection { id: self.id, _marker: PhantomData }
    }
}

// ===== Observer =====
trait Observer<Event> {
    fn on_event(&self, event: &Event);
}

#[derive(Clone, Debug)]
struct ConnectionEvent {
    conn_id: u64,
    kind: EventKind,
}

#[derive(Clone, Debug)]
enum EventKind { Connected, Disconnected, Message(String) }

struct EventBus<Event> {
    observers: Vec<Box<dyn Observer<Event>>>,
}

impl<Event> EventBus<Event> {
    fn new() -> Self { Self { observers: Vec::new() } }
    fn subscribe(&mut self, observer: Box<dyn Observer<Event>>) {
        self.observers.push(observer);
    }
    fn emit(&self, event: Event) {
        for o in &self.observers { o.on_event(&event); }
    }
}

struct LoggingObserver;
impl Observer<ConnectionEvent> for LoggingObserver {
    fn on_event(&self, e: &ConnectionEvent) {
        println!("[LOG] {:?}", e);
    }
}

// ===== Factory =====
trait Factory<Config, Product> {
    fn create(&self, cfg: Config) -> Product;
}

struct ConnectionFactory;
impl Factory<u64, Connection<Disconnected>> for ConnectionFactory {
    fn create(&self, id: u64) -> Connection<Disconnected> {
        Connection::new(id)
    }
}

fn main() {
    let mut bus: EventBus<ConnectionEvent> = EventBus::new();
    bus.subscribe(Box::new(LoggingObserver));

    let factory = ConnectionFactory;
    let conn = factory.create(42);

    let conn = conn.connect();
    bus.emit(ConnectionEvent { conn_id: 42, kind: EventKind::Connected });
    conn.send("hello");

    // Typestate 保证：断开后的连接不能调用 send
    let conn = conn.disconnect();
    bus.emit(ConnectionEvent { conn_id: 42, kind: EventKind::Disconnected });

    // 编译期阻止：conn.send("forbidden");
    let _ = conn;
}
```

**组合分析**：

- Observer 与 Factory 之间是 **⊗ 组合**：前者关心"事件如何传播"，后者关心"对象如何创建"，二者数据集不相交。
- Typestate 与 Observer 之间是 **⊗ 组合约束**：Observer 只能在 `Connected` 状态下触发 `send`，Typestate 在编译期保证这一点，二者生命周期（Lifetimes）兼容。
- 潜在 **⊘ 冲突**：如果 Observer 持有 `Connection<Connected>` 的引用（Reference），断开连接（消耗 `self`）会产生借用（Borrowing）冲突；解决方式是让 Observer 只接收事件副本，不持有状态对象。

---

### 4.2 Singleton vs 依赖注入

#### 问题定义

如何使组件获得共享的依赖（如配置、连接池、日志器）？

#### Singleton 的 Rust 表达与风险

Rust 没有类级别的静态成员，但可以通过 `lazy_static!` / `OnceLock` 实现进程级单例：

```rust
use std::sync::OnceLock;

struct Config { db_url: String }

fn global_config() -> &'static Config {
    static CONFIG: OnceLock<Config> = OnceLock::new();
    CONFIG.get_or_init(|| Config { db_url: "postgres://localhost".to_string() })
}

fn main() {
    println!("{}", global_config().db_url);
}
```

**Singleton 的问题**：

- 引入全局可变状态，测试时需要重置或模拟，破坏可测试性。
- 隐藏依赖关系：调用者不知道函数内部使用了 `global_config()`。
- 与 Rust 的所有权（Ownership）模型冲突：全局可变通常需要 `Mutex`，增加死锁风险。

#### 依赖注入的 Rust 表达

依赖注入通过**显式参数**或 **Trait 抽象**传递依赖：

```rust
trait ConfigProvider {
    fn db_url(&self) -> &str;
}

struct AppConfig { db_url: String }
impl ConfigProvider for AppConfig {
    fn db_url(&self) -> &str { &self.db_url }
}

struct Repository<'a> { config: &'a dyn ConfigProvider }

impl<'a> Repository<'a> {
    fn new(config: &'a dyn ConfigProvider) -> Self { Self { config } }
    fn connect(&self) {
        println!("connecting to {}", self.config.db_url());
    }
}

fn main() {
    let config = AppConfig { db_url: "postgres://test".to_string() };
    let repo = Repository::new(&config);
    repo.connect();
}
```

**裁决**：

- 在 Rust 中优先使用 **依赖注入**（DI）或 **函数参数传递**；Singleton 仅在**进程级唯一、无状态、初始化代价高**的资源（如 `std::sync::OnceLock` 缓存）中使用。
- 该组合对属于 **⇄ 替代** 关系，决策表见第五节。

---

### 4.3 Pipeline + Iterator

#### 问题定义

如何将数据转换组织为可复用、可延迟求值、可组合的线性处理链？

#### 模式映射

| 模式 | 语义 | Rust 表达 |
|:---|:---|:---|
| **Pipeline** | 数据按阶段顺序处理，阶段之间通过标准接口连接 | `Iterator` 适配器链 |
| **Iterator** | 逐个产生元素，支持延迟求值 | `Iterator` trait + `next()` |

Rust 的 `Iterator` 本身就是 Pipeline 模式在语言级别的实现：`.map().filter().collect()` 是一个数据流管道。

#### Rust 示例

```rust
// 模拟日志处理 Pipeline：解析 → 过滤级别 → 提取用户 → 聚合
#[derive(Debug, Clone)]
struct LogLine { level: String, user: String, msg: String }

fn parse_logs(raw: &str) -> impl Iterator<Item = LogLine> + '_ {
    raw.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let mut parts = l.splitn(3, ' ');
            LogLine {
                level: parts.next().unwrap_or("INFO").to_string(),
                user: parts.next().unwrap_or("anonymous").to_string(),
                msg: parts.next().unwrap_or("").to_string(),
            }
        })
}

fn main() {
    let raw = r#"
ERROR alice disk full
WARN bob high memory
INFO alice login success
ERROR alice network timeout
"#;

    // Pipeline: parse → filter ERROR → map user → collect unique users
    let error_users: std::collections::HashSet<_> = parse_logs(raw)
        .filter(|l| l.level == "ERROR")
        .map(|l| l.user)
        .collect();

    println!("users with errors: {:?}", error_users);
}
```

**组合分析**：

- Pipeline ⊗ Iterator 是 Rust 中最自然的组合：Iterator 提供了**阶段接口**（`next`），Pipeline 提供了**阶段编排**（适配器链）。
- 延迟求值保证：中间集合不会被物化，内存占用低。
- 可替代性：当阶段之间有副作用或需要并发时，可用 `Stream`（异步（Async） Pipeline）替代 `Iterator`。

---

## 五、模式选择决策表

下表给出常见设计问题到推荐模式（或模式组合）的映射，并标注替代/组合/冲突关系。

| 设计问题 | 约束条件 | 推荐方案 | 关系 | 不适用方案 |
|:---|:---|:---|:---:|:---|
| 需要事件通知 + 状态安全 | 状态转换必须在编译期可验证 | **Observer + Typestate** | ⊗ | Singleton + 裸回调 |
| 需要全局访问共享配置 | 配置只读、初始化一次、无需测试替换 | **OnceLock Singleton** | ⇄ | 依赖注入（过度） |
| 需要可测试的共享依赖 | 需要 mock/替换配置 | **依赖注入（DI）** | ⇄ | Singleton |
| 线性数据转换链 | 数据量中等、无复杂副作用 | **Pipeline + Iterator** | ⊗ | 手动 for 循环硬编码 |
| 线性数据转换链 + 并发 | 数据量大、需要背压 | **Pipeline + Stream + Backpressure** | ⊗ | 纯 Iterator |
| 失败恢复 | 瞬时错误为主 | **Retry** | ⇄ | Circuit Breaker（过度） |
| 失败恢复 | 级联故障风险高 | **Circuit Breaker + Timeout** | ⊗ | 无限 Retry |
| 异构结构新增操作 | 数据结构稳定、操作频繁新增 | **Visitor** | ⇄ | match 分散在业务代码 |
| 异构结构新增变体 | 变体频繁新增 | **enum + match** | ⇄ | Visitor（频繁修改 accept） |
| 异步任务组合 | 需要取消、超时、组合 | **Future/Async/Await** | ⇄ | 回调地狱 |

---

## 六、反命题与边界分析

### 6.1 反命题 1："模式组合越多越好"

**错误**。每增加一个模式都会引入概念复杂度与维护成本。当模式数量超过 3 个且没有清晰的分层时，系统的认知负荷会指数上升。应当遵循"最小模式集"原则：先用类型系统（Type System）解决问题，再用模式补充。

### 6.2 反命题 2："Singleton 在 Rust 中已被消除"

**错误**。Rust 通过 `OnceLock` / `lazy_static` 仍然可以实现进程级单例。区别在于：Rust 的所有权（Ownership）模型使可变单例变得困难（需要 `Mutex`），从而迫使开发者显式考虑并发安全（Concurrency Safety）。单例并未消失，只是从"默认方案"变为"需要显式辩护的方案"。

### 6.3 反命题 3："Pipeline + Iterator 总是零成本"

**部分错误**。Iterator 适配器链在单态化（Monomorphization）后通常是零成本，但当链路过长或阶段之间数据局部性较差时，编译器可能无法完全内联，导致函数调用开销。此外，如果管道中有 I/O 或锁，零成本抽象（Zero-Cost Abstraction）只保证 CPU 指令层面，不保证端到端延迟。

### 6.4 边界条件

- **状态空间爆炸**：Typestate 的状态数超过 10 个时，组合与转换表会难以维护；此时应退回到运行时（Runtime）状态机（`enum` + `match`）。
- **观察者生命周期**：Observer 持有被观察者的引用会导致循环引用；应使用 `Weak` 引用或事件总线解耦。
- **DI 的过度使用**：当依赖链路过长时，显式注入的参数列表会膨胀；可结合 `Builder` 或 `Provider` 模式分层。

---

## 七、来源与延伸阅读

- [GoF — Design Patterns: Elements of Reusable Object-Oriented Software](https://en.wikipedia.org/wiki/Design_Patterns)
- [POSA — Pattern-Oriented Software Architecture](https://en.wikipedia.org/wiki/Pattern-Oriented_Software_Architecture)
- [Workflow Patterns — van der Aalst](https://www.workflowpatterns.com/)
- [Category Theory for Programmers — Bartosz Milewski](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)
- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

---

> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-06-27
> **状态**: ✅ P1-6 内容深化完成
