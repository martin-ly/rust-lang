> **EN**: Design Patterns Glossary
> **Summary**: Canonical glossary for Rust design patterns: GoF classifications, Rust idioms, concurrency/async terms, and cross-links to authoritative concept pages.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: L1-L2
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: S×Mem — 设计模式术语索引
> **前置依赖**: [Design Patterns](02_patterns.md) · [Pattern Implementation Comparison](36_pattern_implementation_comparison.md)
> **后置概念**: [Pattern Selection Best Practices](37_pattern_selection_best_practices.md) · [Formal Design Pattern Theory](38_formal_design_pattern_theory.md)
> **定理链**: Terminology Standardization ⟹ Concept Alignment ⟹ Communication Efficiency
>
> **权威来源**: 本页为 `Design Patterns Glossary` 的权威概念页；crate 文档仅保留导航 stub。

# C09 设计模式 - 术语表

> **文档类型**: Tier 1 - 基础层
> **文档定位**: 设计模式核心术语快速参考
> **项目状态**: ✅ 活跃维护
> **相关文档**: [Design Patterns](02_patterns.md) · [Pattern Implementation Comparison](36_pattern_implementation_comparison.md) · [Pattern Selection Best Practices](37_pattern_selection_best_practices.md) · [Architecture Patterns](35_architecture_patterns.md) · [Engineering and Production Patterns](82_engineering_and_production_patterns.md) · [Frontier Research and Innovative Patterns](39_frontier_research_and_innovative_patterns.md) · [Algorithm Engineering Practice](../11_domain_applications/76_algorithm_engineering_practice.md)

**最后更新**: 2026-07-09
**适用版本**: Rust 1.97.0+ (Edition 2024)
**文档类型**: 📚 基础参考

---

## 快速索引

**按字母顺序**: [A](#actor-模式) · [B](#零成本抽象-zero-cost-abstraction) · [C](#c09-设计模式---术语表) · [D](#设计模式-design-pattern) · [F](#gof-gang-of-four) · [G](#gof-gang-of-four) · [N](#设计模式-design-pattern) · [O](#gof-gang-of-four) · [R](#reactor-模式) · [S](#设计模式-design-pattern) · [T](#trait-对象) · V

**按类别跳转**:

- [设计模式基础](#设计模式基础)
- [GoF 23 种模式](#gof-23-种模式)
- [Rust 特有概念](#rust-特有概念)
- [并发与异步（Async）](#并发与异步)

---

## 设计模式基础

本节从设计模式 (Design Pattern) 与  GoF (Gang of Four) 两个层面剖析「设计模式基础」。

### 设计模式 (Design Pattern)

在软件设计中反复出现的问题的通用、可复用解决方案。Rust 中的模式实现强调**编译期保证**与**零成本抽象（Zero-Cost Abstraction）**。

- **创建型**: 对象/值创建机制（5 种）
- **结构型**: 对象组合方式（7 种）
- **行为型**: 对象间通信方式（11 种）

### GoF (Gang of Four)

《设计模式：可复用面向对象软件的基础》的四位作者，书中总结了 23 种经典设计模式。Rust 没有继承，因此通常用 **trait + enum + 泛型（Generics）** 实现等价结构。

---

## GoF 23 种模式

| 分类 | 模式 | Rust 实现关键词 | 权威页 |
|:---|:---|:---|:---|
| **创建型** | Singleton | `OnceLock` / `LazyLock` | [Design Patterns](02_patterns.md) |
| | Factory | `match` + enum / `dyn Trait` | [Design Patterns](02_patterns.md) |
| | Abstract Factory | trait 组合 + 注册表 | [Design Patterns](02_patterns.md) |
| | Builder | Typestate / 消费型链式调用 | [Pattern Implementation Comparison](36_pattern_implementation_comparison.md) |
| | Prototype | `Clone` trait | [Design Patterns](02_patterns.md) |
| **结构型** | Adapter | `From` / `Deref` / wrapper | [Design Patterns](02_patterns.md) |
| | Bridge | trait + 组合替代继承 | [Architecture Patterns](35_architecture_patterns.md) |
| | Composite | enum + 递归结构 | [Design Patterns](02_patterns.md) |
| | Decorator | 泛型（Generics）包装 / `Deref` | [Formal Design Pattern Theory](38_formal_design_pattern_theory.md) |
| | Facade | 模块（Module）级 API 封装 | [System Design Principles](05_system_design_principles.md) |
| | Flyweight | `Arc` + 共享不可变数据 | [Pattern Implementation Comparison](36_pattern_implementation_comparison.md) |
| | Proxy | trait object / 生命周期（Lifetimes）守卫 | [Design Patterns](02_patterns.md) |
| **行为型** | Observer | `Weak<dyn Fn>` / broadcast channel | [Design Patterns](02_patterns.md) |
| | Strategy | 泛型单态化（Monomorphization） / `dyn Trait` | [Pattern Implementation Comparison](36_pattern_implementation_comparison.md) |
| | State | enum + `match` / Typestate | [Design Patterns](02_patterns.md) |
| | Command | trait + `Vec<Box<dyn Command>>` | [Design Patterns](02_patterns.md) |
| | Chain of Responsibility | `Iterator` + `and_then` | [Design Patterns](02_patterns.md) |
| | Iterator | `Iterator` trait / GATs | [Formal Design Pattern Theory](38_formal_design_pattern_theory.md) |
| | Template Method | trait 默认实现 | [Design Patterns](02_patterns.md) |
| | Visitor | trait + enum `accept` | [Design Patterns](02_patterns.md) |
| | Mediator | 消息通道 / Actor | [Microservice Patterns](31_microservice_patterns.md) |
| | Memento | `Clone` + 序列化快照 | [Design Patterns](02_patterns.md) |
| | Interpreter | 递归下降 / enum AST | [Design Patterns](02_patterns.md) |

---

## Rust 特有概念

本节将「Rust 特有概念」分解为若干主题： Trait 对象、Typestate 模式、零成本抽象 (Zero-Cost Abstraction)与OnceLock / LazyLock。

### Trait 对象

运行时（Runtime）多态机制，通过 `dyn Trait` 实现动态分派。相比泛型静态分派有虚函数开销，但支持异构集合。

```rust
pub trait Greeter {
    fn greet(&self) -> &'static str;
}

pub fn greet_all(greeters: &[&dyn Greeter]) {
    for g in greeters {
        println!("{}", g.greet());
    }
}
```

### Typestate 模式

使用类型系统（Type System）在编译时保证状态转换合法，零运行时（Runtime）开销。

```rust
use std::marker::PhantomData;

pub struct Unverified;
pub struct Verified;

pub struct Email<State> {
    address: String,
    _state: PhantomData<State>,
}

impl Email<Unverified> {
    pub fn new(address: &str) -> Self {
        Self { address: address.to_string(), _state: PhantomData }
    }

    pub fn verify(self) -> Result<Email<Verified>, &'static str> {
        if self.address.contains('@') {
            Ok(Email { address: self.address, _state: PhantomData })
        } else {
            Err("invalid email")
        }
    }
}

impl Email<Verified> {
    pub fn send(&self) {
        println!("sending to {}", self.address);
    }
}
```

### 零成本抽象 (Zero-Cost Abstraction)

高级语言特性编译后不产生运行时开销的设计原则；泛型单态化（Monomorphization）、迭代器（Iterator）链、`const` 计算均遵循此原则。详见 [零成本抽象（Zero-Cost Abstraction）](../../01_foundation/00_start/06_zero_cost_abstractions.md)。

### OnceLock / LazyLock

标准库提供的线程安全单次初始化类型，常用来实现 Singleton 模式。

```rust
use std::sync::OnceLock;

pub struct Config {
    pub timeout_ms: u64,
}

static CONFIG: OnceLock<Config> = OnceLock::new();

pub fn config() -> &'static Config {
    CONFIG.get_or_init(|| Config { timeout_ms: 1000 })
}
```

---

## 并发与异步

本节围绕「并发与异步」展开，依次讨论 Actor 模式、Reactor 模式、CSP (Communicating Sequential Proce…与Future / async/await。

### Actor 模式

并发计算模型：每个 Actor 独立处理邮箱消息，无共享状态。Rust 中可用 `tokio::mpsc` 或 `actix` 实现。

### Reactor 模式

事件驱动的并发模型，通过事件循环和多路复用处理 I/O。Tokio 运行时基于此模式。

### CSP (Communicating Sequential Processes)

通过通道通信的并发模型。Rust 提供 `std::sync::mpsc`、`crossbeam` 和 `tokio::sync::mpsc`。

### Future / async/await

`Future` 表示尚未完成的异步（Async）计算；`async/await` 是编译器状态机语法糖。

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait SimpleFuture {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

---

## 术语速查表

| 术语 | 一句话定义 | 在 Rust 中的典型实现 |
|:---|:---|:---|
| **RAII** | 资源获取即初始化，离开作用域自动释放 | `Drop` trait |
| **Newtype** | 用单字段结构体（Struct）区分同底层类型的不同语义 | `struct Meters(u64)` |
| **Deref 多态** | 通过自定义解引用（Reference）让类型表现得像另一种类型 | `Deref` / `DerefMut` |
| **Capability** | 将权限编码进类型，调用时需提供能力证明 | `Capability<P>` + PhantomData |
| **Session Type** | 在类型层面保证协议状态转换合法 | Typestate + PhantomData |
| **Backpressure** | 防止生产者压垮消费者的流量控制 | `tokio::sync::Semaphore` / bounded channel |

## 模式选择决策树

```text
面临设计问题
│
├─ 需要创建复杂对象？
│  ├─ 需要分步验证必填字段 → Builder / Typestate
│  └─ 需要运行时选择具体类型 → Factory / Abstract Factory
│
├─ 需要为类型添加行为或包装？
│  ├─ 不改变接口语义 → Decorator / Adapter
│  └─ 控制访问或延迟加载 → Proxy
│
├─ 需要运行时切换算法？
│  ├─ 性能关键 → 泛型 Strategy
│  └─ 需要异构集合 → dyn Trait Strategy
│
├─ 状态转换容易遗漏？
│  └─ enum + match / Typestate State Machine
│
└─ 需要一对多通知？
   ├─ 同步 → Observer + Weak
   └─ 异步 → broadcast channel / event-listener
```

---

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Design Patterns](https://rust-unofficial.github.io/patterns/))
>
> **权威来源对齐变更日志**: 2026-07-09 将内部链接迁移至 `concept/` 权威页，补全 Rust 代码示例、术语表与决策树

**文档版本**: 2.0
**状态**: ✅ 权威页（canonical）

## 过渡段

> **过渡**: 从术语收集过渡到分类维度，可以理解 glossary 不仅是列表，更是概念地图。
>
> **过渡**: 从分类维度过渡到交叉链接，可以建立“查到术语即可进入权威解释”的导航体验。
>
> **过渡**: 从导航体验过渡到学习路径，可以将术语表转化为模式学习的入口。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 统一术语 ⟹ 减少歧义 | 团队与文档使用一致定义 | 提升沟通效率 |
| 术语链接 ⟹ 加速学习 | 每个术语指向权威概念页 | 读者可快速深入 |
| 分类清晰 ⟹ 快速检索 | 按模式类型与适用场景组织 | 缩短查找时间 |

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Design Patterns: Elements of Reusable Object-Oriented Software (GoF, ACM DL)](https://dl.acm.org/doi/book/10.5555/95489)
