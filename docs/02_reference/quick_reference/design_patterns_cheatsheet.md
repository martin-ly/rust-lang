# 设计模式快速参考卡片

> **快速参考** | [完整文档](../../../crates/c09_design_pattern/docs/) | [代码示例](../../../crates/c09_design_pattern/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [设计模式快速参考卡片](#设计模式快速参考卡片)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [单例模式](#单例模式)
    - [工厂模式](#工厂模式)
  - [📋 常用模式 {#-常用模式}](#-常用模式--常用模式)
    - [创建型模式](#创建型模式)
    - [结构型模式](#结构型模式)
    - [行为型模式](#行为型模式)
  - [🦀 Rust 特有模式 {#-rust-特有模式}](#-rust-特有模式--rust-特有模式)
    - [Newtype 模式](#newtype-模式)
    - [RAII 模式](#raii-模式)
    - [类型状态模式](#类型状态模式)
  - [💡 代码示例 {#-代码示例}](#-代码示例--代码示例)
    - [示例 1: 建造者模式（完整实现）](#示例-1-建造者模式完整实现)
    - [示例 2: 策略模式](#示例-2-策略模式)
    - [示例 3: 观察者模式](#示例-3-观察者模式)
    - [示例 4: 装饰器模式](#示例-4-装饰器模式)
    - [示例 5: 适配器模式](#示例-5-适配器模式)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景: Web 服务器配置系统](#场景-web-服务器配置系统)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 3: 单例模式在多线程中的误用](#反例-3-单例模式在多线程中的误用)
    - [反例 4: 模式匹配不完整](#反例-4-模式匹配不完整)
    - [反例 1: 过度使用设计模式](#反例-1-过度使用设计模式)
    - [反例 2: Builder 缺少必填字段校验](#反例-2-builder-缺少必填字段校验)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与决策树](#形式化理论与决策树)
    - [形式化理论与类型系统](#形式化理论与类型系统)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始 {#-快速开始}

### 单例模式

```rust
use std::sync::{Arc, Mutex, OnceLock};

static INSTANCE: OnceLock<Arc<Mutex<Singleton>>> = OnceLock::new();

struct Singleton {
    data: i32,
}

impl Singleton {
    fn get_instance() -> Arc<Mutex<Self>> {
        INSTANCE.get_or_init(|| {
            Arc::new(Mutex::new(Singleton { data: 42 }))
        }).clone()
    }
}
```

### 工厂模式

```rust
trait Product {
    fn operation(&self) -> String;
}

fn create_product(t: ProductType) -> Box<dyn Product> {
    match t {
        ProductType::A => Box::new(ConcreteProductA),
        ProductType::B => Box::new(ConcreteProductB),
    }
}
```

---

## 📋 常用模式 {#-常用模式}

### 创建型模式

| 模式       | Rust 实现                    | 使用场景       |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **工厂**   | `match` + `Box<dyn Trait>`   | 多态对象创建   |
| **建造者** | 链式方法                     | 复杂对象构建   |

### 结构型模式

| 模式       | Rust 实现                   | 使用场景     |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **装饰器** | 包装器结构体                | 功能扩展     |
| **外观**   | 统一接口                    | 简化复杂系统 |

### 行为型模式

| 模式       | Rust 实现                | 使用场景 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **观察者** | `Vec<Arc<dyn Observer>>` | 事件通知 |
| **命令**   | `Box<dyn Command>`       | 操作封装 |

---

## 🦀 Rust 特有模式 {#-rust-特有模式}

### Newtype 模式

```rust
struct UserId(u32);
struct OrderId(u32);

fn process_user(id: UserId) {
    // 类型安全
}
```

### RAII 模式

```rust
struct FileHandle {
    file: std::fs::File,
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        // 自动清理
    }
}
```

### 类型状态模式

```rust
struct Door<State> {
    state: State,
}

struct Open;
struct Closed;

impl Door<Closed> {
    fn open(self) -> Door<Open> {
        Door { state: Open }
    }
}

// 使用示例：编译期状态检查
let door = Door { state: Closed };
let door = door.open();  // ✅ 可以打开
// door.open();          // ❌ 编译错误：Open 状态没有 open 方法
```

---

## 💡 代码示例 {#-代码示例}

### 示例 1: 建造者模式（完整实现）

```rust
#[derive(Debug)]
struct Config {
    host: String,
    port: u16,
    timeout: Duration,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<Duration>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: Some(8080),  // 默认值
            timeout: Some(Duration::from_secs(30)),
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

    fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("host is required")?,
            port: self.port.unwrap(),
            timeout: self.timeout.unwrap(),
        })
    }
}

// 使用
let config = ConfigBuilder::new()
    .host("localhost")
    .port(3000)
    .build()?;
```

### 示例 2: 策略模式

```rust
trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<(), String>;
}

struct CreditCard {
    number: String,
}

impl PaymentStrategy for CreditCard {
    fn pay(&self, amount: f64) -> Result<(), String> {
        println!("Paying {:.2} with credit card {}", amount, self.number);
        Ok(())
    }
}

struct PayPal {
    email: String,
}

impl PaymentStrategy for PayPal {
    fn pay(&self, amount: f64) -> Result<(), String> {
        println!("Paying {:.2} via PayPal account {}", amount, self.email);
        Ok(())
    }
}

struct ShoppingCart {
    strategy: Box<dyn PaymentStrategy>,
}

impl ShoppingCart {
    fn checkout(&self, amount: f64) -> Result<(), String> {
        self.strategy.pay(amount)
    }
}

// 使用
let cart = ShoppingCart {
    strategy: Box::new(CreditCard { number: "1234".to_string() }),
};
cart.checkout(100.0)?;
```

### 示例 3: 观察者模式

```rust
use std::cell::RefCell;
use std::rc::Rc;

trait Observer {
    fn update(&self, event: &str);
}

struct Subject {
    observers: RefCell<Vec<Rc<dyn Observer>>>,
}

impl Subject {
    fn new() -> Self {
        Self { observers: RefCell::new(vec![]) }
    }

    fn attach(&self, observer: Rc<dyn Observer>) {
        self.observers.borrow_mut().push(observer);
    }

    fn notify(&self, event: &str) {
        for observer in self.observers.borrow().iter() {
            observer.update(event);
        }
    }
}

struct EmailNotifier;

impl Observer for EmailNotifier {
    fn update(&self, event: &str) {
        println!("Email: Event '{}' occurred", event);
    }
}

// 使用
let subject = Subject::new();
let notifier = Rc::new(EmailNotifier);
subject.attach(notifier);
subject.notify("UserRegistered");
```

### 示例 4: 装饰器模式

```rust
trait Component {
    fn operation(&self) -> String;
}

struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

struct Decorator<C: Component> {
    component: C,
}

impl<C: Component> Component for Decorator<C> {
    fn operation(&self) -> String {
        format!("Decorator({})", self.component.operation())
    }
}

// 使用
let component = ConcreteComponent;
let decorated = Decorator { component };
assert_eq!(decorated.operation(), "Decorator(ConcreteComponent)");
```

### 示例 5: 适配器模式

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配者
struct Adaptee;

impl Adaptee {
    fn specific_request(&self) -> String {
        "Specific request".to_string()
    }
}

// 适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}

// 使用
let adapter = Adapter { adaptee: Adaptee };
assert_eq!(adapter.request(), "Specific request");
```

---

## 🎯 使用场景 {#-使用场景}

### 场景: Web 服务器配置系统

在实际项目中，设计模式组合使用能解决复杂问题。以下是一个配置系统的完整示例：

```rust
// 使用单例管理全局配置
use std::sync::{Arc, Mutex, OnceLock};

static CONFIG: OnceLock<Arc<Mutex<AppConfig>>> = OnceLock::new();

struct AppConfig {
    db_url: String,
    port: u16,
}

impl AppConfig {
    fn global() -> Arc<Mutex<Self>> {
        CONFIG.get_or_init(|| {
            Arc::new(Mutex::new(Self {
                db_url: "postgres://localhost".to_string(),
                port: 8080,
            }))
        }).clone()
    }
}

// 使用建造者创建数据库连接
struct DbConnectionBuilder {
    url: String,
    timeout: Duration,
}

impl DbConnectionBuilder {
    fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeout: Duration::from_secs(5),
        }
    }

    fn timeout(mut self, secs: u64) -> Self {
        self.timeout = Duration::from_secs(secs);
        self
    }

    fn build(self) -> Result<DbConnection, String> {
        Ok(DbConnection {
            url: self.url,
            timeout: self.timeout,
        })
    }
}

struct DbConnection {
    url: String,
    timeout: Duration,
}
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 3: 单例模式在多线程中的误用

**错误示例**:

```rust
use std::cell::RefCell;

thread_local! {
    static COUNTER: RefCell<i32> = RefCell::new(0);
}

// ❌ 每个线程有自己的计数器，不是真正的全局单例
fn increment() {
    COUNTER.with(|c| *c.borrow_mut() += 1);
}
```

**原因**: `thread_local!` 创建的是线程本地存储，不是全局单例。

**修正**:

```rust
use std::sync::atomic::{AtomicI32, Ordering};

static GLOBAL_COUNTER: AtomicI32 = AtomicI32::new(0);

fn increment() {
    GLOBAL_COUNTER.fetch_add(1, Ordering::SeqCst);
}
```

---

### 反例 4: 模式匹配不完整

**错误示例**:

```rust
trait Shape {
    fn area(&self) -> f64;
}

fn print_area(shape: &dyn Shape) {
    // ❌ 无法知道具体类型，无法进行特定优化
    println!("Area: {}", shape.area());
}
```

**原因**: 过度抽象导致无法针对具体类型优化。

**修正**: 使用枚举代数数据类型（ADT）替代 trait 对象：

```rust
enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
}

impl Shape {
    fn area(&self) -> f64 {
        match self {
            Shape::Circle { radius } => std::f64::consts::PI * radius * radius,
            Shape::Rectangle { width, height } => width * height,
        }
    }
}
```

---

### 反例 1: 过度使用设计模式

**错误示例**:

```rust
// 简单需求却引入 Builder、Factory、Strategy 等
struct Config;
impl Config {
    fn new() -> Self { Self }
    fn with_a(mut self, _: i32) -> Self { self }
}
```

**原因**: 简单场景过度抽象增加复杂度。

**修正**: 按需引入模式，避免为用而用。

---

### 反例 2: Builder 缺少必填字段校验

**错误示例**:

```rust
let c = Config::builder().build();  // ❌ 必填 host 未设置
```

**原因**: 编译期无法保证必填字段。

**修正**: 将必填字段放入 `new()`，或 `build()` 返回 `Result` 校验。

---

## 📚 相关文档 {#-相关文档}

- [设计模式完整文档](../../../crates/c09_design_pattern/docs/)
- [设计模式 README](../../../crates/c09_design_pattern/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例位于 `crates/c09_design_pattern/examples/`，
可直接运行（例如：`cargo run -p c09_design_pattern --example oncelock_singleton_comprehensive`）。

- [单例与 OnceLock](../../../crates/c09_design_pattern/examples/oncelock_singleton_comprehensive.rs)
- [事件总线](../../../crates/c09_design_pattern/examples/event_bus_demo.rs)
- [观察者与 GAT](../../../crates/c09_design_pattern/examples/gats_observer_demo.rs)
- [管道与迭代器](../../../crates/c09_design_pattern/examples/pipeline_iter_demo.rs)
- [异步 trait 演示](../../../crates/c09_design_pattern/examples/async_trait_demo.rs)
- [dyn upcasting 适配器](../../../crates/c09_design_pattern/examples/dyn_upcasting_adapter.rs)

---

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)

### 项目内部文档

- [完整文档](../../../crates/c09_design_pattern/README.md)
- [设计模式使用指南](../../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md)
- [GoF 模式](../../../crates/c09_design_pattern/docs/tier_02_guides/01_创建型模式指南.md)

### 形式化理论与决策树

- [设计模式边界矩阵](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md) — 23 模式 × 三维边界（安全/支持/表达）
- [设计模式表征能力形式化树图](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md#设计模式表征能力形式化树图) — 模式→实现路径→定理（Mermaid/ASCII 树图）
- [表达边界（等价/近似/不可表达）](../../research_notes/software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md)
- [组件成熟度判定树](../../research_notes/software_design_theory/04_compositional_engineering/README.md#构建能力确定性判定树) — L1–L4 成熟度、CE-T1–T3
- [组件构建能力形式化树图](../../research_notes/software_design_theory/04_compositional_engineering/README.md#组件构建能力形式化树图与-43-模式联合) — 模块→crate→进程→网络、与 43 模式联合

### 形式化理论与类型系统

- [设计模式边界矩阵](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md) — 23 模式 × 三维边界（安全/支持/表达）
- [设计模式表征能力形式化树图](../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md#设计模式表征能力形式化树图) — 模式→实现路径→定理
- [创建型模式形式化](../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/) — Singleton、Factory、Builder 等形式化定义
- [结构型模式形式化](../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/) — Adapter、Decorator、Facade 等形式化定义
- [行为型模式形式化](../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/) — Observer、Strategy、Command 等形式化定义
- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 类型理论与设计模式的关系
- [构造能力理论](../../research_notes/type_theory/construction_capability.md) — 类型系统表达能力边界

### 相关速查卡

- [类型系统速查卡](./type_system.md) - Trait 与设计模式
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权模式
- [泛型编程速查卡](./generics_cheatsheet.md) - 泛型与模式
- [智能指针速查卡](./smart_pointers_cheatsheet.md) - 指针模式

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.1+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
