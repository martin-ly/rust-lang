# GoF 23 设计模式在 Rust 中的表达能力边界矩阵

> **研究范围**: GoF (Gang of Four) 设计模式在 Rust 所有权系统下的表达能力分析
> **版本**: 1.0
> **最后更新**: 2026-02-21

---

## 目录

- [GoF 23 设计模式在 Rust 中的表达能力边界矩阵](#gof-23-设计模式在-rust-中的表达能力边界矩阵)
  - [目录](#目录)
  - [1. 执行摘要](#1-执行摘要)
  - [2. 评级标准](#2-评级标准)
  - [3. 创建型模式](#3-创建型模式)
    - [3.1 Singleton（单例模式）](#31-singleton单例模式)
    - [3.2 Factory Method（工厂方法模式）](#32-factory-method工厂方法模式)
    - [3.3 Abstract Factory（抽象工厂模式）](#33-abstract-factory抽象工厂模式)
    - [3.4 Builder（建造者模式）](#34-builder建造者模式)
    - [3.5 Prototype（原型模式）](#35-prototype原型模式)
  - [4. 结构型模式](#4-结构型模式)
    - [4.1 Adapter（适配器模式）](#41-adapter适配器模式)
    - [4.2 Bridge（桥接模式）](#42-bridge桥接模式)
    - [4.3 Composite（组合模式）](#43-composite组合模式)
    - [4.4 Decorator（装饰器模式）](#44-decorator装饰器模式)
    - [4.5 Facade（外观模式）](#45-facade外观模式)
    - [4.6 Flyweight（享元模式）](#46-flyweight享元模式)
    - [4.7 Proxy（代理模式）](#47-proxy代理模式)
  - [5. 行为型模式](#5-行为型模式)
    - [5.1 Observer（观察者模式）](#51-observer观察者模式)
    - [5.2 Strategy（策略模式）](#52-strategy策略模式)
    - [5.3 State（状态模式）](#53-state状态模式)
    - [5.4 Command（命令模式）](#54-command命令模式)
    - [5.5 Iterator（迭代器模式）](#55-iterator迭代器模式)
    - [5.6 Template Method（模板方法模式）](#56-template-method模板方法模式)
    - [5.7 Mediator（中介者模式）](#57-mediator中介者模式)
    - [5.8 Memento（备忘录模式）](#58-memento备忘录模式)
    - [5.9 Chain of Responsibility（责任链模式）](#59-chain-of-responsibility责任链模式)
    - [5.10 Visitor（访问者模式）](#510-visitor访问者模式)
    - [5.11 Interpreter（解释器模式）](#511-interpreter解释器模式)
  - [6. 模式组合兼容性矩阵](#6-模式组合兼容性矩阵)
    - [兼容性说明](#兼容性说明)
  - [7. 所有权系统交互分析](#7-所有权系统交互分析)
    - [7.1 所有权对设计模式的影响](#71-所有权对设计模式的影响)
    - [7.2 常见模式 Rust 化转换](#72-常见模式-rust-化转换)
    - [7.3 生命周期与模式实现](#73-生命周期与模式实现)
  - [7.5 设计模式边界反例索引](#75-设计模式边界反例索引)
  - [8. 相关资源](#8-相关资源)
    - [8.1 内部文档链接](#81-内部文档链接)
    - [8.2 外部资源](#82-外部资源)
    - [8.3 推荐 crate](#83-推荐-crate)
  - [附录：快速参考卡片](#附录快速参考卡片)
    - [Rust 中实现各模式的推荐方式](#rust-中实现各模式的推荐方式)

---

## 1. 执行摘要

| 模式类别 | 完全支持 | 需要变通 | 难以实现 | 总计 |
| :--- | :--- | :--- | :--- | :--- |
| 创建型 | 3 | 2 | 0 | 5 |
| 结构型 | 5 | 2 | 0 | 7 |
| 行为型 | 8 | 3 | 0 | 11 |
| **总计** | **16** | **7** | **0** | **23** |

---

## 2. 评级标准

| 评级 | 含义 | 图标 |
| :--- | :--- | :--- |
| 🟢 **完全支持** | Rust 原生支持该模式，实现简洁直观 | ✅ |
| 🟡 **需要变通** | 需要额外技巧或语言变通，但仍可实现 | ⚠️ |
| 🔴 **难以实现** | 需要大量unsafe代码或与Rust哲学冲突 | ❌ |

---

## 3. 创建型模式

### 3.1 Singleton（单例模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `lazy_static!` / `std::sync::OnceLock` / `const` + `Mutex` |
| **近似实现方式** | `thread_local!` 用于线程本地单例 |
| **不可表达的方面** | 全局可变状态的无锁访问（需同步原语） |
| **限制原因** | 所有权 + 线程安全要求 |
| **推荐实现方式** | `std::sync::OnceLock<T>` 或 `once_cell::sync::Lazy` |
| **代码示例链接** | [singleton.md](01_creational/singleton.md) |

```rust
// 推荐实现
use std::sync::OnceLock;

pub struct Config {
    pub db_url: String,
}

impl Config {
    pub fn global() -> &'static Config {
        static INSTANCE: OnceLock<Config> = OnceLock::new();
        INSTANCE.get_or_init(|| Config {
            db_url: "postgres://localhost".to_string(),
        })
    }
}
```

---

### 3.2 Factory Method（工厂方法模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `Box<dyn Trait>` 返回 / 泛型关联类型 |
| **近似实现方式** | `enum` 作为产品类型 / `From` trait |
| **不可表达的方面** | 动态子类化（无继承） |
| **限制原因** | 无类继承，使用 trait 代替 |
| **推荐实现方式** | Trait + 关联类型 + `Box<dyn Product>` |
| **代码示例链接** | [factory_method.md](01_creational/factory_method.md) |

```rust
pub trait Product {
    fn operation(&self) -> String;
}

pub trait Creator {
    fn factory_method(&self) -> Box<dyn Product>;

    fn some_operation(&self) -> String {
        let product = self.factory_method();
        format!("Creator: {}", product.operation())
    }
}
```

---

### 3.3 Abstract Factory（抽象工厂模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | Trait 组合 + 工厂 trait |
| **近似实现方式** | 泛型工厂结构体 |
| **不可表达的方面** | 运行时动态工厂切换（需额外抽象） |
| **限制原因** | trait 对象需要 `dyn` 显式标注 |
| **推荐实现方式** | 组合 trait + 具体实现类型 |
| **代码示例链接** | [abstract_factory.md](01_creational/abstract_factory.md) |

```rust
pub trait Button {
    fn paint(&self);
}

pub trait Checkbox {
    fn paint(&self);
}

pub trait GUIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}
```

---

### 3.4 Builder（建造者模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | 消耗性 Builder + 链式调用 |
| **近似实现方式** | `#[derive(Builder)]` (derive_builder crate) |
| **不可表达的方面** | 部分字段可选的编译时检查 |
| **限制原因** | 类型系统限制（可用类型状态模式解决） |
| **推荐实现方式** | 消耗性 Builder 模式 |
| **代码示例链接** | [builder.md](01_creational/builder.md) |

```rust
pub struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
}

pub struct HttpRequestBuilder {
    method: Option<String>,
    url: Option<String>,
    headers: Vec<(String, String)>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self { /* ... */ }
    pub fn method(mut self, m: &str) -> Self { /* ... */ self }
    pub fn url(mut self, u: &str) -> Self { /* ... */ self }
    pub fn build(self) -> Result<HttpRequest, String> { /* ... */ }
}
```

---

### 3.5 Prototype（原型模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `Clone` trait 实现 |
| **近似实现方式** | `Rc<RefCell<T>>` 用于共享状态克隆 |
| **不可表达的方面** | 深拷贝 vs 浅拷贝的自动区分 |
| **限制原因** | 所有权系统，需显式 `Clone` |
| **推荐实现方式** | 实现 `Clone` + `#[derive(Clone)]` |
| **代码示例链接** | [prototype.md](01_creational/prototype.md) |

```rust
#[derive(Clone, Debug)]
pub struct Shape {
    pub x: i32,
    pub y: i32,
    pub color: String,
    // Rc 提供共享所有权，克隆时增加引用计数
    pub shared_data: Rc<RefCell<Vec<u8>>>,
}

// 自定义克隆行为
impl Shape {
    pub fn clone_deep(&self) -> Self {
        Self {
            shared_data: Rc::new(RefCell::new(self.shared_data.borrow().clone())),
            ..self.clone()
        }
    }
}
```

---

## 4. 结构型模式

### 4.1 Adapter（适配器模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `From` / `Into` trait / 包装器结构体 |
| **近似实现方式** | `Deref` 自动解引用适配 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | Trait 实现 + 包装器类型 |
| **代码示例链接** | [adapter.md](02_structural/adapter.md) |

```rust
// 目标接口
trait MediaPlayer {
    fn play(&self, filename: &str);
}

// 被适配者
trait AdvancedMediaPlayer {
    fn play_vlc(&self, filename: &str);
    fn play_mp4(&self, filename: &str);
}

// 适配器
struct MediaAdapter<'a> {
    advanced_player: &'a dyn AdvancedMediaPlayer,
}

impl<'a> MediaPlayer for MediaAdapter<'a> {
    fn play(&self, filename: &str) {
        if filename.ends_with(".vlc") {
            self.advanced_player.play_vlc(filename);
        }
    }
}
```

---

### 4.2 Bridge（桥接模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | Trait 组合（实现与抽象分离） |
| **近似实现方式** | 泛型参数化 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | 组合优于继承：抽象持有一个实现 trait |
| **代码示例链接** | [bridge.md](02_structural/bridge.md) |

```rust
// 实现层
pub trait DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64);
}

// 抽象层
pub struct Shape<'a> {
    drawing_api: &'a dyn DrawingAPI,
}

impl<'a> Shape<'a> {
    pub fn new(api: &'a dyn DrawingAPI) -> Self {
        Self { drawing_api: api }
    }

    pub fn draw(&self) {
        self.drawing_api.draw_circle(1.0, 2.0, 3.0);
    }
}
```

---

### 4.3 Composite（组合模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `enum`（代数数据类型）/ `Vec<Box<dyn Component>>` |
| **近似实现方式** | `Rc<dyn Component>` 共享子节点 |
| **不可表达的方面** | 父子双向引用的生命周期安全 |
| **限制原因** | 循环引用导致内存泄漏（需用 `Weak` 打破） |
| **推荐实现方式** | `enum Component { Leaf(...), Composite(Vec<Component>) }` |
| **代码示例链接** | [composite.md](02_structural/composite.md) |

```rust
// Rust 推荐使用 enum 而非 trait 对象
#[derive(Clone)]
pub enum Component {
    Leaf { name: String, price: f64 },
    Composite { name: String, children: Vec<Component> },
}

impl Component {
    pub fn operation(&self) -> f64 {
        match self {
            Component::Leaf { price, .. } => *price,
            Component::Composite { children, .. } => {
                children.iter().map(|c| c.operation()).sum()
            }
        }
    }
}
```

---

### 4.4 Decorator（装饰器模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | 结构体包装 + 实现相同 Trait |
| **近似实现方式** | `Deref` 透明代理 |
| **不可表达的方面** | 运行时动态组合的装饰器链 |
| **限制原因** | 泛型类型爆炸（可用 `dyn` 缓解） |
| **推荐实现方式** | 泛型装饰器或 `Box<dyn Component>` |
| **代码示例链接** | [decorator.md](02_structural/decorator.md) |

```rust
pub trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

// 基础组件
pub struct SimpleCoffee;
impl Coffee for SimpleCoffee { /* ... */ }

// 装饰器
pub struct MilkDecorator<C: Coffee> {
    component: C,
}

impl<C: Coffee> Coffee for MilkDecorator<C> {
    fn cost(&self) -> f64 {
        self.component.cost() + 0.5
    }

    fn description(&self) -> String {
        format!("{}, Milk", self.component.description())
    }
}

// 使用
let coffee = MilkDecorator { component: SimpleCoffee };
```

---

### 4.5 Facade（外观模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | 单一结构体封装子系统 |
| **近似实现方式** | 模块级 `pub use` 重导出 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | Facade 结构体 + 简化 API |
| **代码示例链接** | [facade.md](02_structural/facade.md) |

```rust
// 子系统（复杂）
mod subsystem {
    pub struct CPU;
    pub struct Memory;
    pub struct HardDrive;
    // ... 复杂实现
}

// Facade（简化）
pub struct ComputerFacade {
    cpu: subsystem::CPU,
    memory: subsystem::Memory,
    hard_drive: subsystem::HardDrive,
}

impl ComputerFacade {
    pub fn start(&self) {
        // 封装复杂的启动流程
    }
}
```

---

### 4.6 Flyweight（享元模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `Rc<str>` / `Arc<str>` / `&'static str` 共享不可变数据 |
| **近似实现方式** | 字符串驻留（string-interner crate） |
| **不可表达的方面** | 运行时的享元对象池（生命周期复杂） |
| **限制原因** | 内部可变性需要 `RefCell` / `RwLock` |
| **推荐实现方式** | `Arc<str>` + HashMap 工厂 |
| **代码示例链接** | [flyweight.md](02_structural/flyweight.md) |

```rust
use std::collections::HashMap;
use std::sync::Arc;

pub struct TreeFactory {
    flyweights: HashMap<String, Arc<TreeType>>,
}

impl TreeFactory {
    pub fn get_tree_type(&mut self, name: &str, color: &str) -> Arc<TreeType> {
        let key = format!("{}-{}" , name, color);
        self.flyweights
            .entry(key.clone())
            .or_insert_with(|| Arc::new(TreeType {
                name: name.to_string(),
                color: color.to_string(),
            }))
            .clone()
    }
}

pub struct TreeType {
    name: String,
    color: String,
}
```

---

### 4.7 Proxy（代理模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | 智能指针模式（`Deref` + `Drop`） |
| **近似实现方式** | 自定义代理结构体 |
| **不可表达的方面** | 运行时代理类生成 |
| **限制原因** | 无宏无法自动生成代理 |
| **推荐实现方式** | 结构体包装实现相同 trait |
| **代码示例链接** | [proxy.md](02_structural/proxy.md) |

```rust
pub trait Subject {
    fn request(&self);
}

pub struct RealSubject;
impl Subject for RealSubject {
    fn request(&self) { println!("RealSubject: Handling request."); }
}

// 代理
pub struct Proxy {
    real_subject: Option<Box<RealSubject>>,
}

impl Subject for Proxy {
    fn request(&self) {
        // 访问控制、缓存、延迟加载等
        if let Some(ref rs) = self.real_subject {
            rs.request();
        }
    }
}
```

---

## 5. 行为型模式

### 5.1 Observer（观察者模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `Vec<Box<dyn Observer>>` |
| **近似实现方式** | `tokio::sync::broadcast` / 事件总线 |
| **不可表达的方面** | 双向引用的生命周期安全（Subject ↔ Observer） |
| **限制原因** | 循环引用，需用 `Weak` 或消息传递 |
| **推荐实现方式** | 消息通道（mpsc）或 ID 引用系统 |
| **代码示例链接** | [observer.md](03_behavioral/observer.md) |

```rust
use std::sync::{Arc, Weak};
use std::collections::HashMap;

pub trait Observer {
    fn update(&self, event: &str);
}

pub struct Subject {
    observers: HashMap<u64, Weak<dyn Observer + Send + Sync>>,
    next_id: u64,
}

impl Subject {
    pub fn attach(&mut self, observer: Arc<dyn Observer + Send + Sync>) -> u64 {
        let id = self.next_id;
        self.observers.insert(id, Arc::downgrade(&observer));
        self.next_id += 1;
        id
    }

    pub fn notify(&self, event: &str) {
        for (_, weak) in &self.observers {
            if let Some(observer) = weak.upgrade() {
                observer.update(event);
            }
        }
    }
}
```

---

### 5.2 Strategy（策略模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | Trait 对象或泛型参数 |
| **近似实现方式** | `Fn` trait 闭包策略 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | 泛型参数（零成本抽象） |
| **代码示例链接** | [strategy.md](03_behavioral/strategy.md) |

```rust
pub trait PaymentStrategy {
    fn pay(&self, amount: f64) -> bool;
}

pub struct CreditCard;
impl PaymentStrategy for CreditCard {
    fn pay(&self, amount: f64) -> bool {
        println!("Paying {} using Credit Card", amount);
        true
    }
}

pub struct ShoppingCart<T: PaymentStrategy> {
    strategy: T,
}

impl<T: PaymentStrategy> ShoppingCart<T> {
    pub fn checkout(&self, amount: f64) {
        self.strategy.pay(amount);
    }
}

// 使用
let cart = ShoppingCart { strategy: CreditCard };
cart.checkout(100.0);
```

---

### 5.3 State（状态模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `enum` 状态机 / Trait 状态对象 |
| **近似实现方式** | `typestate` 模式（编译时状态检查） |
| **不可表达的方面** | 状态持有 Context 的反向引用 |
| **限制原因** | 自引用结构体（可用 Pin 或重新设计） |
| **推荐实现方式** | 状态 enum + 转换方法 |
| **代码示例链接** | [state.md](03_behavioral/state.md) |

```rust
// 推荐：使用 enum 而非 trait
pub enum ConnectionState {
    Closed,
    Listening { port: u16 },
    Established { stream: TcpStream },
}

impl ConnectionState {
    pub fn transition(self, event: Event) -> Result<Self, Error> {
        match (self, event) {
            (ConnectionState::Closed, Event::Listen(port)) => {
                Ok(ConnectionState::Listening { port })
            }
            (ConnectionState::Listening { port }, Event::Connect) => {
                // ...
            }
            _ => Err(Error::InvalidTransition),
        }
    }
}
```

---

### 5.4 Command（命令模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | Trait + 结构体封装命令 |
| **近似实现方式** | `Box<dyn Fn()>` 闭包命令 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | Trait + 具体命令结构体 |
| **代码示例链接** | [command.md](03_behavioral/command.md) |

```rust
pub trait Command {
    fn execute(&self);
    fn undo(&self);
}

pub struct LightOnCommand {
    light: Light,
}

impl Command for LightOnCommand {
    fn execute(&self) {
        self.light.on();
    }

    fn undo(&self) {
        self.light.off();
    }
}

pub struct RemoteControl {
    commands: Vec<Box<dyn Command>>,
    history: Vec<Box<dyn Command>>,
}
```

---

### 5.5 Iterator（迭代器模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `Iterator` trait 实现 |
| **近似实现方式** | `IntoIterator` trait |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | 实现 `Iterator` trait |
| **代码示例链接** | [iterator.md](03_behavioral/iterator.md) |

```rust
pub struct BookCollection {
    books: Vec<String>,
}

impl Iterator for BookCollection {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.books.pop()
    }
}

// 或自定义迭代器
pub struct BookIterator<'a> {
    collection: &'a BookCollection,
    index: usize,
}

impl<'a> Iterator for BookIterator<'a> {
    type Item = &'a String;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.collection.books.get(self.index);
        self.index += 1;
        result
    }
}
```

---

### 5.6 Template Method（模板方法模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | Trait 默认方法 + 必须实现的抽象方法 |
| **近似实现方式** | `Fn` 闭包参数 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | Trait 默认方法 |
| **代码示例链接** | [template_method.md](03_behavioral/template_method.md) |

```rust
pub trait DataMiner {
    // 模板方法
    fn mine(&self, path: &str) {
        let file = self.open_file(path);
        let raw_data = self.extract_data(&file);
        let data = self.parse_data(&raw_data);
        self.analyze(&data);
        self.send_report();
        self.close_file(&file);
    }

    // 必须实现
    fn open_file(&self, path: &str) -> File;
    fn extract_data(&self, file: &File) -> String;
    fn parse_data(&self, raw: &str) -> Data;

    // 默认实现
    fn analyze(&self, data: &Data) { /* 默认分析 */ }
    fn send_report(&self) { /* 默认发送 */ }
    fn close_file(&self, file: &File) { /* 默认关闭 */ }
}
```

---

### 5.7 Mediator（中介者模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `Arc<Mutex<dyn Mediator>>` |
| **近似实现方式** | 消息通道（channel） |
| **不可表达的方面** | 组件持有中介者的引用（循环引用） |
| **限制原因** | 循环引用问题 |
| **推荐实现方式** | 消息通道或 ID 引用系统 |
| **代码示例链接** | [mediator.md](03_behavioral/mediator.md) |

```rust
use std::sync::{Arc, Weak};
use std::collections::HashMap;

pub trait Mediator {
    fn notify(&self, sender_id: &str, event: &str);
}

pub trait Component {
    fn set_mediator(&mut self, mediator: Weak<dyn Mediator>);
    fn get_id(&self) -> &str;
}

pub struct ChatMediator {
    components: Mutex<HashMap<String, Weak<dyn Component>>>,
}

impl Mediator for ChatMediator {
    fn notify(&self, sender_id: &str, event: &str) {
        let components = self.components.lock().unwrap();
        for (id, comp) in components.iter() {
            if id != sender_id {
                if let Some(c) = comp.upgrade() {
                    // 转发消息
                }
            }
        }
    }
}
```

---

### 5.8 Memento（备忘录模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | 结构体克隆 + 存储历史 |
| **近似实现方式** | `serde` 序列化快照 |
| **不可表达的方面** | 完全封装状态（需要访问内部） |
| **限制原因** | 隐私规则 |
| **推荐实现方式** | 关联类型 Memento + 保存/恢复方法 |
| **代码示例链接** | [memento.md](03_behavioral/memento.md) |

```rust
pub struct Editor {
    content: String,
    cursor_position: usize,
}

#[derive(Clone)]
pub struct EditorMemento {
    content: String,
    cursor_position: usize,
}

impl Editor {
    pub fn save(&self) -> EditorMemento {
        EditorMemento {
            content: self.content.clone(),
            cursor_position: self.cursor_position,
        }
    }

    pub fn restore(&mut self, memento: &EditorMemento) {
        self.content = memento.content.clone();
        self.cursor_position = memento.cursor_position;
    }
}

pub struct History {
    mementos: Vec<EditorMemento>,
}
```

---

### 5.9 Chain of Responsibility（责任链模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `Vec<Box<dyn Handler>>` 或链表 |
| **近似实现方式** | `Iterator` 链式处理 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | Trait + `Option<Box<dyn Handler>>` 链接 |
| **代码示例链接** | [chain_of_responsibility.md](03_behavioral/chain_of_responsibility.md) |

```rust
pub struct Request {
    pub amount: f64,
}

pub trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>);
    fn handle(&self, request: &Request) -> bool;
}

pub struct BaseHandler {
    next: Option<Box<dyn Handler>>,
}

impl Handler for BaseHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }

    fn handle(&self, request: &Request) -> bool {
        if let Some(ref next) = self.next {
            next.handle(request)
        } else {
            false
        }
    }
}
```

---

### 5.10 Visitor（访问者模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟡 需要变通 |
| **等价实现方式** | `enum` + `match` 模式匹配 |
| **近似实现方式** | `Visitor` trait + `accept` 方法 |
| **不可表达的方面** | 双分发（double dispatch）的编译时安全 |
| **限制原因** | 孤儿规则、trait 实现限制 |
| **推荐实现方式** | `enum` 代数数据类型（更地道） |
| **代码示例链接** | [visitor.md](03_behavioral/visitor.md) |

```rust
// Rust 推荐：使用 enum 而非 trait Visitor
pub enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
}

impl Shape {
    pub fn accept<V: ShapeVisitor>(&self, visitor: &V) -> f64 {
        match self {
            Shape::Circle { radius } => visitor.visit_circle(*radius),
            Shape::Rectangle { width, height } => {
                visitor.visit_rectangle(*width, *height)
            }
        }
    }
}

pub trait ShapeVisitor {
    fn visit_circle(&self, radius: f64) -> f64;
    fn visit_rectangle(&self, width: f64, height: f64) -> f64;
}

// 面积计算访问者
pub struct AreaCalculator;
impl ShapeVisitor for AreaCalculator {
    fn visit_circle(&self, radius: f64) -> f64 {
        std::f64::consts::PI * radius * radius
    }

    fn visit_rectangle(&self, width: f64, height: f64) -> f64 {
        width * height
    }
}
```

---

### 5.11 Interpreter（解释器模式）

| 维度 | 分析 |
| :--- | :--- |
| **Rust表达能力评级** | 🟢 完全支持 |
| **等价实现方式** | `enum` 表示 AST + 递归求值 |
| **近似实现方式** | `Box<dyn Expression>` trait 对象 |
| **不可表达的方面** | 无 |
| **限制原因** | 无 |
| **推荐实现方式** | `enum` 代数数据类型 |
| **代码示例链接** | [interpreter.md](03_behavioral/interpreter.md) |

```rust
pub enum Expression {
    Number(f64),
    Add(Box<Expression>, Box<Expression>),
    Subtract(Box<Expression>, Box<Expression>),
    Multiply(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
}

impl Expression {
    pub fn evaluate(&self) -> f64 {
        match self {
            Expression::Number(n) => *n,
            Expression::Add(left, right) => left.evaluate() + right.evaluate(),
            Expression::Subtract(left, right) => left.evaluate() - right.evaluate(),
            Expression::Multiply(left, right) => left.evaluate() * right.evaluate(),
            Expression::Divide(left, right) => left.evaluate() / right.evaluate(),
        }
    }
}

// 使用
let expr = Expression::Add(
    Box::new(Expression::Number(5.0)),
    Box::new(Expression::Number(3.0)),
);
assert_eq!(expr.evaluate(), 8.0);
```

---

## 6. 模式组合兼容性矩阵

此矩阵显示两种模式同时使用的兼容性评级：

| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Singleton** | - | ✅ | ✅ | ✅ | ✅ | ⚠️ | ✅ | ✅ |
| **Factory** | ✅ | - | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Builder** | ✅ | ✅ | - | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Adapter** | ✅ | ✅ | ✅ | - | ✅ | ✅ | ✅ | ✅ |
| **Bridge** | ✅ | ✅ | ✅ | ✅ | - | ✅ | ✅ | ✅ |
| **Observer** | ⚠️ | ✅ | ✅ | ✅ | ✅ | - | ✅ | ✅ |
| **Strategy** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | - | ✅ |
| **State** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | - |

### 兼容性说明

- **✅ 高兼容**: 模式组合自然，无冲突
- **⚠️ 注意**: 需要小心处理（如 Observer + Singleton 需注意线程安全）
- **❌ 不兼容**: 在当前实现中应避免组合（本矩阵无此情况）

---

## 7. 所有权系统交互分析

### 7.1 所有权对设计模式的影响

| 模式类别 | 所有权影响 | 应对策略 |
| :--- | :--- | :--- |
| **创建型** | 实例创建需明确所有权归属 | 使用智能指针（`Rc`/`Arc`）共享所有权 |
| **结构型** | 组合关系需管理生命周期 | 优先使用 `enum` 而非 trait 对象 |
| **行为型** | 双向引用导致循环引用 | 使用 `Weak` 或消息传递解耦 |

### 7.2 常见模式 Rust 化转换

| 传统 OOP 模式 | Rust 等价物 | 原因 |
| :--- | :--- | :--- |
| 继承 + 多态 | Trait + 泛型 / `dyn` | 无类继承 |
| 抽象类 | Trait 默认方法 | 无抽象类概念 |
| 访问修饰符 | 模块系统（`pub`/`pub(crate)`） | 权限基于模块而非类 |
| 异常处理 | `Result<T, E>` / `Option<T>` | 显式错误处理 |
| 反射 | 宏 / `Any` trait | 编译时类型擦除 |

### 7.3 生命周期与模式实现

```rust
// 模式实现中的生命周期注意事项

// 1. Observer: 使用 Weak 避免循环引用
pub struct Subject<'a> {
    observers: Vec<Weak<dyn Observer + 'a>>,
}

// 2. Strategy: 泛型实现零成本抽象
pub struct Context<S: Strategy> {
    strategy: S,  // 编译时确定，无运行时开销
}

// 3. Flyweight: 'static 生命周期共享
pub struct FlyweightFactory {
    cache: HashMap<String, Arc<str>>,  // Arc<str> 是 'static
}
```

---

## 7.5 设计模式边界反例索引

| 模式 | 边界类型 | 反例说明 | 正确写法 |
| :--- | :--- | :--- | :--- |
| **Singleton** | 全局可变 | `static mut` 违反线程安全 | `OnceLock<T>` 或 `Mutex` |
| **Observer** | 共享可变 | `Rc<RefCell<Vec<Listener>>>` 跨线程不安全 | `Arc<Mutex<Vec<Listener>>>` 或 channel |
| **Strategy** | 生命周期 | `&'a dyn Strategy` 在结构体中难以表达 | `Box<dyn Strategy>` 或泛型 `impl Strategy` |
| **Memento** | 所有权 | 直接存储 `T` 导致移动后原对象失效 | `Clone` 快照或 `Option<T>` 交换 |
| **Chain of Responsibility** | 共享 | `Rc<Handler>` 非 Send | `Arc<dyn Handler + Send + Sync>` |

详见各模式形式化文档（[01_creational](01_creational/README.md)、[02_structural](02_structural/README.md)、[03_behavioral](03_behavioral/README.md)）及 [ANTI_PATTERN_TEMPLATE](../../../02_reference/quick_reference/ANTI_PATTERN_TEMPLATE.md)。

---

## 8. 相关资源

### 8.1 内部文档链接

- [Rust 设计模式实践指南](../../../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md)
- [所有权系统详解](../../../research_notes/formal_methods/ownership_model.md)
- [类型状态模式指南](../06_rust_idioms.md)
- [零成本抽象实践](../../../02_reference/quick_reference/generics_cheatsheet.md)

### 8.2 外部资源

| 资源 | 链接 | 描述 |
| :--- | :--- | :--- |
| Rust Design Patterns | <https://rust-unofficial.github.io/patterns/> | 社区维护的设计模式指南 |
| Refactoring.Guru | <https://refactoring.guru/design-patterns/rust> | 设计模式 Rust 实现 |
| Rust Book | <https://doc.rust-lang.org/book/> | 官方 Rust 教程 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 实例驱动的 Rust 学习 |

### 8.3 推荐 crate

| 模式 | 推荐 crate | 用途 |
| :--- | :--- | :--- |
| Singleton | `once_cell` / `lazy_static` | 延迟初始化 |
| Builder | `derive_builder` | 自动生成 Builder |
| Observer | `tokio::sync::broadcast` | 异步事件广播 |
| State | `machine` / `rustfsm` | 状态机框架 |
| Visitor | `visitor` | 访问者模式宏 |

---

## 附录：快速参考卡片

### Rust 中实现各模式的推荐方式

```rust
// 创建型
Singleton     → OnceLock<T>
Factory       → Trait + dyn/泛型
Builder       → 消耗性构造器
Prototype     → Clone trait

// 结构型
Adapter       → From trait / 包装器
Bridge        → Trait 组合
Composite     → Enum
Decorator     → 泛型包装
Facade        → 简化 API
Flyweight     → Arc<str> + 工厂
Proxy         → Deref / 包装器

// 行为型
Observer      → Channel / Weak 引用
Strategy      → 泛型参数 / Trait
State         → Enum 状态机
Command       → Trait + 结构体
Iterator      → Iterator trait
Template      → Trait 默认方法
Mediator      → Channel / ID 系统
Memento       → 克隆快照
Chain         → Vec<Box<dyn Handler>>
Visitor       → Enum + match
Interpreter   → Enum AST
```

---

*文档生成时间: 2026-02-21*
*作者: Rust Research Team*
*版本: 1.0*
