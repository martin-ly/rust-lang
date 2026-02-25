# 设计模式使用指南

**模块**: C09 Design Patterns
**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.93.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [设计模式使用指南](#设计模式使用指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [📋 概述 {#-概述}](#-概述--概述)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [单例模式](#单例模式)
    - [工厂模式](#工厂模式)
  - [📊 核心模式 {#-核心模式}](#-核心模式--核心模式)
    - [1. 创建型模式](#1-创建型模式)
      - [建造者模式](#建造者模式)
    - [2. 结构型模式](#2-结构型模式)
      - [适配器模式](#适配器模式)
      - [装饰器模式](#装饰器模式)
    - [3. 行为型模式](#3-行为型模式)
      - [策略模式](#策略模式)
      - [观察者模式](#观察者模式)
  - [📐 23种设计模式完整实现 {#-23种设计模式完整实现}](#-23种设计模式完整实现--23种设计模式完整实现)
    - [创建型模式 (Creational Patterns)](#创建型模式-creational-patterns)
      - [1. 单例模式 (Singleton)](#1-单例模式-singleton)
      - [2. 工厂方法 (Factory Method)](#2-工厂方法-factory-method)
      - [3. 抽象工厂 (Abstract Factory)](#3-抽象工厂-abstract-factory)
      - [4. 建造者模式 (Builder)](#4-建造者模式-builder)
      - [5. 原型模式 (Prototype)](#5-原型模式-prototype)
    - [结构型模式 (Structural Patterns)](#结构型模式-structural-patterns)
      - [6. 适配器模式 (Adapter)](#6-适配器模式-adapter)
      - [7. 桥接模式 (Bridge)](#7-桥接模式-bridge)
      - [8. 组合模式 (Composite)](#8-组合模式-composite)
      - [9. 装饰器模式 (Decorator)](#9-装饰器模式-decorator)
      - [10. 外观模式 (Facade)](#10-外观模式-facade)
      - [11. 享元模式 (Flyweight)](#11-享元模式-flyweight)
      - [12. 代理模式 (Proxy)](#12-代理模式-proxy)
    - [行为型模式 (Behavioral Patterns)](#行为型模式-behavioral-patterns)
      - [13. 责任链模式 (Chain of Responsibility)](#13-责任链模式-chain-of-responsibility)
      - [14. 命令模式 (Command)](#14-命令模式-command)
      - [15. 解释器模式 (Interpreter)](#15-解释器模式-interpreter)
      - [16. 迭代器模式 (Iterator)](#16-迭代器模式-iterator)
      - [17. 中介者模式 (Mediator)](#17-中介者模式-mediator)
      - [18. 备忘录模式 (Memento)](#18-备忘录模式-memento)
      - [19. 观察者模式 (Observer)](#19-观察者模式-observer)
      - [20. 状态模式 (State)](#20-状态模式-state)
      - [21. 策略模式 (Strategy)](#21-策略模式-strategy)
      - [22. 模板方法模式 (Template Method)](#22-模板方法模式-template-method)
      - [23. 访问者模式 (Visitor)](#23-访问者模式-visitor)
  - [🦀 Rust 特有模式 {#-rust-特有模式}](#-rust-特有模式--rust-特有模式)
    - [1. Newtype 模式](#1-newtype-模式)
    - [2. RAII 模式](#2-raii-模式)
    - [3. 类型状态模式 (Type State)](#3-类型状态模式-type-state)
    - [4. Builder 模式（消耗型 vs 非消耗型）](#4-builder-模式消耗型-vs-非消耗型)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)

---

## 📋 概述 {#-概述}

本指南介绍如何在 Rust 中使用常见的设计模式，包括 GoF 模式和 Rust 特有的模式。

**形式化引用**：CE-T1、CE-T2、CE-T3（组合工程定理）。详见 [04_compositional_engineering](../research_notes/software_design_theory/04_compositional_engineering/README.md)、[01_design_patterns_formal](../research_notes/software_design_theory/01_design_patterns_formal/README.md)。

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

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Product A".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Product B".to_string()
    }
}

enum ProductType {
    A,
    B,
}

fn create_product(t: ProductType) -> Box<dyn Product> {
    match t {
        ProductType::A => Box::new(ConcreteProductA),
        ProductType::B => Box::new(ConcreteProductB),
    }
}
```

---

## 📊 核心模式 {#-核心模式}

### 1. 创建型模式

#### 建造者模式

```rust
struct Config {
    host: String,
    port: u16,
    timeout: u64,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<u64>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: None,
            timeout: None,
        }
    }

    fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }

    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    fn timeout(mut self, timeout: u64) -> Self {
        self.timeout = Some(timeout);
        self
    }

    fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("host required")?,
            port: self.port.ok_or("port required")?,
            timeout: self.timeout.unwrap_or(30),
        })
    }
}

// 使用
let config = ConfigBuilder::new()
    .host("localhost".to_string())
    .port(8080)
    .timeout(60)
    .build()?;
```

### 2. 结构型模式

#### 适配器模式

```rust
// 旧接口
trait OldInterface {
    fn old_method(&self) -> String;
}

// 新接口
trait NewInterface {
    fn new_method(&self) -> String;
}

// 适配器
struct Adapter {
    old: Box<dyn OldInterface>,
}

impl NewInterface for Adapter {
    fn new_method(&self) -> String {
        self.old.old_method()
    }
}
```

#### 装饰器模式

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

struct Decorator {
    component: Box<dyn Component>,
}

impl Component for Decorator {
    fn operation(&self) -> String {
        format!("Decorator({})", self.component.operation())
    }
}
```

### 3. 行为型模式

#### 策略模式

```rust
trait Strategy {
    fn execute(&self, data: &[i32]) -> i32;
}

struct SumStrategy;
impl Strategy for SumStrategy {
    fn execute(&self, data: &[i32]) -> i32 {
        data.iter().sum()
    }
}

struct MaxStrategy;
impl Strategy for MaxStrategy {
    fn execute(&self, data: &[i32]) -> i32 {
        *data.iter().max().unwrap()
    }
}

struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Self { strategy }
    }

    fn execute(&self, data: &[i32]) -> i32 {
        self.strategy.execute(data)
    }
}
```

#### 观察者模式

```rust
use std::sync::{Arc, Mutex};

trait Observer {
    fn update(&self, data: &str);
}

struct ConcreteObserver {
    name: String,
}

impl Observer for ConcreteObserver {
    fn update(&self, data: &str) {
        println!("{} 收到更新: {}", self.name, data);
    }
}

struct Subject {
    observers: Vec<Arc<dyn Observer>>,
}

impl Subject {
    fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }

    fn attach(&mut self, observer: Arc<dyn Observer>) {
        self.observers.push(observer);
    }

    fn notify(&self, data: &str) {
        for observer in &self.observers {
            observer.update(data);
        }
    }
}
```

---

## 📐 23种设计模式完整实现 {#-23种设计模式完整实现}

### 创建型模式 (Creational Patterns)

#### 1. 单例模式 (Singleton)

```rust
use std::sync::{Arc, Mutex, OnceLock};

// 全局配置单例
static CONFIG: OnceLock<Arc<Mutex<Config>>> = OnceLock::new();

struct Config {
    database_url: String,
    max_connections: usize,
}

impl Config {
    fn instance() -> Arc<Mutex<Config>> {
        CONFIG.get_or_init(|| {
            Arc::new(Mutex::new(Config {
                database_url: "postgres://localhost".to_string(),
                max_connections: 10,
            }))
        }).clone()
    }
}

// 使用场景：全局配置、连接池、日志实例
// 反例：滥用单例会导致代码耦合、难以测试
// ❌ 不要：单例持有大量可变状态
// ✅ 要：单例尽量只读或提供有限的原子操作
```

#### 2. 工厂方法 (Factory Method)

```rust
// 产品 trait
trait Product {
    fn operation(&self) -> String;
    fn price(&self) -> f64;
}

// 具体产品
struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String { "Product A".to_string() }
    fn price(&self) -> f64 { 100.0 }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String { "Product B".to_string() }
    fn price(&self) -> f64 { 200.0 }
}

// 创建者 trait
trait Creator {
    fn factory_method(&self) -> Box<dyn Product>;

    fn business_logic(&self) -> String {
        let product = self.factory_method();
        format!("Creator: 使用 {}", product.operation())
    }
}

// 具体创建者
struct ConcreteCreatorA;
impl Creator for ConcreteCreatorA {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

struct ConcreteCreatorB;
impl Creator for ConcreteCreatorB {
    fn factory_method(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}

// 使用场景：框架扩展、跨平台 UI 组件创建
// 反例：简单场景使用工厂会增加复杂度
// ❌ 不要：只有一个产品时过度设计
// ✅ 要：产品族扩展时使用
```

#### 3. 抽象工厂 (Abstract Factory)

```rust
// 产品族 trait
trait Button {
    fn render(&self);
    fn on_click(&self, callback: Box<dyn Fn()>);
}

trait Checkbox {
    fn render(&self);
    fn toggle(&self);
}

// 抽象工厂 trait
trait GUIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}

// Windows 产品族
struct WinButton;
impl Button for WinButton {
    fn render(&self) { println!("渲染 Windows 按钮"); }
    fn on_click(&self, _callback: Box<dyn Fn()>) {}
}

struct WinCheckbox;
impl Checkbox for WinCheckbox {
    fn render(&self) { println!("渲染 Windows 复选框"); }
    fn toggle(&self) {}
}

struct WinFactory;
impl GUIFactory for WinFactory {
    fn create_button(&self) -> Box<dyn Button> { Box::new(WinButton) }
    fn create_checkbox(&self) -> Box<dyn Checkbox> { Box::new(WinCheckbox) }
}

// Mac 产品族
struct MacButton;
impl Button for MacButton {
    fn render(&self) { println!("渲染 Mac 按钮"); }
    fn on_click(&self, _callback: Box<dyn Fn()>) {}
}

struct MacCheckbox;
impl Checkbox for MacCheckbox {
    fn render(&self) { println!("渲染 Mac 复选框"); }
    fn toggle(&self) {}
}

struct MacFactory;
impl GUIFactory for MacFactory {
    fn create_button(&self) -> Box<dyn Button> { Box::new(MacButton) }
    fn create_checkbox(&self) -> Box<dyn Checkbox> { Box::new(MacCheckbox) }
}

// 客户端代码 - 与具体产品解耦
fn render_ui(factory: &dyn GUIFactory) {
    let button = factory.create_button();
    let checkbox = factory.create_checkbox();
    button.render();
    checkbox.render();
}

// 使用场景：跨平台开发、主题切换、数据库访问层
// 反例：产品族不稳定时难以维护
// ❌ 不要：频繁添加新产品时
// ✅ 要：产品族稳定但需要切换实现时
```

#### 4. 建造者模式 (Builder)

```rust
#[derive(Debug, Clone)]
struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout: u64,
}

struct HttpRequestBuilder {
    method: String,
    url: Option<String>,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout: u64,
}

impl HttpRequestBuilder {
    fn new(method: &str) -> Self {
        Self {
            method: method.to_string(),
            url: None,
            headers: Vec::new(),
            body: None,
            timeout: 30,
        }
    }

    fn get() -> Self { Self::new("GET") }
    fn post() -> Self { Self::new("POST") }

    fn url(mut self, url: &str) -> Self {
        self.url = Some(url.to_string());
        self
    }

    fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }

    fn body(mut self, body: &str) -> Self {
        self.body = Some(body.to_string());
        self
    }

    fn timeout(mut self, seconds: u64) -> Self {
        self.timeout = seconds;
        self
    }

    fn build(self) -> Result<HttpRequest, String> {
        let url = self.url.ok_or("URL 不能为空")?;
        Ok(HttpRequest {
            method: self.method,
            url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
        })
    }
}

// 使用
let request = HttpRequestBuilder::post()
    .url("https://api.example.com/users")
    .header("Content-Type", "application/json")
    .header("Authorization", "Bearer token")
    .body(r#"{"name": "John"}"#)
    .timeout(60)
    .build()?;

// 使用场景：复杂对象构造、参数过多、需要验证
// 反例：简单对象过度设计
// ❌ 不要：只有2-3个参数时使用
// ✅ 要：必选/可选参数混合、需要验证时
```

#### 5. 原型模式 (Prototype)

```rust
use std::clone::Clone;

// 原型 trait
trait Prototype: Clone {
    fn clone_box(&self) -> Box<dyn Prototype>;
    fn describe(&self) -> String;
}

#[derive(Clone)]
struct ConcretePrototype {
    name: String,
    data: Vec<u8>,
}

impl Prototype for ConcretePrototype {
    fn clone_box(&self) -> Box<dyn Prototype> {
        Box::new(self.clone())
    }

    fn describe(&self) -> String {
        format!("{} ({} bytes)", self.name, self.data.len())
    }
}

// 原型注册表
struct PrototypeRegistry {
    prototypes: std::collections::HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeRegistry {
    fn new() -> Self {
        Self {
            prototypes: std::collections::HashMap::new(),
        }
    }

    fn register(&mut self, id: &str, prototype: Box<dyn Prototype>) {
        self.prototypes.insert(id.to_string(), prototype);
    }

    fn create(&self, id: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(id).map(|p| p.clone_box())
    }
}

// 使用场景：对象创建成本高、需要动态配置原型
// 反例：Rust 中 Clone trait 已提供类似能力
// ❌ 不要：简单类型手动实现原型
// ✅ 要：复杂对象需要深拷贝或动态创建时
```

### 结构型模式 (Structural Patterns)

#### 6. 适配器模式 (Adapter)

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配者（旧接口）
struct Adaptee;
impl Adaptee {
    fn specific_request(&self) -> String {
        "特殊请求".to_string()
    }
}

// 对象适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        format!("适配器: {}", self.adaptee.specific_request())
    }
}

// 类适配器（使用泛型）
struct GenericAdapter<T> {
    adaptee: T,
}

impl<T> Target for GenericAdapter<T>
where
    T: SpecificInterface,
{
    fn request(&self) -> String {
        format!("泛型适配器: {}", self.adaptee.specific_request())
    }
}

trait SpecificInterface {
    fn specific_request(&self) -> String;
}

impl SpecificInterface for Adaptee {
    fn specific_request(&self) -> String {
        "特殊请求".to_string()
    }
}

// 使用场景：集成旧代码、第三方库适配、接口统一
// 反例：完全重写更简单时
// ❌ 不要：可以完全重构时强行适配
// ✅ 要：无法修改源码但需要兼容时
```

#### 7. 桥接模式 (Bridge)

```rust
// 实现维度
trait DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64);
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64);
}

struct DrawingAPI1; // OpenGL
impl DrawingAPI for DrawingAPI1 {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) {
        println!("API1: 在 ({}, {}) 绘制半径 {} 的圆", x, y, radius);
    }
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64) {
        println!("API1: 在 ({}, {}) 绘制 {}x{} 的矩形", x, y, width, height);
    }
}

struct DrawingAPI2; // DirectX
impl DrawingAPI for DrawingAPI2 {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) {
        println!("API2: Circle at ({}, {}) radius {}", x, y, radius);
    }
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64) {
        println!("API2: Rectangle at ({}, {}) size {}x{}", x, y, width, height);
    }
}

// 抽象维度
trait Shape {
    fn draw(&self);
    fn resize(&mut self, factor: f64);
}

struct CircleShape {
    x: f64, y: f64, radius: f64,
    drawing_api: Box<dyn DrawingAPI>,
}

impl Shape for CircleShape {
    fn draw(&self) {
        self.drawing_api.draw_circle(self.x, self.y, self.radius);
    }

    fn resize(&mut self, factor: f64) {
        self.radius *= factor;
    }
}

struct RectangleShape {
    x: f64, y: f64, width: f64, height: f64,
    drawing_api: Box<dyn DrawingAPI>,
}

impl Shape for RectangleShape {
    fn draw(&self) {
        self.drawing_api.draw_rectangle(self.x, self.y, self.width, self.height);
    }

    fn resize(&mut self, factor: f64) {
        self.width *= factor;
        self.height *= factor;
    }
}

// 使用场景：多维度变化、避免类爆炸（m×n 类 → m+n 类）
// 反例：变化维度少时增加复杂度
// ❌ 不要：只有单一变化维度时
// ✅ 要：形状和渲染方式独立变化时
```

#### 8. 组合模式 (Composite)

```rust
// 组件 trait
trait Graphic {
    fn draw(&self);
    fn move_to(&mut self, x: i32, y: i32);
}

// 叶节点
struct Dot { x: i32, y: i32 }

impl Graphic for Dot {
    fn draw(&self) {
        println!("在 ({}, {}) 绘制点", self.x, self.y);
    }
    fn move_to(&mut self, x: i32, y: i32) {
        self.x = x; self.y = y;
    }
}

struct Circle { x: i32, y: i32, radius: i32 }

impl Graphic for Circle {
    fn draw(&self) {
        println!("在 ({}, {}) 绘制半径 {} 的圆", self.x, self.y, self.radius);
    }
    fn move_to(&mut self, x: i32, y: i32) {
        self.x = x; self.y = y;
    }
}

// 组合节点
struct CompoundGraphic {
    children: Vec<Box<dyn Graphic>>,
}

impl CompoundGraphic {
    fn new() -> Self {
        Self { children: Vec::new() }
    }

    fn add(&mut self, child: Box<dyn Graphic>) {
        self.children.push(child);
    }

    fn remove(&mut self, index: usize) {
        self.children.remove(index);
    }
}

impl Graphic for CompoundGraphic {
    fn draw(&self) {
        println!("绘制组合图形:");
        for child in &self.children {
            child.draw();
        }
    }

    fn move_to(&mut self, x: i32, y: i32) {
        for child in &mut self.children {
            child.move_to(x, y);
        }
    }
}

// 使用场景：树形结构、递归操作、统一处理单个和组合对象
// 反例：层级结构简单时
// ❌ 不要：只有一层级时
// ✅ 要：递归树结构、文档对象模型时
```

#### 9. 装饰器模式 (Decorator)

```rust
// 组件 trait
trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

// 具体组件
struct SimpleCoffee;
impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 { 2.0 }
    fn description(&self) -> String { "简单咖啡".to_string() }
}

// 装饰器基类（泛型实现）
struct MilkDecorator<C: Coffee> {
    inner: C,
}

impl<C: Coffee> Coffee for MilkDecorator<C> {
    fn cost(&self) -> f64 {
        self.inner.cost() + 0.5
    }

    fn description(&self) -> String {
        format!("{}, 牛奶", self.inner.description())
    }
}

struct SugarDecorator<C: Coffee> {
    inner: C,
}

impl<C: Coffee> Coffee for SugarDecorator<C> {
    fn cost(&self) -> f64 {
        self.inner.cost() + 0.3
    }

    fn description(&self) -> String {
        format!("{}, 糖", self.inner.description())
    }
}

// 使用
let coffee = MilkDecorator {
    inner: SugarDecorator { inner: SimpleCoffee }
};
println!("{}: ${}", coffee.description(), coffee.cost());
// 输出: 简单咖啡, 糖, 牛奶: $2.8

// 使用场景：动态添加职责、中间件链、I/O 流包装
// 反例：对象行为固定不变时
// ❌ 不要：静态行为使用装饰器
// ✅ 要：运行时动态组合功能时
```

#### 10. 外观模式 (Facade)

```rust
// 复杂子系统
mod subsystem {
    pub struct CPU;
    impl CPU {
        pub fn freeze(&self) { println!("CPU: 冻结"); }
        pub fn jump(&self, position: u64) { println!("CPU: 跳转到 {}", position); }
        pub fn execute(&self) { println!("CPU: 执行"); }
    }

    pub struct Memory;
    impl Memory {
        pub fn load(&self, position: u64, data: &[u8]) {
            println!("Memory: 加载 {} 字节到 {}", data.len(), position);
        }
    }

    pub struct HardDrive;
    impl HardDrive {
        pub fn read(&self, lba: u64, size: usize) -> Vec<u8> {
            println!("HardDrive: 从 LBA {} 读取 {} 字节", lba, size);
            vec![0; size]
        }
    }
}

use subsystem::*;

// 外观类
struct ComputerFacade {
    cpu: CPU,
    memory: Memory,
    hard_drive: HardDrive,
}

impl ComputerFacade {
    fn new() -> Self {
        Self {
            cpu: CPU,
            memory: Memory,
            hard_drive: HardDrive,
        }
    }

    // 简化接口
    fn start(&self) {
        self.cpu.freeze();
        let boot_data = self.hard_drive.read(0, 1024);
        self.memory.load(0, &boot_data);
        self.cpu.jump(0);
        self.cpu.execute();
    }
}

// 使用场景：简化复杂系统接口、分层架构、API 网关
// 反例：增加不必要的抽象层
// ❌ 不要：简单系统添加外观
// ✅ 要：复杂子系统需要简化接口时
```

#### 11. 享元模式 (Flyweight)

```rust
use std::collections::HashMap;

// 享元接口
trait TreeType {
    fn display(&self, x: i32, y: i32);
}

// 具体享元（共享状态）
#[derive(Clone)]
struct TreeTypeImpl {
    name: String,
    color: String,
    texture: Vec<u8>, // 大量数据
}

impl TreeType for TreeTypeImpl {
    fn display(&self, x: i32, y: i32) {
        println!("{}树在 ({}, {})，颜色 {}，纹理 {} 字节",
            self.name, x, y, self.color, self.texture.len());
    }
}

// 享元工厂
struct TreeFactory {
    tree_types: HashMap<String, TreeTypeImpl>,
}

impl TreeFactory {
    fn new() -> Self {
        Self { tree_types: HashMap::new() }
    }

    fn get_tree_type(&mut self, name: &str, color: &str) -> TreeTypeImpl {
        let key = format!("{}-{}" , name, color);
        self.tree_types.entry(key.clone()).or_insert_with(|| {
            println!("创建新的树类型: {}", key);
            TreeTypeImpl {
                name: name.to_string(),
                color: color.to_string(),
                texture: vec![0; 1024 * 1024], // 1MB 纹理数据
            }
        }).clone()
    }
}

// 上下文（非共享状态）
struct Tree {
    x: i32,
    y: i32,
    tree_type: TreeTypeImpl,
}

impl Tree {
    fn display(&self) {
        self.tree_type.display(self.x, self.y);
    }
}

// 使用场景：大量相似对象、内存敏感、游戏开发
// 反例：对象差异大时无法共享
// ❌ 不要：每个对象都独特时
// ✅ 要：大量重复状态、内存受限时
```

#### 12. 代理模式 (Proxy)

```rust
use std::time::{Duration, Instant};

// 主题接口
trait Image {
    fn display(&self);
    fn filename(&self) -> &str;
}

// 真实主题
struct RealImage {
    filename: String,
}

impl RealImage {
    fn new(filename: &str) -> Self {
        println!("加载图片: {}", filename);
        // 模拟耗时加载
        std::thread::sleep(Duration::from_millis(100));
        Self { filename: filename.to_string() }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("显示图片: {}", self.filename);
    }
    fn filename(&self) -> &str { &self.filename }
}

// 虚拟代理（延迟加载）
struct ProxyImage {
    filename: String,
    real_image: Option<RealImage>,
}

impl ProxyImage {
    fn new(filename: &str) -> Self {
        println!("创建代理: {}", filename);
        Self { filename: filename.to_string(), real_image: None }
    }

    fn ensure_loaded(&mut self) -> &RealImage {
        if self.real_image.is_none() {
            self.real_image = Some(RealImage::new(&self.filename));
        }
        self.real_image.as_ref().unwrap()
    }
}

impl Image for ProxyImage {
    fn display(&self) {
        // 注意：这里需要可变访问，实际实现需要内部可变性
        println!("通过代理显示...");
    }
    fn filename(&self) -> &str { &self.filename }
}

// 保护代理（访问控制）
struct ProtectedImage<T: Image> {
    inner: T,
    user_role: String,
}

impl<T: Image> Image for ProtectedImage<T> {
    fn display(&self) {
        if self.user_role == "admin" {
            self.inner.display();
        } else {
            println!("拒绝访问: 权限不足");
        }
    }
    fn filename(&self) -> &str { self.inner.filename() }
}

// 使用场景：延迟加载、访问控制、远程代理、缓存
// 反例：简单直接访问时
// ❌ 不要：无额外控制需求时
// ✅ 要：需要控制访问或延迟加载时
```

### 行为型模式 (Behavioral Patterns)

#### 13. 责任链模式 (Chain of Responsibility)

```rust
// 处理者 trait
trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>);
    fn handle(&self, request: &Request) -> Option<Response>;
}

struct Request {
    path: String,
    method: String,
    headers: Vec<(String, String)>,
}

struct Response {
    status: u16,
    body: String,
}

// 基础处理者
struct BaseHandler {
    next: Option<Box<dyn Handler>>,
}

impl BaseHandler {
    fn new() -> Self { Self { next: None } }
}

impl Handler for BaseHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }

    fn handle(&self, request: &Request) -> Option<Response> {
        self.next.as_ref()?.handle(request)
    }
}

// 认证处理者
struct AuthHandler { base: BaseHandler }

impl Handler for AuthHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.base.set_next(next);
    }

    fn handle(&self, request: &Request) -> Option<Response> {
        if !request.headers.iter().any(|(k, _)| k == "Authorization") {
            return Some(Response { status: 401, body: "未授权".to_string() });
        }
        println!("认证通过");
        self.base.handle(request)
    }
}

// 日志处理者
struct LoggingHandler { base: BaseHandler }

impl Handler for LoggingHandler {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.base.set_next(next);
    }

    fn handle(&self, request: &Request) -> Option<Response> {
        println!("[LOG] {} {}", request.method, request.path);
        let response = self.base.handle(request);
        if let Some(ref r) = response {
            println!("[LOG] 响应状态: {}", r.status);
        }
        response
    }
}

// 使用场景：请求处理流水线、中间件、权限检查
// 反例：确定的处理流程
// ❌ 不要：处理顺序固定不变时
// ✅ 要：动态调整处理顺序、可插拔处理器时
```

#### 14. 命令模式 (Command)

```rust
// 命令 trait
trait Command {
    fn execute(&self);
    fn undo(&self);
}

// 接收者
struct TextEditor {
    content: String,
}

impl TextEditor {
    fn new() -> Self { Self { content: String::new() } }
    fn insert(&mut self, text: &str) { self.content.push_str(text); }
    fn delete(&mut self, len: usize) {
        let new_len = self.content.len().saturating_sub(len);
        self.content.truncate(new_len);
    }
    fn content(&self) -> &str { &self.content }
}

// 具体命令
struct InsertCommand {
    editor: std::cell::RefCell<std::rc::Rc<std::cell::RefCell<TextEditor>>>,
    text: String,
}

impl Command for InsertCommand {
    fn execute(&self) {
        self.editor.borrow().borrow_mut().insert(&self.text);
    }

    fn undo(&self) {
        let len = self.text.len();
        self.editor.borrow().borrow_mut().delete(len);
    }
}

// 调用者
struct CommandManager {
    history: Vec<Box<dyn Command>>,
    redo_stack: Vec<Box<dyn Command>>,
}

impl CommandManager {
    fn new() -> Self {
        Self { history: Vec::new(), redo_stack: Vec::new() }
    }

    fn execute(&mut self, cmd: Box<dyn Command>) {
        cmd.execute();
        self.history.push(cmd);
        self.redo_stack.clear();
    }

    fn undo(&mut self) {
        if let Some(cmd) = self.history.pop() {
            cmd.undo();
            self.redo_stack.push(cmd);
        }
    }

    fn redo(&mut self) {
        if let Some(cmd) = self.redo_stack.pop() {
            cmd.execute();
            self.history.push(cmd);
        }
    }
}

// 使用场景：撤销重做、队列请求、事务系统
// 反例：简单直接调用
// ❌ 不要：无需撤销、记录操作时
// ✅ 要：需要 undo/redo、延迟执行时
```

#### 15. 解释器模式 (Interpreter)

```rust
// 表达式 trait
trait Expression {
    fn interpret(&self, context: &Context) -> i32;
}

struct Context {
    variables: std::collections::HashMap<String, i32>,
}

impl Context {
    fn new() -> Self {
        Self { variables: std::collections::HashMap::new() }
    }

    fn set_variable(&mut self, name: &str, value: i32) {
        self.variables.insert(name.to_string(), value);
    }

    fn get_variable(&self, name: &str) -> i32 {
        *self.variables.get(name).unwrap_or(&0)
    }
}

// 终结符表达式
struct NumberExpression { value: i32 }
impl Expression for NumberExpression {
    fn interpret(&self, _context: &Context) -> i32 { self.value }
}

struct VariableExpression { name: String }
impl Expression for VariableExpression {
    fn interpret(&self, context: &Context) -> i32 {
        context.get_variable(&self.name)
    }
}

// 非终结符表达式
struct AddExpression { left: Box<dyn Expression>, right: Box<dyn Expression> }
impl Expression for AddExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) + self.right.interpret(context)
    }
}

struct SubtractExpression { left: Box<dyn Expression>, right: Box<dyn Expression> }
impl Expression for SubtractExpression {
    fn interpret(&self, context: &Context) -> i32 {
        self.left.interpret(context) - self.right.interpret(context)
    }
}

// 使用
let context = Context::new();
let expression = AddExpression {
    left: Box::new(NumberExpression { value: 10 }),
    right: Box::new(NumberExpression { value: 20 }),
};
let result = expression.interpret(&context);

// 使用场景：领域特定语言、表达式求值、配置文件解析
// 反例：语法复杂或性能敏感时
// ❌ 不要：复杂语法分析（用 parser 生成器）
// ✅ 要：简单语法、频繁变化的规则时
```

#### 16. 迭代器模式 (Iterator)

```rust
// Rust 内置强大的迭代器，这里展示自定义实现

struct Book {
    title: String,
    author: String,
}

struct BookCollection {
    books: Vec<Book>,
}

// 自定义迭代器
struct BookIterator<'a> {
    collection: &'a BookCollection,
    index: usize,
}

impl<'a> Iterator for BookIterator<'a> {
    type Item = &'a Book;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.collection.books.len() {
            let book = &self.collection.books[self.index];
            self.index += 1;
            Some(book)
        } else {
            None
        }
    }
}

impl BookCollection {
    fn iter(&self) -> BookIterator {
        BookIterator { collection: self, index: 0 }
    }

    // 使用 IntoIterator trait
    fn into_iter(self) -> std::vec::IntoIter<Book> {
        self.books.into_iter()
    }
}

// 反向迭代器
struct ReverseBookIterator<'a> {
    collection: &'a BookCollection,
    index: isize,
}

impl<'a> Iterator for ReverseBookIterator<'a> {
    type Item = &'a Book;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= 0 {
            let book = &self.collection.books[self.index as usize];
            self.index -= 1;
            Some(book)
        } else {
            None
        }
    }
}

// 使用场景：遍历集合、隐藏内部结构、多种遍历方式
// 反例：Rust 标准库已提供优秀支持
// ❌ 不要：重复实现标准 Iterator
// ✅ 要：特殊遍历需求时
```

#### 17. 中介者模式 (Mediator)

```rust
use std::collections::HashMap;

// 中介者 trait
trait ChatMediator {
    fn send_message(&self, message: &str, user_id: u64);
    fn add_user(&mut self, user: Box<dyn User>);
}

// 同事 trait
trait User {
    fn id(&self) -> u64;
    fn name(&self) -> &str;
    fn receive(&self, message: &str, from: &str);
    fn send(&self, mediator: &dyn ChatMediator, message: &str);
}

// 具体中介者
struct ChatRoom {
    users: HashMap<u64, Box<dyn User>>,
}

impl ChatRoom {
    fn new() -> Self {
        Self { users: HashMap::new() }
    }
}

impl ChatMediator for ChatRoom {
    fn send_message(&self, message: &str, from_id: u64) {
        if let Some(from_user) = self.users.get(&from_id) {
            for (id, user) in &self.users {
                if *id != from_id {
                    user.receive(message, from_user.name());
                }
            }
        }
    }

    fn add_user(&mut self, user: Box<dyn User>) {
        let id = user.id();
        println!("{} 加入聊天室", user.name());
        self.users.insert(id, user);
    }
}

// 具体同事
struct ChatUser { id: u64, name: String }

impl User for ChatUser {
    fn id(&self) -> u64 { self.id }
    fn name(&self) -> &str { &self.name }

    fn receive(&self, message: &str, from: &str) {
        println!("{} 收到来自 {} 的消息: {}", self.name, from, message);
    }

    fn send(&self, mediator: &dyn ChatMediator, message: &str) {
        println!("{} 发送: {}", self.name, message);
        mediator.send_message(message, self.id);
    }
}

// 使用场景：多对象通信、降低耦合、集中控制
// 反例：只有2-3个对象时
// ❌ 不要：简单对象关系时
// ✅ 要：星型通信结构、需要集中管理时
```

#### 18. 备忘录模式 (Memento)

```rust
// 备忘录 - 只读，通过构造函数创建
#[derive(Clone)]
struct EditorMemento {
    content: String,
    cursor_position: usize,
    // 只能通过 Originator 创建
}

impl EditorMemento {
    fn new(content: String, cursor_position: usize) -> Self {
        Self { content, cursor_position }
    }

    fn content(&self) -> &str { &self.content }
    fn cursor_position(&self) -> usize { self.cursor_position }
}

// 原发器
struct TextEditor {
    content: String,
    cursor_position: usize,
}

impl TextEditor {
    fn new() -> Self {
        Self { content: String::new(), cursor_position: 0 }
    }

    fn type_text(&mut self, text: &str) {
        self.content.push_str(text);
        self.cursor_position = self.content.len();
    }

    fn save(&self) -> EditorMemento {
        EditorMemento::new(self.content.clone(), self.cursor_position)
    }

    fn restore(&mut self, memento: &EditorMemento) {
        self.content = memento.content().to_string();
        self.cursor_position = memento.cursor_position();
    }

    fn content(&self) -> &str { &self.content }
}

// 负责人
struct History {
    mementos: Vec<EditorMemento>,
    current: usize,
}

impl History {
    fn new() -> Self {
        Self { mementos: Vec::new(), current: 0 }
    }

    fn push(&mut self, memento: EditorMemento) {
        // 删除当前之后的所有状态
        self.mementos.truncate(self.current);
        self.mementos.push(memento);
        self.current += 1;
    }

    fn undo(&mut self) -> Option<&EditorMemento> {
        if self.current > 1 {
            self.current -= 1;
            self.mementos.get(self.current - 1)
        } else {
            None
        }
    }

    fn redo(&mut self) -> Option<&EditorMemento> {
        if self.current < self.mementos.len() {
            self.current += 1;
            self.mementos.get(self.current - 1)
        } else {
            None
        }
    }
}

// 使用场景：撤销重做、状态快照、游戏存档
// 反例：状态过大时
// ❌ 不要：大量数据频繁快照
// ✅ 要：有限状态、需要回滚时
```

#### 19. 观察者模式 (Observer)

```rust
use std::sync::{Arc, Mutex};

// 观察者 trait
trait Observer {
    fn update(&self, event: &str, data: &str);
}

// 主题 trait
trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer + Send + Sync>);
    fn detach(&mut self, observer_id: usize);
    fn notify(&self, event: &str, data: &str);
}

// 具体主题
struct NewsAgency {
    observers: Mutex<Vec<(usize, Arc<dyn Observer + Send + Sync>)>>,
    next_id: Mutex<usize>,
}

impl NewsAgency {
    fn new() -> Self {
        Self {
            observers: Mutex::new(Vec::new()),
            next_id: Mutex::new(0),
        }
    }
}

impl Subject for NewsAgency {
    fn attach(&mut self, observer: Arc<dyn Observer + Send + Sync>) {
        let id = *self.next_id.lock().unwrap();
        *self.next_id.lock().unwrap() += 1;
        self.observers.lock().unwrap().push((id, observer));
    }

    fn detach(&mut self, observer_id: usize) {
        let mut observers = self.observers.lock().unwrap();
        observers.retain(|(id, _)| *id != observer_id);
    }

    fn notify(&self, event: &str, data: &str) {
        let observers = self.observers.lock().unwrap();
        for (_, observer) in observers.iter() {
            observer.update(event, data);
        }
    }
}

// 具体观察者
struct NewsChannel { name: String }

impl Observer for NewsChannel {
    fn update(&self, event: &str, data: &str) {
        println!("[{}] 收到 {}: {}", self.name, event, data);
    }
}

// 使用场景：事件订阅、数据绑定、消息通知
// 反例：简单回调函数即可时
// ❌ 不要：一对一简单通知
// ✅ 要：一对多、动态订阅关系时
```

#### 20. 状态模式 (State)

```rust
// 状态 trait
trait DocumentState {
    fn edit(&self, content: &str) -> Result<(), String>;
    fn publish(&self) -> Box<dyn DocumentState>;
    fn state_name(&self) -> &'static str;
}

// 具体状态：草稿
struct Draft;
impl DocumentState for Draft {
    fn edit(&self, _content: &str) -> Result<(), String> {
        println!("编辑内容");
        Ok(())
    }

    fn publish(&self) -> Box<dyn DocumentState> {
        println!("提交审核");
        Box::new(Moderation)
    }

    fn state_name(&self) -> &'static str { "草稿" }
}

// 具体状态：审核中
struct Moderation;
impl DocumentState for Moderation {
    fn edit(&self, _content: &str) -> Result<(), String> {
        Err("审核中不能编辑".to_string())
    }

    fn publish(&self) -> Box<dyn DocumentState> {
        println!("审核通过，发布");
        Box::new(Published)
    }

    fn state_name(&self) -> &'static str { "审核中" }
}

// 具体状态：已发布
struct Published;
impl DocumentState for Published {
    fn edit(&self, _content: &str) -> Result<(), String> {
        Err("已发布不能编辑".to_string())
    }

    fn publish(&self) -> Box<dyn DocumentState> {
        println!("已经是发布状态");
        Box::new(Published)
    }

    fn state_name(&self) -> &'static str { "已发布" }
}

// 上下文
struct Document {
    state: Box<dyn DocumentState>,
    content: String,
}

impl Document {
    fn new() -> Self {
        Self { state: Box::new(Draft), content: String::new() }
    }

    fn edit(&mut self, content: &str) -> Result<(), String> {
        self.state.edit(content)?;
        self.content.push_str(content);
        Ok(())
    }

    fn publish(&mut self) {
        self.state = self.state.publish();
    }

    fn state(&self) -> &'static str {
        self.state.state_name()
    }
}

// 使用场景：状态机、工作流、游戏角色状态
// 反例：状态少且转换简单时
// ❌ 不要：只有2-3个简单状态时
// ✅ 要：多状态、转换复杂、行为随状态变化时
```

#### 21. 策略模式 (Strategy)

```rust
// 策略 trait
trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<String, String>;
    fn validate(&self) -> bool;
}

// 具体策略：信用卡
struct CreditCardPayment {
    card_number: String,
    cvv: String,
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> Result<String, String> {
        println!("使用信用卡 {} 支付 ${}", self.card_number, amount);
        Ok(format!("CC-{}" , uuid::Uuid::new_v4()))
    }

    fn validate(&self) -> bool {
        self.card_number.len() == 16 && self.cvv.len() == 3
    }
}

// 具体策略：PayPal
struct PayPalPayment {
    email: String,
    password: String,
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> Result<String, String> {
        println!("使用 PayPal ({}) 支付 ${}", self.email, amount);
        Ok(format!("PP-{}", uuid::Uuid::new_v4()))
    }

    fn validate(&self) -> bool {
        self.email.contains('@') && !self.password.is_empty()
    }
}

// 具体策略：加密货币
struct CryptoPayment {
    wallet_address: String,
}

impl PaymentStrategy for CryptoPayment {
    fn pay(&self, amount: f64) -> Result<String, String> {
        println!("从钱包 {} 支付 ${} 等值加密货币", self.wallet_address, amount);
        Ok(format!("CRYPTO-{}", uuid::Uuid::new_v4()))
    }

    fn validate(&self) -> bool {
        self.wallet_address.starts_with("0x") && self.wallet_address.len() == 42
    }
}

// 上下文
struct ShoppingCart {
    items: Vec<(String, f64)>,
    strategy: Box<dyn PaymentStrategy>,
}

impl ShoppingCart {
    fn new(strategy: Box<dyn PaymentStrategy>) -> Self {
        Self { items: Vec::new(), strategy }
    }

    fn add_item(&mut self, name: &str, price: f64) {
        self.items.push((name.to_string(), price));
    }

    fn total(&self) -> f64 {
        self.items.iter().map(|(_, price)| price).sum()
    }

    fn checkout(&self) -> Result<String, String> {
        if !self.strategy.validate() {
            return Err("支付方式验证失败".to_string());
        }
        self.strategy.pay(self.total())
    }

    fn set_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = strategy;
    }
}

// 使用场景：多种算法选择、运行时切换、避免条件分支
// 反例：策略数量固定且很少变化
// ❌ 不要：永远只用一种策略
// ✅ 要：多种可互换算法、需要动态切换时
```

#### 22. 模板方法模式 (Template Method)

```rust
// 抽象类（trait 定义算法骨架）
trait DataMiner {
    // 模板方法 - 定义算法骨架
    fn mine(&self, path: &str) -> String {
        let file = self.open_file(path);
        let raw_data = self.extract_data(&file);
        let data = self.parse(&raw_data);
        let analysis = self.analyze(&data);
        self.send_report(&analysis);
        self.close_file(&file);
        analysis
    }

    // 必须由子类实现
    fn open_file(&self, path: &str) -> String;
    fn extract_data(&self, file: &str) -> String;
    fn parse(&self, raw_data: &str) -> Vec<String>;

    // 默认实现（钩子）
    fn analyze(&self, data: &[String]) -> String {
        format!("分析 {} 条数据", data.len())
    }

    fn send_report(&self, analysis: &str) {
        println!("发送报告: {}", analysis);
    }

    fn close_file(&self, file: &str) {
        println!("关闭文件: {}", file);
    }
}

// 具体类：PDF 挖掘
struct PdfDataMiner;

impl DataMiner for PdfDataMiner {
    fn open_file(&self, path: &str) -> String {
        format!("PDF: {}", path)
    }

    fn extract_data(&self, file: &str) -> String {
        println!("提取 PDF 数据: {}", file);
        "pdf raw data".to_string()
    }

    fn parse(&self, raw_data: &str) -> Vec<String> {
        vec![raw_data.to_string(), "page 1".to_string()]
    }
}

// 具体类：CSV 挖掘
struct CsvDataMiner {
    delimiter: char,
}

impl DataMiner for CsvDataMiner {
    fn open_file(&self, path: &str) -> String {
        format!("CSV: {}", path)
    }

    fn extract_data(&self, file: &str) -> String {
        println!("提取 CSV 数据: {}", file);
        "csv raw data".to_string()
    }

    fn parse(&self, raw_data: &str) -> Vec<String> {
        raw_data.split(self.delimiter).map(|s| s.to_string()).collect()
    }

    fn analyze(&self, data: &[String]) -> String {
        format!("CSV 分析: {} 行数据", data.len())
    }
}

// 使用场景：算法骨架固定、步骤可变、代码复用
// 反例：算法完全不同
// ❌ 不要：无共同步骤时
// ✅ 要：有固定流程、部分步骤可定制时
```

#### 23. 访问者模式 (Visitor)

```rust
// 元素 trait
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者 trait
trait Visitor {
    fn visit_circle(&self, circle: &Circle);
    fn visit_rectangle(&self, rectangle: &Rectangle);
    fn visit_triangle(&self, triangle: &Triangle);
}

// 具体元素
struct Circle { radius: f64 }
struct Rectangle { width: f64, height: f64 }
struct Triangle { base: f64, height: f64 }

impl Element for Circle {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_circle(self);
    }
}

impl Element for Rectangle {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_rectangle(self);
    }
}

impl Element for Triangle {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_triangle(self);
    }
}

// 具体访问者：面积计算
struct AreaCalculator;

impl Visitor for AreaCalculator {
    fn visit_circle(&self, circle: &Circle) {
        let area = std::f64::consts::PI * circle.radius * circle.radius;
        println!("圆面积: {:.2}", area);
    }

    fn visit_rectangle(&self, rectangle: &Rectangle) {
        let area = rectangle.width * rectangle.height;
        println!("矩形面积: {:.2}", area);
    }

    fn visit_triangle(&self, triangle: &Triangle) {
        let area = 0.5 * triangle.base * triangle.height;
        println!("三角形面积: {:.2}", area);
    }
}

// 具体访问者：绘图
struct DrawingVisitor;

impl Visitor for DrawingVisitor {
    fn visit_circle(&self, circle: &Circle) {
        println!("绘制圆: 半径 {}", circle.radius);
    }

    fn visit_rectangle(&self, rectangle: &Rectangle) {
        println!("绘制矩形: {} x {}", rectangle.width, rectangle.height);
    }

    fn visit_triangle(&self, triangle: &Triangle) {
        println!("绘制三角形: 底 {} 高 {}", triangle.base, triangle.height);
    }
}

// 对象结构
struct ShapeCollection {
    shapes: Vec<Box<dyn Element>>,
}

impl ShapeCollection {
    fn new() -> Self {
        Self { shapes: Vec::new() }
    }

    fn add(&mut self, shape: Box<dyn Element>) {
        self.shapes.push(shape);
    }

    fn accept(&self, visitor: &dyn Visitor) {
        for shape in &self.shapes {
            shape.accept(visitor);
        }
    }
}

// 使用场景：元素结构稳定、操作频繁变化、双分派
// 反例：元素经常变化
// ❌ 不要：类层次不稳定时
// ✅ 要：数据结构稳定、需要多种操作算法时
```

---

## 🦀 Rust 特有模式 {#-rust-特有模式}

### 1. Newtype 模式

```rust
// 类型安全包装 - 区分相同底层类型的不同语义
struct UserId(u64);
struct OrderId(u64);
struct ProductId(u64);

fn process_user(id: UserId) { /* ... */ }
fn process_order(id: OrderId) { /* ... */ }

// 使用场景：防止 ID 混淆、类型安全
// 编译错误：类型不匹配
// process_user(OrderId(1)); // 错误！
// process_user(UserId(1));  // 正确
```

### 2. RAII 模式

```rust
struct FileGuard {
    file: std::fs::File,
}

impl FileGuard {
    fn open(path: &str) -> std::io::Result<Self> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .open(path)?;
        println!("打开文件: {}", path);
        Ok(Self { file })
    }
}

impl Drop for FileGuard {
    fn drop(&mut self) {
        // 自动清理资源
        println!("自动关闭文件");
    }
}

// 使用场景：资源管理、锁守卫、连接池
```

### 3. 类型状态模式 (Type State)

```rust
// 使用泛型参数编码状态
struct Connection<State> {
    state: State,
}

struct Disconnected;
struct Connected { stream: std::net::TcpStream };

// 只能在 Disconnected 状态调用 connect
impl Connection<Disconnected> {
    fn new() -> Self {
        Self { state: Disconnected }
    }

    fn connect(self, addr: &str) -> std::io::Result<Connection<Connected>> {
        let stream = std::net::TcpStream::connect(addr)?;
        Ok(Connection { state: Connected { stream } })
    }
}

// 只能在 Connected 状态调用 send/receive
impl Connection<Connected> {
    fn send(&mut self, data: &[u8]) -> std::io::Result<()> {
        use std::io::Write;
        self.state.stream.write_all(data)
    }

    fn disconnect(self) -> Connection<Disconnected> {
        Connection { state: Disconnected }
    }
}

// 使用场景：状态机、API 使用顺序约束、编译期状态检查
// 编译期确保：必须先 connect 才能 send
```

### 4. Builder 模式（消耗型 vs 非消耗型）

```rust
// 非消耗型 Builder（使用 &mut self）
struct RequestBuilder {
    url: Option<String>,
    method: String,
}

impl RequestBuilder {
    fn new() -> Self {
        Self { url: None, method: "GET".to_string() }
    }

    fn url(&mut self, url: &str) -> &mut Self {
        self.url = Some(url.to_string());
        self
    }

    fn method(&mut self, method: &str) -> &mut Self {
        self.method = method.to_string();
        self
    }

    fn build(&self) -> Result<Request, String> {
        Ok(Request {
            url: self.url.clone().ok_or("URL required")?,
            method: self.method.clone(),
        })
    }
}

// 使用
let mut builder = RequestBuilder::new();
builder.url("https://example.com").method("POST");
let req1 = builder.build()?;
let req2 = builder.build()?; // 可以重用
```

---

## 📚 相关文档 {#-相关文档}

- [完整文档](../../crates/c09_design_pattern/README.md)
- [GoF 模式](../../crates/c09_design_pattern/docs/tier_02_guides/01_创建型模式指南.md)
- [Rust 特有模式](../../crates/c09_design_pattern/docs/tier_02_guides/05_最佳实践与反模式.md)
- [设计模式形式化文档](../research_notes/software_design_theory/01_design_patterns_formal/) - 23种设计模式的形式化定义与分析

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-02-20
