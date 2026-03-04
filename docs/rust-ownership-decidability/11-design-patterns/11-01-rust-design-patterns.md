# Rust设计模式全面指南

> **Rust版本**: 1.93.1
> **覆盖范围**: 创建型、结构型、行为型设计模式在Rust中的实现
> **权威参考**: Rust Design Patterns Book, Rust API Guidelines, Effective Rust

---

## 目录

- [Rust设计模式全面指南](#rust设计模式全面指南)
  - [目录](#目录)
  - [1. 设计模式概述](#1-设计模式概述)
    - [Rust设计模式哲学](#rust设计模式哲学)
      - [核心原则](#核心原则)
    - [设计模式分类](#设计模式分类)
    - [为什么Rust需要不同的设计模式](#为什么rust需要不同的设计模式)
      - [1. 所有权系统的影响](#1-所有权系统的影响)
      - [2. 编译时保证 vs 运行时检查](#2-编译时保证-vs-运行时检查)
  - [2. 创建型模式 (Creational Patterns)](#2-创建型模式-creational-patterns)
    - [2.1 构建者模式 (Builder Pattern)](#21-构建者模式-builder-pattern)
      - [基本实现](#基本实现)
      - [类型状态构建者 (Type State Builder)](#类型状态构建者-type-state-builder)
    - [2.2 工厂模式 (Factory Pattern)](#22-工厂模式-factory-pattern)
      - [简单工厂](#简单工厂)
      - [工厂方法](#工厂方法)
    - [2.3 抽象工厂模式 (Abstract Factory)](#23-抽象工厂模式-abstract-factory)
    - [2.4 单例模式 (Singleton Pattern)](#24-单例模式-singleton-pattern)
    - [2.5 原型模式 (Prototype Pattern)](#25-原型模式-prototype-pattern)
  - [3. 结构型模式 (Structural Patterns)](#3-结构型模式-structural-patterns)
    - [3.1 适配器模式 (Adapter Pattern)](#31-适配器模式-adapter-pattern)
    - [3.2 装饰器模式 (Decorator Pattern)](#32-装饰器模式-decorator-pattern)
    - [3.3 组合模式 (Composite Pattern)](#33-组合模式-composite-pattern)
    - [3.4 外观模式 (Facade Pattern)](#34-外观模式-facade-pattern)
    - [3.5 桥接模式 (Bridge Pattern)](#35-桥接模式-bridge-pattern)
    - [3.6 代理模式 (Proxy Pattern)](#36-代理模式-proxy-pattern)
  - [4. 行为型模式 (Behavioral Patterns)](#4-行为型模式-behavioral-patterns)
    - [4.1 命令模式 (Command Pattern)](#41-命令模式-command-pattern)
    - [4.2 策略模式 (Strategy Pattern)](#42-策略模式-strategy-pattern)
    - [4.3 观察者模式 (Observer Pattern)](#43-观察者模式-observer-pattern)
    - [4.4 迭代器模式 (Iterator Pattern)](#44-迭代器模式-iterator-pattern)
    - [4.5 状态模式 (State Pattern)](#45-状态模式-state-pattern)
    - [4.6 模板方法模式 (Template Method)](#46-模板方法模式-template-method)
    - [4.7 责任链模式 (Chain of Responsibility)](#47-责任链模式-chain-of-responsibility)
    - [4.8 访问者模式 (Visitor Pattern)](#48-访问者模式-visitor-pattern)
    - [4.9 备忘录模式 (Memento Pattern)](#49-备忘录模式-memento-pattern)
    - [4.10 中介者模式 (Mediator Pattern)](#410-中介者模式-mediator-pattern)
  - [5. Rust特有模式](#5-rust特有模式)
    - [5.1 Newtype模式](#51-newtype模式)
    - [5.2 类型状态模式 (Type State Pattern)](#52-类型状态模式-type-state-pattern)
    - [5.3 RAII守卫模式](#53-raii守卫模式)
    - [5.4 折中方案模式 (Default Trait)](#54-折中方案模式-default-trait)
  - [6. 反模式与陷阱](#6-反模式与陷阱)
    - [6.1 过度使用 `Rc<RefCell<T>>`](#61-过度使用-rcrefcellt)
    - [6.2 忽视所有权转移](#62-忽视所有权转移)
    - [6.3 过度泛型化](#63-过度泛型化)
    - [6.4 过度使用unwrap()](#64-过度使用unwrap)
  - [7. 最佳实践总结](#7-最佳实践总结)
    - [7.1 设计模式选择指南](#71-设计模式选择指南)
    - [7.2 Rust设计原则](#72-rust设计原则)
  - [参考文献](#参考文献)

---

## 1. 设计模式概述

### Rust设计模式哲学

Rust的设计模式哲学与传统面向对象语言有着显著差异，这源于Rust独特的所有权系统和类型系统：

#### 核心原则

- **利用类型系统编码不变量**: 编译时保证 > 运行时检查

  ```rust
  // 类型系统确保状态转换的合法性
  pub struct ConnectedConnection;
  pub struct DisconnectedConnection;

  impl Connection<DisconnectedConnection> {
      pub fn connect(self) -> Connection<ConnectedConnection> {
          // 只能在断开状态下连接
      }
  }
  ```

- **零成本抽象**: 设计模式不应有运行时开销

  ```rust
  // 泛型在编译期单态化，无运行时开销
  pub fn process<T: Processor>(item: T) -> Output {
      item.process()  // 直接调用，无虚表查找开销
  }
  ```

- **显式优于隐式**: 所有权转移显式可见

  ```rust
  // 所有权转移在类型签名中清晰表达
  pub fn consume(self) -> Transformed { ... }
  pub fn borrow(&self) -> &Data { ... }
  pub fn mutate(&mut self) { ... }
  ```

- **组合优于继承**: Trait系统替代继承层次

  ```rust
  // 通过Trait组合功能，而非继承
  pub trait Drawable { fn draw(&self); }
  pub trait Movable { fn move_to(&mut self, pos: Position); }

  pub struct GameObject;
  impl Drawable for GameObject { ... }
  impl Movable for GameObject { ... }
  ```

### 设计模式分类

| 类型 | 模式 | Rust特殊考量 |
|------|------|-------------|
| **创建型** | 构建者、工厂、单例、原型 | 所有权转移、 consuming builder |
| **结构型** | 适配器、装饰器、组合、外观、桥接、代理 | 生命周期、零成本抽象 |
| **行为型** | 命令、策略、观察者、迭代器、状态 | 所有权与借用、闭包 |
| **Rust特有** | Newtype、Type State、RAII守卫 | 类型安全、编译期保证 |

### 为什么Rust需要不同的设计模式

#### 1. 所有权系统的影响

```rust
// 传统OO语言：观察者持有被观察者引用
// Rust：必须使用Weak引用避免循环引用
use std::rc::{Rc, Weak};
use std::cell::RefCell;

pub trait Observer {
    fn update(&self, data: &str);
}

pub struct Subject {
    observers: RefCell<Vec<Weak<dyn Observer>>>,
}

impl Subject {
    pub fn notify(&self, data: &str) {
        let mut observers = self.observers.borrow_mut();
        // 清理失效的观察者
        observers.retain(|obs| {
            if let Some(obs) = obs.upgrade() {
                obs.update(data);
                true
            } else {
                false
            }
        });
    }
}
```

#### 2. 编译时保证 vs 运行时检查

```rust
// 传统语言：运行时状态检查
pub struct Connection {
    state: ConnectionState,  // 需要运行时检查
}

impl Connection {
    pub fn send(&self, data: &[u8]) -> Result<(), Error> {
        if self.state != ConnectionState::Connected {
            return Err(Error::NotConnected);
        }
        // ...
    }
}

// Rust Type State：编译时保证
pub struct Connected;
pub struct Disconnected;

pub struct Connection<State> {
    _state: std::marker::PhantomData<State>,
}

impl Connection<Connected> {
    pub fn send(&self, data: &[u8]) {  // 无需Result，必然已连接
        // ...
    }
}
```

---

## 2. 创建型模式 (Creational Patterns)

### 2.1 构建者模式 (Builder Pattern)

构建者模式在Rust中广泛使用，特别是处理复杂配置的对象创建。

#### 基本实现

```rust
#[derive(Debug, Clone)]
pub struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
    timeout: Duration,
    follow_redirects: bool,
}

pub struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
    timeout: Duration,
    follow_redirects: bool,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        Self {
            method: "GET".to_string(),
            url: String::new(),
            headers: Vec::new(),
            body: None,
            timeout: Duration::from_secs(30),
            follow_redirects: true,
        }
    }

    pub fn method(mut self, method: &str) -> Self {
        self.method = method.to_string();
        self
    }

    pub fn url(mut self, url: &str) -> Self {
        self.url = url.to_string();
        self
    }

    pub fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }

    pub fn body(mut self, body: Vec<u8>) -> Self {
        self.body = Some(body);
        self
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    pub fn follow_redirects(mut self, follow: bool) -> Self {
        self.follow_redirects = follow;
        self
    }

    pub fn build(self) -> Result<HttpRequest, BuilderError> {
        if self.url.is_empty() {
            return Err(BuilderError::MissingUrl);
        }

        Ok(HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout: self.timeout,
            follow_redirects: self.follow_redirects,
        })
    }
}

#[derive(Debug)]
pub enum BuilderError {
    MissingUrl,
    InvalidMethod,
}

// 使用示例
fn main() {
    let request = HttpRequestBuilder::new()
        .url("https://api.example.com/users")
        .method("POST")
        .header("Content-Type", "application/json")
        .header("Authorization", "Bearer token123")
        .body(r#"{"name": "John"}"#.as_bytes().to_vec())
        .timeout(Duration::from_secs(60))
        .build()
        .expect("Failed to build request");

    println!("{:?}", request);
}
```

#### 类型状态构建者 (Type State Builder)

```rust
use std::marker::PhantomData;

// 类型标记
pub struct NoUrl;
pub struct HasUrl;
pub struct NoMethod;
pub struct HasMethod;

pub struct RequestBuilder<UrlState, MethodState> {
    url: String,
    method: String,
    _url: PhantomData<UrlState>,
    _method: PhantomData<MethodState>,
}

impl RequestBuilder<NoUrl, NoMethod> {
    pub fn new() -> Self {
        Self {
            url: String::new(),
            method: String::new(),
            _url: PhantomData,
            _method: PhantomData,
        }
    }
}

impl<MethodState> RequestBuilder<NoUrl, MethodState> {
    pub fn url(self, url: &str) -> RequestBuilder<HasUrl, MethodState> {
        RequestBuilder {
            url: url.to_string(),
            method: self.method,
            _url: PhantomData,
            _method: PhantomData,
        }
    }
}

impl<UrlState> RequestBuilder<UrlState, NoMethod> {
    pub fn method(self, method: &str) -> RequestBuilder<UrlState, HasMethod> {
        RequestBuilder {
            url: self.url,
            method: method.to_string(),
            _url: PhantomData,
            _method: PhantomData,
        }
    }
}

impl RequestBuilder<HasUrl, HasMethod> {
    pub fn build(self) -> Request {
        Request {
            url: self.url,
            method: self.method,
        }
    }
}

pub struct Request {
    url: String,
    method: String,
}

// 只能在设置了url和method后才能build
fn usage() {
    let req = RequestBuilder::new()
        .url("https://example.com")
        .method("GET")
        .build();  // 编译时保证必须的字段已设置
}
```

### 2.2 工厂模式 (Factory Pattern)

工厂模式用于创建对象而不指定具体类。

#### 简单工厂

```rust
pub trait Animal: Send + Sync {
    fn speak(&self) -> String;
    fn name(&self) -> &str;
}

pub struct Dog {
    name: String,
}

impl Animal for Dog {
    fn speak(&self) -> String {
        format!("{} says: Woof!", self.name)
    }
    fn name(&self) -> &str {
        &self.name
    }
}

pub struct Cat {
    name: String,
}

impl Animal for Cat {
    fn speak(&self) -> String {
        format!("{} says: Meow!", self.name)
    }
    fn name(&self) -> &str {
        &self.name
    }
}

pub enum AnimalType {
    Dog,
    Cat,
}

pub struct AnimalFactory;

impl AnimalFactory {
    pub fn create(animal_type: AnimalType, name: &str) -> Box<dyn Animal> {
        match animal_type {
            AnimalType::Dog => Box::new(Dog {
                name: name.to_string(),
            }),
            AnimalType::Cat => Box::new(Cat {
                name: name.to_string(),
            }),
        }
    }
}
```

#### 工厂方法

```rust
pub trait Product {
    fn operation(&self) -> String;
}

pub trait Factory {
    type ProductType: Product;
    fn create(&self) -> Self::ProductType;
}

pub struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Product A operation".to_string()
    }
}

pub struct ConcreteFactoryA;
impl Factory for ConcreteFactoryA {
    type ProductType = ConcreteProductA;
    fn create(&self) -> Self::ProductType {
        ConcreteProductA
    }
}
```

### 2.3 抽象工厂模式 (Abstract Factory)

```rust
// UI组件家族
trait Button {
    fn paint(&self);
}

trait Checkbox {
    fn paint(&self);
}

// Windows风格
trait WindowsButton;
impl Button for dyn WindowsButton {
    fn paint(&self) {
        println!("Rendering Windows button");
    }
}

trait WindowsCheckbox;
impl Checkbox for dyn WindowsCheckbox {
    fn paint(&self) {
        println!("Rendering Windows checkbox");
    }
}

// Mac风格
trait MacButton;
impl Button for dyn MacButton {
    fn paint(&self) {
        println!("Rendering Mac button");
    }
}

trait MacCheckbox;
impl Checkbox for dyn MacCheckbox {
    fn paint(&self) {
        println!("Rendering Mac checkbox");
    }
}

// 抽象工厂
trait GUIFactory {
    fn create_button(&self) -> Box<dyn Button>;
    fn create_checkbox(&self) -> Box<dyn Checkbox>;
}

struct WindowsFactory;
impl GUIFactory for WindowsFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(()) as Box<dyn WindowsButton>
    }
    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(()) as Box<dyn WindowsCheckbox>
    }
}

struct MacFactory;
impl GUIFactory for MacFactory {
    fn create_button(&self) -> Box<dyn Button> {
        Box::new(()) as Box<dyn MacButton>
    }
    fn create_checkbox(&self) -> Box<dyn Checkbox> {
        Box::new(()) as Box<dyn MacCheckbox>
    }
}
```

### 2.4 单例模式 (Singleton Pattern)

Rust中的单例模式需要特别注意线程安全。

```rust
use std::sync::{Arc, Mutex, OnceLock};

pub struct DatabaseConnection {
    connection_string: String,
}

impl DatabaseConnection {
    fn new() -> Self {
        Self {
            connection_string: "postgresql://localhost/db".to_string(),
        }
    }

    pub fn query(&self, sql: &str) -> Vec<String> {
        println!("Executing: {}", sql);
        vec!["result1".to_string()]
    }
}

// 线程安全的单例
static DB_INSTANCE: OnceLock<Arc<Mutex<DatabaseConnection>>> = OnceLock::new();

pub fn get_database() -> Arc<Mutex<DatabaseConnection>> {
    DB_INSTANCE
        .get_or_init(|| Arc::new(Mutex::new(DatabaseConnection::new())))
        .clone()
}

// 使用示例
fn main() {
    let db1 = get_database();
    let db2 = get_database();

    // db1和db2指向同一个实例
    assert!(Arc::ptr_eq(&db1, &db2));

    db1.lock().unwrap().query("SELECT * FROM users");
}
```

### 2.5 原型模式 (Prototype Pattern)

```rust
pub trait Prototype: Clone {
    fn clone_box(&self) -> Box<dyn Prototype>;
}

#[derive(Clone)]
pub struct ConcretePrototype {
    pub field1: String,
    pub field2: i32,
}

impl Prototype for ConcretePrototype {
    fn clone_box(&self) -> Box<dyn Prototype> {
        Box::new(self.clone())
    }
}

// 原型注册表
pub struct PrototypeRegistry {
    prototypes: std::collections::HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeRegistry {
    pub fn new() -> Self {
        Self {
            prototypes: std::collections::HashMap::new(),
        }
    }

    pub fn register(&mut self, name: &str, prototype: Box<dyn Prototype>) {
        self.prototypes.insert(name.to_string(), prototype);
    }

    pub fn create(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(name).map(|p| p.clone_box())
    }
}
```

---

## 3. 结构型模式 (Structural Patterns)

### 3.1 适配器模式 (Adapter Pattern)

适配器模式允许不兼容的接口协同工作。

```rust
// 目标接口
pub trait MediaPlayer {
    fn play(&self, audio_type: &str, file_name: &str);
}

// 被适配者（旧接口）
pub struct AdvancedMediaPlayer;

impl AdvancedMediaPlayer {
    pub fn play_vlc(&self, file_name: &str) {
        println!("Playing vlc file: {}", file_name);
    }

    pub fn play_mp4(&self, file_name: &str) {
        println!("Playing mp4 file: {}", file_name);
    }
}

// 适配器
pub struct MediaAdapter {
    advanced_player: AdvancedMediaPlayer,
}

impl MediaAdapter {
    pub fn new() -> Self {
        Self {
            advanced_player: AdvancedMediaPlayer,
        }
    }
}

impl MediaPlayer for MediaAdapter {
    fn play(&self, audio_type: &str, file_name: &str) {
        match audio_type {
            "vlc" => self.advanced_player.play_vlc(file_name),
            "mp4" => self.advanced_player.play_mp4(file_name),
            _ => println!("Unsupported format: {}", audio_type),
        }
    }
}

// 客户端使用
pub struct AudioPlayer {
    adapter: MediaAdapter,
}

impl AudioPlayer {
    pub fn new() -> Self {
        Self {
            adapter: MediaAdapter::new(),
        }
    }

    pub fn play(&self, audio_type: &str, file_name: &str) {
        if audio_type == "mp3" {
            println!("Playing mp3 file: {}", file_name);
        } else {
            self.adapter.play(audio_type, file_name);
        }
    }
}
```

### 3.2 装饰器模式 (Decorator Pattern)

```rust
// 组件接口
pub trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

// 具体组件
pub struct SimpleCoffee;

impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 {
        2.0
    }
    fn description(&self) -> String {
        "Simple coffee".to_string()
    }
}

// 装饰器基类
pub struct CoffeeDecorator<T: Coffee> {
    component: T,
}

impl<T: Coffee> CoffeeDecorator<T> {
    pub fn new(component: T) -> Self {
        Self { component }
    }
}

// 牛奶装饰器
pub struct MilkDecorator<T: Coffee> {
    decorator: CoffeeDecorator<T>,
}

impl<T: Coffee> MilkDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            decorator: CoffeeDecorator::new(component),
        }
    }
}

impl<T: Coffee> Coffee for MilkDecorator<T> {
    fn cost(&self) -> f64 {
        self.decorator.component.cost() + 0.5
    }
    fn description(&self) -> String {
        format!("{}, Milk", self.decorator.component.description())
    }
}

// 糖装饰器
pub struct SugarDecorator<T: Coffee> {
    decorator: CoffeeDecorator<T>,
}

impl<T: Coffee> SugarDecorator<T> {
    pub fn new(component: T) -> Self {
        Self {
            decorator: CoffeeDecorator::new(component),
        }
    }
}

impl<T: Coffee> Coffee for SugarDecorator<T> {
    fn cost(&self) -> f64 {
        self.decorator.component.cost() + 0.3
    }
    fn description(&self) -> String {
        format!("{}, Sugar", self.decorator.component.description())
    }
}

// 使用
fn main() {
    let coffee = SimpleCoffee;
    println!("{} ${}", coffee.description(), coffee.cost());

    let coffee_with_milk = MilkDecorator::new(coffee);
    println!("{} ${}", coffee_with_milk.description(), coffee_with_milk.cost());

    let coffee_with_milk_and_sugar = SugarDecorator::new(coffee_with_milk);
    println!("{} ${}",
        coffee_with_milk_and_sugar.description(),
        coffee_with_milk_and_sugar.cost()
    );
}
```

### 3.3 组合模式 (Composite Pattern)

```rust
// 组件接口
pub trait Graphic {
    fn draw(&self);
    fn move_to(&mut self, x: i32, y: i32);
}

// 叶子节点
pub struct Dot {
    x: i32,
    y: i32,
}

impl Dot {
    pub fn new(x: i32, y: i32) -> Self {
        Self { x, y }
    }
}

impl Graphic for Dot {
    fn draw(&self) {
        println!("Drawing dot at ({}, {})", self.x, self.y);
    }

    fn move_to(&mut self, x: i32, y: i32) {
        self.x = x;
        self.y = y;
    }
}

// 组合节点
pub struct CompoundGraphic {
    children: Vec<Box<dyn Graphic>>,
    x: i32,
    y: i32,
}

impl CompoundGraphic {
    pub fn new() -> Self {
        Self {
            children: Vec::new(),
            x: 0,
            y: 0,
        }
    }

    pub fn add(&mut self, child: Box<dyn Graphic>) {
        self.children.push(child);
    }

    pub fn remove(&mut self, index: usize) {
        if index < self.children.len() {
            self.children.remove(index);
        }
    }
}

impl Graphic for CompoundGraphic {
    fn draw(&self) {
        println!("Drawing compound graphic:");
        for child in &self.children {
            child.draw();
        }
    }

    fn move_to(&mut self, x: i32, y: i32) {
        let dx = x - self.x;
        let dy = y - self.y;
        for child in &mut self.children {
            // 这里简化处理，实际应该获取子元素位置
        }
        self.x = x;
        self.y = y;
    }
}

// 使用
fn main() {
    let mut canvas = CompoundGraphic::new();

    canvas.add(Box::new(Dot::new(1, 2)));
    canvas.add(Box::new(Dot::new(3, 4)));

    let mut subgroup = CompoundGraphic::new();
    subgroup.add(Box::new(Dot::new(5, 6)));
    canvas.add(Box::new(subgroup));

    canvas.draw();
}
```

### 3.4 外观模式 (Facade Pattern)

```rust
// 复杂子系统
mod subsystem {
    pub struct CPU;
    impl CPU {
        pub fn freeze(&self) { println!("CPU frozen"); }
        pub fn jump(&self, position: u64) { println!("CPU jump to {}", position); }
        pub fn execute(&self) { println!("CPU executing"); }
    }

    pub struct Memory;
    impl Memory {
        pub fn load(&self, position: u64, data: &[u8]) {
            println!("Memory loaded at {}", position);
        }
    }

    pub struct HardDrive;
    impl HardDrive {
        pub fn read(&self, lba: u64, size: usize) -> Vec<u8> {
            println!("HardDrive reading {} bytes from {}", size, lba);
            vec![0; size]
        }
    }
}

use subsystem::*;

// 外观
pub struct ComputerFacade {
    cpu: CPU,
    memory: Memory,
    hard_drive: HardDrive,
}

impl ComputerFacade {
    pub fn new() -> Self {
        Self {
            cpu: CPU,
            memory: Memory,
            hard_drive: HardDrive,
        }
    }

    pub fn start(&self) {
        self.cpu.freeze();
        let boot_data = self.hard_drive.read(0, 1024);
        self.memory.load(0, &boot_data);
        self.cpu.jump(0);
        self.cpu.execute();
    }
}

// 使用
fn main() {
    let computer = ComputerFacade::new();
    computer.start();  // 简化调用
}
```

### 3.5 桥接模式 (Bridge Pattern)

```rust
// 实现接口
pub trait DrawingAPI {
    fn draw_circle(&self, x: f64, y: f64, radius: f64);
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64);
}

// 具体实现
pub struct DrawingAPI1;
impl DrawingAPI for DrawingAPI1 {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) {
        println!("API1: Circle at ({}, {}) radius {}", x, y, radius);
    }
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64) {
        println!("API1: Rectangle at ({}, {}) size {}x{}", x, y, width, height);
    }
}

pub struct DrawingAPI2;
impl DrawingAPI for DrawingAPI2 {
    fn draw_circle(&self, x: f64, y: f64, radius: f64) {
        println!("API2: Circle at ({}, {}) radius {}", x, y, radius);
    }
    fn draw_rectangle(&self, x: f64, y: f64, width: f64, height: f64) {
        println!("API2: Rectangle at ({}, {}) size {}x{}", x, y, width, height);
    }
}

// 抽象
pub trait Shape {
    fn draw(&self);
    fn resize(&mut self, factor: f64);
}

pub struct CircleShape<T: DrawingAPI> {
    x: f64,
    y: f64,
    radius: f64,
    drawing_api: T,
}

impl<T: DrawingAPI> CircleShape<T> {
    pub fn new(x: f64, y: f64, radius: f64, api: T) -> Self {
        Self { x, y, radius, drawing_api: api }
    }
}

impl<T: DrawingAPI> Shape for CircleShape<T> {
    fn draw(&self) {
        self.drawing_api.draw_circle(self.x, self.y, self.radius);
    }
    fn resize(&mut self, factor: f64) {
        self.radius *= factor;
    }
}
```

### 3.6 代理模式 (Proxy Pattern)

```rust
use std::collections::HashMap;

// 主题接口
pub trait Image {
    fn display(&self);
    fn get_filename(&self) -> &str;
}

// 真实主题
pub struct RealImage {
    filename: String,
    data: Vec<u8>,
}

impl RealImage {
    pub fn new(filename: &str) -> Self {
        println!("Loading image from disk: {}", filename);
        Self {
            filename: filename.to_string(),
            data: vec![0; 1024 * 1024],  // 模拟加载大量数据
        }
    }
}

impl Image for RealImage {
    fn display(&self) {
        println!("Displaying image: {}", self.filename);
    }
    fn get_filename(&self) -> &str {
        &self.filename
    }
}

// 代理
pub struct ProxyImage {
    filename: String,
    real_image: Option<RealImage>,
}

impl ProxyImage {
    pub fn new(filename: &str) -> Self {
        Self {
            filename: filename.to_string(),
            real_image: None,
        }
    }
}

impl Image for ProxyImage {
    fn display(&self) {
        // 延迟加载
        let real = self.real_image.as_ref()
            .expect("Image not loaded");
        real.display();
    }
    fn get_filename(&self) -> &str {
        &self.filename
    }
}

// 缓存代理
pub struct CachedImageProxy {
    cache: RefCell<HashMap<String, RealImage>>,
}

impl CachedImageProxy {
    pub fn new() -> Self {
        Self {
            cache: RefCell::new(HashMap::new()),
        }
    }

    pub fn get_image(&self, filename: &str) -> &RealImage {
        // 简化版本，实际实现更复杂
        unimplemented!()
    }
}
```

---

## 4. 行为型模式 (Behavioral Patterns)

### 4.1 命令模式 (Command Pattern)

命令模式将请求封装为对象，支持参数化、队列化和撤销操作。

```rust
use std::collections::VecDeque;

// 命令接口
pub trait Command {
    fn execute(&self);
    fn undo(&self);
}

// 接收者
pub struct TextEditor {
    content: String,
}

impl TextEditor {
    pub fn new() -> Self {
        Self {
            content: String::new(),
        }
    }

    pub fn insert(&mut self, text: &str, position: usize) {
        self.content.insert_str(position, text);
    }

    pub fn delete(&mut self, start: usize, len: usize) {
        self.content.drain(start..start + len);
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }
}

// 具体命令：插入
pub struct InsertCommand {
    editor: Rc<RefCell<TextEditor>>,
    text: String,
    position: usize,
}

impl InsertCommand {
    pub fn new(editor: Rc<RefCell<TextEditor>>, text: &str, position: usize) -> Self {
        Self {
            editor,
            text: text.to_string(),
            position,
        }
    }
}

impl Command for InsertCommand {
    fn execute(&self) {
        self.editor.borrow_mut().insert(&self.text, self.position);
    }

    fn undo(&self) {
        let len = self.text.len();
        self.editor.borrow_mut().delete(self.position, len);
    }
}

// 删除命令
pub struct DeleteCommand {
    editor: Rc<RefCell<TextEditor>>,
    position: usize,
    length: usize,
    deleted_text: RefCell<String>,
}

impl DeleteCommand {
    pub fn new(editor: Rc<RefCell<TextEditor>>, position: usize, length: usize) -> Self {
        Self {
            editor,
            position,
            length,
            deleted_text: RefCell::new(String::new()),
        }
    }
}

impl Command for DeleteCommand {
    fn execute(&self) {
        let content = self.editor.borrow().get_content().to_string();
        let deleted = content[self.position..self.position + self.length].to_string();
        *self.deleted_text.borrow_mut() = deleted;
        self.editor.borrow_mut().delete(self.position, self.length);
    }

    fn undo(&self) {
        let text = self.deleted_text.borrow();
        self.editor.borrow_mut().insert(&text, self.position);
    }
}

// 调用者
pub struct CommandManager {
    history: VecDeque<Box<dyn Command>>,
    redo_stack: VecDeque<Box<dyn Command>>,
}

impl CommandManager {
    pub fn new() -> Self {
        Self {
            history: VecDeque::new(),
            redo_stack: VecDeque::new(),
        }
    }

    pub fn execute(&mut self, command: Box<dyn Command>) {
        command.execute();
        self.history.push_back(command);
        self.redo_stack.clear();
    }

    pub fn undo(&mut self) {
        if let Some(command) = self.history.pop_back() {
            command.undo();
            self.redo_stack.push_back(command);
        }
    }

    pub fn redo(&mut self) {
        if let Some(command) = self.redo_stack.pop_back() {
            command.execute();
            self.history.push_back(command);
        }
    }
}

// 使用示例
use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let editor = Rc::new(RefCell::new(TextEditor::new()));
    let mut manager = CommandManager::new();

    manager.execute(Box::new(InsertCommand::new(
        editor.clone(), "Hello ", 0
    )));

    manager.execute(Box::new(InsertCommand::new(
        editor.clone(), "World!", 6
    )));

    println!("Content: {}", editor.borrow().get_content());
    // 输出: Content: Hello World!

    manager.undo();
    println!("After undo: {}", editor.borrow().get_content());
    // 输出: After undo: Hello

    manager.redo();
    println!("After redo: {}", editor.borrow().get_content());
    // 输出: After redo: Hello World!
}
```

### 4.2 策略模式 (Strategy Pattern)

```rust
// 策略接口
pub trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<(), PaymentError>;
    fn get_name(&self) -> &str;
}

#[derive(Debug)]
pub enum PaymentError {
    InsufficientFunds,
    InvalidCard,
    NetworkError,
}

// 信用卡策略
pub struct CreditCardPayment {
    card_number: String,
    cvv: String,
    expiry: String,
}

impl CreditCardPayment {
    pub fn new(card_number: &str, cvv: &str, expiry: &str) -> Self {
        Self {
            card_number: card_number.to_string(),
            cvv: cvv.to_string(),
            expiry: expiry.to_string(),
        }
    }
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> Result<(), PaymentError> {
        println!("Paying ${} using Credit Card ending in {}",
            amount,
            &self.card_number[self.card_number.len() - 4..]
        );
        Ok(())
    }

    fn get_name(&self) -> &str {
        "Credit Card"
    }
}

// PayPal策略
pub struct PayPalPayment {
    email: String,
    password: String,
}

impl PayPalPayment {
    pub fn new(email: &str, password: &str) -> Self {
        Self {
            email: email.to_string(),
            password: password.to_string(),
        }
    }
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> Result<(), PaymentError> {
        println!("Paying ${} using PayPal account {}", amount, self.email);
        Ok(())
    }

    fn get_name(&self) -> &str {
        "PayPal"
    }
}

// 上下文
pub struct ShoppingCart {
    items: Vec<(String, f64)>,
    strategy: Option<Box<dyn PaymentStrategy>>,
}

impl ShoppingCart {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            strategy: None,
        }
    }

    pub fn add_item(&mut self, name: &str, price: f64) {
        self.items.push((name.to_string(), price));
    }

    pub fn set_payment_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = Some(strategy);
    }

    pub fn total(&self) -> f64 {
        self.items.iter().map(|(_, price)| price).sum()
    }

    pub fn checkout(&self) -> Result<(), PaymentError> {
        let strategy = self.strategy.as_ref()
            .ok_or(PaymentError::InvalidCard)?;

        let total = self.total();
        println!("Checking out with total: ${}", total);
        strategy.pay(total)
    }
}

// 使用
fn main() {
    let mut cart = ShoppingCart::new();
    cart.add_item("Book", 29.99);
    cart.add_item("Pen", 5.99);

    // 使用信用卡支付
    cart.set_payment_strategy(Box::new(CreditCardPayment::new(
        "1234567890123456", "123", "12/25"
    )));
    cart.checkout().unwrap();

    // 更换为PayPal支付
    cart.set_payment_strategy(Box::new(PayPalPayment::new(
        "user@example.com", "password"
    )));
    cart.checkout().unwrap();
}
```

### 4.3 观察者模式 (Observer Pattern)

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::collections::HashMap;

// 观察者接口
pub trait Observer {
    fn update(&self, event: &str, data: &str);
}

// 主题接口
pub trait Subject {
    fn attach(&mut self, observer: Rc<dyn Observer>);
    fn detach(&mut self, observer_id: usize);
    fn notify(&self, event: &str, data: &str);
}

// 具体主题：新闻发布者
pub struct NewsPublisher {
    observers: RefCell<HashMap<usize, Weak<dyn Observer>>>,
    next_id: RefCell<usize>,
}

impl NewsPublisher {
    pub fn new() -> Self {
        Self {
            observers: RefCell::new(HashMap::new()),
            next_id: RefCell::new(0),
        }
    }

    pub fn publish(&self, news: &str) {
        println!("Publishing news: {}", news);
        self.notify("news", news);
    }
}

impl Subject for NewsPublisher {
    fn attach(&mut self, observer: Rc<dyn Observer>) {
        let id = *self.next_id.borrow();
        self.observers.borrow_mut().insert(id, Rc::downgrade(&observer));
        *self.next_id.borrow_mut() += 1;
    }

    fn detach(&mut self, observer_id: usize) {
        self.observers.borrow_mut().remove(&observer_id);
    }

    fn notify(&self, event: &str, data: &str) {
        let mut observers = self.observers.borrow_mut();
        let mut to_remove = Vec::new();

        for (id, weak_observer) in observers.iter() {
            if let Some(observer) = weak_observer.upgrade() {
                observer.update(event, data);
            } else {
                to_remove.push(*id);
            }
        }

        for id in to_remove {
            observers.remove(&id);
        }
    }
}

// 具体观察者：邮件订阅者
pub struct EmailSubscriber {
    email: String,
}

impl EmailSubscriber {
    pub fn new(email: &str) -> Self {
        Self {
            email: email.to_string(),
        }
    }
}

impl Observer for EmailSubscriber {
    fn update(&self, event: &str, data: &str) {
        println!("[Email to {}] Event: {}, Data: {}",
            self.email, event, data);
    }
}

// 具体观察者：短信订阅者
pub struct SmsSubscriber {
    phone: String,
}

impl SmsSubscriber {
    pub fn new(phone: &str) -> Self {
        Self {
            phone: phone.to_string(),
        }
    }
}

impl Observer for SmsSubscriber {
    fn update(&self, event: &str, data: &str) {
        println!("[SMS to {}] Event: {}, Data: {}",
            self.phone, event, data);
    }
}

// 使用
fn main() {
    let mut publisher = NewsPublisher::new();

    let email_sub = Rc::new(EmailSubscriber::new("user@example.com"));
    let sms_sub = Rc::new(SmsSubscriber::new("+1234567890"));

    publisher.attach(email_sub);
    publisher.attach(sms_sub);

    publisher.publish("Rust 1.93 Released!");
    // 输出:
    // Publishing news: Rust 1.93 Released!
    // [Email to user@example.com] Event: news, Data: Rust 1.93 Released!
    // [SMS to +1234567890] Event: news, Data: Rust 1.93 Released!
}
```

### 4.4 迭代器模式 (Iterator Pattern)

Rust的标准库已经内置了强大的迭代器支持。

```rust
// 自定义集合
pub struct TreeNode<T> {
    value: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

impl<T> TreeNode<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            left: None,
            right: None,
        }
    }
}

// 中序遍历迭代器
pub struct InOrderIterator<'a, T> {
    stack: Vec<&'a TreeNode<T>>,
    current: Option<&'a TreeNode<T>>,
}

impl<'a, T> InOrderIterator<'a, T> {
    pub fn new(root: &'a TreeNode<T>) -> Self {
        Self {
            stack: Vec::new(),
            current: Some(root),
        }
    }
}

impl<'a, T> Iterator for InOrderIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.current {
            self.stack.push(node);
            self.current = node.left.as_deref();
        }

        if let Some(node) = self.stack.pop() {
            self.current = node.right.as_deref();
            Some(&node.value)
        } else {
            None
        }
    }
}

// 实现IntoIterator trait
pub struct Tree<T>(Option<Box<TreeNode<T>>>);

impl<T> Tree<T> {
    pub fn iter(&self) -> TreeIter<'_, T> {
        TreeIter {
            stack: Vec::new(),
            current: self.0.as_deref(),
        }
    }
}

pub struct TreeIter<'a, T> {
    stack: Vec<&'a TreeNode<T>>,
    current: Option<&'a TreeNode<T>>,
}

impl<'a, T> Iterator for TreeIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.current {
            self.stack.push(node);
            self.current = node.left.as_deref();
        }

        self.stack.pop().map(|node| {
            self.current = node.right.as_deref();
            &node.value
        })
    }
}

// 使用示例
fn main() {
    let mut root = TreeNode::new(5);
    root.left = Some(Box::new(TreeNode::new(3)));
    root.right = Some(Box::new(TreeNode::new(7)));

    let iter = InOrderIterator::new(&root);
    for value in iter {
        println!("{}", value);  // 输出: 3, 5, 7
    }
}
```

### 4.5 状态模式 (State Pattern)

```rust
// 状态接口
trait State {
    fn handle(&self, context: &mut Context);
    fn name(&self) -> &str;
}

// 上下文
pub struct Context {
    state: Box<dyn State>,
}

impl Context {
    pub fn new(state: Box<dyn State>) -> Self {
        Self { state }
    }

    pub fn request(&mut self) {
        self.state.handle(self);
    }

    pub fn transition_to(&mut self, state: Box<dyn State>) {
        println!("Transitioning from {} to {}",
            self.state.name(), state.name());
        self.state = state;
    }
}

// 具体状态
pub struct ConcreteStateA;
impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) {
        println!("State A handling request");
        context.transition_to(Box::new(ConcreteStateB));
    }
    fn name(&self) -> &str {
        "State A"
    }
}

pub struct ConcreteStateB;
impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) {
        println!("State B handling request");
        context.transition_to(Box::new(ConcreteStateA));
    }
    fn name(&self) -> &str {
        "State B"
    }
}

// 使用
fn main() {
    let mut context = Context::new(Box::new(ConcreteStateA));
    context.request();
    context.request();
    context.request();
}
```

### 4.6 模板方法模式 (Template Method)

```rust
// 抽象类
trait DataMiner {
    // 模板方法
    fn mine(&self, path: &str) {
        let file = self.open_file(path);
        let raw_data = self.extract_data(&file);
        let data = self.parse_data(&raw_data);
        let analysis = self.analyze_data(&data);
        self.send_report(&analysis);
        self.close_file(&file);
    }

    // 必须由子类实现的抽象方法
    fn open_file(&self, path: &str) -> String;
    fn close_file(&self, file: &str);
    fn extract_data(&self, file: &str) -> Vec<u8>;

    // 默认实现
    fn parse_data(&self, raw_data: &[u8]) -> Vec<String> {
        String::from_utf8_lossy(raw_data)
            .lines()
            .map(|s| s.to_string())
            .collect()
    }

    fn analyze_data(&self, data: &[String]) -> String {
        format!("Analyzed {} records", data.len())
    }

    fn send_report(&self, analysis: &str) {
        println!("Sending report: {}", analysis);
    }
}

// 具体实现：PDF数据挖掘器
pub struct PdfDataMiner;

impl DataMiner for PdfDataMiner {
    fn open_file(&self, path: &str) -> String {
        println!("Opening PDF: {}", path);
        path.to_string()
    }

    fn close_file(&self, file: &str) {
        println!("Closing PDF: {}", file);
    }

    fn extract_data(&self, file: &str) -> Vec<u8> {
        println!("Extracting PDF data from: {}", file);
        b"PDF content here".to_vec()
    }
}

// 具体实现：CSV数据挖掘器
pub struct CsvDataMiner;

impl DataMiner for CsvDataMiner {
    fn open_file(&self, path: &str) -> String {
        println!("Opening CSV: {}", path);
        path.to_string()
    }

    fn close_file(&self, file: &str) {
        println!("Closing CSV: {}", file);
    }

    fn extract_data(&self, file: &str) -> Vec<u8> {
        println!("Extracting CSV data from: {}", file);
        b"col1,col2\nval1,val2".to_vec()
    }
}

// 使用
fn main() {
    let pdf_miner = PdfDataMiner;
    pdf_miner.mine("data.pdf");

    println!("---");

    let csv_miner = CsvDataMiner;
    csv_miner.mine("data.csv");
}
```

### 4.7 责任链模式 (Chain of Responsibility)

```rust
// 处理者接口
pub trait Handler {
    fn set_next(&mut self, handler: Box<dyn Handler>) -> &mut dyn Handler;
    fn handle(&self, request: &str) -> Option<String>;
}

// 基础处理者
pub struct BaseHandler {
    next: Option<Box<dyn Handler>>,
}

impl BaseHandler {
    pub fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for BaseHandler {
    fn set_next(&mut self, handler: Box<dyn Handler>) -> &mut dyn Handler {
        self.next = Some(handler);
        self
    }

    fn handle(&self, request: &str) -> Option<String> {
        if let Some(ref next) = self.next {
            next.handle(request)
        } else {
            None
        }
    }
}

// 具体处理者：认证
pub struct AuthHandler {
    base: BaseHandler,
}

impl AuthHandler {
    pub fn new() -> Self {
        Self {
            base: BaseHandler::new(),
        }
    }
}

impl Handler for AuthHandler {
    fn set_next(&mut self, handler: Box<dyn Handler>) -> &mut dyn Handler {
        self.base.set_next(handler)
    }

    fn handle(&self, request: &str) -> Option<String> {
        if request.contains("token") {
            println!("AuthHandler: Authentication passed");
            self.base.handle(request)
        } else {
            Some("Error: Authentication failed".to_string())
        }
    }
}

// 具体处理者：限流
pub struct ThrottlingHandler {
    base: BaseHandler,
    requests: RefCell<u32>,
}

impl ThrottlingHandler {
    pub fn new() -> Self {
        Self {
            base: BaseHandler::new(),
            requests: RefCell::new(0),
        }
    }
}

impl Handler for ThrottlingHandler {
    fn set_next(&mut self, handler: Box<dyn Handler>) -> &mut dyn Handler {
        self.base.set_next(handler)
    }

    fn handle(&self, request: &str) -> Option<String> {
        let mut requests = self.requests.borrow_mut();
        *requests += 1;

        if *requests > 100 {
            Some("Error: Too many requests".to_string())
        } else {
            println!("ThrottlingHandler: Request {} allowed", *requests);
            self.base.handle(request)
        }
    }
}

// 使用
use std::cell::RefCell;

fn main() {
    let mut auth = AuthHandler::new();
    let throttle = ThrottlingHandler::new();

    auth.set_next(Box::new(throttle));

    let result = auth.handle("request with token");
    println!("{:?}", result);
}
```

### 4.8 访问者模式 (Visitor Pattern)

```rust
// 元素接口
pub trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者接口
pub trait Visitor {
    fn visit_circle(&self, circle: &Circle);
    fn visit_rectangle(&self, rectangle: &Rectangle);
}

// 具体元素：圆形
pub struct Circle {
    pub radius: f64,
    pub x: f64,
    pub y: f64,
}

impl Element for Circle {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_circle(self);
    }
}

// 具体元素：矩形
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
    pub x: f64,
    pub y: f64,
}

impl Element for Rectangle {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_rectangle(self);
    }
}

// 具体访问者：面积计算
pub struct AreaCalculator;

impl Visitor for AreaCalculator {
    fn visit_circle(&self, circle: &Circle) {
        let area = std::f64::consts::PI * circle.radius * circle.radius;
        println!("Circle area: {:.2}", area);
    }

    fn visit_rectangle(&self, rectangle: &Rectangle) {
        let area = rectangle.width * rectangle.height;
        println!("Rectangle area: {:.2}", area);
    }
}

// 具体访问者：JSON导出
pub struct JsonExporter;

impl Visitor for JsonExporter {
    fn visit_circle(&self, circle: &Circle) {
        println!(
            "{{ \"type\": \"circle\", \"radius\": {}, \"x\": {}, \"y\": {} }}",
            circle.radius, circle.x, circle.y
        );
    }

    fn visit_rectangle(&self, rectangle: &Rectangle) {
        println!(
            "{{ \"type\": \"rectangle\", \"width\": {}, \"height\": {}, \"x\": {}, \"y\": {} }}",
            rectangle.width, rectangle.height, rectangle.x, rectangle.y
        );
    }
}

// 对象结构
pub struct ShapeCollection {
    shapes: Vec<Box<dyn Element>>,
}

impl ShapeCollection {
    pub fn new() -> Self {
        Self { shapes: Vec::new() }
    }

    pub fn add(&mut self, shape: Box<dyn Element>) {
        self.shapes.push(shape);
    }

    pub fn accept(&self, visitor: &dyn Visitor) {
        for shape in &self.shapes {
            shape.accept(visitor);
        }
    }
}

// 使用
fn main() {
    let mut shapes = ShapeCollection::new();
    shapes.add(Box::new(Circle { radius: 5.0, x: 0.0, y: 0.0 }));
    shapes.add(Box::new(Rectangle { width: 10.0, height: 20.0, x: 1.0, y: 1.0 }));

    println!("=== Area Calculation ===");
    shapes.accept(&AreaCalculator);

    println!("\n=== JSON Export ===");
    shapes.accept(&JsonExporter);
}
```

### 4.9 备忘录模式 (Memento Pattern)

```rust
// 备忘录
#[derive(Clone)]
pub struct EditorMemento {
    content: String,
    cursor_position: usize,
}

impl EditorMemento {
    fn new(content: String, cursor_position: usize) -> Self {
        Self { content, cursor_position }
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }
}

// 原发器
pub struct Editor {
    content: String,
    cursor_position: usize,
}

impl Editor {
    pub fn new() -> Self {
        Self {
            content: String::new(),
            cursor_position: 0,
        }
    }

    pub fn type_text(&mut self, text: &str) {
        self.content.insert_str(self.cursor_position, text);
        self.cursor_position += text.len();
    }

    pub fn delete(&mut self, length: usize) {
        let start = self.cursor_position;
        let end = (start + length).min(self.content.len());
        self.content.drain(start..end);
    }

    pub fn save(&self) -> EditorMemento {
        EditorMemento::new(self.content.clone(), self.cursor_position)
    }

    pub fn restore(&mut self, memento: &EditorMemento) {
        self.content = memento.content.clone();
        self.cursor_position = memento.cursor_position;
    }

    pub fn get_content(&self) -> &str {
        &self.content
    }
}

// 管理者
pub struct History {
    mementos: Vec<EditorMemento>,
    current: usize,
}

impl History {
    pub fn new() -> Self {
        Self {
            mementos: Vec::new(),
            current: 0,
        }
    }

    pub fn push(&mut self, memento: EditorMemento) {
        // 如果在历史中间，删除后面的记录
        self.mementos.truncate(self.current);
        self.mementos.push(memento);
        self.current += 1;
    }

    pub fn undo(&self) -> Option<&EditorMemento> {
        if self.current > 0 {
            self.current -= 1;
            self.mementos.get(self.current)
        } else {
            None
        }
    }

    pub fn redo(&mut self) -> Option<&EditorMemento> {
        if self.current < self.mementos.len() {
            let memento = self.mementos.get(self.current);
            self.current += 1;
            memento
        } else {
            None
        }
    }
}

// 使用
fn main() {
    let mut editor = Editor::new();
    let mut history = History::new();

    editor.type_text("Hello");
    history.push(editor.save());

    editor.type_text(" World");
    history.push(editor.save());

    println!("Current: {}", editor.get_content());

    if let Some(memento) = history.undo() {
        editor.restore(memento);
        println!("After undo: {}", editor.get_content());
    }
}
```

### 4.10 中介者模式 (Mediator Pattern)

```rust
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::HashMap;

// 中介者接口
pub trait ChatMediator {
    fn send_message(&self, message: &str, sender_id: usize);
    fn add_user(&mut self, user: Rc<RefCell<dyn User>>);
}

// 同事接口
pub trait User {
    fn get_id(&self) -> usize;
    fn get_name(&self) -> &str;
    fn send(&self, message: &str);
    fn receive(&self, message: &str, from: &str);
    fn set_mediator(&mut self, mediator: Rc<RefCell<dyn ChatMediator>>);
}

// 具体中介者
pub struct ChatRoom {
    users: HashMap<usize, Rc<RefCell<dyn User>>>,
}

impl ChatRoom {
    pub fn new() -> Self {
        Self {
            users: HashMap::new(),
        }
    }
}

impl ChatMediator for ChatRoom {
    fn send_message(&self, message: &str, sender_id: usize) {
        let sender_name = self.users
            .get(&sender_id)
            .map(|u| u.borrow().get_name().to_string())
            .unwrap_or_default();

        for (id, user) in &self.users {
            if *id != sender_id {
                user.borrow().receive(message, &sender_name);
            }
        }
    }

    fn add_user(&mut self, user: Rc<RefCell<dyn User>>) {
        let id = user.borrow().get_id();
        self.users.insert(id, user);
    }
}

// 具体同事
pub struct ChatUser {
    id: usize,
    name: String,
    mediator: Option<Rc<RefCell<dyn ChatMediator>>>,
}

impl ChatUser {
    pub fn new(id: usize, name: &str) -> Self {
        Self {
            id,
            name: name.to_string(),
            mediator: None,
        }
    }
}

impl User for ChatUser {
    fn get_id(&self) -> usize {
        self.id
    }

    fn get_name(&self) -> &str {
        &self.name
    }

    fn send(&self, message: &str) {
        println!("{} sends: {}", self.name, message);
        if let Some(ref mediator) = self.mediator {
            mediator.borrow().send_message(message, self.id);
        }
    }

    fn receive(&self, message: &str, from: &str) {
        println!("{} receives from {}: {}", self.name, from, message);
    }

    fn set_mediator(&mut self, mediator: Rc<RefCell<dyn ChatMediator>>) {
        self.mediator = Some(mediator);
    }
}

// 使用
fn main() {
    let mediator = Rc::new(RefCell::new(ChatRoom::new()));

    let user1 = Rc::new(RefCell::new(ChatUser::new(1, "Alice")));
    let user2 = Rc::new(RefCell::new(ChatUser::new(2, "Bob")));
    let user3 = Rc::new(RefCell::new(ChatUser::new(3, "Charlie")));

    user1.borrow_mut().set_mediator(mediator.clone());
    user2.borrow_mut().set_mediator(mediator.clone());
    user3.borrow_mut().set_mediator(mediator.clone());

    mediator.borrow_mut().add_user(user1.clone());
    mediator.borrow_mut().add_user(user2.clone());
    mediator.borrow_mut().add_user(user3.clone());

    user1.borrow().send("Hello everyone!");
    // 输出:
    // Alice sends: Hello everyone!
    // Bob receives from Alice: Hello everyone!
    // Charlie receives from Alice: Hello everyone!
}
```

---

## 5. Rust特有模式

### 5.1 Newtype模式

Newtype模式用于给现有类型提供不同的语义。

```rust
// 基本Newtype
pub struct UserId(u64);
pub struct OrderId(u64);

impl UserId {
    pub fn new(id: u64) -> Self {
        Self(id)
    }

    pub fn value(&self) -> u64 {
        self.0
    }
}

// 防止不同ID类型混淆
fn process_user(id: UserId) { /* ... */ }
fn process_order(id: OrderId) { /* ... */ }

// 实现Deref提供透明访问
use std::ops::Deref;

pub struct EmailAddress(String);

impl Deref for EmailAddress {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl EmailAddress {
    pub fn new(email: &str) -> Result<Self, String> {
        if email.contains('@') {
            Ok(Self(email.to_string()))
        } else {
            Err("Invalid email".to_string())
        }
    }
}

// 使用
fn main() {
    let user_id = UserId::new(123);
    let order_id = OrderId(456);

    // process_user(order_id);  // 编译错误！类型不匹配
    process_user(user_id);  // OK

    let email = EmailAddress::new("user@example.com").unwrap();
    println!("Email: {}", &*email);  // 可以直接当作str使用
}
```

### 5.2 类型状态模式 (Type State Pattern)

类型状态模式利用Rust的类型系统在编译时保证状态转换的正确性。

```rust
use std::marker::PhantomData;

// 状态标记
trait ConnectionState {}
pub struct Disconnected;
pub struct Connected;
pub struct Authenticated;

impl ConnectionState for Disconnected {}
impl ConnectionState for Connected {}
impl ConnectionState for Authenticated {}

// 连接类型根据状态参数化
pub struct Connection<S: ConnectionState> {
    addr: String,
    _state: PhantomData<S>,
}

// 断开状态下的操作
impl Connection<Disconnected> {
    pub fn new(addr: &str) -> Self {
        Self {
            addr: addr.to_string(),
            _state: PhantomData,
        }
    }

    pub fn connect(self) -> Connection<Connected> {
        println!("Connecting to {}", self.addr);
        Connection {
            addr: self.addr,
            _state: PhantomData,
        }
    }
}

// 连接状态下的操作
impl Connection<Connected> {
    pub fn authenticate(self, token: &str) -> Connection<Authenticated> {
        println!("Authenticating with token {}", token);
        Connection {
            addr: self.addr,
            _state: PhantomData,
        }
    }

    pub fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnecting from {}", self.addr);
        Connection {
            addr: self.addr,
            _state: PhantomData,
        }
    }
}

// 认证后的操作
impl Connection<Authenticated> {
    pub fn query(&self, sql: &str) -> Vec<String> {
        println!("Executing query on {}: {}", self.addr, sql);
        vec!["result".to_string()]
    }

    pub fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnecting from {}", self.addr);
        Connection {
            addr: self.addr,
            _state: PhantomData,
        }
    }
}

// 使用
fn main() {
    let conn = Connection::new("localhost:5432");

    // 状态转换链
    let results = conn
        .connect()           // Connection<Connected>
        .authenticate("secret")  // Connection<Authenticated>
        .query("SELECT * FROM users");

    println!("{:?}", results);

    // 以下代码编译错误：
    // let conn = Connection::new("localhost");
    // conn.query("SELECT *");  // 错误：Disconnected状态不能query
}
```

### 5.3 RAII守卫模式

RAII（资源获取即初始化）是Rust的核心模式，守卫模式是其重要应用。

```rust
use std::ops::{Deref, DerefMut};
use std::sync::Mutex;

// 互斥锁守卫示例
pub struct ResourceGuard<'a, T> {
    resource: &'a mut T,
    cleanup: Box<dyn FnOnce()>,
}

impl<'a, T> ResourceGuard<'a, T> {
    pub fn new<F>(resource: &'a mut T, cleanup: F) -> Self
    where
        F: FnOnce() + 'static,
    {
        Self {
            resource,
            cleanup: Box::new(cleanup),
        }
    }
}

impl<'a, T> Deref for ResourceGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.resource
    }
}

impl<'a, T> DerefMut for ResourceGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.resource
    }
}

impl<'a, T> Drop for ResourceGuard<'a, T> {
    fn drop(&mut self) {
        // 在drop中执行清理
        let cleanup = std::mem::replace(&mut self.cleanup, Box::new(|| {}));
        cleanup();
    }
}

// 文件锁示例
pub struct FileLock {
    path: String,
}

impl FileLock {
    pub fn new(path: &str) -> Self {
        Self {
            path: path.to_string(),
        }
    }

    pub fn lock(&self) -> FileLockGuard {
        println!("Locking file: {}", self.path);
        FileLockGuard {
            path: self.path.clone(),
        }
    }
}

pub struct FileLockGuard {
    path: String,
}

impl Drop for FileLockGuard {
    fn drop(&mut self) {
        println!("Unlocking file: {}", self.path);
    }
}

// 作用域守卫
pub struct ScopeGuard<F: FnOnce()> {
    cleanup: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    pub fn new(cleanup: F) -> Self {
        Self {
            cleanup: Some(cleanup),
        }
    }

    pub fn dismiss(mut self) {
        self.cleanup.take();
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(cleanup) = self.cleanup.take() {
            cleanup();
        }
    }
}

// 使用示例
fn main() {
    let lock = FileLock::new("/tmp/myfile.lock");
    {
        let _guard = lock.lock();
        // 文件已锁定
        println!("Working with locked file...");
    }  // 守卫drop，文件解锁

    // 作用域守卫
    let guard = ScopeGuard::new(|| {
        println!("Cleanup executed");
    });
    // guard.dismiss();  // 如果需要取消清理
}  // 清理在这里执行
```

### 5.4 折中方案模式 (Default Trait)

```rust
// 实现Default trait提供合理的默认值
#[derive(Debug, Clone)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub timeout: std::time::Duration,
    pub enable_ssl: bool,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            workers: num_cpus::get(),
            timeout: std::time::Duration::from_secs(30),
            enable_ssl: false,
        }
    }
}

impl ServerConfig {
    // Builder风格的配置方法
    pub fn with_host(mut self, host: &str) -> Self {
        self.host = host.to_string();
        self
    }

    pub fn with_port(mut self, port: u16) -> Self {
        self.port = port;
        self
    }

    pub fn with_workers(mut self, workers: usize) -> Self {
        self.workers = workers;
        self
    }
}

// 使用
fn main() {
    // 使用默认值
    let config1 = ServerConfig::default();

    // 覆盖部分默认值
    let config2 = ServerConfig::default()
        .with_host("0.0.0.0")
        .with_port(3000);

    println!("{:?}", config2);
}
```

---

## 6. 反模式与陷阱

### 6.1 过度使用 `Rc<RefCell<T>>`

```rust
// 反模式：过度使用运行时检查
pub struct BadDesign {
    data: Rc<RefCell<Vec<i32>>>,
}

// 更好的设计：利用借用检查器
pub struct GoodDesign<'a> {
    data: &'a mut Vec<i32>,
}
```

### 6.2 忽视所有权转移

```rust
// 错误：使用已移动的值
pub fn bad_usage() {
    let s = String::from("hello");
    let t = s;
    // println!("{}", s);  // 编译错误：s已被移动
}
```

### 6.3 过度泛型化

```rust
// 过度设计
pub fn over_generic<T, U, V, F>(a: T, b: U, f: F) -> V
where
    T: Clone + Send + Sync + 'static,
    U: Default + Debug,
    V: From<T> + From<U>,
    F: FnOnce(T, U) -> V,
{
    // ...
}

// 适度设计
pub fn simple_generic<T: Into<String>>(input: T) -> String {
    input.into()
}
```

### 6.4 过度使用unwrap()

```rust
// 反模式
let value = some_option.unwrap();

// 更好
let value = some_option.expect("critical invariant violated");
// 或
let value = some_option?;
// 或
let value = some_option.unwrap_or(default);
```

---

## 7. 最佳实践总结

### 7.1 设计模式选择指南

| 场景 | 推荐模式 | 原因 |
|------|---------|------|
| 复杂对象创建 | Builder + Type State | 编译时验证 + 流畅API |
| 运行时多态 | Strategy | Trait对象替代继承 |
| 撤销/重做 | Command | 封装操作为对象 |
| 资源管理 | RAII守卫 | 自动清理保证 |
| 状态机 | Type State | 编译时状态验证 |
| 事件通知 | Observer | Weak引用避免循环 |

### 7.2 Rust设计原则

1. **优先使用组合**：Trait系统比继承更灵活
2. **利用类型系统**：在编译时捕获错误
3. **最小化运行时开销**：零成本抽象
4. **显式资源管理**：RAII模式
5. **避免内部可变性**：优先使用不可变借用

---

## 参考文献

1. Rust Design Patterns: <https://rust-unofficial.github.io/patterns/>
2. Rust API Guidelines: <https://rust-lang.github.io/api-guidelines/>
3. Effective Rust: <https://www.lurklurk.org/effective-rust/>
4. Design Patterns: Elements of Reusable Object-Oriented Software (GoF)
5. Programming Rust, 2nd Edition
