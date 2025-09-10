# Rust设计模式与架构实践

## 目录

- [Rust设计模式与架构实践](#rust设计模式与架构实践)
  - [目录](#目录)
  - [1. 设计模式概述](#1-设计模式概述)
    - [1.1 Rust中的设计模式特点](#11-rust中的设计模式特点)
    - [1.2 模式分类](#12-模式分类)
  - [2. 创建型模式](#2-创建型模式)
    - [2.1 单例模式 (Singleton)](#21-单例模式-singleton)
    - [2.2 建造者模式 (Builder)](#22-建造者模式-builder)
    - [2.3 工厂模式 (Factory)](#23-工厂模式-factory)
  - [3. 结构型模式](#3-结构型模式)
    - [3.1 适配器模式 (Adapter)](#31-适配器模式-adapter)
    - [3.2 装饰器模式 (Decorator)](#32-装饰器模式-decorator)
    - [3.3 外观模式 (Facade)](#33-外观模式-facade)
  - [4. 行为型模式](#4-行为型模式)
    - [4.1 观察者模式 (Observer)](#41-观察者模式-observer)
    - [4.2 策略模式 (Strategy)](#42-策略模式-strategy)
    - [4.3 命令模式 (Command)](#43-命令模式-command)
  - [5. 并发模式](#5-并发模式)
    - [5.1 生产者-消费者模式](#51-生产者-消费者模式)
    - [5.2 线程池模式](#52-线程池模式)
  - [6. 函数式模式](#6-函数式模式)
    - [6.1 高阶函数模式](#61-高阶函数模式)
    - [6.2 单子模式](#62-单子模式)
  - [7. 架构模式](#7-架构模式)
    - [7.1 分层架构模式](#71-分层架构模式)
    - [7.2 微服务架构模式](#72-微服务架构模式)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 错误处理模式](#81-错误处理模式)
    - [8.2 配置管理模式](#82-配置管理模式)
  - [总结](#总结)

## 1. 设计模式概述

设计模式是软件工程中解决常见问题的可重用解决方案。在Rust中，由于所有权系统和类型系统的特性，许多传统设计模式需要重新思考或采用不同的实现方式。

### 1.1 Rust中的设计模式特点

- **所有权安全**：利用Rust的所有权系统避免内存安全问题
- **类型安全**：利用强类型系统在编译时捕获错误
- **零成本抽象**：设计模式不引入运行时开销
- **函数式编程**：结合函数式编程范式

### 1.2 模式分类

| 模式类型 | 特点 | Rust实现重点 |
|---------|------|-------------|
| 创建型 | 对象创建 | 使用智能指针和RAII |
| 结构型 | 对象组合 | 利用trait和泛型 |
| 行为型 | 对象交互 | 使用闭包和trait对象 |
| 并发型 | 并发安全 | 利用Send/Sync trait |
| 函数式 | 函数组合 | 使用迭代器和闭包 |

## 2. 创建型模式

### 2.1 单例模式 (Singleton)

在Rust中，单例模式可以通过多种方式实现：

```rust
use std::sync::{Mutex, Once};
use std::sync::atomic::{AtomicPtr, Ordering};

/// 线程安全的单例模式实现
pub struct Singleton {
    data: String,
}

impl Singleton {
    // 使用Once确保只初始化一次
    static INIT: Once = Once::new();
    static mut INSTANCE: *mut Singleton = 0 as *mut _;

    pub fn get_instance() -> &'static Singleton {
        unsafe {
            INIT.call_once(|| {
                let instance = Box::new(Singleton {
                    data: "Singleton instance".to_string(),
                });
                INSTANCE = Box::into_raw(instance);
            });
            &*INSTANCE
        }
    }

    pub fn get_data(&self) -> &str {
        &self.data
    }
}

/// 使用AtomicPtr的线程安全单例
pub struct AtomicSingleton {
    data: String,
}

impl AtomicSingleton {
    static INSTANCE: AtomicPtr<AtomicSingleton> = AtomicPtr::new(std::ptr::null_mut());

    pub fn get_instance() -> &'static AtomicSingleton {
        let instance = Self::INSTANCE.load(Ordering::Acquire);
        if instance.is_null() {
            let new_instance = Box::new(AtomicSingleton {
                data: "Atomic Singleton".to_string(),
            });
            let new_ptr = Box::into_raw(new_instance);
            
            match Self::INSTANCE.compare_exchange(
                std::ptr::null_mut(),
                new_ptr,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => unsafe { &*new_ptr },
                Err(_) => {
                    // 其他线程已经创建了实例
                    unsafe {
                        let _ = Box::from_raw(new_ptr);
                        &*Self::INSTANCE.load(Ordering::Acquire)
                    }
                }
            }
        } else {
            unsafe { &*instance }
        }
    }
}

/// 使用lazy_static的简单实现
#[cfg(feature = "lazy_static")]
use lazy_static::lazy_static;

#[cfg(feature = "lazy_static")]
lazy_static! {
    static ref LAZY_SINGLETON: Mutex<Singleton> = Mutex::new(Singleton {
        data: "Lazy Singleton".to_string(),
    });
}
```

### 2.2 建造者模式 (Builder)

Rust中的建造者模式通常使用方法链：

```rust
/// 复杂对象的建造者模式
#[derive(Debug, Clone)]
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub password: String,
    pub database: String,
    pub max_connections: u32,
    pub timeout: u64,
    pub ssl_enabled: bool,
}

impl DatabaseConfig {
    pub fn new() -> DatabaseConfigBuilder {
        DatabaseConfigBuilder::new()
    }
}

/// 建造者
pub struct DatabaseConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    username: Option<String>,
    password: Option<String>,
    database: Option<String>,
    max_connections: Option<u32>,
    timeout: Option<u64>,
    ssl_enabled: Option<bool>,
}

impl DatabaseConfigBuilder {
    pub fn new() -> Self {
        Self {
            host: None,
            port: None,
            username: None,
            password: None,
            database: None,
            max_connections: None,
            timeout: None,
            ssl_enabled: None,
        }
    }

    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    pub fn username(mut self, username: impl Into<String>) -> Self {
        self.username = Some(username.into());
        self
    }

    pub fn password(mut self, password: impl Into<String>) -> Self {
        self.password = Some(password.into());
        self
    }

    pub fn database(mut self, database: impl Into<String>) -> Self {
        self.database = Some(database.into());
        self
    }

    pub fn max_connections(mut self, max_connections: u32) -> Self {
        self.max_connections = Some(max_connections);
        self
    }

    pub fn timeout(mut self, timeout: u64) -> Self {
        self.timeout = Some(timeout);
        self
    }

    pub fn ssl_enabled(mut self, ssl_enabled: bool) -> Self {
        self.ssl_enabled = Some(ssl_enabled);
        self
    }

    pub fn build(self) -> Result<DatabaseConfig, String> {
        Ok(DatabaseConfig {
            host: self.host.ok_or("Host is required")?,
            port: self.port.ok_or("Port is required")?,
            username: self.username.ok_or("Username is required")?,
            password: self.password.ok_or("Password is required")?,
            database: self.database.ok_or("Database is required")?,
            max_connections: self.max_connections.unwrap_or(10),
            timeout: self.timeout.unwrap_or(30),
            ssl_enabled: self.ssl_enabled.unwrap_or(false),
        })
    }
}

/// 使用示例
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_database_config_builder() {
        let config = DatabaseConfig::new()
            .host("localhost")
            .port(5432)
            .username("admin")
            .password("secret")
            .database("mydb")
            .max_connections(20)
            .timeout(60)
            .ssl_enabled(true)
            .build()
            .unwrap();

        assert_eq!(config.host, "localhost");
        assert_eq!(config.port, 5432);
        assert_eq!(config.max_connections, 20);
        assert!(config.ssl_enabled);
    }
}
```

### 2.3 工厂模式 (Factory)

```rust
/// 抽象产品
pub trait Product {
    fn name(&self) -> &str;
    fn price(&self) -> f64;
}

/// 具体产品
pub struct Book {
    name: String,
    price: f64,
}

impl Product for Book {
    fn name(&self) -> &str {
        &self.name
    }

    fn price(&self) -> f64 {
        self.price
    }
}

pub struct Electronics {
    name: String,
    price: f64,
}

impl Product for Electronics {
    fn name(&self) -> &str {
        &self.name
    }

    fn price(&self) -> f64 {
        self.price
    }
}

/// 产品类型
#[derive(Debug, Clone)]
pub enum ProductType {
    Book,
    Electronics,
}

/// 工厂trait
pub trait ProductFactory {
    fn create_product(&self, product_type: ProductType, name: String, price: f64) -> Box<dyn Product>;
}

/// 具体工厂
pub struct ConcreteProductFactory;

impl ProductFactory for ConcreteProductFactory {
    fn create_product(&self, product_type: ProductType, name: String, price: f64) -> Box<dyn Product> {
        match product_type {
            ProductType::Book => Box::new(Book { name, price }),
            ProductType::Electronics => Box::new(Electronics { name, price }),
        }
    }
}

/// 使用函数式方法的工厂
pub fn create_product(product_type: ProductType, name: String, price: f64) -> Box<dyn Product> {
    match product_type {
        ProductType::Book => Box::new(Book { name, price }),
        ProductType::Electronics => Box::new(Electronics { name, price }),
    }
}
```

## 3. 结构型模式

### 3.1 适配器模式 (Adapter)

```rust
/// 目标接口
pub trait Target {
    fn request(&self) -> String;
}

/// 被适配者
pub struct Adaptee {
    specific_request: String,
}

impl Adaptee {
    pub fn new(specific_request: String) -> Self {
        Self { specific_request }
    }

    pub fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.specific_request)
    }
}

/// 适配器
pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 将Adaptee的接口适配到Target接口
        self.adaptee.specific_request()
    }
}

/// 使用示例
#[cfg(test)]
mod adapter_tests {
    use super::*;

    #[test]
    fn test_adapter() {
        let adaptee = Adaptee::new("Hello".to_string());
        let adapter = Adapter::new(adaptee);
        
        assert_eq!(adapter.request(), "Adaptee: Hello");
    }
}
```

### 3.2 装饰器模式 (Decorator)

```rust
/// 组件接口
pub trait Component {
    fn operation(&self) -> String;
}

/// 具体组件
pub struct ConcreteComponent {
    data: String,
}

impl ConcreteComponent {
    pub fn new(data: String) -> Self {
        Self { data }
    }
}

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        self.data.clone()
    }
}

/// 装饰器基类
pub struct Decorator {
    component: Box<dyn Component>,
}

impl Decorator {
    pub fn new(component: Box<dyn Component>) -> Self {
        Self { component }
    }
}

impl Component for Decorator {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

/// 具体装饰器
pub struct ConcreteDecoratorA {
    decorator: Decorator,
}

impl ConcreteDecoratorA {
    pub fn new(component: Box<dyn Component>) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl Component for ConcreteDecoratorA {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorA({})", self.decorator.operation())
    }
}

pub struct ConcreteDecoratorB {
    decorator: Decorator,
}

impl ConcreteDecoratorB {
    pub fn new(component: Box<dyn Component>) -> Self {
        Self {
            decorator: Decorator::new(component),
        }
    }
}

impl Component for ConcreteDecoratorB {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorB({})", self.decorator.operation())
    }
}
```

### 3.3 外观模式 (Facade)

```rust
/// 子系统A
pub struct SubsystemA;

impl SubsystemA {
    pub fn operation_a(&self) -> String {
        "SubsystemA operation".to_string()
    }
}

/// 子系统B
pub struct SubsystemB;

impl SubsystemB {
    pub fn operation_b(&self) -> String {
        "SubsystemB operation".to_string()
    }
}

/// 子系统C
pub struct SubsystemC;

impl SubsystemC {
    pub fn operation_c(&self) -> String {
        "SubsystemC operation".to_string()
    }
}

/// 外观
pub struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC,
}

impl Facade {
    pub fn new() -> Self {
        Self {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC,
        }
    }

    pub fn operation(&self) -> String {
        format!(
            "Facade: {} + {} + {}",
            self.subsystem_a.operation_a(),
            self.subsystem_b.operation_b(),
            self.subsystem_c.operation_c()
        )
    }
}
```

## 4. 行为型模式

### 4.1 观察者模式 (Observer)

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};

/// 观察者trait
pub trait Observer {
    fn update(&self, data: &str);
}

/// 具体观察者
pub struct ConcreteObserver {
    name: String,
}

impl ConcreteObserver {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, data: &str) {
        println!("Observer {} received: {}", self.name, data);
    }
}

/// 主题trait
pub trait Subject {
    fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>);
    fn detach(&mut self, observer: Weak<RefCell<dyn Observer>>);
    fn notify(&self, data: &str);
}

/// 具体主题
pub struct ConcreteSubject {
    observers: Vec<Weak<RefCell<dyn Observer>>>,
    data: String,
}

impl ConcreteSubject {
    pub fn new() -> Self {
        Self {
            observers: Vec::new(),
            data: String::new(),
        }
    }

    pub fn set_data(&mut self, data: String) {
        self.data = data;
        self.notify(&self.data);
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>) {
        self.observers.push(Rc::downgrade(&observer));
    }

    fn detach(&mut self, observer: Weak<RefCell<dyn Observer>>) {
        self.observers.retain(|o| !Weak::ptr_eq(o, &observer));
    }

    fn notify(&self, data: &str) {
        for observer in &self.observers {
            if let Some(observer) = observer.upgrade() {
                observer.borrow().update(data);
            }
        }
    }
}
```

### 4.2 策略模式 (Strategy)

```rust
/// 策略trait
pub trait Strategy {
    fn execute(&self, data: &str) -> String;
}

/// 具体策略A
pub struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn execute(&self, data: &str) -> String {
        format!("StrategyA: {}", data.to_uppercase())
    }
}

/// 具体策略B
pub struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn execute(&self, data: &str) -> String {
        format!("StrategyB: {}", data.to_lowercase())
    }
}

/// 上下文
pub struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    pub fn new(strategy: Box<dyn Strategy>) -> Self {
        Self { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }

    pub fn execute_strategy(&self, data: &str) -> String {
        self.strategy.execute(data)
    }
}
```

### 4.3 命令模式 (Command)

```rust
/// 命令trait
pub trait Command {
    fn execute(&self);
    fn undo(&self);
}

/// 接收者
pub struct Receiver {
    data: String,
}

impl Receiver {
    pub fn new() -> Self {
        Self {
            data: String::new(),
        }
    }

    pub fn action(&mut self, data: String) {
        self.data = data;
        println!("Receiver: {}", self.data);
    }

    pub fn get_data(&self) -> &str {
        &self.data
    }
}

/// 具体命令
pub struct ConcreteCommand {
    receiver: Rc<RefCell<Receiver>>,
    data: String,
    previous_data: String,
}

impl ConcreteCommand {
    pub fn new(receiver: Rc<RefCell<Receiver>>, data: String) -> Self {
        let previous_data = receiver.borrow().get_data().to_string();
        Self {
            receiver,
            data,
            previous_data,
        }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) {
        self.receiver.borrow_mut().action(self.data.clone());
    }

    fn undo(&self) {
        self.receiver.borrow_mut().action(self.previous_data.clone());
    }
}

/// 调用者
pub struct Invoker {
    commands: Vec<Box<dyn Command>>,
}

impl Invoker {
    pub fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }

    pub fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }

    pub fn execute_all(&self) {
        for command in &self.commands {
            command.execute();
        }
    }
}
```

## 5. 并发模式

### 5.1 生产者-消费者模式

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// 消息类型
#[derive(Debug, Clone)]
pub struct Message {
    pub id: u32,
    pub data: String,
}

/// 生产者
pub struct Producer {
    sender: mpsc::Sender<Message>,
}

impl Producer {
    pub fn new(sender: mpsc::Sender<Message>) -> Self {
        Self { sender }
    }

    pub fn produce(&self, id: u32, data: String) -> Result<(), mpsc::SendError<Message>> {
        let message = Message { id, data };
        self.sender.send(message)?;
        Ok(())
    }
}

/// 消费者
pub struct Consumer {
    receiver: mpsc::Receiver<Message>,
}

impl Consumer {
    pub fn new(receiver: mpsc::Receiver<Message>) -> Self {
        Self { receiver }
    }

    pub fn consume(&self) -> Result<Message, mpsc::RecvError> {
        self.receiver.recv()
    }
}

/// 生产者-消费者系统
pub struct ProducerConsumerSystem {
    producer: Producer,
    consumer: Consumer,
}

impl ProducerConsumerSystem {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        Self {
            producer: Producer::new(sender),
            consumer: Consumer::new(receiver),
        }
    }

    pub fn run(&self) {
        let producer = self.producer.clone();
        let consumer = self.consumer.clone();

        // 生产者线程
        let producer_handle = thread::spawn(move || {
            for i in 0..10 {
                producer.produce(i, format!("Message {}", i)).unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });

        // 消费者线程
        let consumer_handle = thread::spawn(move || {
            loop {
                match consumer.consume() {
                    Ok(message) => println!("Consumed: {:?}", message),
                    Err(_) => break,
                }
            }
        });

        producer_handle.join().unwrap();
        consumer_handle.join().unwrap();
    }
}

impl Clone for Producer {
    fn clone(&self) -> Self {
        Self {
            sender: self.sender.clone(),
        }
    }
}

impl Clone for Consumer {
    fn clone(&self) -> Self {
        Self {
            receiver: self.receiver.clone(),
        }
    }
}
```

### 5.2 线程池模式

```rust
use std::sync::{Arc, Mutex};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// 任务trait
pub trait Task: Send + 'static {
    fn execute(self);
}

/// 具体任务
pub struct PrintTask {
    message: String,
}

impl PrintTask {
    pub fn new(message: String) -> Self {
        Self { message }
    }
}

impl Task for PrintTask {
    fn execute(self) {
        println!("Task executed: {}", self.message);
        thread::sleep(Duration::from_millis(100));
    }
}

/// 线程池
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Box<dyn Task>>,
}

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self { workers, sender }
    }

    pub fn execute<T>(&self, task: T) -> Result<(), mpsc::SendError<Box<dyn Task>>>
    where
        T: Task,
    {
        self.sender.send(Box::new(task))
    }
}

/// 工作线程
struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Box<dyn Task>>>>) -> Self {
        let thread = thread::spawn(move || loop {
            let task = receiver.lock().unwrap().recv();
            match task {
                Ok(task) => {
                    println!("Worker {} got a task", id);
                    task.execute();
                }
                Err(_) => {
                    println!("Worker {} disconnected", id);
                    break;
                }
            }
        });

        Self { id, thread }
    }
}
```

## 6. 函数式模式

### 6.1 高阶函数模式

```rust
/// 高阶函数示例
pub fn map<T, U, F>(items: Vec<T>, f: F) -> Vec<U>
where
    F: Fn(T) -> U,
{
    items.into_iter().map(f).collect()
}

pub fn filter<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
where
    F: Fn(&T) -> bool,
{
    items.into_iter().filter(predicate).collect()
}

pub fn reduce<T, F>(items: Vec<T>, initial: T, f: F) -> T
where
    F: Fn(T, T) -> T,
{
    items.into_iter().fold(initial, f)
}

/// 函数组合
pub fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(B) -> C,
    G: Fn(A) -> B,
{
    move |x| f(g(x))
}

/// 柯里化
pub fn curry<A, B, C, F>(f: F) -> impl Fn(A) -> impl Fn(B) -> C
where
    F: Fn(A, B) -> C,
{
    move |a| move |b| f(a, b)
}

/// 使用示例
#[cfg(test)]
mod functional_tests {
    use super::*;

    #[test]
    fn test_higher_order_functions() {
        let numbers = vec![1, 2, 3, 4, 5];
        
        // Map
        let doubled = map(numbers.clone(), |x| x * 2);
        assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
        
        // Filter
        let evens = filter(numbers.clone(), |&x| x % 2 == 0);
        assert_eq!(evens, vec![2, 4]);
        
        // Reduce
        let sum = reduce(numbers, 0, |acc, x| acc + x);
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_function_composition() {
        let add_one = |x: i32| x + 1;
        let multiply_by_two = |x: i32| x * 2;
        
        let composed = compose(multiply_by_two, add_one);
        assert_eq!(composed(5), 12); // (5 + 1) * 2 = 12
    }
}
```

### 6.2 单子模式

```rust
/// Maybe单子
#[derive(Debug, Clone, PartialEq)]
pub enum Maybe<T> {
    Just(T),
    Nothing,
}

impl<T> Maybe<T> {
    pub fn new(value: T) -> Self {
        Maybe::Just(value)
    }

    pub fn nothing() -> Self {
        Maybe::Nothing
    }

    /// Functor的map操作
    pub fn map<U, F>(self, f: F) -> Maybe<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Maybe::Just(value) => Maybe::Just(f(value)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    /// Monad的bind操作
    pub fn bind<U, F>(self, f: F) -> Maybe<U>
    where
        F: FnOnce(T) -> Maybe<U>,
    {
        match self {
            Maybe::Just(value) => f(value),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    /// 提取值或返回默认值
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Maybe::Just(value) => value,
            Maybe::Nothing => default,
        }
    }
}

/// Result单子
pub type Result<T, E> = std::result::Result<T, E>;

pub trait Monad<T> {
    type Output<U>;
    
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(T) -> Self::Output<U>;
}

impl<T, E> Monad<T> for Result<T, E> {
    type Output<U> = Result<U, E>;
    
    fn bind<U, F>(self, f: F) -> Result<U, E>
    where
        F: FnOnce(T) -> Result<U, E>,
    {
        match self {
            Ok(value) => f(value),
            Err(e) => Err(e),
        }
    }
}
```

## 7. 架构模式

### 7.1 分层架构模式

```rust
/// 表示层
pub mod presentation {
    use super::business::BusinessService;
    use super::data::DataService;

    pub struct PresentationLayer {
        business_service: BusinessService,
    }

    impl PresentationLayer {
        pub fn new() -> Self {
            Self {
                business_service: BusinessService::new(),
            }
        }

        pub fn handle_request(&self, request: &str) -> String {
            let result = self.business_service.process_request(request);
            format!("Response: {}", result)
        }
    }
}

/// 业务层
pub mod business {
    use super::data::DataService;

    pub struct BusinessService {
        data_service: DataService,
    }

    impl BusinessService {
        pub fn new() -> Self {
            Self {
                data_service: DataService::new(),
            }
        }

        pub fn process_request(&self, request: &str) -> String {
            // 业务逻辑处理
            let data = self.data_service.get_data(request);
            format!("Processed: {}", data)
        }
    }
}

/// 数据层
pub mod data {
    pub struct DataService;

    impl DataService {
        pub fn new() -> Self {
            Self
        }

        pub fn get_data(&self, key: &str) -> String {
            // 模拟数据访问
            format!("Data for key: {}", key)
        }
    }
}
```

### 7.2 微服务架构模式

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

/// 服务注册表
#[derive(Debug, Clone)]
pub struct ServiceRegistry {
    services: HashMap<String, ServiceInfo>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInfo {
    pub name: String,
    pub url: String,
    pub version: String,
    pub health_check_url: String,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: HashMap::new(),
        }
    }

    pub fn register(&mut self, service: ServiceInfo) {
        self.services.insert(service.name.clone(), service);
    }

    pub fn discover(&self, service_name: &str) -> Option<&ServiceInfo> {
        self.services.get(service_name)
    }

    pub fn list_services(&self) -> Vec<&ServiceInfo> {
        self.services.values().collect()
    }
}

/// 服务发现
pub struct ServiceDiscovery {
    registry: ServiceRegistry,
}

impl ServiceDiscovery {
    pub fn new(registry: ServiceRegistry) -> Self {
        Self { registry }
    }

    pub fn find_service(&self, name: &str) -> Option<&ServiceInfo> {
        self.registry.discover(name)
    }
}

/// API网关
pub struct ApiGateway {
    service_discovery: ServiceDiscovery,
    routes: HashMap<String, String>,
}

impl ApiGateway {
    pub fn new(service_discovery: ServiceDiscovery) -> Self {
        Self {
            service_discovery,
            routes: HashMap::new(),
        }
    }

    pub fn add_route(&mut self, path: String, service_name: String) {
        self.routes.insert(path, service_name);
    }

    pub fn route_request(&self, path: &str) -> Option<&ServiceInfo> {
        if let Some(service_name) = self.routes.get(path) {
            self.service_discovery.find_service(service_name)
        } else {
            None
        }
    }
}
```

## 8. 最佳实践

### 8.1 错误处理模式

```rust
use thiserror::Error;

/// 自定义错误类型
#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),
    
    #[error("Custom error: {message}")]
    Custom { message: String },
    
    #[error("Validation error: {field}")]
    Validation { field: String },
}

/// 结果类型别名
pub type AppResult<T> = Result<T, AppError>;

/// 错误处理示例
pub struct ErrorHandler;

impl ErrorHandler {
    pub fn handle_error(error: AppError) -> String {
        match error {
            AppError::Io(e) => format!("IO错误: {}", e),
            AppError::Parse(e) => format!("解析错误: {}", e),
            AppError::Custom { message } => format!("自定义错误: {}", message),
            AppError::Validation { field } => format!("验证错误: {}", field),
        }
    }

    pub fn process_data(data: &str) -> AppResult<i32> {
        if data.is_empty() {
            return Err(AppError::Validation {
                field: "data".to_string(),
            });
        }

        data.parse::<i32>()
            .map_err(|e| AppError::Parse(e))
    }
}
```

### 8.2 配置管理模式

```rust
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

/// 配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    pub database: DatabaseConfig,
    pub server: ServerConfig,
    pub logging: LoggingConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub database: String,
    pub username: String,
    pub password: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub file: Option<String>,
}

/// 配置管理器
pub struct ConfigManager;

impl ConfigManager {
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Config, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let config: Config = toml::from_str(&content)?;
        Ok(config)
    }

    pub fn load_from_env() -> Result<Config, Box<dyn std::error::Error>> {
        Ok(Config {
            database: DatabaseConfig {
                host: std::env::var("DB_HOST").unwrap_or_else(|_| "localhost".to_string()),
                port: std::env::var("DB_PORT")
                    .unwrap_or_else(|_| "5432".to_string())
                    .parse()?,
                database: std::env::var("DB_NAME").unwrap_or_else(|_| "app".to_string()),
                username: std::env::var("DB_USER").unwrap_or_else(|_| "user".to_string()),
                password: std::env::var("DB_PASSWORD").unwrap_or_else(|_| "password".to_string()),
            },
            server: ServerConfig {
                host: std::env::var("SERVER_HOST").unwrap_or_else(|_| "0.0.0.0".to_string()),
                port: std::env::var("SERVER_PORT")
                    .unwrap_or_else(|_| "8080".to_string())
                    .parse()?,
                workers: std::env::var("WORKERS")
                    .unwrap_or_else(|_| "4".to_string())
                    .parse()?,
            },
            logging: LoggingConfig {
                level: std::env::var("LOG_LEVEL").unwrap_or_else(|_| "info".to_string()),
                file: std::env::var("LOG_FILE").ok(),
            },
        })
    }
}
```

## 总结

本文档展示了Rust中各种设计模式的实现方式，包括：

1. **创建型模式**：单例、建造者、工厂模式
2. **结构型模式**：适配器、装饰器、外观模式
3. **行为型模式**：观察者、策略、命令模式
4. **并发模式**：生产者-消费者、线程池模式
5. **函数式模式**：高阶函数、单子模式
6. **架构模式**：分层架构、微服务架构
7. **最佳实践**：错误处理、配置管理

这些模式充分利用了Rust的所有权系统、类型系统和并发特性，提供了安全、高效的解决方案。
在实际开发中，应该根据具体需求选择合适的模式，并考虑Rust特有的语言特性。
