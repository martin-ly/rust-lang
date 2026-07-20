# 设计模式常见问题解答

## 目录

- [基础概念](#基础概念)
- [创建型模式](#创建型模式)
- [结构型模式](#结构型模式)
- [行为型模式](#行为型模式)
- [Rust特定模式](#rust特定模式)
- [最佳实践](#最佳实践)

## 基础概念

### Q1: 什么是设计模式？

**A:** 设计模式是解决常见设计问题的可重用解决方案：

```rust
// 设计模式示例：单例模式
use std::sync::{Mutex, Once};
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct Singleton {
    data: String,
}

impl Singleton {
    fn new(data: String) -> Self {
        Self { data }
    }
    
    pub fn get_instance() -> &'static Singleton {
        static INSTANCE: AtomicPtr<Singleton> = AtomicPtr::new(std::ptr::null_mut());
        static ONCE: Once = Once::new();
        
        ONCE.call_once(|| {
            let instance = Box::new(Singleton::new("Singleton data".to_string()));
            INSTANCE.store(Box::into_raw(instance), Ordering::SeqCst);
        });
        
        unsafe { &*INSTANCE.load(Ordering::SeqCst) }
    }
    
    pub fn get_data(&self) -> &str {
        &self.data
    }
}
```

### Q2: 设计模式如何分类？

**A:** 设计模式分为三类：

```rust
// 1. 创建型模式 - 对象创建
// 工厂模式
trait Product {
    fn operation(&self);
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) {
        println!("Product A operation");
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) {
        println!("Product B operation");
    }
}

enum ProductType {
    A,
    B,
}

struct Factory;
impl Factory {
    fn create_product(product_type: ProductType) -> Box<dyn Product> {
        match product_type {
            ProductType::A => Box::new(ConcreteProductA),
            ProductType::B => Box::new(ConcreteProductB),
        }
    }
}

// 2. 结构型模式 - 对象组合
// 适配器模式
trait Target {
    fn request(&self);
}

struct Adaptee;
impl Adaptee {
    fn specific_request(&self) {
        println!("Specific request");
    }
}

struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) {
        self.adaptee.specific_request();
    }
}

// 3. 行为型模式 - 对象交互
// 观察者模式
use std::rc::Rc;
use std::cell::RefCell;

trait Observer {
    fn update(&self, data: &str);
}

struct ConcreteObserver {
    name: String,
}

impl Observer for ConcreteObserver {
    fn update(&self, data: &str) {
        println!("Observer {} received: {}", self.name, data);
    }
}

struct Subject {
    observers: Vec<Rc<RefCell<dyn Observer>>>,
}

impl Subject {
    fn new() -> Self {
        Self { observers: Vec::new() }
    }
    
    fn attach(&mut self, observer: Rc<RefCell<dyn Observer>>) {
        self.observers.push(observer);
    }
    
    fn notify(&self, data: &str) {
        for observer in &self.observers {
            observer.borrow().update(data);
        }
    }
}
```

## 创建型模式

### Q3: 如何实现建造者模式？

**A:** 建造者模式的实现：

```rust
#[derive(Debug, Clone)]
pub struct Computer {
    pub cpu: String,
    pub memory: String,
    pub storage: String,
    pub graphics: Option<String>,
}

pub struct ComputerBuilder {
    cpu: Option<String>,
    memory: Option<String>,
    storage: Option<String>,
    graphics: Option<String>,
}

impl ComputerBuilder {
    pub fn new() -> Self {
        Self {
            cpu: None,
            memory: None,
            storage: None,
            graphics: None,
        }
    }
    
    pub fn cpu(mut self, cpu: String) -> Self {
        self.cpu = Some(cpu);
        self
    }
    
    pub fn memory(mut self, memory: String) -> Self {
        self.memory = Some(memory);
        self
    }
    
    pub fn storage(mut self, storage: String) -> Self {
        self.storage = Some(storage);
        self
    }
    
    pub fn graphics(mut self, graphics: String) -> Self {
        self.graphics = Some(graphics);
        self
    }
    
    pub fn build(self) -> Result<Computer, String> {
        Ok(Computer {
            cpu: self.cpu.ok_or("CPU is required")?,
            memory: self.memory.ok_or("Memory is required")?,
            storage: self.storage.ok_or("Storage is required")?,
            graphics: self.graphics,
        })
    }
}

// 使用
fn main() {
    let computer = ComputerBuilder::new()
        .cpu("Intel i7".to_string())
        .memory("16GB DDR4".to_string())
        .storage("512GB SSD".to_string())
        .graphics("NVIDIA RTX 3080".to_string())
        .build()
        .unwrap();
    
    println!("{:?}", computer);
}
```

### Q4: 如何实现原型模式？

**A:** 原型模式的实现：

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Document {
    pub title: String,
    pub content: String,
    pub author: String,
}

impl Document {
    pub fn new(title: String, content: String, author: String) -> Self {
        Self { title, content, author }
    }
    
    pub fn clone_with_title(&self, new_title: String) -> Self {
        Self {
            title: new_title,
            content: self.content.clone(),
            author: self.author.clone(),
        }
    }
}

pub struct DocumentManager {
    templates: HashMap<String, Document>,
}

impl DocumentManager {
    pub fn new() -> Self {
        Self {
            templates: HashMap::new(),
        }
    }
    
    pub fn register_template(&mut self, name: String, template: Document) {
        self.templates.insert(name, template);
    }
    
    pub fn create_document(&self, template_name: &str, title: String) -> Option<Document> {
        self.templates.get(template_name)
            .map(|template| template.clone_with_title(title))
    }
}

// 使用
fn main() {
    let mut manager = DocumentManager::new();
    
    let template = Document::new(
        "Template".to_string(),
        "This is a template document.".to_string(),
        "Admin".to_string(),
    );
    
    manager.register_template("report".to_string(), template);
    
    let document = manager.create_document("report", "Monthly Report".to_string())
        .unwrap();
    
    println!("{:?}", document);
}
```

## 结构型模式

### Q5: 如何实现装饰器模式？

**A:** 装饰器模式的实现：

```rust
trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

struct SimpleCoffee;
impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 {
        2.0
    }
    
    fn description(&self) -> String {
        "Simple coffee".to_string()
    }
}

struct CoffeeDecorator {
    coffee: Box<dyn Coffee>,
}

impl CoffeeDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        Self { coffee }
    }
}

impl Coffee for CoffeeDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost()
    }
    
    fn description(&self) -> String {
        self.coffee.description()
    }
}

struct MilkDecorator {
    coffee: Box<dyn Coffee>,
}

impl MilkDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        Self { coffee }
    }
}

impl Coffee for MilkDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost() + 0.5
    }
    
    fn description(&self) -> String {
        format!("{}, milk", self.coffee.description())
    }
}

struct SugarDecorator {
    coffee: Box<dyn Coffee>,
}

impl SugarDecorator {
    fn new(coffee: Box<dyn Coffee>) -> Self {
        Self { coffee }
    }
}

impl Coffee for SugarDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost() + 0.2
    }
    
    fn description(&self) -> String {
        format!("{}, sugar", self.coffee.description())
    }
}

// 使用
fn main() {
    let coffee = Box::new(SimpleCoffee);
    let coffee_with_milk = Box::new(MilkDecorator::new(coffee));
    let coffee_with_milk_and_sugar = Box::new(SugarDecorator::new(coffee_with_milk));
    
    println!("{}: ${:.2}", coffee_with_milk_and_sugar.description(), coffee_with_milk_and_sugar.cost());
}
```

### Q6: 如何实现外观模式？

**A:** 外观模式的实现：

```rust
// 子系统组件
struct CPU {
    name: String,
}

impl CPU {
    fn new(name: String) -> Self {
        Self { name }
    }
    
    fn start(&self) {
        println!("CPU {} starting", self.name);
    }
    
    fn stop(&self) {
        println!("CPU {} stopping", self.name);
    }
}

struct Memory {
    size: u32,
}

impl Memory {
    fn new(size: u32) -> Self {
        Self { size }
    }
    
    fn load(&self) {
        println!("Loading {}GB memory", self.size);
    }
    
    fn unload(&self) {
        println!("Unloading memory");
    }
}

struct HardDrive {
    capacity: u32,
}

impl HardDrive {
    fn new(capacity: u32) -> Self {
        Self { capacity }
    }
    
    fn read(&self) {
        println!("Reading from {}GB hard drive", self.capacity);
    }
    
    fn write(&self) {
        println!("Writing to hard drive");
    }
}

// 外观
struct ComputerFacade {
    cpu: CPU,
    memory: Memory,
    hard_drive: HardDrive,
}

impl ComputerFacade {
    fn new() -> Self {
        Self {
            cpu: CPU::new("Intel i7".to_string()),
            memory: Memory::new(16),
            hard_drive: HardDrive::new(512),
        }
    }
    
    fn start_computer(&self) {
        println!("Starting computer...");
        self.cpu.start();
        self.memory.load();
        self.hard_drive.read();
        println!("Computer started successfully");
    }
    
    fn stop_computer(&self) {
        println!("Stopping computer...");
        self.cpu.stop();
        self.memory.unload();
        self.hard_drive.write();
        println!("Computer stopped successfully");
    }
}

// 使用
fn main() {
    let computer = ComputerFacade::new();
    computer.start_computer();
    computer.stop_computer();
}
```

## 行为型模式

### Q7: 如何实现策略模式？

**A:** 策略模式的实现：

```rust
trait PaymentStrategy {
    fn pay(&self, amount: f64) -> String;
}

struct CreditCardPayment {
    card_number: String,
}

impl CreditCardPayment {
    fn new(card_number: String) -> Self {
        Self { card_number }
    }
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> String {
        format!("Paid ${:.2} using credit card ending in {}", amount, &self.card_number[12..])
    }
}

struct PayPalPayment {
    email: String,
}

impl PayPalPayment {
    fn new(email: String) -> Self {
        Self { email }
    }
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> String {
        format!("Paid ${:.2} using PayPal account {}", amount, self.email)
    }
}

struct BankTransferPayment {
    account_number: String,
}

impl BankTransferPayment {
    fn new(account_number: String) -> Self {
        Self { account_number }
    }
}

impl PaymentStrategy for BankTransferPayment {
    fn pay(&self, amount: f64) -> String {
        format!("Paid ${:.2} using bank transfer to account {}", amount, self.account_number)
    }
}

struct PaymentContext {
    strategy: Box<dyn PaymentStrategy>,
}

impl PaymentContext {
    fn new(strategy: Box<dyn PaymentStrategy>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = strategy;
    }
    
    fn execute_payment(&self, amount: f64) -> String {
        self.strategy.pay(amount)
    }
}

// 使用
fn main() {
    let credit_card = Box::new(CreditCardPayment::new("1234567890123456".to_string()));
    let mut payment_context = PaymentContext::new(credit_card);
    
    println!("{}", payment_context.execute_payment(100.0));
    
    let paypal = Box::new(PayPalPayment::new("user@example.com".to_string()));
    payment_context.set_strategy(paypal);
    
    println!("{}", payment_context.execute_payment(50.0));
}
```

### Q8: 如何实现命令模式？

**A:** 命令模式的实现：

```rust
// 命令接口
trait Command {
    fn execute(&self);
    fn undo(&self);
}

// 接收者
struct Light {
    is_on: bool,
}

impl Light {
    fn new() -> Self {
        Self { is_on: false }
    }
    
    fn turn_on(&mut self) {
        self.is_on = true;
        println!("Light is on");
    }
    
    fn turn_off(&mut self) {
        self.is_on = false;
        println!("Light is off");
    }
}

// 具体命令
struct LightOnCommand {
    light: std::rc::Rc<std::cell::RefCell<Light>>,
}

impl LightOnCommand {
    fn new(light: std::rc::Rc<std::cell::RefCell<Light>>) -> Self {
        Self { light }
    }
}

impl Command for LightOnCommand {
    fn execute(&self) {
        self.light.borrow_mut().turn_on();
    }
    
    fn undo(&self) {
        self.light.borrow_mut().turn_off();
    }
}

struct LightOffCommand {
    light: std::rc::Rc<std::cell::RefCell<Light>>,
}

impl LightOffCommand {
    fn new(light: std::rc::Rc<std::cell::RefCell<Light>>) -> Self {
        Self { light }
    }
}

impl Command for LightOffCommand {
    fn execute(&self) {
        self.light.borrow_mut().turn_off();
    }
    
    fn undo(&self) {
        self.light.borrow_mut().turn_on();
    }
}

// 调用者
struct RemoteControl {
    commands: Vec<Box<dyn Command>>,
    last_command: Option<Box<dyn Command>>,
}

impl RemoteControl {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
            last_command: None,
        }
    }
    
    fn set_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
    
    fn press_button(&mut self, index: usize) {
        if let Some(command) = self.commands.get(index) {
            command.execute();
            self.last_command = Some(Box::new(*command));
        }
    }
    
    fn press_undo(&self) {
        if let Some(command) = &self.last_command {
            command.undo();
        }
    }
}

// 使用
fn main() {
    let light = std::rc::Rc::new(std::cell::RefCell::new(Light::new()));
    
    let mut remote = RemoteControl::new();
    remote.set_command(Box::new(LightOnCommand::new(light.clone())));
    remote.set_command(Box::new(LightOffCommand::new(light.clone())));
    
    remote.press_button(0); // 开灯
    remote.press_button(1); // 关灯
    remote.press_undo();    // 撤销
}
```

## Rust特定模式

### Q9: 如何在Rust中实现单例模式？

**A:** Rust中的单例模式实现：

```rust
use std::sync::{Mutex, Once};
use std::sync::atomic::{AtomicPtr, Ordering};

pub struct Singleton {
    data: String,
}

impl Singleton {
    fn new(data: String) -> Self {
        Self { data }
    }
    
    pub fn get_instance() -> &'static Singleton {
        static INSTANCE: AtomicPtr<Singleton> = AtomicPtr::new(std::ptr::null_mut());
        static ONCE: Once = Once::new();
        
        ONCE.call_once(|| {
            let instance = Box::new(Singleton::new("Singleton data".to_string()));
            INSTANCE.store(Box::into_raw(instance), Ordering::SeqCst);
        });
        
        unsafe { &*INSTANCE.load(Ordering::SeqCst) }
    }
    
    pub fn get_data(&self) -> &str {
        &self.data
    }
}

// 使用
fn main() {
    let instance1 = Singleton::get_instance();
    let instance2 = Singleton::get_instance();
    
    println!("{}", instance1.get_data());
    println!("{}", instance2.get_data());
    
    // 两个实例是同一个对象
    assert!(std::ptr::eq(instance1, instance2));
}
```

### Q10: 如何在Rust中实现建造者模式？

**A:** Rust中的建造者模式实现：

```rust
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: String,
    pub url: String,
    pub headers: Vec<(String, String)>,
    pub body: Option<String>,
}

pub struct HttpRequestBuilder {
    method: Option<String>,
    url: Option<String>,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            headers: Vec::new(),
            body: None,
        }
    }
    
    pub fn method(mut self, method: String) -> Self {
        self.method = Some(method);
        self
    }
    
    pub fn url(mut self, url: String) -> Self {
        self.url = Some(url);
        self
    }
    
    pub fn header(mut self, key: String, value: String) -> Self {
        self.headers.push((key, value));
        self
    }
    
    pub fn body(mut self, body: String) -> Self {
        self.body = Some(body);
        self
    }
    
    pub fn build(self) -> Result<HttpRequest, String> {
        Ok(HttpRequest {
            method: self.method.ok_or("Method is required")?,
            url: self.url.ok_or("URL is required")?,
            headers: self.headers,
            body: self.body,
        })
    }
}

// 使用
fn main() {
    let request = HttpRequestBuilder::new()
        .method("GET".to_string())
        .url("https://api.example.com/users".to_string())
        .header("Content-Type".to_string(), "application/json".to_string())
        .header("Authorization".to_string(), "Bearer token".to_string())
        .build()
        .unwrap();
    
    println!("{:?}", request);
}
```

## 最佳实践

### Q11: 设计模式的最佳实践是什么？

**A:** 设计模式的最佳实践：

```rust
// 1. 优先使用组合而非继承
trait Flyable {
    fn fly(&self);
}

trait Quackable {
    fn quack(&self);
}

struct Duck {
    fly_behavior: Box<dyn Flyable>,
    quack_behavior: Box<dyn Quackable>,
}

impl Duck {
    fn new(fly_behavior: Box<dyn Flyable>, quack_behavior: Box<dyn Quackable>) -> Self {
        Self { fly_behavior, quack_behavior }
    }
    
    fn perform_fly(&self) {
        self.fly_behavior.fly();
    }
    
    fn perform_quack(&self) {
        self.quack_behavior.quack();
    }
}

// 2. 使用特征定义接口
trait Shape {
    fn area(&self) -> f64;
    fn perimeter(&self) -> f64;
}

struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
    
    fn perimeter(&self) -> f64 {
        2.0 * std::f64::consts::PI * self.radius
    }
}

// 3. 使用枚举处理状态
enum State {
    Idle,
    Running,
    Paused,
    Stopped,
}

impl State {
    fn next(&self) -> State {
        match self {
            State::Idle => State::Running,
            State::Running => State::Paused,
            State::Paused => State::Running,
            State::Stopped => State::Idle,
        }
    }
}

// 4. 使用Result处理错误
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}
```

## 总结

设计模式是解决常见设计问题的可重用解决方案。在Rust中，设计模式的应用需要考虑语言特性，如所有权、借用检查和特征系统。通过合理使用设计模式，可以提高代码的可维护性、可扩展性和可重用性。

## 相关资源

- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
- [Design Patterns: Elements of Reusable Object-Oriented Software](https://en.wikipedia.org/wiki/Design_Patterns)
- [Head First Design Patterns](https://www.oreilly.com/library/view/head-first-design/0596007124/)
