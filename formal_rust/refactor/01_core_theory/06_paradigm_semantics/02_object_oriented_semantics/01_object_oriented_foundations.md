# Rust面向对象编程基础语义

## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: 2025-08-11  
**最后更新**: 2025-08-11  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---



**文档编号**: RFTS-06-OOF  
**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 核心理论文档

---

## 目录

- [Rust面向对象编程基础语义](#rust面向对象编程基础语义)
  - [目录](#目录)
  - [1. 面向对象编程理论基础](#1-面向对象编程理论基础)
    - [1.1 面向对象语义模型](#11-面向对象语义模型)
    - [1.2 Rust中的面向对象特性](#12-rust中的面向对象特性)
  - [2. 封装与数据抽象](#2-封装与数据抽象)
    - [2.1 结构体封装](#21-结构体封装)
    - [2.2 模块化封装](#22-模块化封装)
  - [3. 继承与组合](#3-继承与组合)
    - [3.1 trait继承](#31-trait继承)
    - [3.2 组合模式](#32-组合模式)
  - [4. 多态与动态分发](#4-多态与动态分发)
    - [4.1 trait对象多态](#41-trait对象多态)
    - [4.2 泛型多态](#42-泛型多态)
  - [总结](#总结)

## 1. 面向对象编程理论基础

### 1.1 面向对象语义模型

**定义 1.1** (面向对象编程系统)  
面向对象编程系统是一个五元组 $OOP = (O, M, I, P, E)$，其中：

- $O$ 是对象集合
- $M$ 是方法集合
- $I$ 是接口集合
- $P$ 是多态关系集合
- $E: O × M × I → Behavior$ 是行为函数

**定理 1.1** (面向对象正确性)  
面向对象系统保证：

1. **封装性**: $∀o ∈ O, internal\_state(o)$ 只能通过定义的接口访问
2. **继承性**: $∀o_1, o_2 ∈ O, inherits(o_1, o_2) ⟹ methods(o_2) ⊆ methods(o_1)$
3. **多态性**: $∀m ∈ M, dispatch(m, o)$ 根据对象类型正确分发

### 1.2 Rust中的面向对象特性

**定义 1.2** (Rust面向对象模型)  
Rust通过以下机制实现面向对象：

- **结构体**: 数据封装
- **impl块**: 方法定义
- **trait**: 接口抽象
- **trait对象**: 动态分发

## 2. 封装与数据抽象

### 2.1 结构体封装

```rust
// 数据封装的实现
pub struct BankAccount {
    account_number: String,
    balance: f64,
    is_active: bool,
}

impl BankAccount {
    // 构造函数
    pub fn new(account_number: String, initial_balance: f64) -> Result<Self, String> {
        if initial_balance < 0.0 {
            return Err("Initial balance cannot be negative".to_string());
        }
        
        Ok(BankAccount {
            account_number,
            balance: initial_balance,
            is_active: true,
        })
    }
    
    // 公共接口方法
    pub fn get_balance(&self) -> f64 {
        if self.is_active {
            self.balance
        } else {
            0.0
        }
    }
    
    pub fn deposit(&mut self, amount: f64) -> Result<(), String> {
        if !self.is_active {
            return Err("Account is not active".to_string());
        }
        
        if amount <= 0.0 {
            return Err("Deposit amount must be positive".to_string());
        }
        
        self.balance += amount;
        Ok(())
    }
    
    pub fn withdraw(&mut self, amount: f64) -> Result<(), String> {
        if !self.is_active {
            return Err("Account is not active".to_string());
        }
        
        if amount <= 0.0 {
            return Err("Withdrawal amount must be positive".to_string());
        }
        
        if amount > self.balance {
            return Err("Insufficient funds".to_string());
        }
        
        self.balance -= amount;
        Ok(())
    }
    
    pub fn close_account(&mut self) {
        self.is_active = false;
        self.balance = 0.0;
    }
    
    // 私有辅助方法
    fn validate_transaction(&self, amount: f64) -> bool {
        self.is_active && amount > 0.0
    }
}

// 访问控制示例
mod banking {
    pub struct SecureAccount {
        pub account_id: u64,           // 公共字段
        balance: f64,                  // 私有字段
        pin: u32,                      // 私有字段
    }
    
    impl SecureAccount {
        pub fn new(account_id: u64, pin: u32) -> Self {
            Self {
                account_id,
                balance: 0.0,
                pin,
            }
        }
        
        pub fn authenticate(&self, input_pin: u32) -> bool {
            self.pin == input_pin
        }
        
        pub fn get_balance(&self, pin: u32) -> Option<f64> {
            if self.authenticate(pin) {
                Some(self.balance)
            } else {
                None
            }
        }
        
        pub fn transfer(&mut self, amount: f64, pin: u32) -> Result<(), String> {
            if !self.authenticate(pin) {
                return Err("Authentication failed".to_string());
            }
            
            if amount > self.balance {
                return Err("Insufficient funds".to_string());
            }
            
            self.balance -= amount;
            Ok(())
        }
    }
}

// 封装示例使用
fn demonstrate_encapsulation() {
    let mut account = BankAccount::new("ACC001".to_string(), 1000.0).unwrap();
    
    println!("Initial balance: {}", account.get_balance());
    
    // 通过公共接口操作
    account.deposit(500.0).unwrap();
    println!("After deposit: {}", account.get_balance());
    
    account.withdraw(200.0).unwrap();
    println!("After withdrawal: {}", account.get_balance());
    
    // 私有字段无法直接访问
    // account.balance = 999999.0; // 编译错误
    
    account.close_account();
    println!("After closing: {}", account.get_balance());
}
```

**定理 2.1** (封装正确性)  
封装机制保证：

1. **数据隐藏**: 私有字段不能被外部直接访问
2. **接口一致性**: 公共方法提供一致的访问接口
3. **状态完整性**: 对象状态只能通过定义的方法修改

### 2.2 模块化封装

```rust
// 模块化的面向对象设计
pub mod geometry {
    use std::f64::consts::PI;
    
    // 抽象基础
    pub trait Shape {
        fn area(&self) -> f64;
        fn perimeter(&self) -> f64;
        fn name(&self) -> &'static str;
    }
    
    // 具体实现
    pub struct Circle {
        radius: f64,
    }
    
    impl Circle {
        pub fn new(radius: f64) -> Result<Self, String> {
            if radius <= 0.0 {
                Err("Radius must be positive".to_string())
            } else {
                Ok(Circle { radius })
            }
        }
        
        pub fn get_radius(&self) -> f64 {
            self.radius
        }
        
        pub fn set_radius(&mut self, radius: f64) -> Result<(), String> {
            if radius <= 0.0 {
                Err("Radius must be positive".to_string())
            } else {
                self.radius = radius;
                Ok(())
            }
        }
    }
    
    impl Shape for Circle {
        fn area(&self) -> f64 {
            PI * self.radius * self.radius
        }
        
        fn perimeter(&self) -> f64 {
            2.0 * PI * self.radius
        }
        
        fn name(&self) -> &'static str {
            "Circle"
        }
    }
    
    pub struct Rectangle {
        width: f64,
        height: f64,
    }
    
    impl Rectangle {
        pub fn new(width: f64, height: f64) -> Result<Self, String> {
            if width <= 0.0 || height <= 0.0 {
                Err("Width and height must be positive".to_string())
            } else {
                Ok(Rectangle { width, height })
            }
        }
        
        pub fn get_dimensions(&self) -> (f64, f64) {
            (self.width, self.height)
        }
        
        pub fn set_dimensions(&mut self, width: f64, height: f64) -> Result<(), String> {
            if width <= 0.0 || height <= 0.0 {
                Err("Width and height must be positive".to_string())
            } else {
                self.width = width;
                self.height = height;
                Ok(())
            }
        }
    }
    
    impl Shape for Rectangle {
        fn area(&self) -> f64 {
            self.width * self.height
        }
        
        fn perimeter(&self) -> f64 {
            2.0 * (self.width + self.height)
        }
        
        fn name(&self) -> &'static str {
            "Rectangle"
        }
    }
}

// 使用模块化封装
fn demonstrate_modular_encapsulation() {
    use geometry::{Shape, Circle, Rectangle};
    
    let circle = Circle::new(5.0).unwrap();
    let rectangle = Rectangle::new(4.0, 6.0).unwrap();
    
    let shapes: Vec<&dyn Shape> = vec![&circle, &rectangle];
    
    for shape in shapes {
        println!("{}: area = {:.2}, perimeter = {:.2}", 
                 shape.name(), shape.area(), shape.perimeter());
    }
}
```

**定理 2.2** (模块化封装正确性)  
模块化封装保证：

1. **命名空间隔离**: 不同模块的实现不会冲突
2. **接口统一**: 相同trait的实现提供统一接口
3. **实现隐藏**: 内部实现细节对外部不可见

## 3. 继承与组合

### 3.1 trait继承

```rust
// trait继承机制
trait Animal {
    fn name(&self) -> &str;
    fn make_sound(&self) -> &str;
    
    // 默认实现
    fn describe(&self) -> String {
        format!("{} makes sound: {}", self.name(), self.make_sound())
    }
}

trait Mammal: Animal {
    fn body_temperature(&self) -> f64;
    fn has_fur(&self) -> bool;
    
    fn is_warm_blooded(&self) -> bool {
        self.body_temperature() > 35.0
    }
}

trait Carnivore: Animal {
    fn hunt(&self) -> String;
    fn preferred_prey(&self) -> Vec<&str>;
}

// 多重trait边界
trait Predator: Mammal + Carnivore {
    fn pack_size(&self) -> usize;
    
    fn hunting_strategy(&self) -> String {
        if self.pack_size() > 1 {
            format!("{} hunts in packs of {}", self.name(), self.pack_size())
        } else {
            format!("{} hunts alone", self.name())
        }
    }
}

// 具体实现
struct Wolf {
    name: String,
    pack_size: usize,
}

impl Wolf {
    fn new(name: String, pack_size: usize) -> Self {
        Self { name, pack_size }
    }
}

impl Animal for Wolf {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn make_sound(&self) -> &str {
        "Howl"
    }
}

impl Mammal for Wolf {
    fn body_temperature(&self) -> f64 {
        38.5
    }
    
    fn has_fur(&self) -> bool {
        true
    }
}

impl Carnivore for Wolf {
    fn hunt(&self) -> String {
        "Stalks prey silently".to_string()
    }
    
    fn preferred_prey(&self) -> Vec<&str> {
        vec!["deer", "elk", "moose"]
    }
}

impl Predator for Wolf {
    fn pack_size(&self) -> usize {
        self.pack_size
    }
}

// trait继承使用示例
fn demonstrate_trait_inheritance() {
    let wolf = Wolf::new("Gray Wolf".to_string(), 6);
    
    // 使用基础trait方法
    println!("{}", wolf.describe());
    
    // 使用继承的trait方法
    println!("Body temperature: {}°C", wolf.body_temperature());
    println!("Is warm blooded: {}", wolf.is_warm_blooded());
    
    // 使用多重继承的trait方法
    println!("{}", wolf.hunting_strategy());
    println!("Preferred prey: {:?}", wolf.preferred_prey());
}
```

**定理 3.1** (trait继承正确性)  
trait继承保证：

1. **接口继承**: 子trait包含父trait的所有方法
2. **实现一致性**: 实现子trait必须实现所有父trait
3. **多重继承**: 支持多个父trait的组合

### 3.2 组合模式

```rust
// 组合优于继承的设计
trait Engine {
    fn start(&mut self) -> Result<(), String>;
    fn stop(&mut self) -> Result<(), String>;
    fn get_power(&self) -> u32; // 马力
    fn is_running(&self) -> bool;
}

struct GasolineEngine {
    power: u32,
    running: bool,
    fuel_level: f64,
}

impl GasolineEngine {
    fn new(power: u32) -> Self {
        Self {
            power,
            running: false,
            fuel_level: 100.0,
        }
    }
}

impl Engine for GasolineEngine {
    fn start(&mut self) -> Result<(), String> {
        if self.fuel_level <= 0.0 {
            Err("No fuel".to_string())
        } else {
            self.running = true;
            Ok(())
        }
    }
    
    fn stop(&mut self) -> Result<(), String> {
        self.running = false;
        Ok(())
    }
    
    fn get_power(&self) -> u32 {
        self.power
    }
    
    fn is_running(&self) -> bool {
        self.running
    }
}

struct ElectricEngine {
    power: u32,
    running: bool,
    battery_level: f64,
}

impl ElectricEngine {
    fn new(power: u32) -> Self {
        Self {
            power,
            running: false,
            battery_level: 100.0,
        }
    }
}

impl Engine for ElectricEngine {
    fn start(&mut self) -> Result<(), String> {
        if self.battery_level <= 0.0 {
            Err("Battery depleted".to_string())
        } else {
            self.running = true;
            Ok(())
        }
    }
    
    fn stop(&mut self) -> Result<(), String> {
        self.running = false;
        Ok(())
    }
    
    fn get_power(&self) -> u32 {
        self.power
    }
    
    fn is_running(&self) -> bool {
        self.running
    }
}

// 使用组合的汽车类
struct Car {
    model: String,
    engine: Box<dyn Engine>,
    speed: f64,
}

impl Car {
    fn new(model: String, engine: Box<dyn Engine>) -> Self {
        Self {
            model,
            engine,
            speed: 0.0,
        }
    }
    
    fn start(&mut self) -> Result<(), String> {
        self.engine.start()
    }
    
    fn stop(&mut self) -> Result<(), String> {
        self.speed = 0.0;
        self.engine.stop()
    }
    
    fn accelerate(&mut self, delta: f64) -> Result<(), String> {
        if !self.engine.is_running() {
            return Err("Engine is not running".to_string());
        }
        
        let max_speed = self.engine.get_power() as f64 * 2.0; // 简化计算
        self.speed = (self.speed + delta).min(max_speed);
        Ok(())
    }
    
    fn get_status(&self) -> String {
        format!("{}: speed = {:.1} km/h, engine power = {} HP, running = {}",
                self.model, self.speed, self.engine.get_power(), self.engine.is_running())
    }
}

// 组合模式使用示例
fn demonstrate_composition() {
    let gasoline_engine = Box::new(GasolineEngine::new(200));
    let electric_engine = Box::new(ElectricEngine::new(150));
    
    let mut gas_car = Car::new("Toyota Camry".to_string(), gasoline_engine);
    let mut electric_car = Car::new("Tesla Model 3".to_string(), electric_engine);
    
    // 操作汽油车
    gas_car.start().unwrap();
    gas_car.accelerate(50.0).unwrap();
    println!("Gas car: {}", gas_car.get_status());
    
    // 操作电动车
    electric_car.start().unwrap();
    electric_car.accelerate(60.0).unwrap();
    println!("Electric car: {}", electric_car.get_status());
    
    gas_car.stop().unwrap();
    electric_car.stop().unwrap();
}
```

**定理 3.2** (组合模式正确性)  
组合模式保证：

1. **灵活性**: 可以在运行时改变组合的对象
2. **可扩展性**: 新的组件可以独立添加
3. **松耦合**: 组件之间通过接口交互

## 4. 多态与动态分发

### 4.1 trait对象多态

```rust
// 多态的实现机制
trait Drawable {
    fn draw(&self) -> String;
    fn area(&self) -> f64;
    fn center(&self) -> (f64, f64);
}

struct Circle {
    x: f64,
    y: f64,
    radius: f64,
}

struct Rectangle {
    x: f64,
    y: f64,
    width: f64,
    height: f64,
}

struct Triangle {
    x1: f64, y1: f64,
    x2: f64, y2: f64,
    x3: f64, y3: f64,
}

impl Drawable for Circle {
    fn draw(&self) -> String {
        format!("Drawing circle at ({}, {}) with radius {}", self.x, self.y, self.radius)
    }
    
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
    
    fn center(&self) -> (f64, f64) {
        (self.x, self.y)
    }
}

impl Drawable for Rectangle {
    fn draw(&self) -> String {
        format!("Drawing rectangle at ({}, {}) with size {}x{}", 
                self.x, self.y, self.width, self.height)
    }
    
    fn area(&self) -> f64 {
        self.width * self.height
    }
    
    fn center(&self) -> (f64, f64) {
        (self.x + self.width / 2.0, self.y + self.height / 2.0)
    }
}

impl Drawable for Triangle {
    fn draw(&self) -> String {
        format!("Drawing triangle with vertices ({}, {}), ({}, {}), ({}, {})",
                self.x1, self.y1, self.x2, self.y2, self.x3, self.y3)
    }
    
    fn area(&self) -> f64 {
        let a = ((self.x2 - self.x1).powi(2) + (self.y2 - self.y1).powi(2)).sqrt();
        let b = ((self.x3 - self.x2).powi(2) + (self.y3 - self.y2).powi(2)).sqrt();
        let c = ((self.x1 - self.x3).powi(2) + (self.y1 - self.y3).powi(2)).sqrt();
        let s = (a + b + c) / 2.0;
        (s * (s - a) * (s - b) * (s - c)).sqrt()
    }
    
    fn center(&self) -> (f64, f64) {
        ((self.x1 + self.x2 + self.x3) / 3.0, (self.y1 + self.y2 + self.y3) / 3.0)
    }
}

// 多态容器和操作
struct Canvas {
    shapes: Vec<Box<dyn Drawable>>,
}

impl Canvas {
    fn new() -> Self {
        Self {
            shapes: Vec::new(),
        }
    }
    
    fn add_shape(&mut self, shape: Box<dyn Drawable>) {
        self.shapes.push(shape);
    }
    
    fn draw_all(&self) -> Vec<String> {
        self.shapes.iter().map(|shape| shape.draw()).collect()
    }
    
    fn total_area(&self) -> f64 {
        self.shapes.iter().map(|shape| shape.area()).sum()
    }
    
    fn find_shapes_near(&self, x: f64, y: f64, distance: f64) -> Vec<usize> {
        self.shapes
            .iter()
            .enumerate()
            .filter(|(_, shape)| {
                let (cx, cy) = shape.center();
                ((cx - x).powi(2) + (cy - y).powi(2)).sqrt() <= distance
            })
            .map(|(i, _)| i)
            .collect()
    }
}

// 多态使用示例
fn demonstrate_polymorphism() {
    let mut canvas = Canvas::new();
    
    // 添加不同类型的形状
    canvas.add_shape(Box::new(Circle { x: 0.0, y: 0.0, radius: 5.0 }));
    canvas.add_shape(Box::new(Rectangle { x: 10.0, y: 10.0, width: 8.0, height: 6.0 }));
    canvas.add_shape(Box::new(Triangle { 
        x1: 0.0, y1: 0.0, 
        x2: 3.0, y2: 0.0, 
        x3: 1.5, y3: 3.0 
    }));
    
    // 多态操作
    let drawings = canvas.draw_all();
    for drawing in drawings {
        println!("{}", drawing);
    }
    
    println!("Total area: {:.2}", canvas.total_area());
    
    let nearby = canvas.find_shapes_near(5.0, 5.0, 10.0);
    println!("Shapes near (5, 5): {:?}", nearby);
}
```

**定理 4.1** (多态正确性)  
多态机制保证：

1. **类型安全**: 动态分发保持类型安全
2. **行为一致**: 相同接口的不同实现行为一致
3. **运行时分发**: 根据实际类型正确分发方法调用

### 4.2 泛型多态

```rust
// 泛型多态与trait边界
trait Serializable {
    fn serialize(&self) -> String;
    fn deserialize(data: &str) -> Result<Self, String> where Self: Sized;
}

trait Comparable {
    fn compare(&self, other: &Self) -> std::cmp::Ordering;
}

// 泛型容器
struct Container<T> {
    items: Vec<T>,
}

impl<T> Container<T>
where
    T: Serializable + Comparable + Clone,
{
    fn new() -> Self {
        Self {
            items: Vec::new(),
        }
    }
    
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn sort(&mut self) {
        self.items.sort_by(|a, b| a.compare(b));
    }
    
    fn serialize_all(&self) -> Vec<String> {
        self.items.iter().map(|item| item.serialize()).collect()
    }
    
    fn find_max(&self) -> Option<&T> {
        self.items.iter().max_by(|a, b| a.compare(b))
    }
    
    fn filter_by<F>(&self, predicate: F) -> Vec<T>
    where
        F: Fn(&T) -> bool,
    {
        self.items.iter().filter(|item| predicate(item)).cloned().collect()
    }
}

// 具体类型实现
#[derive(Clone)]
struct Person {
    name: String,
    age: u32,
}

impl Person {
    fn new(name: String, age: u32) -> Self {
        Self { name, age }
    }
}

impl Serializable for Person {
    fn serialize(&self) -> String {
        format!("{}:{}", self.name, self.age)
    }
    
    fn deserialize(data: &str) -> Result<Self, String> {
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() != 2 {
            return Err("Invalid format".to_string());
        }
        
        let name = parts[0].to_string();
        let age = parts[1].parse::<u32>().map_err(|_| "Invalid age".to_string())?;
        
        Ok(Person::new(name, age))
    }
}

impl Comparable for Person {
    fn compare(&self, other: &Self) -> std::cmp::Ordering {
        self.age.cmp(&other.age)
    }
}

// 泛型多态使用示例
fn demonstrate_generic_polymorphism() {
    let mut container = Container::new();
    
    container.add(Person::new("Alice".to_string(), 30));
    container.add(Person::new("Bob".to_string(), 25));
    container.add(Person::new("Charlie".to_string(), 35));
    
    // 排序
    container.sort();
    
    // 序列化
    let serialized = container.serialize_all();
    println!("Serialized: {:?}", serialized);
    
    // 查找最大值
    if let Some(oldest) = container.find_max() {
        println!("Oldest person: {}", oldest.serialize());
    }
    
    // 过滤
    let adults = container.filter_by(|person| person.age >= 30);
    println!("Adults: {:?}", adults.iter().map(|p| p.serialize()).collect::<Vec<_>>());
}
```

**定理 4.2** (泛型多态正确性)  
泛型多态保证：

1. **编译时多态**: 泛型在编译时单态化
2. **零成本抽象**: 泛型不增加运行时开销
3. **类型约束**: trait边界确保类型安全

---

## 总结

本文档建立了Rust面向对象编程的完整理论基础，包括：

1. **封装机制**: 数据隐藏和接口设计
2. **继承模式**: trait继承和多重继承
3. **组合优于继承**: 灵活的对象组合
4. **多态实现**: trait对象和泛型多态
5. **动态分发**: 运行时方法分发机制

这些理论展示了Rust如何在没有传统类继承的情况下实现面向对象编程的核心特性。

---

*文档状态: 完成*  
*版本: 1.0*  
*字数: ~8KB*

