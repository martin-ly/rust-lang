# 设计模式使用指南

**模块**: C09 Design Patterns
**创建日期**: 2025-12-11
**最后更新**: 2026-01-26
**Rust 版本**: 1.93.0+
**Edition**: 2024

---

## 📋 目录

- [设计模式使用指南](#设计模式使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [单例模式](#单例模式)
    - [工厂模式](#工厂模式)
  - [📊 核心模式](#-核心模式)
    - [1. 创建型模式](#1-创建型模式)
      - [建造者模式](#建造者模式)
    - [2. 结构型模式](#2-结构型模式)
      - [适配器模式](#适配器模式)
      - [装饰器模式](#装饰器模式)
    - [3. 行为型模式](#3-行为型模式)
      - [策略模式](#策略模式)
      - [观察者模式](#观察者模式)
  - [🦀 Rust 特有模式](#-rust-特有模式)
    - [1. Newtype 模式](#1-newtype-模式)
    - [2. RAII 模式](#2-raii-模式)
    - [3. 类型状态模式](#3-类型状态模式)
  - [📚 相关文档](#-相关文档)

---

## 📋 概述

本指南介绍如何在 Rust 中使用常见的设计模式，包括 GoF 模式和 Rust 特有的模式。

---

## 🚀 快速开始

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

## 📊 核心模式

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

## 🦀 Rust 特有模式

### 1. Newtype 模式

```rust
// 类型安全包装
struct UserId(u32);
struct OrderId(u32);

fn process_user(id: UserId) {
    // 类型安全
}

// 编译错误：类型不匹配
// process_user(OrderId(1));
```

### 2. RAII 模式

```rust
struct FileHandle {
    file: std::fs::File,
}

impl Drop for FileHandle {
    fn drop(&mut self) {
        // 自动清理资源
        println!("文件已关闭");
    }
}
```

### 3. 类型状态模式

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

impl Door<Open> {
    fn close(self) -> Door<Closed> {
        Door { state: Closed }
    }
}
```

---

## 📚 相关文档

- [完整文档](../../crates/c09_design_pattern/README.md)
- [GoF 模式](../../crates/c09_design_pattern/docs/tier_02_guides/01_创建型模式指南.md)
- [Rust 特有模式](../../crates/c09_design_pattern/docs/tier_02_guides/05_最佳实践与反模式.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-01-26
