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
  - [2. 创建型模式](#2-创建型模式)
    - [工厂模式](#工厂模式)
    - [Builder模式](#builder模式)
  - [3. 结构型模式](#3-结构型模式)
    - [适配器模式](#适配器模式)
  - [4. 行为型模式](#4-行为型模式)
    - [观察者模式](#观察者模式)
  - [5. Rust特有的模式](#5-rust特有的模式)
    - [Type State模式](#type-state模式)
  - [6. 反模式](#6-反模式)
  - [7. 最佳实践](#7-最佳实践)
  - [参考文献](#参考文献)

---

## 1. 设计模式概述

### Rust设计模式哲学

- **利用类型系统编码不变量**: 编译时保证 > 运行时检查
- **零成本抽象**: 设计模式不应有运行时开销
- **显式优于隐式**: 所有权转移显式
- **组合优于继承**: Trait系统替代继承

---

## 2. 创建型模式

### 工厂模式

```rust
pub trait Product: Send + Sync {
    fn operation(&self) -> String;
}

pub trait Factory<P: Product> {
    fn create(&self) -> P;
}
```

### Builder模式

```rust
pub struct HttpRequestBuilder {
    method: String,
    url: String,
}

impl HttpRequestBuilder {
    pub fn method(mut self, method: &str) -> Self {
        self.method = method.to_string();
        self
    }

    pub fn build(self) -> Result<HttpRequest, String> {
        // ...
    }
}
```

---

## 3. 结构型模式

### 适配器模式

```rust
pub trait Target {
    fn request(&self) -> String;
}

pub struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        format!("Adapted: {}", self.adaptee.specific_request())
    }
}
```

---

## 4. 行为型模式

### 观察者模式

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};

pub trait Observer {
    fn update(&self, event: &str);
}

pub struct Subject {
    observers: RefCell<Vec<Weak<dyn Observer>>>,
}
```

---

## 5. Rust特有的模式

### Type State模式

```rust
pub struct StateMachine<State> {
    value: i32,
    _state: std::marker::PhantomData<State>,
}

impl StateMachine<Idle> {
    pub fn start(self) -> StateMachine<Running> {
        // 编译时防止非法状态转换
    }
}
```

---

## 6. 反模式

- 过度使用`Rc<RefCell<T>>`
- 忽视所有权转移
- 过度泛型化

---

## 7. 最佳实践

- 优先使用组合
- 利用类型系统防止非法操作
- 使用Type State模式

---

## 参考文献

1. Rust Design Patterns: <https://rust-unofficial.github.io/patterns/>
2. Rust API Guidelines: <https://rust-lang.github.io/api-guidelines/>
3. Effective Rust: <https://www.lurklurk.org/effective-rust/>
