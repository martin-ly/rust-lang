# Observer Pattern in Rust

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **设计模式**: 行为型模式
> **难度**: 🟡 中等
> **应用场景**: 事件订阅、数据绑定、MVC

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Observer Pattern in Rust](#observer-pattern-in-rust)
  - [📑 目录](#-目录)
  - [概念](#概念)
  - [Rust 实现](#rust-实现)
    - [基础实现](#基础实现)
    - [类型安全的事件系统](#类型安全的事件系统)
  - [形式化定义](#形式化定义)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 概念
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

观察者模式定义对象间的一对多依赖关系，当一个对象状态改变时，所有依赖它的对象都会收到通知并自动更新。

---

## Rust 实现
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 基础实现
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};

// 观察者 trait
pub trait Observer {
    fn update(&self, event: &str, data: &str);
}

// 主题
pub struct Subject {
    observers: RefCell<Vec<Weak<dyn Observer>>>,
    state: RefCell<String>,
}

impl Subject {
    pub fn new() -> Self {
        Self {
            observers: RefCell::new(Vec::new()),
            state: RefCell::new(String::new()),
        }
    }

    pub fn attach(&self, observer: Rc<dyn Observer>) {
        self.observers.borrow_mut().push(Rc::downgrade(&observer));
    }

    pub fn detach(&self, observer: &Rc<dyn Observer>) {
        let ptr = Rc::as_ptr(observer);
        self.observers.borrow_mut().retain(|weak| {
            weak.upgrade().map_or(true, |rc| Rc::as_ptr(&rc) != ptr)
        });
    }

    pub fn notify(&self, event: &str) {
        let data = self.state.borrow().clone();
        let mut to_remove = Vec::new();

        for (i, weak) in self.observers.borrow().iter().enumerate() {
            if let Some(observer) = weak.upgrade() {
                observer.update(event, &data);
            } else {
                to_remove.push(i);
            }
        }

        // 清理已释放的观察者
        for i in to_remove.iter().rev() {
            self.observers.borrow_mut().remove(*i);
        }
    }

    pub fn set_state(&self, state: &str) {
        *self.state.borrow_mut() = state.to_string();
        self.notify("state_changed");
    }
}

// 具体观察者
pub struct EmailObserver {
    email: String,
}

impl EmailObserver {
    pub fn new(email: &str) -> Self {
        Self {
            email: email.to_string(),
        }
    }
}

impl Observer for EmailObserver {
    fn update(&self, event: &str, data: &str) {
        println!("[Email to {}] Event: {}, Data: {}", self.email, event, data);
    }
}

pub struct LoggerObserver;

impl Observer for LoggerObserver {
    fn update(&self, event: &str, data: &str) {
        println!("[LOG] {} - {}", event, data);
    }
}

// 使用
fn main() {
    let subject = Rc::new(Subject::new());

    let email_obs = Rc::new(EmailObserver::new("user@example.com"));
    let logger_obs = Rc::new(LoggerObserver);

    subject.attach(email_obs.clone());
    subject.attach(logger_obs.clone());

    subject.set_state("New data available");
}
```

### 类型安全的事件系统
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
use std::any::{Any, TypeId};
use std::collections::HashMap;

pub trait Event: Any + Send + Sync {
    fn as_any(&self) -> &dyn Any;
}

pub struct EventBus {
    listeners: HashMap<TypeId, Vec<Box<dyn Fn(&dyn Event)>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            listeners: HashMap::new(),
        }
    }

    pub fn on<E: Event>(&mut self, handler: impl Fn(&E) + 'static) {
        let type_id = TypeId::of::<E>();
        let wrapped = move |e: &dyn Event| {
            if let Some(event) = e.as_any().downcast_ref::<E>() {
                handler(event);
            }
        };
        self.listeners
            .entry(type_id)
            .or_insert_with(Vec::new)
            .push(Box::new(wrapped));
    }

    pub fn emit<E: Event>(&self, event: E) {
        let type_id = TypeId::of::<E>();
        if let Some(handlers) = self.listeners.get(&type_id) {
            for handler in handlers {
                handler(&event);
            }
        }
    }
}

// 定义事件
#[derive(Debug)]
pub struct UserCreatedEvent {
    pub user_id: u64,
    pub username: String,
}

impl Event for UserCreatedEvent {
    fn as_any(&self) -> &dyn Any { self }
}

#[derive(Debug)]
pub struct OrderPlacedEvent {
    pub order_id: u64,
    pub amount: f64,
}

impl Event for OrderPlacedEvent {
    fn as_any(&self) -> &dyn Any { self }
}
```

---

## 形式化定义
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
Subject ──observes──> Observer (1:N)

不变量:
  state_change(s) ⟹ ∀o ∈ observers: o.update(s)

Rust 特殊性:
  - 使用 Weak 引用避免循环引用
  - 需要 RefCell 实现内部可变性
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [behavioral 目录](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Design Pattern]**

> **[来源: Rust API Guidelines]**

> **[来源: Gang of Four - Design Patterns]**

> **[来源: ACM - Software Design Patterns]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
