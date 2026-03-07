# Observer Pattern in Rust

> **设计模式**: 行为型模式
> **难度**: 🟡 中等
> **应用场景**: 事件订阅、数据绑定、MVC

---

## 概念

观察者模式定义对象间的一对多依赖关系，当一个对象状态改变时，所有依赖它的对象都会收到通知并自动更新。

---

## Rust 实现

### 基础实现

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

```
Subject ──observes──> Observer (1:N)

不变量:
  state_change(s) ⟹ ∀o ∈ observers: o.update(s)

Rust 特殊性:
  - 使用 Weak 引用避免循环引用
  - 需要 RefCell 实现内部可变性
```
