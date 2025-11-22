# 观察者模式（Observer Pattern）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [观察者模式](#观察者模式observer-pattern)
  - [概述](#概述)
  - [问题场景](#问题场景)
  - [解决方案](#解决方案)
  - [Rust 实现](#rust-实现)
  - [实践示例](#实践示例)
  - [优缺点](#优缺点)
  - [参考资料](#参考资料)

---

## 概述

观察者模式（Observer Pattern）是一种行为型设计模式，它定义了一种一对多的依赖关系，让多个观察者对象同时监听某一个主题对象。当主题对象状态发生变化时，它的所有依赖者（观察者）都会收到通知并自动更新。

## 问题场景

假设我们需要实现一个新闻发布系统，当有新闻发布时，多个订阅者（邮件订阅者、短信订阅者、推送订阅者）需要收到通知。

## 解决方案

使用观察者模式，将订阅者抽象为观察者，新闻发布系统作为主题：

```rust
use std::sync::{Arc, Weak};
use std::collections::HashMap;

// 观察者 Trait
pub trait Observer {
    fn update(&self, event: &str);
}

// 主题 Trait
pub trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer_id: usize);
    fn notify(&self, event: &str);
}

// 具体主题
pub struct NewsPublisher {
    observers: HashMap<usize, Weak<dyn Observer>>,
    observer_id_counter: usize,
}

impl NewsPublisher {
    pub fn new() -> Self {
        NewsPublisher {
            observers: HashMap::new(),
            observer_id_counter: 0,
        }
    }

    pub fn publish_news(&self, news: &str) {
        println!("发布新闻: {}", news);
        self.notify(news);
    }
}

impl Subject for NewsPublisher {
    fn attach(&mut self, observer: Arc<dyn Observer>) -> usize {
        let id = self.observer_id_counter;
        self.observer_id_counter += 1;
        self.observers.insert(id, Arc::downgrade(&observer));
        id
    }

    fn detach(&mut self, observer_id: usize) {
        self.observers.remove(&observer_id);
    }

    fn notify(&self, event: &str) {
        let mut to_remove = Vec::new();

        for (id, observer_weak) in &self.observers {
            if let Some(observer) = observer_weak.upgrade() {
                observer.update(event);
            } else {
                to_remove.push(*id);
            }
        }

        // 清理已失效的观察者
        for id in to_remove {
            // 注意：这里需要可变引用，实际实现中可能需要使用内部可变性
        }
    }
}
```

## Rust 实现

### 使用 Trait 对象

```rust
// 观察者
pub struct EmailSubscriber {
    email: String,
}

impl Observer for EmailSubscriber {
    fn update(&self, event: &str) {
        println!("发送邮件到 {}: {}", self.email, event);
    }
}

pub struct SMSSubscriber {
    phone: String,
}

impl Observer for SMSSubscriber {
    fn update(&self, event: &str) {
        println!("发送短信到 {}: {}", self.phone, event);
    }
}

// 使用
let mut publisher = NewsPublisher::new();
let email_sub = Arc::new(EmailSubscriber {
    email: "user@example.com".to_string(),
});
let sms_sub = Arc::new(SMSSubscriber {
    phone: "1234567890".to_string(),
});

publisher.attach(email_sub);
publisher.attach(sms_sub);
publisher.publish_news("重要新闻");
```

### 使用闭包

```rust
use std::sync::mpsc;

pub struct EventNotifier {
    subscribers: Vec<mpsc::Sender<String>>,
}

impl EventNotifier {
    pub fn new() -> Self {
        EventNotifier {
            subscribers: Vec::new(),
        }
    }

    pub fn subscribe(&mut self) -> mpsc::Receiver<String> {
        let (tx, rx) = mpsc::channel();
        self.subscribers.push(tx);
        rx
    }

    pub fn notify(&self, event: &str) {
        for subscriber in &self.subscribers {
            let _ = subscriber.send(event.to_string());
        }
    }
}
```

## 实践示例

### 示例 1：股票价格监控

```rust
use std::sync::{Arc, RwLock};

#[derive(Debug, Clone)]
pub struct StockPrice {
    pub symbol: String,
    pub price: f64,
}

pub trait StockObserver {
    fn on_price_change(&self, price: &StockPrice);
}

pub struct StockMarket {
    observers: Vec<Arc<dyn StockObserver + Send + Sync>>,
    prices: Arc<RwLock<HashMap<String, f64>>>,
}

impl StockMarket {
    pub fn new() -> Self {
        StockMarket {
            observers: Vec::new(),
            prices: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub fn subscribe(&mut self, observer: Arc<dyn StockObserver + Send + Sync>) {
        self.observers.push(observer);
    }

    pub fn update_price(&self, symbol: String, price: f64) {
        {
            let mut prices = self.prices.write().unwrap();
            prices.insert(symbol.clone(), price);
        }

        let stock_price = StockPrice { symbol, price };
        for observer in &self.observers {
            observer.on_price_change(&stock_price);
        }
    }
}

pub struct PriceAlert {
    symbol: String,
    threshold: f64,
}

impl StockObserver for PriceAlert {
    fn on_price_change(&self, price: &StockPrice) {
        if price.symbol == self.symbol && price.price > self.threshold {
            println!("⚠️  价格警报: {} 价格 {} 超过阈值 {}",
                price.symbol, price.price, self.threshold);
        }
    }
}
```

### 示例 2：文件系统监控

```rust
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub enum FileEvent {
    Created(PathBuf),
    Modified(PathBuf),
    Deleted(PathBuf),
}

pub trait FileSystemObserver {
    fn on_file_event(&self, event: &FileEvent);
}

pub struct FileSystemWatcher {
    observers: Vec<Arc<dyn FileSystemObserver + Send + Sync>>,
}

impl FileSystemWatcher {
    pub fn new() -> Self {
        FileSystemWatcher {
            observers: Vec::new(),
        }
    }

    pub fn subscribe(&mut self, observer: Arc<dyn FileSystemObserver + Send + Sync>) {
        self.observers.push(observer);
    }

    pub fn notify(&self, event: FileEvent) {
        for observer in &self.observers {
            observer.on_file_event(&event);
        }
    }
}

pub struct LoggingObserver;

impl FileSystemObserver for LoggingObserver {
    fn on_file_event(&self, event: &FileEvent) {
        match event {
            FileEvent::Created(path) => println!("文件创建: {:?}", path),
            FileEvent::Modified(path) => println!("文件修改: {:?}", path),
            FileEvent::Deleted(path) => println!("文件删除: {:?}", path),
        }
    }
}
```

## 优缺点

### 优点

1. **开闭原则**：可以在不修改主题的情况下添加新的观察者
2. **松耦合**：主题和观察者之间是松耦合的
3. **动态关系**：可以在运行时建立和删除观察者关系

### 缺点

1. **通知顺序**：观察者的通知顺序可能不确定
2. **循环依赖**：可能导致循环依赖问题
3. **性能开销**：大量观察者可能导致性能问题

## 参考资料

- [行为型模式索引](./00_index.md)
- [设计模式实现](../../../../crates/c09_design_pattern/src/behavioral/)
- [设计模式总索引](../00_index.md)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
