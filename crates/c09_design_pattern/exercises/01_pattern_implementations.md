# C09 设计模式练习

> 难度: 中级-高级 | 预计时间: 90 分钟

---

## 🎯 练习目标

- 掌握常用设计模式
- 理解模式之间的关系
- 能在实际项目中应用

---

## 练习 1: 单例模式

实现线程安全的单例模式。

```rust
use std::sync::{Arc, Mutex, OnceLock};

pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
}

impl DatabaseConfig {
    fn new() -> Self {
        Self {
            url: "localhost:5432".to_string(),
            max_connections: 10,
        }
    }
}

// 使用 OnceLock 实现单例
static INSTANCE: OnceLock<Arc<Mutex<DatabaseConfig>>> = OnceLock::new();

pub fn get_config() -> Arc<Mutex<DatabaseConfig>> {
    INSTANCE
        .get_or_init(|| Arc::new(Mutex::new(DatabaseConfig::new())))
        .clone()
}

fn main() {
    let config1 = get_config();
    let config2 = get_config();

    assert!(Arc::ptr_eq(&config1, &config2));
    println!("Singleton verified!");
}
```

**任务**:

1. 实现延迟初始化
2. 添加配置热更新

---

## 练习 2: 工厂模式

实现一个泛型工厂。

```rust
// 产品 trait
trait Product: std::fmt::Debug {
    fn operation(&self) -> String;
}

// 具体产品
#[derive(Debug)]
struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Product A operation".to_string()
    }
}

#[derive(Debug)]
struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Product B operation".to_string()
    }
}

// 工厂 trait
trait Factory {
    type ProductType: Product;
    fn create_product(&self) -> Self::ProductType;
}

// 具体工厂
struct FactoryA;
impl Factory for FactoryA {
    type ProductType = ConcreteProductA;

    fn create_product(&self) -> Self::ProductType {
        ConcreteProductA
    }
}

struct FactoryB;
impl Factory for FactoryB {
    type ProductType = ConcreteProductB;

    fn create_product(&self) -> Self::ProductType {
        ConcreteProductB
    }
}

fn main() {
    let factory_a = FactoryA;
    let product_a = factory_a.create_product();
    println!("{}", product_a.operation());

    let factory_b = FactoryB;
    let product_b = factory_b.create_product();
    println!("{}", product_b.operation());
}
```

**任务**:

1. 实现抽象工厂模式
2. 添加工厂注册表

---

## 练习 3: 观察者模式

实现事件订阅系统。

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex, Weak};

type EventHandler = Box<dyn Fn(&str) + Send + Sync>;

pub struct EventBus {
    subscribers: Mutex<HashMap<String, Vec<EventHandler>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            subscribers: Mutex::new(HashMap::new()),
        }
    }

    pub fn subscribe<F>(&self, event: &str, handler: F)
    where
        F: Fn(&str) + Send + Sync + 'static,
    {
        let mut subs = self.subscribers.lock().unwrap();
        subs.entry(event.to_string())
            .or_insert_with(Vec::new)
            .push(Box::new(handler));
    }

    pub fn publish(&self, event: &str, data: &str) {
        let subs = self.subscribers.lock().unwrap();
        if let Some(handlers) = subs.get(event) {
            for handler in handlers {
                handler(data);
            }
        }
    }
}

fn main() {
    let event_bus = Arc::new(EventBus::new());

    event_bus.subscribe("user.login", |data| {
        println!("User logged in: {}", data);
    });

    event_bus.subscribe("user.logout", |data| {
        println!("User logged out: {}", data);
    });

    event_bus.publish("user.login", "Alice");
    event_bus.publish("user.logout", "Alice");
}
```

**任务**:

1. 实现取消订阅
2. 添加异步事件处理

<details>
<summary>取消订阅答案</summary>

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub struct SubscriptionId(usize);

pub struct EventBus {
    subscribers: Mutex<HashMap<String, Vec<(usize, EventHandler)>>>,
    next_id: Mutex<usize>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            subscribers: Mutex::new(HashMap::new()),
            next_id: Mutex::new(0),
        }
    }

    pub fn subscribe<F>(&self, event: &str, handler: F) -> SubscriptionId
    where
        F: Fn(&str) + Send + Sync + 'static,
    {
        let id = {
            let mut next = self.next_id.lock().unwrap();
            let id = *next;
            *next += 1;
            id
        };

        let mut subs = self.subscribers.lock().unwrap();
        subs.entry(event.to_string())
            .or_insert_with(Vec::new)
            .push((id, Box::new(handler)));

        SubscriptionId(id)
    }

    pub fn unsubscribe(&self, event: &str, id: SubscriptionId) {
        let mut subs = self.subscribers.lock().unwrap();
        if let Some(handlers) = subs.get_mut(event) {
            handlers.retain(|(handler_id, _)| *handler_id != id.0);
        }
    }

    pub fn publish(&self, event: &str, data: &str) {
        let subs = self.subscribers.lock().unwrap();
        if let Some(handlers) = subs.get(event) {
            for (_, handler) in handlers {
                handler(data);
            }
        }
    }
}
```

</details>

---

## 练习 4: 策略模式

实现可切换的排序策略。

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

struct BubbleSort;
impl SortStrategy for BubbleSort {
    fn sort(&self, data: &mut [i32]) {
        let n = data.len();
        for i in 0..n {
            for j in 0..n - i - 1 {
                if data[j] > data[j + 1] {
                    data.swap(j, j + 1);
                }
            }
        }
    }
}

struct QuickSort;
impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) {
        if data.len() > 1 {
            quick_sort_helper(data);
        }
    }
}

fn quick_sort_helper(data: &mut [i32]) {
    if data.len() <= 1 {
        return;
    }
    let pivot = partition(data);
    quick_sort_helper(&mut data[0..pivot]);
    quick_sort_helper(&mut data[pivot + 1..]);
}

fn partition(data: &mut [i32]) -> usize {
    let len = data.len();
    let pivot = data[len - 1];
    let mut i = 0;
    for j in 0..len - 1 {
        if data[j] <= pivot {
            data.swap(i, j);
            i += 1;
        }
    }
    data.swap(i, len - 1);
    i
}

struct Context {
    strategy: Box<dyn SortStrategy>,
}

impl Context {
    fn new(strategy: Box<dyn SortStrategy>) -> Self {
        Self { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn SortStrategy>) {
        self.strategy = strategy;
    }

    fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}

fn main() {
    let mut data = vec![64, 34, 25, 12, 22, 11, 90];

    let context = Context::new(Box::new(BubbleSort));
    context.sort(&mut data);
    println!("Bubble sorted: {:?}", data);

    let mut data = vec![64, 34, 25, 12, 22, 11, 90];
    let context = Context::new(Box::new(QuickSort));
    context.sort(&mut data);
    println!("Quick sorted: {:?}", data);
}
```

**任务**:

1. 添加更多排序策略
2. 实现运行时策略切换

---

## 📚 相关文档

- [C09 设计模式](../README.md)
- [Rust 设计模式](https://rust-unofficial.github.io/patterns/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
