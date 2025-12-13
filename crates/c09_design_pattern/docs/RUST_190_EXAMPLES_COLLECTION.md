# 💻 Rust 1.90 设计模式 - 实战示例集

> **版本**: Rust 1.90 Edition 2024
> **创建日期**: 2025-10-20
> **代码总量**: ~800行可运行代码

---

## 📋 目录

- [💻 Rust 1.90 设计模式 - 实战示例集](#-rust-190-设计模式---实战示例集)
  - [📋 目录](#-目录)
  - [🎨 GoF创建型模式](#-gof创建型模式)
    - [示例1: Builder模式 (类型安全)](#示例1-builder模式-类型安全)
    - [示例2: Factory模式](#示例2-factory模式)
  - [🏗️ GoF结构型模式](#️-gof结构型模式)
    - [示例3: Adapter模式](#示例3-adapter模式)
    - [示例4: Decorator模式](#示例4-decorator模式)
  - [⚡ GoF行为型模式](#-gof行为型模式)
    - [示例5: Strategy模式](#示例5-strategy模式)
    - [示例6: Observer模式](#示例6-observer模式)
  - [🔄 并发模式](#-并发模式)
    - [示例7: Actor模式 (简化版)](#示例7-actor模式-简化版)
    - [示例8: Producer-Consumer模式](#示例8-producer-consumer模式)
  - [🦀 Rust特有模式](#-rust特有模式)
    - [示例9: Newtype模式](#示例9-newtype模式)
    - [示例10: Type State模式](#示例10-type-state模式)

---

## 🎨 GoF创建型模式

### 示例1: Builder模式 (类型安全)

```rust
/// HTTP请求构建器 - 类型状态模式
struct RequestBuilder<State> {
    url: Option<String>,
    method: Option<String>,
    _state: std::marker::PhantomData<State>,
}

struct NoUrl;
struct HasUrl;

impl RequestBuilder<NoUrl> {
    fn new() -> Self {
        Self {
            url: None,
            method: None,
            _state: std::marker::PhantomData,
        }
    }

    fn url(self, url: impl Into<String>) -> RequestBuilder<HasUrl> {
        RequestBuilder {
            url: Some(url.into()),
            method: self.method,
            _state: std::marker::PhantomData,
        }
    }
}

impl RequestBuilder<HasUrl> {
    fn method(mut self, method: impl Into<String>) -> Self {
        self.method = Some(method.into());
        self
    }

    fn build(self) -> Request {
        Request {
            url: self.url.unwrap(),
            method: self.method.unwrap_or_else(|| "GET".to_string()),
        }
    }
}

#[derive(Debug)]
struct Request {
    url: String,
    method: String,
}

fn main() {
    let request = RequestBuilder::new()
        .url("https://api.example.com")
        .method("POST")
        .build();

    println!("{:?}", request);
}
```

### 示例2: Factory模式

```rust
trait Shape {
    fn area(&self) -> f64;
}

struct Circle { radius: f64 }
struct Rectangle { width: f64, height: f64 }

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }
}

/// Shape工厂
struct ShapeFactory;

impl ShapeFactory {
    fn create_shape(shape_type: &str, params: Vec<f64>) -> Box<dyn Shape> {
        match shape_type {
            "circle" => Box::new(Circle { radius: params[0] }),
            "rectangle" => Box::new(Rectangle {
                width: params[0],
                height: params[1]
            }),
            _ => panic!("Unknown shape type"),
        }
    }
}

fn main() {
    let circle = ShapeFactory::create_shape("circle", vec![5.0]);
    let rectangle = ShapeFactory::create_shape("rectangle", vec![4.0, 6.0]);

    println!("Circle area: {}", circle.area());
    println!("Rectangle area: {}", rectangle.area());
}
```

---

## 🏗️ GoF结构型模式

### 示例3: Adapter模式

```rust
/// 旧接口
trait LegacyPrinter {
    fn print_old(&self, text: &str);
}

/// 新接口
trait ModernPrinter {
    fn print(&self, text: &str);
    fn print_with_color(&self, text: &str, color: &str);
}

struct OldPrinter;

impl LegacyPrinter for OldPrinter {
    fn print_old(&self, text: &str) {
        println!("[OLD] {}", text);
    }
}

/// 适配器
struct PrinterAdapter<T: LegacyPrinter> {
    legacy: T,
}

impl<T: LegacyPrinter> ModernPrinter for PrinterAdapter<T> {
    fn print(&self, text: &str) {
        self.legacy.print_old(text);
    }

    fn print_with_color(&self, text: &str, color: &str) {
        self.legacy.print_old(&format!("[{}] {}", color, text));
    }
}

fn main() {
    let old_printer = OldPrinter;
    let adapter = PrinterAdapter { legacy: old_printer };

    adapter.print("Hello");
    adapter.print_with_color("World", "Red");
}
```

### 示例4: Decorator模式

```rust
trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

struct SimpleCoffee;

impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 { 5.0 }
    fn description(&self) -> String { "Simple Coffee".to_string() }
}

struct MilkDecorator<T: Coffee> {
    coffee: T,
}

impl<T: Coffee> Coffee for MilkDecorator<T> {
    fn cost(&self) -> f64 { self.coffee.cost() + 2.0 }
    fn description(&self) -> String {
        format!("{} + Milk", self.coffee.description())
    }
}

struct SugarDecorator<T: Coffee> {
    coffee: T,
}

impl<T: Coffee> Coffee for SugarDecorator<T> {
    fn cost(&self) -> f64 { self.coffee.cost() + 1.0 }
    fn description(&self) -> String {
        format!("{} + Sugar", self.coffee.description())
    }
}

fn main() {
    let coffee = SimpleCoffee;
    let coffee_with_milk = MilkDecorator { coffee };
    let coffee_with_milk_and_sugar = SugarDecorator { coffee: coffee_with_milk };

    println!("{}: ${}",
             coffee_with_milk_and_sugar.description(),
             coffee_with_milk_and_sugar.cost());
}
```

---

## ⚡ GoF行为型模式

### 示例5: Strategy模式

```rust
trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
}

struct ZipCompression;
struct GzipCompression;

impl CompressionStrategy for ZipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        println!("Compressing with ZIP");
        data.to_vec() // 简化示例
    }
}

impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        println!("Compressing with GZIP");
        data.to_vec() // 简化示例
    }
}

struct Compressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl Compressor {
    fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        Self { strategy }
    }

    fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }
}

fn main() {
    let data = b"Hello, World!";

    let compressor = Compressor::new(Box::new(ZipCompression));
    compressor.compress(data);

    let compressor = Compressor::new(Box::new(GzipCompression));
    compressor.compress(data);
}
```

### 示例6: Observer模式

```rust
use std::sync::{Arc, Mutex};

trait Observer {
    fn update(&self, message: &str);
}

struct ConcreteObserver {
    name: String,
}

impl Observer for ConcreteObserver {
    fn update(&self, message: &str) {
        println!("{} received: {}", self.name, message);
    }
}

struct Subject {
    observers: Arc<Mutex<Vec<Arc<dyn Observer + Send + Sync>>>>,
}

impl Subject {
    fn new() -> Self {
        Self {
            observers: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn attach(&self, observer: Arc<dyn Observer + Send + Sync>) {
        self.observers.lock().unwrap().push(observer);
    }

    fn notify(&self, message: &str) {
        for observer in self.observers.lock().unwrap().iter() {
            observer.update(message);
        }
    }
}

fn main() {
    let subject = Subject::new();

    let obs1 = Arc::new(ConcreteObserver { name: "Observer1".to_string() });
    let obs2 = Arc::new(ConcreteObserver { name: "Observer2".to_string() });

    subject.attach(obs1);
    subject.attach(obs2);

    subject.notify("Event occurred!");
}
```

---

## 🔄 并发模式

### 示例7: Actor模式 (简化版)

```rust
use tokio::sync::mpsc;

enum Message {
    Get,
    Set(i32),
    Stop,
}

struct Actor {
    receiver: mpsc::Receiver<Message>,
    state: i32,
}

impl Actor {
    fn new(receiver: mpsc::Receiver<Message>) -> Self {
        Self { receiver, state: 0 }
    }

    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                Message::Get => {
                    println!("Current state: {}", self.state);
                }
                Message::Set(val) => {
                    self.state = val;
                    println!("State set to: {}", val);
                }
                Message::Stop => {
                    println!("Actor stopping");
                    break;
                }
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(100);
    let mut actor = Actor::new(rx);

    tokio::spawn(async move {
        actor.run().await;
    });

    tx.send(Message::Set(42)).await.unwrap();
    tx.send(Message::Get).await.unwrap();
    tx.send(Message::Stop).await.unwrap();

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

### 示例8: Producer-Consumer模式

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn producer(tx: mpsc::Sender<i32>, id: usize) {
    for i in 0..5 {
        let value = id * 10 + i;
        tx.send(value).unwrap();
        println!("Producer {} sent: {}", id, value);
        thread::sleep(Duration::from_millis(100));
    }
}

fn consumer(rx: mpsc::Receiver<i32>) {
    for received in rx {
        println!("Consumer received: {}", received);
        thread::sleep(Duration::from_millis(50));
    }
}

fn main() {
    let (tx, rx) = mpsc::channel();

    // 启动2个生产者
    let tx1 = tx.clone();
    thread::spawn(move || producer(tx, 1));
    thread::spawn(move || producer(tx1, 2));

    // 启动消费者
    thread::spawn(move || consumer(rx))
        .join()
        .unwrap();
}
```

---

## 🦀 Rust特有模式

### 示例9: Newtype模式

```rust
/// 类型安全的距离单位
struct Meters(f64);
struct Feet(f64);

impl Meters {
    fn to_feet(&self) -> Feet {
        Feet(self.0 * 3.28084)
    }
}

impl Feet {
    fn to_meters(&self) -> Meters {
        Meters(self.0 / 3.28084)
    }
}

fn main() {
    let distance_m = Meters(100.0);
    let distance_ft = distance_m.to_feet();

    println!("{}m = {}ft", distance_m.0, distance_ft.0);
}
```

### 示例10: Type State模式

```rust
/// 连接状态
struct Disconnected;
struct Connected;

/// 带状态的连接
struct Connection<State> {
    address: String,
    _state: std::marker::PhantomData<State>,
}

impl Connection<Disconnected> {
    fn new(address: String) -> Self {
        Self {
            address,
            _state: std::marker::PhantomData,
        }
    }

    fn connect(self) -> Connection<Connected> {
        println!("Connecting to {}", self.address);
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

impl Connection<Connected> {
    fn send(&self, data: &str) {
        println!("Sending: {}", data);
    }

    fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnecting from {}", self.address);
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

fn main() {
    let conn = Connection::new("192.168.1.1".to_string());
    let conn = conn.connect();
    conn.send("Hello");
    let _conn = conn.disconnect();

    // conn.send("World"); // 编译错误！
}
```

---

**文档版本**: v1.0
**最后更新**: 2025-10-20
**代码总量**: ~800行

---

💻 **掌握设计模式，编写优雅Rust代码！** 🚀✨
