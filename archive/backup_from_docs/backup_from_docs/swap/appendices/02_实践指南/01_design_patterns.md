# 从同伦类型论、范畴论与控制论视角看Rust的类型系统设计

## 目录

- [从同伦类型论、范畴论与控制论视角看Rust的类型系统设计](#从同伦类型论范畴论与控制论视角看rust的类型系统设计)
  - [目录](#目录)
  - [引言](#引言)
  - [类型、变量与所有权生命周期借用](#类型变量与所有权生命周期借用)
    - [2.1 类型与变量的定义](#21-类型与变量的定义)
    - [2.2 所有权与生命周期的关系](#22-所有权与生命周期的关系)
    - [2.3 借用机制的形式化分析](#23-借用机制的形式化分析)
  - [类型的分类与关联性](#类型的分类与关联性)
    - [3.1 原始类型与代数类型](#31-原始类型与代数类型)
    - [3.2 组合类型与Trait类型](#32-组合类型与trait类型)
    - [3.3 类型之间的关系](#33-类型之间的关系)
  - [类型与解构的映射关系](#类型与解构的映射关系)
    - [4.1 类型解构的定义](#41-类型解构的定义)
    - [4.2 控制流与容错机制](#42-控制流与容错机制)
    - [4.3 一致性与类型映射](#43-一致性与类型映射)
  - [类型的型变与代数运算](#类型的型变与代数运算)
    - [5.1 不变、协变与逆变](#51-不变协变与逆变)
    - [5.2 双变与类型代数运算](#52-双变与类型代数运算)
  - [控制流与执行流的关系](#控制流与执行流的关系)
    - [6.1 同步与异步执行流](#61-同步与异步执行流)
    - [6.2 同构关系与转换](#62-同构关系与转换)
  - [总结与展望](#总结与展望)
  - [思维导图](#思维导图)

## 引言

Rust的类型系统设计在现代编程语言中占据了重要地位，其独特的所有权、生命周期和借用机制为内存安全提供了强有力的保障。
通过同伦类型论、范畴论和控制论的视角，我们可以更深入地理解Rust类型系统的设计理念及其在实际编程中的应用。

本文将从多个维度对Rust的类型系统进行批判性分析，探讨类型、变量、所有权、生命周期、借用等概念的内在联系，以及类型的分类、解构映射关系、型变规则和控制流的执行机制。

## 类型、变量与所有权生命周期借用

### 2.1 类型与变量的定义

在Rust中，类型是对数据结构的抽象描述，而变量则是对这些数据的命名引用。
类型系统确保了数据的安全性和一致性。
Rust的类型系统包括原始类型、复合类型和自定义类型（如结构体和枚举）。

**形式化定义**：

- 类型 \( T \) 是一组值的集合，定义了这些值的结构和操作。
- 变量 \( v \) 是对类型 \( T \) 的实例的命名引用，表示在某一作用域内的值。

### 2.2 所有权与生命周期的关系

Rust的所有权系统通过静态分析确保每个值有唯一的所有者，并在编译时检查生命周期。
所有权与生命周期的结合确保了内存安全，避免了悬垂引用和数据竞争。

**形式化分析**：

- 所有权规则：每个值有一个所有者，所有权可以转移。
- 生命周期规则：引用的有效期不能超过其所指向数据的有效期。

```rust
fn main() {
    let s1 = String::from("Hello");
    let s2 = s1; // 所有权转移，s1不再有效
    // println!("{}", s1); // 编译错误
}
```

### 2.3 借用机制的形式化分析

借用机制允许通过引用访问数据，分为不可变借用和可变借用。
Rust的借用检查器在编译时确保借用规则的正确性。

**形式化定义**：

- 不可变借用：允许多个不可变引用同时存在。
- 可变借用：在同一时间只能有一个可变引用，且不可与不可变引用共存。

```rust
fn main() {
    let mut data = vec![1, 2, 3];
    let r1 = &data; // 不可变借用
    let r2 = &data; // 另一个不可变借用
    // let r3 = &mut data; // 编译错误：不可同时存在可变和不可变借用
}
```

## 类型的分类与关联性

### 3.1 原始类型与代数类型

Rust的类型系统包括原始类型（如整数、布尔值）和代数类型（如结构体、枚举）。
原始类型是不可变的基本数据单元，而代数类型则允许组合多个类型。

**形式化定义**：

- 原始类型 \( P \) 是基本数据类型的集合。
- 代数类型 \( A \) 是通过组合原始类型或其他代数类型构成的类型。

```rust
struct Point {
    x: i32,
    y: i32,
}

enum Shape {
    Circle(Point, f64),
    Rectangle(Point, Point),
}
```

### 3.2 组合类型与Trait类型

组合类型允许将多个类型组合在一起，而Trait类型则定义了一组共享的行为。
Trait为Rust提供了多态性，使得不同类型可以通过相同的接口进行操作。

**形式化定义**：

- 组合类型 \( C \) 是由多个类型构成的复合类型。
- Trait \( T \) 是一组方法的集合，允许不同类型实现相同的接口。

```rust
trait Drawable {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        // 绘制圆形
    }
}
```

### 3.3 类型之间的关系

Rust的类型系统通过类型层次结构（如Trait继承）建立了类型之间的关系。
类型之间的关系可以通过协变、逆变和不变性来描述。

- **协变**：子类型可以替代父类型。
- **逆变**：父类型可以替代子类型。
- **不变**：类型之间没有替代关系。

## 类型与解构的映射关系

### 4.1 类型解构的定义

类型解构是将复杂类型分解为其组成部分的过程。
在Rust中，解构通常通过模式匹配实现。

**形式化定义**：

- 解构操作将类型 \( T \) 的实例分解为其组成部分。

```rust
let point = (3, 4);
let (x, y) = point; // 解构元组
```

### 4.2 控制流与容错机制

Rust的控制流通过模式匹配和错误处理机制（如Result和Option类型）实现。
容错机制确保在运行时处理潜在错误。

**形式化定义**：

- 控制流 \( C \) 是程序执行路径的集合。
- 容错机制 \( E \) 是处理错误的策略。

```rust
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Cannot divide by zero".to_string())
    } else {
        Ok(a / b)
    }
}
```

### 4.3 一致性与类型映射

一致性是指在类型转换和解构过程中保持数据的完整性。
Rust的类型系统通过所有权和借用规则确保一致性。

**形式化定义**：

- 一致性 \( I \) 是在类型转换和解构过程中保持数据完整性的属性。

```rust
let data = vec![1, 2, 3];
let borrowed = &data; // 借用
// borrowed.push(4); // 编译错误：保持一致性
```

## 类型的型变与代数运算

### 5.1 不变、协变与逆变

型变规则定义了在类型层次结构中如何安全地进行类型替换。
Rust的类型系统支持协变和逆变，但不支持不变性。

**形式化定义**：

- 协变：如果 \( A \) 是 \( B \) 的子类型，则 \( F(A) \) 是 \( F(B) \) 的子类型。
- 逆变：如果 \( A \) 是 \( B \) 的子类型，则 \( F(B) \) 是 \( F(A) \) 的子类型。

### 5.2 双变与类型代数运算

双变是指在某些情况下，类型可以同时表现出协变和逆变的特性。
Rust的类型系统通过Trait和泛型支持类型代数运算。

**形式化定义**：

- 双变：类型 \( A \) 和类型 \( B \) 之间存在协变和逆变关系。

```rust
fn process<F>(f: F) where F: Fn(&Dog) {
    // ...
}
```

## 控制流与执行流的关系

### 6.1 同步与异步执行流

Rust支持同步和异步编程模型。
同步执行流是线性的，而异步执行流则允许并发操作。

**形式化定义**：

- 同步流 \( S \) 是线性执行的过程。
- 异步流 \( A \) 是并发执行的过程。

```rust
async fn async_function() {
    // 异步操作
}
```

### 6.2 同构关系与转换

同构关系描述了不同类型之间的结构相似性。
Rust的类型系统通过Trait和泛型实现类型之间的转换。

**形式化定义**：

- 同构关系 \( H \) 是在不同类型之间建立的结构相似性。

```rust
fn convert<T: Into<U>, U>(value: T) -> U {
    value.into()
}
```

## 总结与展望

Rust的类型系统设计在同伦类型论、范畴论和控制论的视角下展现出其独特的复杂性与灵活性。
通过对类型、变量、所有权、生命周期、借用等概念的深入分析，我们可以更好地理解Rust的设计理念及其在实际编程中的应用。

未来的研究方向可以集中在以下几个方面：

1. **更深入的形式化模型**：探索更复杂的型变规则和类型转换机制。
2. **跨语言比较**：分析其他语言中的型变规则与Rust的异同。
3. **实际应用案例**：研究Rust在大型项目中的类型转换与型变应用。

## 思维导图

```text
Rust类型系统设计
├── 类型与变量
│   ├── 类型定义
│   ├── 变量引用
│   └── 所有权与生命周期
├── 类型分类
│   ├── 原始类型
│   ├── 代数类型
│   ├── 组合类型
│   └── Trait类型
├── 类型解构
│   ├── 解构定义
│   ├── 控制流
│   └── 一致性
├── 型变规则
│   ├── 协变
│   ├── 逆变
│   ├── 不变
│   └── 双变
├── 控制流
│   ├── 同步执行流
│   ├── 异步执行流
│   └── 同构关系
└── 总结与展望
    ├── 形式化模型
    ├── 跨语言比较
    └── 实际应用案例
```
# Rust 设计模式实战扩展

## 🎨 创建型模式

### 1. Builder 模式（构建器模式）

**问题**：如何优雅地创建具有多个可选参数的复杂对象？

**解决方案**：使用Builder模式，提供流畅的链式API。

```rust
#[derive(Debug, Clone)]
pub struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout_ms: u64,
}

pub struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
    timeout_ms: u64,
}

impl HttpRequestBuilder {
    pub fn new(method: &str, url: &str) -> Self {
        Self {
            method: method.to_string(),
            url: url.to_string(),
            headers: Vec::new(),
            body: None,
            timeout_ms: 5000,
        }
    }
    
    pub fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }
    
    pub fn body(mut self, body: String) -> Self {
        self.body = Some(body);
        self
    }
    
    pub fn timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }
    
    pub fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
            timeout_ms: self.timeout_ms,
        }
    }
}

// 使用示例
fn builder_pattern_example() {
    let request = HttpRequestBuilder::new("POST", "https://api.example.com/users")
        .header("Content-Type", "application/json")
        .header("Authorization", "Bearer token")
        .body(r#"{"name": "Alice"}"#.to_string())
        .timeout(10000)
        .build();
    
    println!("Request: {:?}", request);
}
```

---

### 2. Factory 模式（工厂模式）

**问题**：如何根据不同条件创建不同类型的对象？

**解决方案**：使用Factory模式封装对象创建逻辑。

```rust
use std::fmt::Debug;

trait Database: Debug {
    fn connect(&self) -> Result<String, String>;
    fn query(&self, sql: &str) -> Result<Vec<String>, String>;
}

#[derive(Debug)]
struct PostgresDB {
    host: String,
    port: u16,
}

impl Database for PostgresDB {
    fn connect(&self) -> Result<String, String> {
        Ok(format!("Connected to Postgres at {}:{}", self.host, self.port))
    }
    
    fn query(&self, sql: &str) -> Result<Vec<String>, String> {
        Ok(vec![format!("Postgres result for: {}", sql)])
    }
}

#[derive(Debug)]
struct MySQLDB {
    host: String,
    port: u16,
}

impl Database for MySQLDB {
    fn connect(&self) -> Result<String, String> {
        Ok(format!("Connected to MySQL at {}:{}", self.host, self.port))
    }
    
    fn query(&self, sql: &str) -> Result<Vec<String>, String> {
        Ok(vec![format!("MySQL result for: {}", sql)])
    }
}

// 工厂
struct DatabaseFactory;

impl DatabaseFactory {
    fn create(db_type: &str, host: &str, port: u16) -> Result<Box<dyn Database>, String> {
        match db_type {
            "postgres" => Ok(Box::new(PostgresDB {
                host: host.to_string(),
                port,
            })),
            "mysql" => Ok(Box::new(MySQLDB {
                host: host.to_string(),
                port,
            })),
            _ => Err(format!("Unknown database type: {}", db_type)),
        }
    }
}

// 使用示例
fn factory_pattern_example() -> Result<(), String> {
    let db = DatabaseFactory::create("postgres", "localhost", 5432)?;
    println!("{}", db.connect()?);
    println!("{:?}", db.query("SELECT * FROM users")?);
    Ok(())
}
```

---

### 3. Singleton 模式（单例模式）

**问题**：如何确保一个类只有一个实例？

**解决方案**：使用`lazy_static`或`once_cell`实现线程安全的单例。

```rust
use std::sync::{Arc, Mutex, Once};

static INIT: Once = Once::new();
static mut INSTANCE: Option<Arc<Mutex<Config>>> = None;

#[derive(Debug, Clone)]
struct Config {
    api_key: String,
    timeout_ms: u64,
}

impl Config {
    fn global() -> Arc<Mutex<Config>> {
        unsafe {
            INIT.call_once(|| {
                INSTANCE = Some(Arc::new(Mutex::new(Config {
                    api_key: "default_key".to_string(),
                    timeout_ms: 5000,
                })));
            });
            INSTANCE.clone().unwrap()
        }
    }
}

// 更推荐的方式：使用 once_cell
use once_cell::sync::Lazy;

static CONFIG: Lazy<Arc<Mutex<Config>>> = Lazy::new(|| {
    Arc::new(Mutex::new(Config {
        api_key: "default_key".to_string(),
        timeout_ms: 5000,
    }))
});

fn singleton_pattern_example() {
    // 方式1：使用Once
    let config1 = Config::global();
    println!("{:?}", config1.lock().unwrap());
    
    // 方式2：使用 Lazy (推荐)
    let config2 = CONFIG.clone();
    config2.lock().unwrap().api_key = "new_key".to_string();
    println!("{:?}", config2.lock().unwrap());
}
```

---

## 🏗️ 结构型模式

### 4. Adapter 模式（适配器模式）

**问题**：如何让不兼容的接口协同工作？

**解决方案**：创建一个适配器类，转换接口。

```rust
// 旧接口
trait LegacyLogger {
    fn log_message(&self, msg: &str);
}

struct OldLogger;

impl LegacyLogger for OldLogger {
    fn log_message(&self, msg: &str) {
        println!("[OLD] {}", msg);
    }
}

// 新接口
trait ModernLogger {
    fn info(&self, msg: &str);
    fn error(&self, msg: &str);
}

// 适配器
struct LoggerAdapter<T: LegacyLogger> {
    legacy: T,
}

impl<T: LegacyLogger> ModernLogger for LoggerAdapter<T> {
    fn info(&self, msg: &str) {
        self.legacy.log_message(&format!("INFO: {}", msg));
    }
    
    fn error(&self, msg: &str) {
        self.legacy.log_message(&format!("ERROR: {}", msg));
    }
}

// 使用示例
fn adapter_pattern_example() {
    let old_logger = OldLogger;
    let adapter = LoggerAdapter { legacy: old_logger };
    
    adapter.info("Application started");
    adapter.error("Something went wrong");
}
```

---

### 5. Decorator 模式（装饰器模式）

**问题**：如何动态地为对象添加新功能？

**解决方案**：使用装饰器包装原始对象。

```rust
trait DataSource {
    fn read(&self) -> String;
    fn write(&self, data: &str);
}

struct FileDataSource {
    filename: String,
}

impl DataSource for FileDataSource {
    fn read(&self) -> String {
        format!("Reading from {}", self.filename)
    }
    
    fn write(&self, data: &str) {
        println!("Writing to {}: {}", self.filename, data);
    }
}

// 加密装饰器
struct EncryptionDecorator<T: DataSource> {
    wrapped: T,
}

impl<T: DataSource> DataSource for EncryptionDecorator<T> {
    fn read(&self) -> String {
        let data = self.wrapped.read();
        format!("Decrypted({})", data)
    }
    
    fn write(&self, data: &str) {
        let encrypted = format!("Encrypted({})", data);
        self.wrapped.write(&encrypted);
    }
}

// 压缩装饰器
struct CompressionDecorator<T: DataSource> {
    wrapped: T,
}

impl<T: DataSource> DataSource for CompressionDecorator<T> {
    fn read(&self) -> String {
        let data = self.wrapped.read();
        format!("Decompressed({})", data)
    }
    
    fn write(&self, data: &str) {
        let compressed = format!("Compressed({})", data);
        self.wrapped.write(&compressed);
    }
}

// 使用示例
fn decorator_pattern_example() {
    let file = FileDataSource {
        filename: "data.txt".to_string(),
    };
    
    // 多层装饰
    let encrypted = EncryptionDecorator { wrapped: file };
    let compressed = CompressionDecorator { wrapped: encrypted };
    
    compressed.write("Secret data");
    println!("{}", compressed.read());
}
```

---

### 6. Facade 模式（外观模式）

**问题**：如何简化复杂子系统的接口？

**解决方案**：提供一个统一的高层接口。

```rust
// 复杂子系统
struct CPU {
    temp: f32,
}

impl CPU {
    fn freeze(&mut self) {
        println!("CPU: Freezing");
    }
    
    fn jump(&mut self, address: usize) {
        println!("CPU: Jumping to {:#x}", address);
    }
    
    fn execute(&mut self) {
        println!("CPU: Executing");
    }
}

struct Memory {
    data: Vec<u8>,
}

impl Memory {
    fn load(&mut self, address: usize, data: &[u8]) {
        println!("Memory: Loading {} bytes at {:#x}", data.len(), address);
        self.data.extend_from_slice(data);
    }
}

struct HardDrive {
    sectors: Vec<Vec<u8>>,
}

impl HardDrive {
    fn read(&self, lba: usize, size: usize) -> Vec<u8> {
        println!("HardDrive: Reading {} bytes from LBA {}", size, lba);
        vec![0; size]
    }
}

// Facade
struct ComputerFacade {
    cpu: CPU,
    memory: Memory,
    hd: HardDrive,
}

impl ComputerFacade {
    fn new() -> Self {
        Self {
            cpu: CPU { temp: 37.0 },
            memory: Memory { data: Vec::new() },
            hd: HardDrive { sectors: Vec::new() },
        }
    }
    
    fn start(&mut self) {
        println!("=== Computer Starting ===");
        self.cpu.freeze();
        
        let boot_sector = self.hd.read(0, 512);
        self.memory.load(0x0000, &boot_sector);
        
        self.cpu.jump(0x0000);
        self.cpu.execute();
        println!("=== Computer Started ===");
    }
}

// 使用示例
fn facade_pattern_example() {
    let mut computer = ComputerFacade::new();
    computer.start(); // 简化的启动接口
}
```

---

## 🎭 行为型模式

### 7. Strategy 模式（策略模式）

**问题**：如何在运行时选择算法？

**解决方案**：定义一系列算法，并使它们可以互换。

```rust
trait CompressionStrategy {
    fn compress(&self, data: &str) -> Vec<u8>;
    fn decompress(&self, data: &[u8]) -> String;
}

struct ZipCompression;

impl CompressionStrategy for ZipCompression {
    fn compress(&self, data: &str) -> Vec<u8> {
        println!("Compressing with ZIP");
        data.as_bytes().to_vec()
    }
    
    fn decompress(&self, data: &[u8]) -> String {
        println!("Decompressing with ZIP");
        String::from_utf8_lossy(data).to_string()
    }
}

struct GzipCompression;

impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &str) -> Vec<u8> {
        println!("Compressing with GZIP");
        data.as_bytes().to_vec()
    }
    
    fn decompress(&self, data: &[u8]) -> String {
        println!("Decompressing with GZIP");
        String::from_utf8_lossy(data).to_string()
    }
}

struct Compressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl Compressor {
    fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }
    
    fn compress(&self, data: &str) -> Vec<u8> {
        self.strategy.compress(data)
    }
    
    fn decompress(&self, data: &[u8]) -> String {
        self.strategy.decompress(data)
    }
}

// 使用示例
fn strategy_pattern_example() {
    let mut compressor = Compressor::new(Box::new(ZipCompression));
    
    let compressed = compressor.compress("Hello World");
    println!("Compressed: {:?}", compressed);
    
    // 运行时切换策略
    compressor.set_strategy(Box::new(GzipCompression));
    let compressed2 = compressor.compress("Hello World");
    println!("Compressed with new strategy: {:?}", compressed2);
}
```

---

### 8. Observer 模式（观察者模式）

**问题**：如何在对象状态改变时通知多个观察者？

**解决方案**：定义一对多的依赖关系。

```rust
use std::cell::RefCell;
use std::rc::Rc;

trait Observer {
    fn update(&self, temperature: f32, humidity: f32, pressure: f32);
}

struct WeatherData {
    observers: Vec<Rc<RefCell<dyn Observer>>>,
    temperature: f32,
    humidity: f32,
    pressure: f32,
}

impl WeatherData {
    fn new() -> Self {
        Self {
            observers: Vec::new(),
            temperature: 0.0,
            humidity: 0.0,
            pressure: 0.0,
        }
    }
    
    fn register_observer(&mut self, observer: Rc<RefCell<dyn Observer>>) {
        self.observers.push(observer);
    }
    
    fn set_measurements(&mut self, temperature: f32, humidity: f32, pressure: f32) {
        self.temperature = temperature;
        self.humidity = humidity;
        self.pressure = pressure;
        self.notify_observers();
    }
    
    fn notify_observers(&self) {
        for observer in &self.observers {
            observer.borrow().update(self.temperature, self.humidity, self.pressure);
        }
    }
}

struct CurrentConditionsDisplay {
    temperature: f32,
    humidity: f32,
}

impl CurrentConditionsDisplay {
    fn new() -> Self {
        Self {
            temperature: 0.0,
            humidity: 0.0,
        }
    }
    
    fn display(&self) {
        println!("Current conditions: {:.1}°C and {:.1}% humidity", 
                 self.temperature, self.humidity);
    }
}

impl Observer for CurrentConditionsDisplay {
    fn update(&self, temperature: f32, humidity: f32, _pressure: f32) {
        println!("CurrentConditionsDisplay: Temperature={:.1}°C, Humidity={:.1}%", 
                 temperature, humidity);
    }
}

// 使用示例
fn observer_pattern_example() {
    let mut weather_data = WeatherData::new();
    
    let display = Rc::new(RefCell::new(CurrentConditionsDisplay::new()));
    weather_data.register_observer(display.clone());
    
    // 更新天气数据，自动通知所有观察者
    weather_data.set_measurements(25.5, 65.0, 1013.0);
    weather_data.set_measurements(26.0, 70.0, 1012.0);
}
```

---

### 9. Command 模式（命令模式）

**问题**：如何将请求封装为对象？

**解决方案**：使用命令对象封装请求。

```rust
trait Command {
    fn execute(&self);
    fn undo(&self);
}

struct Light {
    is_on: std::cell::RefCell<bool>,
}

impl Light {
    fn new() -> Self {
        Self {
            is_on: std::cell::RefCell::new(false),
        }
    }
    
    fn turn_on(&self) {
        *self.is_on.borrow_mut() = true;
        println!("Light is ON");
    }
    
    fn turn_off(&self) {
        *self.is_on.borrow_mut() = false;
        println!("Light is OFF");
    }
}

struct LightOnCommand {
    light: std::rc::Rc<Light>,
}

impl Command for LightOnCommand {
    fn execute(&self) {
        self.light.turn_on();
    }
    
    fn undo(&self) {
        self.light.turn_off();
    }
}

struct LightOffCommand {
    light: std::rc::Rc<Light>,
}

impl Command for LightOffCommand {
    fn execute(&self) {
        self.light.turn_off();
    }
    
    fn undo(&self) {
        self.light.turn_on();
    }
}

struct RemoteControl {
    command: Option<Box<dyn Command>>,
}

impl RemoteControl {
    fn new() -> Self {
        Self { command: None }
    }
    
    fn set_command(&mut self, command: Box<dyn Command>) {
        self.command = Some(command);
    }
    
    fn press_button(&self) {
        if let Some(cmd) = &self.command {
            cmd.execute();
        }
    }
    
    fn press_undo(&self) {
        if let Some(cmd) = &self.command {
            cmd.undo();
        }
    }
}

// 使用示例
fn command_pattern_example() {
    let light = std::rc::Rc::new(Light::new());
    let mut remote = RemoteControl::new();
    
    // 设置开灯命令
    remote.set_command(Box::new(LightOnCommand {
        light: light.clone(),
    }));
    remote.press_button(); // 开灯
    remote.press_undo();   // 撤销（关灯）
    
    // 设置关灯命令
    remote.set_command(Box::new(LightOffCommand {
        light: light.clone(),
    }));
    remote.press_button(); // 关灯
}
```

---

## 🦀 Rust 特有模式

### 10. Newtype 模式

**问题**：如何为现有类型添加新的语义和行为？

**解决方案**：使用元组结构体包装类型。

```rust
// Newtype 包装器
struct Meters(f64);
struct Kilometers(f64);

impl Meters {
    fn to_kilometers(&self) -> Kilometers {
        Kilometers(self.0 / 1000.0)
    }
}

impl Kilometers {
    fn to_meters(&self) -> Meters {
        Meters(self.0 * 1000.0)
    }
}

// 类型安全的ID
struct UserId(u64);
struct ProductId(u64);

fn get_user(id: UserId) -> String {
    format!("User with ID: {}", id.0)
}

fn get_product(id: ProductId) -> String {
    format!("Product with ID: {}", id.0)
}

// 使用示例
fn newtype_pattern_example() {
    let distance = Meters(5000.0);
    let km = distance.to_kilometers();
    println!("Distance: {} km", km.0);
    
    let user_id = UserId(123);
    let product_id = ProductId(456);
    
    println!("{}", get_user(user_id));
    println!("{}", get_product(product_id));
    
    // 编译错误：类型不匹配
    // get_user(product_id);
}
```

---

### 11. RAII 模式（资源获取即初始化）

**问题**：如何确保资源被正确释放？

**解决方案**：利用Rust的Drop trait自动管理资源。

```rust
use std::fs::File;
use std::io::Write;

struct FileGuard {
    file: File,
    auto_close: bool,
}

impl FileGuard {
    fn new(path: &str) -> std::io::Result<Self> {
        Ok(Self {
            file: File::create(path)?,
            auto_close: true,
        })
    }
    
    fn write(&mut self, data: &str) -> std::io::Result<()> {
        self.file.write_all(data.as_bytes())
    }
}

impl Drop for FileGuard {
    fn drop(&mut self) {
        if self.auto_close {
            println!("FileGuard: Automatically closing file");
        }
    }
}

// 使用示例
fn raii_pattern_example() -> std::io::Result<()> {
    {
        let mut guard = FileGuard::new("test.txt")?;
        guard.write("Hello RAII")?;
        // 离开作用域时自动调用Drop
    } // FileGuard::drop() 在这里被调用
    
    println!("File closed automatically!");
    Ok(())
}
```

---

### 12. Type State 模式（类型状态模式）

**问题**：如何在编译时强制状态机的正确性？

**解决方案**：使用类型系统表示状态。

```rust
struct Locked;
struct Unlocked;

struct Door<State> {
    _state: std::marker::PhantomData<State>,
}

impl Door<Locked> {
    fn new() -> Self {
        println!("Creating a locked door");
        Self {
            _state: std::marker::PhantomData,
        }
    }
    
    fn unlock(self) -> Door<Unlocked> {
        println!("Unlocking door");
        Door {
            _state: std::marker::PhantomData,
        }
    }
}

impl Door<Unlocked> {
    fn open(&self) {
        println!("Opening door");
    }
    
    fn lock(self) -> Door<Locked> {
        println!("Locking door");
        Door {
            _state: std::marker::PhantomData,
        }
    }
}

// 使用示例
fn type_state_pattern_example() {
    let door = Door::<Locked>::new();
    
    // 编译错误：locked的门不能打开
    // door.open();
    
    let door = door.unlock();
    door.open(); // OK: unlocked的门可以打开
    
    let door = door.lock();
    // 编译错误：又locked了
    // door.open();
}
```

---

## 📊 模式对比与选择

| 模式 | 使用场景 | 优点 | 缺点 |
|------|---------|------|------|
| **Builder** | 复杂对象构建 | 灵活、可读性好 | 代码量大 |
| **Factory** | 对象创建逻辑复杂 | 解耦创建和使用 | 增加类数量 |
| **Singleton** | 全局唯一实例 | 节省资源 | 难以测试 |
| **Adapter** | 接口不兼容 | 复用现有代码 | 增加复杂度 |
| **Decorator** | 动态添加功能 | 灵活扩展 | 层次多时难debug |
| **Facade** | 简化复杂系统 | 降低耦合 | 可能成为上帝对象 |
| **Strategy** | 算法可互换 | 易扩展 | 客户端需了解策略 |
| **Observer** | 一对多依赖 | 松耦合 | 可能内存泄漏 |
| **Command** | 请求参数化 | 支持撤销 | 命令类膨胀 |
| **Newtype** | 类型安全 | 零成本抽象 | 需要手动实现trait |
| **RAII** | 资源管理 | 自动释放 | 需理解生命周期 |
| **Type State** | 状态机 | 编译时检查 | 学习曲线陡峭 |

---

## 🚀 实战建议

1. **优先使用Rust惯用模式**：Newtype, RAII, Type State
2. **避免过度设计**：只在需要时使用模式
3. **利用类型系统**：让编译器帮你检查
4. **零成本抽象**：确保模式不影响性能
5. **测试驱动**：为每个模式编写单元测试

---

**更新日期**: 2025-10-24  
**文档版本**: 2.0  
**维护者**: C02 Type System Team

