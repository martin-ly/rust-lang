# Trait系统高级代码示例补充

## 🚀 异步Trait（Rust 1.75+稳定）

### 案例：异步数据库接口

```rust
use std::error::Error;

// 异步trait（Rust 1.75+原生支持）
trait AsyncDatabase {
    async fn connect(&self, url: &str) -> Result<(), Box<dyn Error>>;
    async fn query(&self, sql: &str) -> Result<Vec<String>, Box<dyn Error>>;
    async fn execute(&self, sql: &str) -> Result<u64, Box<dyn Error>>;
}

struct PostgresDB;

impl AsyncDatabase for PostgresDB {
    async fn connect(&self, url: &str) -> Result<(), Box<dyn Error>> {
        println!("Connecting to PostgreSQL at {}", url);
        // 模拟异步连接
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Ok(())
    }

    async fn query(&self, sql: &str) -> Result<Vec<String>, Box<dyn Error>> {
        println!("Executing query: {}", sql);
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        Ok(vec!["result1".to_string(), "result2".to_string()])
    }

    async fn execute(&self, sql: &str) -> Result<u64, Box<dyn Error>> {
        println!("Executing: {}", sql);
        tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
        Ok(1)
    }
}

#[tokio::main]
async fn async_trait_example() -> Result<(), Box<dyn Error>> {
    let db = PostgresDB;
    db.connect("postgres://localhost/mydb").await?;
    let results = db.query("SELECT * FROM users").await?;
    println!("Results: {:?}", results);
    Ok(())
}
```

---

## 🎯 Trait对象高级应用

### 案例：插件系统实现

```rust
use std::any::Any;
use std::collections::HashMap;

// 插件接口
trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn initialize(&mut self) -> Result<(), String>;
    fn execute(&self, input: &str) -> Result<String, String>;
    fn shutdown(&mut self);

    // 向下转型支持
    fn as_any(&self) -> &dyn Any;
}

// 日志插件
struct LoggerPlugin {
    initialized: bool,
    log_buffer: Vec<String>,
}

impl LoggerPlugin {
    fn new() -> Self {
        Self {
            initialized: false,
            log_buffer: Vec::new(),
        }
    }

    // 插件特定方法
    fn get_logs(&self) -> &[String] {
        &self.log_buffer
    }
}

impl Plugin for LoggerPlugin {
    fn name(&self) -> &str {
        "Logger"
    }

    fn version(&self) -> &str {
        "1.0.0"
    }

    fn initialize(&mut self) -> Result<(), String> {
        self.initialized = true;
        println!("[Logger] Initialized");
        Ok(())
    }

    fn execute(&self, input: &str) -> Result<String, String> {
        if !self.initialized {
            return Err("Plugin not initialized".to_string());
        }
        println!("[Logger] Logging: {}", input);
        Ok(format!("Logged: {}", input))
    }

    fn shutdown(&mut self) {
        self.initialized = false;
        println!("[Logger] Shutdown");
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// 插件管理器
struct PluginManager {
    plugins: HashMap<String, Box<dyn Plugin>>,
}

impl PluginManager {
    fn new() -> Self {
        Self {
            plugins: HashMap::new(),
        }
    }

    fn register(&mut self, plugin: Box<dyn Plugin>) -> Result<(), String> {
        let name = plugin.name().to_string();
        if self.plugins.contains_key(&name) {
            return Err(format!("Plugin '{}' already registered", name));
        }
        self.plugins.insert(name, plugin);
        Ok(())
    }

    fn initialize_all(&mut self) -> Result<(), String> {
        for (name, plugin) in &mut self.plugins {
            println!("Initializing plugin: {}", name);
            plugin.initialize()?;
        }
        Ok(())
    }

    fn execute(&self, plugin_name: &str, input: &str) -> Result<String, String> {
        self.plugins
            .get(plugin_name)
            .ok_or_else(|| format!("Plugin '{}' not found", plugin_name))?
            .execute(input)
    }

    // 向下转型示例
    fn get_logger_logs(&self) -> Option<&[String]> {
        self.plugins
            .get("Logger")
            .and_then(|p| p.as_any().downcast_ref::<LoggerPlugin>())
            .map(|logger| logger.get_logs())
    }
}

fn plugin_system_example() -> Result<(), String> {
    let mut manager = PluginManager::new();

    manager.register(Box::new(LoggerPlugin::new()))?;
    manager.initialize_all()?;

    let result = manager.execute("Logger", "Test message")?;
    println!("Result: {}", result);

    // 访问插件特定方法
    if let Some(logs) = manager.get_logger_logs() {
        println!("Logs: {:?}", logs);
    }

    Ok(())
}
```

---

## 📊 性能对比：静态 vs 动态分发

### 完整基准测试

```rust
use std::time::Instant;

trait Processor {
    fn process(&self, data: &[i32]) -> i64;
}

struct SumProcessor;

impl Processor for SumProcessor {
    fn process(&self, data: &[i32]) -> i64 {
        data.iter().map(|&x| x as i64).sum()
    }
}

struct ProductProcessor;

impl Processor for ProductProcessor {
    fn process(&self, data: &[i32]) -> i64 {
        data.iter().map(|&x| x as i64).product()
    }
}

// 静态分发（泛型）
fn process_static<T: Processor>(processor: &T, data: &[i32]) -> i64 {
    processor.process(data)
}

// 动态分发（trait对象）
fn process_dynamic(processor: &dyn Processor, data: &[i32]) -> i64 {
    processor.process(data)
}

fn benchmark_dispatch() {
    let data: Vec<i32> = (1..=1000).collect();
    let processor = SumProcessor;

    // 基准测试1：静态分发
    let start = Instant::now();
    for _ in 0..100_000 {
        let _ = process_static(&processor, &data);
    }
    let static_duration = start.elapsed();

    // 基准测试2：动态分发
    let processor_dyn: &dyn Processor = &processor;
    let start = Instant::now();
    for _ in 0..100_000 {
        let _ = process_dynamic(processor_dyn, &data);
    }
    let dynamic_duration = start.elapsed();

    println!("静态分发: {:?}", static_duration);
    println!("动态分发: {:?}", dynamic_duration);
    println!("性能差异: {:.2}x",
             dynamic_duration.as_nanos() as f64 / static_duration.as_nanos() as f64);
}
```

---

## 🔧 标准库Trait深度应用

### From/Into实战

```rust
use std::convert::{From, Into};

// 自定义错误类型
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
    Custom(String),
}

// 实现From以支持 ? 操作符
impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError::Io(err)
    }
}

impl From<std::num::ParseIntError> for AppError {
    fn from(err: std::num::ParseIntError) -> Self {
        AppError::Parse(err)
    }
}

impl From<String> for AppError {
    fn from(msg: String) -> Self {
        AppError::Custom(msg)
    }
}

// 使用Into简化转换
fn process_value<T: Into<String>>(value: T) -> String {
    let s: String = value.into();
    format!("Processed: {}", s)
}

fn from_into_example() -> Result<(), AppError> {
    // From自动提供Into
    let s: String = 42.into();  // i32 -> String (需要实现)

    // 使用Into约束
    println!("{}", process_value("hello"));
    println!("{}", process_value(String::from("world")));

    // ? 操作符自动转换
    let _value: i32 = "42".parse()?;  // ParseIntError -> AppError

    Ok(())
}
```

---

### Iterator Trait 高级应用

```rust
// 自定义迭代器
struct Fibonacci {
    current: u64,
    next: u64,
}

impl Fibonacci {
    fn new() -> Self {
        Fibonacci {
            current: 0,
            next: 1,
        }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current;

        // 防止溢出
        self.current = self.next;
        self.next = match current.checked_add(self.next) {
            Some(sum) => sum,
            None => return None,
        };

        Some(current)
    }
}

// 组合迭代器
struct ChainedIterator<T> {
    iterators: Vec<Box<dyn Iterator<Item = T>>>,
    current_index: usize,
}

impl<T> ChainedIterator<T> {
    fn new() -> Self {
        Self {
            iterators: Vec::new(),
            current_index: 0,
        }
    }

    fn add<I: Iterator<Item = T> + 'static>(mut self, iter: I) -> Self {
        self.iterators.push(Box::new(iter));
        self
    }
}

impl<T> Iterator for ChainedIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current_index < self.iterators.len() {
            if let Some(item) = self.iterators[self.current_index].next() {
                return Some(item);
            }
            self.current_index += 1;
        }
        None
    }
}

fn iterator_example() {
    // Fibonacci迭代器
    let fib = Fibonacci::new();
    let first_10: Vec<u64> = fib.take(10).collect();
    println!("Fibonacci: {:?}", first_10);

    // 组合迭代器
    let chained = ChainedIterator::new()
        .add(1..=5)
        .add(10..=15)
        .add(20..=25);

    let combined: Vec<i32> = chained.collect();
    println!("Chained: {:?}", combined);
}
```

---

## 🎨 Trait组合模式

### Mixin模式

```rust
// 基础trait
trait Serializable {
    fn serialize(&self) -> String;
}

trait Deserializable: Sized {
    fn deserialize(data: &str) -> Result<Self, String>;
}

trait Persistable: Serializable + Deserializable {
    fn save(&self, path: &str) -> Result<(), String> {
        let data = self.serialize();
        std::fs::write(path, data)
            .map_err(|e| e.to_string())
    }

    fn load(path: &str) -> Result<Self, String> {
        let data = std::fs::read_to_string(path)
            .map_err(|e| e.to_string())?;
        Self::deserialize(&data)
    }
}

// 实现示例
#[derive(Debug, Clone)]
struct User {
    id: u32,
    name: String,
}

impl Serializable for User {
    fn serialize(&self) -> String {
        format!("{}:{}", self.id, self.name)
    }
}

impl Deserializable for User {
    fn deserialize(data: &str) -> Result<Self, String> {
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() != 2 {
            return Err("Invalid format".to_string());
        }

        let id = parts[0].parse()
            .map_err(|_| "Invalid ID".to_string())?;
        let name = parts[1].to_string();

        Ok(User { id, name })
    }
}

// 自动获得Persistable
impl Persistable for User {}

fn mixin_example() -> Result<(), String> {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
    };

    user.save("user.txt")?;
    let loaded = User::load("user.txt")?;
    println!("Loaded: {:?}", loaded);

    Ok(())
}
```

---

### 装饰器Trait模式

```rust
trait Logger {
    fn log(&self, message: &str);
}

struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        println!("[LOG] {}", message);
    }
}

// 装饰器
struct TimestampLogger<L: Logger> {
    inner: L,
}

impl<L: Logger> Logger for TimestampLogger<L> {
    fn log(&self, message: &str) {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        self.inner.log(&format!("[{}] {}", now, message));
    }
}

struct PrefixLogger<L: Logger> {
    inner: L,
    prefix: String,
}

impl<L: Logger> Logger for PrefixLogger<L> {
    fn log(&self, message: &str) {
        self.inner.log(&format!("[{}] {}", self.prefix, message));
    }
}

fn decorator_example() {
    // 基础日志
    let console = ConsoleLogger;
    console.log("Basic message");

    // 添加时间戳
    let timestamped = TimestampLogger { inner: ConsoleLogger };
    timestamped.log("With timestamp");

    // 多层装饰
    let decorated = PrefixLogger {
        inner: TimestampLogger { inner: ConsoleLogger },
        prefix: "APP".to_string(),
    };
    decorated.log("Fully decorated");
}
```

---

## 🧪 类型状态模式（高级）

### 构建器的类型安全

```rust
use std::marker::PhantomData;

// 状态标记
struct Unset;
struct Set<T>(T);

// 构建器
struct ConfigBuilder<Name, Port, Timeout> {
    name: Name,
    port: Port,
    timeout: Timeout,
}

impl ConfigBuilder<Unset, Unset, Unset> {
    fn new() -> Self {
        Self {
            name: Unset,
            port: Unset,
            timeout: Unset,
        }
    }
}

impl<Port, Timeout> ConfigBuilder<Unset, Port, Timeout> {
    fn name(self, name: String) -> ConfigBuilder<Set<String>, Port, Timeout> {
        ConfigBuilder {
            name: Set(name),
            port: self.port,
            timeout: self.timeout,
        }
    }
}

impl<Name, Timeout> ConfigBuilder<Name, Unset, Timeout> {
    fn port(self, port: u16) -> ConfigBuilder<Name, Set<u16>, Timeout> {
        ConfigBuilder {
            name: self.name,
            port: Set(port),
            timeout: self.timeout,
        }
    }
}

impl<Name, Port> ConfigBuilder<Name, Port, Unset> {
    fn timeout(self, timeout: u64) -> ConfigBuilder<Name, Port, Set<u64>> {
        ConfigBuilder {
            name: self.name,
            port: self.port,
            timeout: Set(timeout),
        }
    }
}

struct Config {
    name: String,
    port: u16,
    timeout: u64,
}

// 只有所有字段都设置了才能build
impl ConfigBuilder<Set<String>, Set<u16>, Set<u64>> {
    fn build(self) -> Config {
        Config {
            name: self.name.0,
            port: self.port.0,
            timeout: self.timeout.0,
        }
    }
}

fn typestate_example() {
    // 类型系统确保所有字段都被设置
    let config = ConfigBuilder::new()
        .name("MyApp".to_string())
        .port(8080)
        .timeout(30)
        .build();

    println!("Config: {} on port {}", config.name, config.port);

    // 编译错误：缺少name
    // let config = ConfigBuilder::new()
    //     .port(8080)
    //     .timeout(30)
    //     .build();
}
```

---

## 🏆 完整实战案例：HTTP客户端

```rust
use std::collections::HashMap;
use std::error::Error;
use std::fmt;

// 请求trait
trait HttpRequest {
    fn method(&self) -> &str;
    fn url(&self) -> &str;
    fn headers(&self) -> &HashMap<String, String>;
    fn body(&self) -> Option<&[u8]>;
}

// 响应trait
trait HttpResponse {
    fn status(&self) -> u16;
    fn headers(&self) -> &HashMap<String, String>;
    fn body(&self) -> &[u8];
}

// 客户端trait
trait HttpClient {
    fn send(&self, request: &dyn HttpRequest) -> Result<Box<dyn HttpResponse>, Box<dyn Error>>;
}

// 具体实现
struct Request {
    method: String,
    url: String,
    headers: HashMap<String, String>,
    body: Option<Vec<u8>>,
}

impl HttpRequest for Request {
    fn method(&self) -> &str {
        &self.method
    }

    fn url(&self) -> &str {
        &self.url
    }

    fn headers(&self) -> &HashMap<String, String> {
        &self.headers
    }

    fn body(&self) -> Option<&[u8]> {
        self.body.as_deref()
    }
}

struct Response {
    status: u16,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}

impl HttpResponse for Response {
    fn status(&self) -> u16 {
        self.status
    }

    fn headers(&self) -> &HashMap<String, String> {
        &self.headers
    }

    fn body(&self) -> &[u8] {
        &self.body
    }
}

struct SimpleClient;

impl HttpClient for SimpleClient {
    fn send(&self, request: &dyn HttpRequest) -> Result<Box<dyn HttpResponse>, Box<dyn Error>> {
        println!("Sending {} to {}", request.method(), request.url());

        // 模拟响应
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "text/plain".to_string());

        Ok(Box::new(Response {
            status: 200,
            headers,
            body: b"Hello, World!".to_vec(),
        }))
    }
}

fn http_client_example() -> Result<(), Box<dyn Error>> {
    let mut headers = HashMap::new();
    headers.insert("User-Agent".to_string(), "RustClient/1.0".to_string());

    let request = Request {
        method: "GET".to_string(),
        url: "https://example.com".to_string(),
        headers,
        body: None,
    };

    let client = SimpleClient;
    let response = client.send(&request)?;

    println!("Status: {}", response.status());
    println!("Body: {}", String::from_utf8_lossy(response.body()));

    Ok(())
}
```

---

**更新日期**: 2025-10-24
**文档版本**: 2.0
**作者**: C02 Trait System Advanced Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
