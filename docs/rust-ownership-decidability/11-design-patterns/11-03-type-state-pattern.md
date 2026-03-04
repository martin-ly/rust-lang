# 类型状态模式详解

> **Rust版本**: 1.93.1
> **难度**: 中高级
> **学习目标**: 掌握Rust类型系统最强大的应用，实现编译时状态验证

---

## 目录

- [类型状态模式详解](#类型状态模式详解)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [什么是类型状态模式](#什么是类型状态模式)
    - [为什么Rust特别适合](#为什么rust特别适合)
    - [与传统状态模式的对比](#与传统状态模式的对比)
  - [2. 核心概念](#2-核心概念)
    - [PhantomData](#phantomdata)
    - [类型参数作为状态标记](#类型参数作为状态标记)
    - [状态转换的编码](#状态转换的编码)
  - [3. 基础实现](#3-基础实现)
    - [最简单的类型状态机](#最简单的类型状态机)
    - [消费式状态转换](#消费式状态转换)
    - [状态相关数据](#状态相关数据)
  - [4. 实战案例](#4-实战案例)
    - [案例1：数据库连接](#案例1数据库连接)
    - [案例2：HTTP请求构建器](#案例2http请求构建器)
    - [案例3：文件解析器](#案例3文件解析器)
    - [案例4：订单工作流](#案例4订单工作流)
  - [5. 高级技巧](#5-高级技巧)
    - [可逆状态转换](#可逆状态转换)
    - [状态转换守卫](#状态转换守卫)
    - [组合多个状态](#组合多个状态)
    - [与异步结合](#与异步结合)
  - [6. 权衡与局限](#6-权衡与局限)
    - [代码复杂度](#代码复杂度)
    - [类型爆炸问题](#类型爆炸问题)
    - [序列化挑战](#序列化挑战)
    - [与动态分发的对比](#与动态分发的对比)
  - [7. 最佳实践](#7-最佳实践)
    - [何时使用](#何时使用)
    - [命名约定](#命名约定)
    - [文档与错误信息](#文档与错误信息)
  - [8. 对比其他语言](#8-对比其他语言)
    - [C++](#c)
    - [TypeScript](#typescript)
    - [Haskell](#haskell)
  - [9. 总结](#9-总结)
    - [学习检查清单](#学习检查清单)
    - [进一步阅读](#进一步阅读)

---

## 1. 引言

### 什么是类型状态模式

类型状态模式（Type State Pattern）是一种利用类型系统在编译时编码和验证对象状态的编程技术。它将状态从运行时值提升为编译期类型，使得非法状态转换在编译时被阻止。

```rust
// 传统运行时状态检查
pub struct Connection {
    state: ConnectionState,  // 运行时值
}

impl Connection {
    pub fn query(&self, sql: &str) -> Result<Data, Error> {
        if self.state != ConnectionState::Connected {
            return Err(Error::NotConnected);  // 运行时错误
        }
        // ...
    }
}

// 类型状态：编译时保证
pub struct Connection<State> {
    _state: PhantomData<State>,
}

impl Connection<Connected> {
    pub fn query(&self, sql: &str) -> Data {  // 无需检查，必然已连接
        // ...
    }
}
```

### 为什么Rust特别适合

1. **零成本抽象**: 类型参数在编译期单态化，运行时无开销
2. **所有权系统**: 消费式状态转换自然契合所有权转移
3. **类型推断**: 减少显式类型标注的繁琐
4. **没有空值**: Option类型配合类型状态更安全

```rust
// 编译期移除不可能状态
let conn = Connection::<Disconnected>::new("localhost");
conn.query("SELECT 1");  // 编译错误！Disconnected状态没有query方法
```

### 与传统状态模式的对比

| 特性 | 传统状态模式 | 类型状态模式 |
|------|-------------|-------------|
| 错误检测时机 | 运行时 | 编译时 |
| 运行时开销 | 状态检查、虚函数 | 零成本 |
| 灵活性 | 高（动态状态） | 低（静态状态） |
| 错误信息 | 运行时异常 | 编译错误 |
| 适用场景 | 复杂动态状态 | 有限明确的状态转换 |

---

## 2. 核心概念

### PhantomData

`PhantomData<T>`是一个零大小类型，用于在结构体中"假装"存储一个`T`类型的值，实际不占用内存。

```rust
use std::marker::PhantomData;

pub struct StateMachine<State> {
    data: String,
    // PhantomData<State>告诉编译器我们逻辑上拥有State
    // 但不实际存储它
    _state: PhantomData<State>,
}

// PhantomData影响类型行为：
// - 如果State !Send，则StateMachine !Send
// - 如果State !Sync，则StateMachine !Sync
// - Drop检查认为StateMachine拥有State
```

### 类型参数作为状态标记

```rust
// 定义状态标记（零大小类型）
pub struct Idle;
pub struct Running;
pub struct Stopped;
pub struct Error;

// 泛型结构体以状态为参数
pub struct Process<State> {
    pid: u32,
    _state: PhantomData<State>,
}
```

### 状态转换的编码

状态转换通过方法实现，消费旧状态，返回新状态：

```rust
impl Process<Idle> {
    // start消费Idle状态的Process，返回Running状态的Process
    pub fn start(self) -> Process<Running> {
        println!("Starting process {}", self.pid);
        Process {
            pid: self.pid,
            _state: PhantomData,
        }
    }
}

impl Process<Running> {
    // stop消费Running状态的Process，返回Stopped状态的Process
    pub fn stop(self) -> Process<Stopped> {
        println!("Stopping process {}", self.pid);
        Process {
            pid: self.pid,
            _state: PhantomData,
        }
    }

    // fail消费Running状态的Process，返回Error状态的Process
    pub fn fail(self, code: u32) -> Process<Error> {
        println!("Process {} failed with code {}", self.pid, code);
        Process {
            pid: self.pid,
            _state: PhantomData,
        }
    }
}
```

---

## 3. 基础实现

### 最简单的类型状态机

```rust
use std::marker::PhantomData;

// 状态标记
struct Off;
struct On;

// 类型状态机
struct Light<State> {
    _state: PhantomData<State>,
}

// Off状态的实现
impl Light<Off> {
    fn new() -> Self {
        println!("Creating light (off)");
        Light { _state: PhantomData }
    }

    fn turn_on(self) -> Light<On> {
        println!("Turning light on");
        Light { _state: PhantomData }
    }
}

// On状态的实现
impl Light<On> {
    fn turn_off(self) -> Light<Off> {
        println!("Turning light off");
        Light { _state: PhantomData }
    }

    fn brightness(&self) -> u8 {
        100
    }
}

fn main() {
    let light = Light::new();
    let light = light.turn_on();
    println!("Brightness: {}", light.brightness());
    let light = light.turn_off();
    // light.brightness();  // 编译错误：Off状态没有brightness方法
}
```

### 消费式状态转换

```rust
// 关键点：self（非&self）消费所有权
impl Connection<Disconnected> {
    pub fn connect(self) -> Connection<Connected> {
        // self的所有权被移动，不能再次使用
        Connection {
            stream: TcpStream::connect(&self.address).unwrap(),
            address: self.address,
            _state: PhantomData,
        }
    }
}

// 对比：如果尝试重复转换
let conn = Connection::new("localhost");
let conn = conn.connect();
// conn.connect();  // 编译错误：conn已被移动
```

### 状态相关数据

```rust
// 不同状态可以存储不同数据
struct Disconnected;
struct Connecting {
    attempts: u32,
};
struct Connected {
    session_id: String,
};

struct Client<State> {
    server_address: String,
    state_data: State,  // 实际存储状态数据
}

impl Client<Disconnected> {
    fn new(server: &str) -> Self {
        Client {
            server_address: server.to_string(),
            state_data: Disconnected,
        }
    }

    fn connect(self) -> Client<Connecting> {
        Client {
            server_address: self.server_address,
            state_data: Connecting { attempts: 1 },
        }
    }
}

impl Client<Connecting> {
    fn retry(self) -> Client<Connecting> {
        Client {
            server_address: self.server_address,
            state_data: Connecting {
                attempts: self.state_data.attempts + 1,
            },
        }
    }

    fn connected(self, session: &str) -> Client<Connected> {
        Client {
            server_address: self.server_address,
            state_data: Connected {
                session_id: session.to_string(),
            },
        }
    }
}

impl Client<Connected> {
    fn query(&self, q: &str) -> String {
        format!("Session {} executing: {}", self.state_data.session_id, q)
    }
}
```

---

## 4. 实战案例

### 案例1：数据库连接

```rust
use std::marker::PhantomData;

// 状态标记
pub struct Disconnected;
pub struct Connected;
pub struct Authenticated {
    username: String,
};
pub struct InTransaction {
    username: String,
    tx_id: u64,
};

pub struct DatabaseConnection<State> {
    server: String,
    port: u16,
    state_data: State,
}

// Disconnected状态
impl DatabaseConnection<Disconnected> {
    pub fn new(server: &str, port: u16) -> Self {
        Self {
            server: server.to_string(),
            port,
            state_data: Disconnected,
        }
    }

    pub fn connect(self) -> Result<DatabaseConnection<Connected>, ConnectionError> {
        // 模拟连接
        if self.port == 0 {
            return Err(ConnectionError::InvalidPort);
        }

        println!("Connected to {}:{}", self.server, self.port);
        Ok(DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Connected,
        })
    }
}

// Connected状态
impl DatabaseConnection<Connected> {
    pub fn authenticate(
        self,
        username: &str,
        password: &str,
    ) -> Result<DatabaseConnection<Authenticated>, AuthError> {
        // 验证凭据
        if username.is_empty() || password.is_empty() {
            return Err(AuthError::InvalidCredentials);
        }

        println!("Authenticated as {}", username);
        Ok(DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Authenticated {
                username: username.to_string(),
            },
        })
    }

    pub fn disconnect(self) -> DatabaseConnection<Disconnected> {
        println!("Disconnected from {}:{}", self.server, self.port);
        DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Disconnected,
        }
    }
}

// Authenticated状态
impl DatabaseConnection<Authenticated> {
    pub fn query(&self, sql: &str) -> Result<Vec<Row>, QueryError> {
        println!("[{}] Executing: {}", self.state_data.username, sql);
        Ok(vec![Row { data: "result".to_string() }])
    }

    pub fn begin_transaction(self) -> DatabaseConnection<InTransaction> {
        let tx_id = generate_tx_id();
        println!("[{}] Started transaction {}", self.state_data.username, tx_id);

        DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: InTransaction {
                username: self.state_data.username,
                tx_id,
            },
        }
    }

    pub fn disconnect(self) -> DatabaseConnection<Disconnected> {
        println!("[{}] Disconnected", self.state_data.username);
        DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Disconnected,
        }
    }
}

// InTransaction状态
impl DatabaseConnection<InTransaction> {
    pub fn execute(&self, sql: &str) -> Result<ExecutionResult, QueryError> {
        println!("[Tx {}] Executing: {}", self.state_data.tx_id, sql);
        Ok(ExecutionResult { rows_affected: 1 })
    }

    pub fn commit(self) -> DatabaseConnection<Authenticated> {
        println!("[Tx {}] Committed", self.state_data.tx_id);
        DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Authenticated {
                username: self.state_data.username,
            },
        }
    }

    pub fn rollback(self) -> DatabaseConnection<Authenticated> {
        println!("[Tx {}] Rolled back", self.state_data.tx_id);
        DatabaseConnection {
            server: self.server,
            port: self.port,
            state_data: Authenticated {
                username: self.state_data.username,
            },
        }
    }
}

// 辅助类型
#[derive(Debug)]
pub enum ConnectionError {
    InvalidPort,
    NetworkError(String),
}

#[derive(Debug)]
pub enum AuthError {
    InvalidCredentials,
    AccountLocked,
}

#[derive(Debug)]
pub enum QueryError {
    SyntaxError(String),
    PermissionDenied,
}

pub struct Row {
    data: String,
}

pub struct ExecutionResult {
    rows_affected: u64,
}

fn generate_tx_id() -> u64 {
    42 // 简化实现
}

// 使用示例
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let conn = DatabaseConnection::new("localhost", 5432);

    // 状态转换链
    let results = conn
        .connect()?
        .authenticate("admin", "secret")?
        .query("SELECT * FROM users")?;

    println!("Got {} results", results.len());

    // 事务
    let conn = DatabaseConnection::new("localhost", 5432)
        .connect()?
        .authenticate("admin", "secret")?;

    let tx = conn.begin_transaction();
    tx.execute("INSERT INTO logs VALUES (1)")?;
    tx.execute("INSERT INTO logs VALUES (2)")?;
    let conn = tx.commit();

    conn.disconnect();

    Ok(())
}
```

### 案例2：HTTP请求构建器

```rust
use std::marker::PhantomData;

// 状态标记，使用类型区分构建阶段
pub struct NoUrl;
pub struct HasUrl {
    url: String,
};
pub struct HasMethod {
    url: String,
    method: String,
};
pub struct Ready {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
}

pub struct HttpRequestBuilder<State> {
    state: State,
}

// 初始状态：没有任何必需字段
impl HttpRequestBuilder<NoUrl> {
    pub fn new() -> Self {
        Self { state: NoUrl }
    }

    pub fn url(self, url: &str) -> HttpRequestBuilder<HasUrl> {
        HttpRequestBuilder {
            state: HasUrl {
                url: url.to_string(),
            },
        }
    }
}

// 有URL但未设置方法
impl HttpRequestBuilder<HasUrl> {
    pub fn method(self, method: &str) -> HttpRequestBuilder<HasMethod> {
        HttpRequestBuilder {
            state: HasMethod {
                url: self.state.url,
                method: method.to_string(),
            },
        }
    }

    // 快捷方法
    pub fn get(self) -> HttpRequestBuilder<HasMethod> {
        self.method("GET")
    }

    pub fn post(self) -> HttpRequestBuilder<HasMethod> {
        self.method("POST")
    }
}

// 有URL和方法
impl HttpRequestBuilder<HasMethod> {
    pub fn header(mut self, key: &str, value: &str) -> Self {
        // 这里简化处理，实际需要存储headers
        self
    }

    pub fn body(self, body: Vec<u8>) -> HttpRequestBuilder<Ready> {
        HttpRequestBuilder {
            state: Ready {
                url: self.state.url,
                method: self.state.method,
                headers: Vec::new(),
                body: Some(body),
            },
        }
    }

    pub fn finalize(self) -> HttpRequestBuilder<Ready> {
        HttpRequestBuilder {
            state: Ready {
                url: self.state.url,
                method: self.state.method,
                headers: Vec::new(),
                body: None,
            },
        }
    }
}

// 就绪状态：可以构建或添加可选参数
impl HttpRequestBuilder<Ready> {
    pub fn header(mut self, key: &str, value: &str) -> Self {
        self.state.headers.push((key.to_string(), value.to_string()));
        self
    }

    pub fn build(self) -> HttpRequest {
        HttpRequest {
            url: self.state.url,
            method: self.state.method,
            headers: self.state.headers,
            body: self.state.body,
        }
    }
}

pub struct HttpRequest {
    url: String,
    method: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
}

impl HttpRequest {
    pub fn send(&self) -> Result<HttpResponse, HttpError> {
        println!("Sending {} {}", self.method, self.url);
        Ok(HttpResponse {
            status: 200,
            body: "OK".to_string(),
        })
    }
}

pub struct HttpResponse {
    status: u16,
    body: String,
}

pub struct HttpError;

// 使用
fn main() {
    // 必须按顺序设置必需字段
    let request = HttpRequestBuilder::new()
        .url("https://api.example.com/users")
        .get()
        .header("Authorization", "Bearer token")
        .finalize()
        .build();

    let response = request.send().unwrap();
    println!("Status: {}", response.status);

    // 以下代码无法编译：
    // let builder = HttpRequestBuilder::new();
    // builder.build();  // 错误：NoUrl状态没有build方法

    // let builder = HttpRequestBuilder::new().url("...");
    // builder.build();  // 错误：HasUrl状态没有build方法
}
```

### 案例3：文件解析器

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::marker::PhantomData;
use std::path::Path;

// 解析器状态
pub struct NotOpened;
pub struct Opened {
    reader: BufReader<File>,
    line_count: usize,
};
pub struct Parsed {
    records: Vec<Record>,
};

pub struct CsvParser<State> {
    path: String,
    delimiter: char,
    state_data: State,
}

#[derive(Debug)]
pub struct Record {
    pub fields: Vec<String>,
}

// NotOpened状态
impl CsvParser<NotOpened> {
    pub fn new<P: AsRef<Path>>(path: P) -> Self {
        Self {
            path: path.as_ref().to_string_lossy().to_string(),
            delimiter: ',',
            state_data: NotOpened,
        }
    }

    pub fn delimiter(mut self, delimiter: char) -> Self {
        self.delimiter = delimiter;
        self
    }

    pub fn open(self) -> io::Result<CsvParser<Opened>> {
        let file = File::open(&self.path)?;
        let reader = BufReader::new(file);

        Ok(CsvParser {
            path: self.path,
            delimiter: self.delimiter,
            state_data: Opened {
                reader,
                line_count: 0,
            },
        })
    }
}

// Opened状态
impl CsvParser<Opened> {
    pub fn parse(mut self) -> io::Result<CsvParser<Parsed>> {
        let mut records = Vec::new();
        let mut line = String::new();

        while self.state_data.reader.read_line(&mut line)? > 0 {
            self.state_data.line_count += 1;

            let fields: Vec<String> = line
                .trim()
                .split(self.delimiter)
                .map(|s| s.to_string())
                .collect();

            records.push(Record { fields });
            line.clear();
        }

        println!("Parsed {} lines from {}", self.state_data.line_count, self.path);

        Ok(CsvParser {
            path: self.path,
            delimiter: self.delimiter,
            state_data: Parsed { records },
        })
    }

    pub fn parse_header(mut self) -> io::Result<(Vec<String>, CsvParser<Opened>)> {
        let mut line = String::new();
        self.state_data.reader.read_line(&mut line)?;
        self.state_data.line_count += 1;

        let headers: Vec<String> = line
            .trim()
            .split(self.delimiter)
            .map(|s| s.to_string())
            .collect();

        Ok((headers, self))
    }

    pub fn lines_read(&self) -> usize {
        self.state_data.line_count
    }
}

// Parsed状态
impl CsvParser<Parsed> {
    pub fn records(&self) -> &[Record] {
        &self.state_data.records
    }

    pub fn record_count(&self) -> usize {
        self.state_data.records.len()
    }

    pub fn into_records(self) -> Vec<Record> {
        self.state_data.records
    }
}

// 使用
fn main() -> io::Result<()> {
    // 创建临时测试文件
    std::fs::write("test.csv", "name,age\nAlice,30\nBob,25")?;

    let parser = CsvParser::new("test.csv")
        .delimiter(',')
        .open()?
        .parse()?;

    println!("Records: {}", parser.record_count());
    for record in parser.records() {
        println!("{:?}", record);
    }

    // 清理
    std::fs::remove_file("test.csv")?;

    Ok(())
}
```

### 案例4：订单工作流

```rust
use std::marker::PhantomData;
use std::collections::HashMap;

// 订单状态
pub struct Cart {
    items: Vec<(String, f64)>,
};
pub struct Checkout {
    items: Vec<(String, f64)>,
    shipping_address: String,
};
pub struct PaymentPending {
    items: Vec<(String, f64)>,
    shipping_address: String,
    payment_method: String,
};
pub struct Paid {
    order_id: String,
    items: Vec<(String, f64)>,
    total: f64,
};
pub struct Shipped {
    order_id: String,
    tracking_number: String,
};
pub struct Delivered {
    order_id: String,
    delivered_at: String,
};

pub struct Order<State> {
    state_data: State,
}

// Cart状态
impl Order<Cart> {
    pub fn new() -> Self {
        Order {
            state_data: Cart {
                items: Vec::new(),
            },
        }
    }

    pub fn add_item(mut self, name: &str, price: f64) -> Self {
        self.state_data.items.push((name.to_string(), price));
        self
    }

    pub fn total(&self) -> f64 {
        self.state_data.items.iter().map(|(_, price)| price).sum()
    }

    pub fn checkout(self, address: &str) -> Order<Checkout> {
        Order {
            state_data: Checkout {
                items: self.state_data.items,
                shipping_address: address.to_string(),
            },
        }
    }
}

// Checkout状态
impl Order<Checkout> {
    pub fn select_payment(self, method: &str) -> Order<PaymentPending> {
        Order {
            state_data: PaymentPending {
                items: self.state_data.items,
                shipping_address: self.state_data.shipping_address,
                payment_method: method.to_string(),
            },
        }
    }

    pub fn items(&self) -> &[(String, f64)] {
        &self.state_data.items
    }
}

// PaymentPending状态
impl Order<PaymentPending> {
    pub fn pay(self, transaction_id: &str) -> Result<Order<Paid>, PaymentError> {
        let total: f64 = self.state_data.items.iter().map(|(_, p)| p).sum();

        println!("Processing payment via {}", self.state_data.payment_method);
        println!("Transaction: {}", transaction_id);

        Ok(Order {
            state_data: Paid {
                order_id: generate_order_id(),
                items: self.state_data.items,
                total,
            },
        })
    }
}

// Paid状态
impl Order<Paid> {
    pub fn order_id(&self) -> &str {
        &self.state_data.order_id
    }

    pub fn ship(self, tracking: &str) -> Order<Shipped> {
        println!("Order {} shipped with tracking {}",
            self.state_data.order_id, tracking);

        Order {
            state_data: Shipped {
                order_id: self.state_data.order_id,
                tracking_number: tracking.to_string(),
            },
        }
    }
}

// Shipped状态
impl Order<Shipped> {
    pub fn tracking_number(&self) -> &str {
        &self.state_data.tracking_number
    }

    pub fn deliver(self) -> Order<Delivered> {
        Order {
            state_data: Delivered {
                order_id: self.state_data.order_id,
                delivered_at: "2026-03-04".to_string(),
            },
        }
    }
}

// Delivered状态
impl Order<Delivered> {
    pub fn delivered_at(&self) -> &str {
        &self.state_data.delivered_at
    }
}

#[derive(Debug)]
pub enum PaymentError {
    InsufficientFunds,
    CardDeclined,
    NetworkError,
}

fn generate_order_id() -> String {
    "ORD-12345".to_string()
}

// 使用
fn main() -> Result<(), PaymentError> {
    let order = Order::new()
        .add_item("Laptop", 999.99)
        .add_item("Mouse", 29.99)
        .checkout("123 Main St")
        .select_payment("Credit Card")
        .pay("TXN-789")?
        .ship("TRK-456")
        .deliver();

    println!("Delivered at: {}", order.delivered_at());

    // 非法状态转换在编译时被阻止：
    // Order::new().pay(...);  // 错误：Cart状态没有pay方法
    // Order::new().ship(...); // 错误：Cart状态没有ship方法

    Ok(())
}
```

---

## 5. 高级技巧

### 可逆状态转换

```rust
// 某些状态转换可以逆转
impl Connection<Connected> {
    pub fn disconnect(self) -> Connection<Disconnected> {
        Connection {
            server: self.server,
            port: self.port,
            _state: PhantomData,
        }
    }
}

impl Connection<Disconnected> {
    pub fn connect(self) -> Result<Connection<Connected>, Error> {
        // ...
    }
}
```

### 状态转换守卫

```rust
use std::marker::PhantomData;

struct Restricted<S>(PhantomData<S>);
struct Unrestricted<S>(PhantomData<S>);

trait AccessLevel {}
struct ReadOnly;
struct ReadWrite;
impl AccessLevel for ReadOnly {}
impl AccessLevel for ReadWrite {}

struct DatabaseConnection<Access: AccessLevel> {
    _access: PhantomData<Access>,
}

impl DatabaseConnection<ReadOnly> {
    fn query(&self) -> Vec<Row> {
        vec![]
    }

    // ReadOnly不能升级，只能创建新的连接
}

impl DatabaseConnection<ReadWrite> {
    fn query(&self) -> Vec<Row> {
        vec![]
    }

    fn insert(&mut self, data: &str) {
        println!("Inserting: {}", data);
    }
}

// 只能通过特定方式创建ReadWrite连接
impl DatabaseConnection<ReadWrite> {
    fn with_credentials(user: &str, pass: &str) -> Option<Self> {
        if authenticate(user, pass) {
            Some(Self { _access: PhantomData })
        } else {
            None
        }
    }
}

fn authenticate(_user: &str, _pass: &str) -> bool {
    true
}

struct Row;
```

### 组合多个状态

```rust
use std::marker::PhantomData;

// 独立的维度可以组合
struct Connection<NetworkState, AuthState> {
    _network: PhantomData<NetworkState>,
    _auth: PhantomData<AuthState>,
}

struct Disconnected;
struct Connected;
struct Anonymous;
struct Authenticated {
    user: String,
};

// 实现各种组合
impl Connection<Disconnected, Anonymous> {
    fn new() -> Self {
        Connection {
            _network: PhantomData,
            _auth: PhantomData,
        }
    }

    fn connect(self) -> Connection<Connected, Anonymous> {
        Connection {
            _network: PhantomData,
            _auth: PhantomData,
        }
    }
}

impl<T> Connection<Connected, T> {
    fn disconnect(self) -> Connection<Disconnected, Anonymous> {
        Connection {
            _network: PhantomData,
            _auth: PhantomData,
        }
    }
}

impl Connection<Connected, Anonymous> {
    fn login(self, user: &str) -> Connection<Connected, Authenticated> {
        Connection {
            _network: PhantomData,
            _auth: PhantomData,
        }
    }
}

impl Connection<Connected, Authenticated> {
    fn query(&self) -> Vec<String> {
        vec!["data".to_string()]
    }

    fn logout(self) -> Connection<Connected, Anonymous> {
        Connection {
            _network: PhantomData,
            _auth: PhantomData,
        }
    }
}
```

### 与异步结合

```rust
use std::future::Future;
use std::marker::PhantomData;
use std::pin::Pin;

struct AsyncConnection<State> {
    _state: PhantomData<State>,
}

struct Disconnected;
struct Connected;

impl AsyncConnection<Disconnected> {
    async fn connect(self) -> Result<AsyncConnection<Connected>, Error> {
        // 异步连接
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        println!("Connected!");
        Ok(AsyncConnection { _state: PhantomData })
    }
}

impl AsyncConnection<Connected> {
    async fn query(&self, sql: &str) -> Result<Vec<Row>, Error> {
        println!("Querying: {}", sql);
        Ok(vec![Row])
    }

    async fn disconnect(self) -> AsyncConnection<Disconnected> {
        println!("Disconnected!");
        AsyncConnection { _state: PhantomData }
    }
}

struct Row;
struct Error;

// 使用
async fn example() -> Result<(), Error> {
    let conn = AsyncConnection::<Disconnected> { _state: PhantomData };
    let conn = conn.connect().await?;
    let rows = conn.query("SELECT 1").await?;
    println!("Got {} rows", rows.len());
    let _conn = conn.disconnect().await;
    Ok(())
}
```

---

## 6. 权衡与局限

### 代码复杂度

类型状态模式增加了代码量和复杂性：

```rust
// 无类型状态：一个impl块
struct Connection {
    state: State,
}

impl Connection {
    fn connect(&mut self) { ... }
    fn query(&self) { ... }
    fn disconnect(&mut self) { ... }
}

// 类型状态：多个impl块
struct Connection<S> { ... }

impl Connection<Disconnected> {
    fn connect(self) -> Connection<Connected> { ... }
}

impl Connection<Connected> {
    fn query(&self) { ... }
    fn disconnect(self) -> Connection<Disconnected> { ... }
}
```

### 类型爆炸问题

当状态维度增加时，类型组合呈指数增长：

```rust
// 2个维度，每个2个状态 = 4种组合
Connection<Connected, Authenticated>
Connection<Connected, Anonymous>
Connection<Disconnected, Authenticated>  // 可能非法
Connection<Disconnected, Anonymous>
```

### 序列化挑战

类型状态难以序列化，因为状态是类型而非值：

```rust
// 难以存储到数据库
impl serde::Serialize for Connection<Connected> {
    // 反序列化后恢复为什么类型？
}
```

解决方案：使用单独的枚举表示状态，序列化后通过运行时检查转换。

### 与动态分发的对比

```rust
// 类型状态：静态分发，零成本
let conn = Connection::new().connect().authenticate()?;

// trait对象：动态分发，运行时检查
let conn: Box<dyn Connection> = Connection::new();
conn.connect();  // 运行时检查当前状态
```

---

## 7. 最佳实践

### 何时使用

**适合使用类型状态**:

- 状态数量有限且明确
- 状态转换规则严格
- 非法状态转换必须是编译错误
- 性能要求高（避免运行时检查）

**不适合使用**:

- 状态过多或动态
- 需要序列化/持久化状态
- 状态转换规则经常变化
- 需要运行时配置状态机

### 命名约定

```rust
// 状态类型使用名词或形容词
struct Connected;
struct Authenticated;
struct InTransaction;

// 可选：使用命名空间
mod state {
    pub struct Connected;
    pub struct Disconnected;
}

// 方法使用动词短语
impl Connection<Disconnected> {
    fn connect(self) -> Connection<Connected> { ... }
}

impl Connection<Connected> {
    fn disconnect(self) -> Connection<Disconnected> { ... }
    fn authenticate(self) -> Connection<Authenticated> { ... }
}
```

### 文档与错误信息

```rust
/// A database connection.
///
/// The connection uses type states to ensure at compile time that:
/// - You cannot query before connecting
/// - You cannot disconnect before connecting
/// - You must authenticate before executing sensitive operations
///
/// # Example
/// ```
/// let conn = Connection::new("localhost")
///     .connect()?  // Must connect first
///     .authenticate("user", "pass")?  // Must authenticate
///     .query("SELECT *")?;  // Now you can query
/// ```
pub struct Connection<State> { ... }
```

---

## 8. 对比其他语言

### C++

C++可以使用模板实现类似模式，但缺乏Rust的所有权系统：

```cpp
// C++使用CRTP或模板
struct Disconnected {};
struct Connected {};

template<typename State>
class Connection {
public:
    Connection<Connected> connect() && {
        return Connection<Connected>{};
    }
};

// 问题：没有所有权系统保证状态转换，容易出错
```

### TypeScript

TypeScript可以使用条件类型和泛型，但只在编译时有效：

```typescript
// 使用条件类型
type Connection<State> = {
    state: State;
} & (State extends 'disconnected' ? {
    connect(): Connection<'connected'>;
} : State extends 'connected' ? {
    query(): any[];
    disconnect(): Connection<'disconnected'>;
} : {});

// 实际运行时没有类型信息
```

### Haskell

Haskell与Rust最接近，使用类型类和代数数据类型：

```haskell
-- 使用GADTs或类型类
{-# LANGUAGE GADTs #-}

data Disconnected
data Connected

data Connection state where
    DisconnectedConn :: Connection Disconnected
    ConnectedConn :: Connection Connected

connect :: Connection Disconnected -> IO (Connection Connected)
connect _ = return ConnectedConn

query :: Connection Connected -> IO [Row]
query _ = return []
```

---

## 9. 总结

类型状态模式是Rust类型系统的强大应用，它将运行时检查转移到编译时，提供：

1. **类型安全**: 非法状态转换在编译时被阻止
2. **零成本抽象**: 运行时无开销
3. **自文档化**: API显示可用的操作
4. **重构安全**: 改变状态规则会立即显示所有受影响的代码

然而，它也带来了复杂性和局限性。合理权衡后，在适当场景下使用类型状态模式，可以显著提升代码质量和可靠性。

### 学习检查清单

- [ ] 理解PhantomData的作用
- [ ] 能实现基础类型状态机
- [ ] 能设计多状态的复杂系统
- [ ] 了解何时不使用类型状态
- [ ] 能权衡类型状态与运行时检查

### 进一步阅读

- [Rust Design Patterns - Type State](https://rust-unofficial.github.io/patterns/patterns/behavioural/type-state.html)
- [PhantomData documentation](https://doc.rust-lang.org/std/marker/struct.PhantomData.html)
- [Rust By Example - Generics](https://doc.rust-lang.org/rust-by-example/generics.html)
