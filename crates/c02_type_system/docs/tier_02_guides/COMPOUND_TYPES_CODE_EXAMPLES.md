# 复合类型高级代码示例补充

## 🚀 高级实战案例

### 案例 5: JSON解析器实现

**完整的递归枚举应用**：

```rust
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum JsonValue {
    Null,
    Boolean(bool),
    Number(f64),
    String(String),
    Array(Vec<JsonValue>),
    Object(HashMap<String, JsonValue>),
}

impl JsonValue {
    /// 类型判断辅助方法
    pub fn is_null(&self) -> bool {
        matches!(self, JsonValue::Null)
    }

    pub fn is_object(&self) -> bool {
        matches!(self, JsonValue::Object(_))
    }

    pub fn is_array(&self) -> bool {
        matches!(self, JsonValue::Array(_))
    }

    /// 路径访问
    pub fn get(&self, path: &str) -> Option<&JsonValue> {
        let parts: Vec<&str> = path.split('.').collect();
        let mut current = self;

        for part in parts {
            match current {
                JsonValue::Object(map) => {
                    current = map.get(part)?;
                }
                JsonValue::Array(arr) => {
                    let index: usize = part.parse().ok()?;
                    current = arr.get(index)?;
                }
                _ => return None,
            }
        }

        Some(current)
    }

    /// 递归转换为字符串
    pub fn stringify(&self) -> String {
        match self {
            JsonValue::Null => "null".to_string(),
            JsonValue::Boolean(b) => b.to_string(),
            JsonValue::Number(n) => n.to_string(),
            JsonValue::String(s) => format!("\"{}\"", s),
            JsonValue::Array(arr) => {
                let items: Vec<String> = arr.iter().map(|v| v.stringify()).collect();
                format!("[{}]", items.join(", "))
            }
            JsonValue::Object(obj) => {
                let items: Vec<String> = obj
                    .iter()
                    .map(|(k, v)| format!("\"{}\": {}", k, v.stringify()))
                    .collect();
                format!("{{{}}}", items.join(", "))
            }
        }
    }
}

impl fmt::Display for JsonValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.stringify())
    }
}

// 使用示例
fn json_example() {
    let mut user = HashMap::new();
    user.insert("name".to_string(), JsonValue::String("Alice".to_string()));
    user.insert("age".to_string(), JsonValue::Number(30.0));
    user.insert("active".to_string(), JsonValue::Boolean(true));

    let mut address = HashMap::new();
    address.insert("city".to_string(), JsonValue::String("Beijing".to_string()));
    address.insert("zip".to_string(), JsonValue::String("100000".to_string()));

    user.insert("address".to_string(), JsonValue::Object(address));

    let json = JsonValue::Object(user);

    // 打印
    println!("{}", json);

    // 路径访问
    if let Some(city) = json.get("address.city") {
        println!("City: {}", city);
    }
}
```

---

### 案例 6: 状态机（游戏角色）

**类型安全的状态转换**：

```rust
// 使用类型系统表示状态
struct Idle;
struct Walking;
struct Running;
struct Jumping;

struct Character<State> {
    name: String,
    health: u32,
    position: (f32, f32),
    _state: std::marker::PhantomData<State>,
}

// 通用方法（所有状态共享）
impl<State> Character<State> {
    fn name(&self) -> &str {
        &self.name
    }

    fn health(&self) -> u32 {
        self.health
    }

    fn take_damage(&mut self, damage: u32) {
        self.health = self.health.saturating_sub(damage);
    }
}

// Idle 状态特定方法
impl Character<Idle> {
    fn new(name: String) -> Self {
        Character {
            name,
            health: 100,
            position: (0.0, 0.0),
            _state: std::marker::PhantomData,
        }
    }

    fn start_walking(self) -> Character<Walking> {
        println!("{} starts walking", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }

    fn jump(self) -> Character<Jumping> {
        println!("{} jumps from idle", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }
}

// Walking 状态特定方法
impl Character<Walking> {
    fn walk(&mut self, dx: f32, dy: f32) {
        self.position.0 += dx;
        self.position.1 += dy;
        println!("{} walks to {:?}", self.name, self.position);
    }

    fn stop(self) -> Character<Idle> {
        println!("{} stops walking", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }

    fn start_running(self) -> Character<Running> {
        println!("{} starts running", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }
}

// Running 状态特定方法
impl Character<Running> {
    fn run(&mut self, dx: f32, dy: f32) {
        self.position.0 += dx * 2.0; // 跑步速度是走路的2倍
        self.position.1 += dy * 2.0;
        println!("{} runs to {:?}", self.name, self.position);
    }

    fn slow_down(self) -> Character<Walking> {
        println!("{} slows down", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }
}

// Jumping 状态特定方法
impl Character<Jumping> {
    fn land(self) -> Character<Idle> {
        println!("{} lands", self.name);
        Character {
            name: self.name,
            health: self.health,
            position: self.position,
            _state: std::marker::PhantomData,
        }
    }
}

// 使用示例：编译时保证状态转换正确
fn character_example() {
    let hero = Character::<Idle>::new("Hero".to_string());

    // 编译通过：idle -> walking
    let mut hero = hero.start_walking();
    hero.walk(1.0, 0.0);

    // 编译通过：walking -> running
    let mut hero = hero.start_running();
    hero.run(2.0, 0.0);

    // 编译通过：running -> walking -> idle
    let hero = hero.slow_down().stop();

    // 编译错误：idle 状态不能调用 run()
    // hero.run(1.0, 0.0);

    println!("Final position: {:?}", hero.position);
}
```

---

### 案例 7: 类型安全的单位系统

**零成本抽象的物理单位**：

```rust
use std::ops::{Add, Sub, Mul, Div};
use std::marker::PhantomData;

// 单位类型标记
struct Meters;
struct Seconds;
struct MetersPerSecond;

// 带单位的值
#[derive(Debug, Clone, Copy)]
struct Quantity<Unit> {
    value: f64,
    _unit: PhantomData<Unit>,
}

impl<Unit> Quantity<Unit> {
    fn new(value: f64) -> Self {
        Quantity {
            value,
            _unit: PhantomData,
        }
    }

    fn value(&self) -> f64 {
        self.value
    }
}

// 相同单位可以相加
impl<Unit> Add for Quantity<Unit> {
    type Output = Quantity<Unit>;

    fn add(self, rhs: Self) -> Self::Output {
        Quantity::new(self.value + rhs.value)
    }
}

// 相同单位可以相减
impl<Unit> Sub for Quantity<Unit> {
    type Output = Quantity<Unit>;

    fn sub(self, rhs: Self) -> Self::Output {
        Quantity::new(self.value - rhs.value)
    }
}

// 距离 / 时间 = 速度
impl Div<Quantity<Seconds>> for Quantity<Meters> {
    type Output = Quantity<MetersPerSecond>;

    fn div(self, rhs: Quantity<Seconds>) -> Self::Output {
        Quantity::new(self.value / rhs.value)
    }
}

// 速度 * 时间 = 距离
impl Mul<Quantity<Seconds>> for Quantity<MetersPerSecond> {
    type Output = Quantity<Meters>;

    fn mul(self, rhs: Quantity<Seconds>) -> Self::Output {
        Quantity::new(self.value * rhs.value)
    }
}

// 便捷构造函数
fn meters(value: f64) -> Quantity<Meters> {
    Quantity::new(value)
}

fn seconds(value: f64) -> Quantity<Seconds> {
    Quantity::new(value)
}

// 使用示例
fn physics_example() {
    let distance = meters(100.0);
    let time = seconds(10.0);

    // 类型安全：计算速度
    let speed = distance / time;
    println!("Speed: {} m/s", speed.value());

    // 类型安全：计算新距离
    let new_time = seconds(5.0);
    let new_distance = speed * new_time;
    println!("New distance: {} m", new_distance.value());

    // 编译错误：不能将距离和时间相加
    // let wrong = distance + time;

    // 编译错误：不能将速度和距离相乘
    // let wrong = speed * distance;
}
```

---

### 案例 8: 构建器模式（高级）

**支持复杂验证和默认值**：

```rust
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum BuilderError {
    MissingField(&'static str),
    InvalidValue(String),
}

impl fmt::Display for BuilderError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuilderError::MissingField(field) => write!(f, "Missing required field: {}", field),
            BuilderError::InvalidValue(msg) => write!(f, "Invalid value: {}", msg),
        }
    }
}

impl Error for BuilderError {}

#[derive(Debug, Clone)]
pub struct DatabaseConfig {
    host: String,
    port: u16,
    database: String,
    username: String,
    password: String,
    pool_size: usize,
    timeout_seconds: u64,
    ssl_enabled: bool,
}

pub struct DatabaseConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    database: Option<String>,
    username: Option<String>,
    password: Option<String>,
    pool_size: Option<usize>,
    timeout_seconds: Option<u64>,
    ssl_enabled: Option<bool>,
}

impl DatabaseConfigBuilder {
    pub fn new() -> Self {
        Self {
            host: None,
            port: None,
            database: None,
            username: None,
            password: None,
            pool_size: None,
            timeout_seconds: None,
            ssl_enabled: None,
        }
    }

    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    pub fn database(mut self, database: impl Into<String>) -> Self {
        self.database = Some(database.into());
        self
    }

    pub fn username(mut self, username: impl Into<String>) -> Self {
        self.username = Some(username.into());
        self
    }

    pub fn password(mut self, password: impl Into<String>) -> Self {
        self.password = Some(password.into());
        self
    }

    pub fn pool_size(mut self, size: usize) -> Self {
        self.pool_size = Some(size);
        self
    }

    pub fn timeout_seconds(mut self, seconds: u64) -> Self {
        self.timeout_seconds = Some(seconds);
        self
    }

    pub fn ssl_enabled(mut self, enabled: bool) -> Self {
        self.ssl_enabled = Some(enabled);
        self
    }

    pub fn build(self) -> Result<DatabaseConfig, BuilderError> {
        // 验证必填字段
        let host = self.host
            .ok_or(BuilderError::MissingField("host"))?;

        let database = self.database
            .ok_or(BuilderError::MissingField("database"))?;

        let username = self.username
            .ok_or(BuilderError::MissingField("username"))?;

        let password = self.password
            .ok_or(BuilderError::MissingField("password"))?;

        // 提供默认值
        let port = self.port.unwrap_or(5432);
        let pool_size = self.pool_size.unwrap_or(10);
        let timeout_seconds = self.timeout_seconds.unwrap_or(30);
        let ssl_enabled = self.ssl_enabled.unwrap_or(false);

        // 验证值的有效性
        if port == 0 {
            return Err(BuilderError::InvalidValue("Port cannot be 0".to_string()));
        }

        if pool_size == 0 || pool_size > 1000 {
            return Err(BuilderError::InvalidValue(
                "Pool size must be between 1 and 1000".to_string()
            ));
        }

        Ok(DatabaseConfig {
            host,
            port,
            database,
            username,
            password,
            pool_size,
            timeout_seconds,
            ssl_enabled,
        })
    }
}

// 使用示例
fn builder_example() -> Result<(), BuilderError> {
    let config = DatabaseConfigBuilder::new()
        .host("localhost")
        .database("mydb")
        .username("admin")
        .password("secret")
        .pool_size(20)
        .ssl_enabled(true)
        .build()?;

    println!("Config: {:?}", config);

    // 缺少必填字段会编译通过但运行时报错
    let result = DatabaseConfigBuilder::new()
        .host("localhost")
        .build();

    match result {
        Ok(_) => println!("Unexpected success"),
        Err(e) => println!("Expected error: {}", e),
    }

    Ok(())
}
```

---

## 📊 性能优化进阶

### 内存布局优化实例

```rust
use std::mem;

// ❌ 内存布局不佳
#[derive(Debug)]
struct BadLayout {
    flag: bool,      // 1 byte
    // padding: 7 bytes (对齐到u64)
    number: u64,     // 8 bytes
    small: u8,       // 1 byte
    // padding: 7 bytes
}

// ✅ 优化的内存布局
#[derive(Debug)]
struct GoodLayout {
    number: u64,     // 8 bytes
    flag: bool,      // 1 byte
    small: u8,       // 1 byte
    // padding: 6 bytes
}

// 使用 repr(C) 控制布局
#[repr(C)]
struct CLayout {
    number: u64,
    flag: bool,
    small: u8,
}

// repr(packed) 去除padding（慎用）
#[repr(packed)]
struct PackedLayout {
    flag: bool,
    number: u64,
    small: u8,
}

fn layout_example() {
    println!("BadLayout size: {} bytes", mem::size_of::<BadLayout>());
    println!("GoodLayout size: {} bytes", mem::size_of::<GoodLayout>());
    println!("CLayout size: {} bytes", mem::size_of::<CLayout>());
    println!("PackedLayout size: {} bytes", mem::size_of::<PackedLayout>());

    // 典型输出：
    // BadLayout size: 24 bytes  (浪费!)
    // GoodLayout size: 16 bytes
    // CLayout size: 16 bytes
    // PackedLayout size: 10 bytes (但访问速度可能变慢)
}
```

---

### 枚举判别式优化

```rust
// 使用小的判别式类型
#[repr(u8)]  // 只使用1字节作为判别值
enum Status {
    Pending = 0,
    InProgress = 1,
    Completed = 2,
    Failed = 3,
}

// 显式指定判别值
#[repr(u16)]
enum ErrorCode {
    NetworkError = 1000,
    DatabaseError = 2000,
    AuthError = 3000,
}

impl ErrorCode {
    fn as_u16(&self) -> u16 {
        *self as u16
    }

    fn from_u16(value: u16) -> Option<Self> {
        match value {
            1000 => Some(ErrorCode::NetworkError),
            2000 => Some(ErrorCode::DatabaseError),
            3000 => Some(ErrorCode::AuthError),
            _ => None,
        }
    }
}

fn discriminant_example() {
    use std::mem;

    let status = Status::Completed;
    println!("Status size: {} bytes", mem::size_of_val(&status));

    let code = ErrorCode::DatabaseError;
    println!("Error code: {}", code.as_u16());
}
```

---

## 🔥 高级模式匹配技巧

### 匹配多个模式

```rust
enum Message {
    Text(String),
    Image(String, Vec<u8>),
    Video(String, Vec<u8>, u32),
}

fn process_media(msg: Message) {
    match msg {
        // 匹配多个模式
        Message::Image(name, _) | Message::Video(name, _, _) => {
            println!("Processing media: {}", name);
        }
        Message::Text(content) => {
            println!("Processing text: {}", content);
        }
    }
}
```

---

### 范围模式

```rust
fn classify_age(age: u32) -> &'static str {
    match age {
        0..=12 => "Child",
        13..=19 => "Teenager",
        20..=64 => "Adult",
        65.. => "Senior",
    }
}

fn classify_char(c: char) -> &'static str {
    match c {
        'a'..='z' => "lowercase",
        'A'..='Z' => "uppercase",
        '0'..='9' => "digit",
        _ => "other",
    }
}
```

---

### 嵌套匹配与解构

```rust
enum Response {
    Success(Result<String, String>),
    Redirect(String),
    Error(u16, String),
}

fn handle_response(response: Response) {
    match response {
        // 嵌套匹配
        Response::Success(Ok(data)) => {
            println!("Success with data: {}", data);
        }
        Response::Success(Err(reason)) => {
            println!("Success but error: {}", reason);
        }
        Response::Redirect(url) => {
            println!("Redirect to: {}", url);
        }
        // 守卫 + 解构
        Response::Error(code, msg) if code >= 500 => {
            println!("Server error {}: {}", code, msg);
        }
        Response::Error(code, msg) => {
            println!("Client error {}: {}", code, msg);
        }
    }
}
```

---

## 🎯 实战练习题

### 练习 1: 实现命令行参数解析器

```rust
#[derive(Debug)]
enum Arg {
    Flag(String),
    Option(String, String),
    Positional(String),
}

struct ArgParser {
    args: Vec<Arg>,
}

impl ArgParser {
    fn parse(input: &[String]) -> Self {
        let mut args = Vec::new();
        let mut iter = input.iter();

        while let Some(arg) = iter.next() {
            if arg.starts_with("--") {
                let name = arg[2..].to_string();
                if let Some(value) = iter.next() {
                    args.push(Arg::Option(name, value.clone()));
                } else {
                    args.push(Arg::Flag(name));
                }
            } else if arg.starts_with("-") {
                args.push(Arg::Flag(arg[1..].to_string()));
            } else {
                args.push(Arg::Positional(arg.clone()));
            }
        }

        ArgParser { args }
    }

    fn get_flag(&self, name: &str) -> bool {
        self.args.iter().any(|arg| match arg {
            Arg::Flag(flag_name) => flag_name == name,
            _ => false,
        })
    }

    fn get_option(&self, name: &str) -> Option<&str> {
        self.args.iter().find_map(|arg| match arg {
            Arg::Option(opt_name, value) if opt_name == name => Some(value.as_str()),
            _ => None,
        })
    }
}

// 使用示例
fn parser_example() {
    let args = vec![
        "--verbose".to_string(),
        "--output".to_string(),
        "file.txt".to_string(),
        "-h".to_string(),
        "input.txt".to_string(),
    ];

    let parser = ArgParser::parse(&args);

    println!("Has verbose: {}", parser.get_flag("verbose"));
    println!("Has help: {}", parser.get_flag("h"));
    println!("Output: {:?}", parser.get_option("output"));
}
```

---

**更新日期**: 2025-10-24
**文档版本**: 2.0
**作者**: C02 Type System Code Examples Team
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
