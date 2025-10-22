# 04. 控制流设计模式

本文档介绍在 Rust 中使用控制流实现常见设计模式的方法和最佳实践。

## 目录

- [04. 控制流设计模式](#04-控制流设计模式)
  - [目录](#目录)
  - [状态机模式](#状态机模式)
    - [类型状态模式](#类型状态模式)
    - [基于枚举的状态机](#基于枚举的状态机)
  - [策略模式](#策略模式)
    - [基于特征的策略](#基于特征的策略)
    - [基于闭包的策略](#基于闭包的策略)
  - [责任链模式](#责任链模式)
    - [基于枚举的责任链](#基于枚举的责任链)
    - [基于函数组合的责任链](#基于函数组合的责任链)
  - [访问者模式](#访问者模式)
  - [命令模式](#命令模式)
  - [最佳实践](#最佳实践)
    - [1. 优先使用类型状态模式](#1-优先使用类型状态模式)
    - [2. 使用 match 表达式处理复杂逻辑](#2-使用-match-表达式处理复杂逻辑)
    - [3. 组合小型函数而非大型 match](#3-组合小型函数而非大型-match)
  - [总结](#总结)

## 状态机模式

状态机模式使用类型系统在编译时验证状态转换的正确性。

### 类型状态模式

使用 Rust 的类型系统编码状态：

```rust
// 定义状态标记
struct Locked;
struct Unlocked;

// 使用泛型参数表示状态
struct Door<State> {
    _state: std::marker::PhantomData<State>,
}

// 初始状态：锁定
impl Door<Locked> {
    fn new() -> Self {
        Door {
            _state: std::marker::PhantomData,
        }
    }
    
    // 只有锁定状态可以解锁
    fn unlock(self) -> Door<Unlocked> {
        println!("门已解锁");
        Door {
            _state: std::marker::PhantomData,
        }
    }
}

// 解锁状态
impl Door<Unlocked> {
    // 只有解锁状态可以打开
    fn open(&self) {
        println!("门已打开");
    }
    
    // 重新锁定
    fn lock(self) -> Door<Locked> {
        println!("门已锁定");
        Door {
            _state: std::marker::PhantomData,
        }
    }
}

// 使用示例
fn use_door() {
    let door = Door::<Locked>::new();
    let door = door.unlock();  // 转换到 Unlocked 状态
    door.open();
    let door = door.lock();    // 转换回 Locked 状态
    
    // 编译错误：不能对锁定的门调用 open()
    // door.open();
}
```

### 基于枚举的状态机

使用枚举表示状态，通过 match 处理状态转换：

```rust
enum ConnectionState {
    Disconnected,
    Connecting,
    Connected { session_id: u64 },
    Error { message: String },
}

struct Connection {
    state: ConnectionState,
}

impl Connection {
    fn new() -> Self {
        Connection {
            state: ConnectionState::Disconnected,
        }
    }
    
    fn connect(&mut self) -> Result<(), String> {
        match self.state {
            ConnectionState::Disconnected => {
                self.state = ConnectionState::Connecting;
                Ok(())
            }
            ConnectionState::Connecting => {
                Err("已在连接中".to_string())
            }
            ConnectionState::Connected { .. } => {
                Err("已连接".to_string())
            }
            ConnectionState::Error { ref message } => {
                Err(format!("连接错误: {}", message))
            }
        }
    }
    
    fn complete_connection(&mut self, session_id: u64) {
        if matches!(self.state, ConnectionState::Connecting) {
            self.state = ConnectionState::Connected { session_id };
        }
    }
    
    fn disconnect(&mut self) {
        self.state = ConnectionState::Disconnected;
    }
}
```

## 策略模式

使用特征和闭包实现策略模式。

### 基于特征的策略

```rust
// 策略特征
trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
    fn decompress(&self, data: &[u8]) -> Vec<u8>;
}

// 具体策略：Gzip
struct GzipCompression;

impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Gzip 压缩");
        data.to_vec()  // 简化实现
    }
    
    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Gzip 解压");
        data.to_vec()
    }
}

// 具体策略：Zstd
struct ZstdCompression;

impl CompressionStrategy for ZstdCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Zstd 压缩");
        data.to_vec()
    }
    
    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Zstd 解压");
        data.to_vec()
    }
}

// 上下文
struct Compressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl Compressor {
    fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        Compressor { strategy }
    }
    
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }
}

// 使用示例
fn use_strategy() {
    let data = b"Hello, World!";
    
    let mut compressor = Compressor::new(Box::new(GzipCompression));
    compressor.compress(data);
    
    // 切换策略
    compressor.set_strategy(Box::new(ZstdCompression));
    compressor.compress(data);
}
```

### 基于闭包的策略

```rust
// 使用函数指针作为策略
struct Calculator {
    strategy: fn(i32, i32) -> i32,
}

impl Calculator {
    fn new(strategy: fn(i32, i32) -> i32) -> Self {
        Calculator { strategy }
    }
    
    fn calculate(&self, a: i32, b: i32) -> i32 {
        (self.strategy)(a, b)
    }
    
    fn set_strategy(&mut self, strategy: fn(i32, i32) -> i32) {
        self.strategy = strategy;
    }
}

// 策略函数
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn multiply(a: i32, b: i32) -> i32 {
    a * b
}

// 使用示例
fn use_closure_strategy() {
    let mut calc = Calculator::new(add);
    println!("加法: {}", calc.calculate(5, 3));
    
    calc.set_strategy(multiply);
    println!("乘法: {}", calc.calculate(5, 3));
    
    // 使用闭包
    calc.set_strategy(|a, b| a - b);
    println!("减法: {}", calc.calculate(5, 3));
}
```

## 责任链模式

使用递归或迭代器实现责任链。

### 基于枚举的责任链

```rust
// 请求类型
enum Request {
    BasicAuth(String),
    TokenAuth(String),
    ApiKeyAuth(String),
}

// 处理结果
enum AuthResult {
    Authorized(String),
    Unauthorized,
    NextHandler,
}

// 处理器特征
trait AuthHandler {
    fn handle(&self, request: &Request) -> AuthResult;
}

// 基础认证处理器
struct BasicAuthHandler {
    next: Option<Box<dyn AuthHandler>>,
}

impl AuthHandler for BasicAuthHandler {
    fn handle(&self, request: &Request) -> AuthResult {
        match request {
            Request::BasicAuth(credentials) => {
                if credentials == "admin:password" {
                    AuthResult::Authorized("基础认证成功".to_string())
                } else {
                    AuthResult::Unauthorized
                }
            }
            _ => {
                // 传递给下一个处理器
                if let Some(ref next_handler) = self.next {
                    next_handler.handle(request)
                } else {
                    AuthResult::NextHandler
                }
            }
        }
    }
}

// Token 认证处理器
struct TokenAuthHandler {
    next: Option<Box<dyn AuthHandler>>,
}

impl AuthHandler for TokenAuthHandler {
    fn handle(&self, request: &Request) -> AuthResult {
        match request {
            Request::TokenAuth(token) => {
                if token.len() == 32 {
                    AuthResult::Authorized("Token 认证成功".to_string())
                } else {
                    AuthResult::Unauthorized
                }
            }
            _ => {
                if let Some(ref next_handler) = self.next {
                    next_handler.handle(request)
                } else {
                    AuthResult::NextHandler
                }
            }
        }
    }
}

// 使用示例
fn use_chain_of_responsibility() {
    let chain = BasicAuthHandler {
        next: Some(Box::new(TokenAuthHandler { next: None })),
    };
    
    let request1 = Request::BasicAuth("admin:password".to_string());
    match chain.handle(&request1) {
        AuthResult::Authorized(msg) => println!("{}", msg),
        AuthResult::Unauthorized => println!("认证失败"),
        AuthResult::NextHandler => println!("无处理器"),
    }
}
```

### 基于函数组合的责任链

```rust
type Handler = fn(&str) -> Option<String>;

fn create_chain(handlers: Vec<Handler>) -> impl Fn(&str) -> Option<String> {
    move |input: &str| {
        for handler in &handlers {
            if let Some(result) = handler(input) {
                return Some(result);
            }
        }
        None
    }
}

// 处理器函数
fn handle_number(input: &str) -> Option<String> {
    if input.chars().all(|c| c.is_numeric()) {
        Some(format!("数字: {}", input))
    } else {
        None
    }
}

fn handle_email(input: &str) -> Option<String> {
    if input.contains('@') {
        Some(format!("邮箱: {}", input))
    } else {
        None
    }
}

fn handle_url(input: &str) -> Option<String> {
    if input.starts_with("http://") || input.starts_with("https://") {
        Some(format!("URL: {}", input))
    } else {
        None
    }
}

// 使用示例
fn use_function_chain() {
    let chain = create_chain(vec![handle_number, handle_email, handle_url]);
    
    println!("{:?}", chain("12345"));
    println!("{:?}", chain("user@example.com"));
    println!("{:?}", chain("https://example.com"));
}
```

## 访问者模式

使用特征和 match 实现访问者模式。

```rust
// 抽象语法树节点
enum AstNode {
    Number(i32),
    Add(Box<AstNode>, Box<AstNode>),
    Multiply(Box<AstNode>, Box<AstNode>),
}

// 访问者特征
trait Visitor<T> {
    fn visit_number(&mut self, n: i32) -> T;
    fn visit_add(&mut self, left: T, right: T) -> T;
    fn visit_multiply(&mut self, left: T, right: T) -> T;
    
    fn visit(&mut self, node: &AstNode) -> T {
        match node {
            AstNode::Number(n) => self.visit_number(*n),
            AstNode::Add(left, right) => {
                let l = self.visit(left);
                let r = self.visit(right);
                self.visit_add(l, r)
            }
            AstNode::Multiply(left, right) => {
                let l = self.visit(left);
                let r = self.visit(right);
                self.visit_multiply(l, r)
            }
        }
    }
}

// 求值访问者
struct EvaluatorVisitor;

impl Visitor<i32> for EvaluatorVisitor {
    fn visit_number(&mut self, n: i32) -> i32 {
        n
    }
    
    fn visit_add(&mut self, left: i32, right: i32) -> i32 {
        left + right
    }
    
    fn visit_multiply(&mut self, left: i32, right: i32) -> i32 {
        left * right
    }
}

// 打印访问者
struct PrinterVisitor;

impl Visitor<String> for PrinterVisitor {
    fn visit_number(&mut self, n: i32) -> String {
        n.to_string()
    }
    
    fn visit_add(&mut self, left: String, right: String) -> String {
        format!("({} + {})", left, right)
    }
    
    fn visit_multiply(&mut self, left: String, right: String) -> String {
        format!("({} * {})", left, right)
    }
}

// 使用示例
fn use_visitor() {
    // 构造 AST: (2 + 3) * 4
    let ast = AstNode::Multiply(
        Box::new(AstNode::Add(
            Box::new(AstNode::Number(2)),
            Box::new(AstNode::Number(3)),
        )),
        Box::new(AstNode::Number(4)),
    );
    
    let mut evaluator = EvaluatorVisitor;
    println!("结果: {}", evaluator.visit(&ast));
    
    let mut printer = PrinterVisitor;
    println!("表达式: {}", printer.visit(&ast));
}
```

## 命令模式

使用特征和闭包实现命令模式。

```rust
// 命令特征
trait Command {
    fn execute(&mut self);
    fn undo(&mut self);
}

// 具体命令：移动
struct MoveCommand {
    x: i32,
    y: i32,
    previous_x: i32,
    previous_y: i32,
}

impl MoveCommand {
    fn new(x: i32, y: i32) -> Self {
        MoveCommand {
            x,
            y,
            previous_x: 0,
            previous_y: 0,
        }
    }
}

impl Command for MoveCommand {
    fn execute(&mut self) {
        self.previous_x = self.x;
        self.previous_y = self.y;
        self.x += 10;
        self.y += 10;
        println!("移动到 ({}, {})", self.x, self.y);
    }
    
    fn undo(&mut self) {
        self.x = self.previous_x;
        self.y = self.previous_y;
        println!("撤销移动到 ({}, {})", self.x, self.y);
    }
}

// 命令调用者
struct Invoker {
    history: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Invoker {
            history: Vec::new(),
        }
    }
    
    fn execute(&mut self, mut command: Box<dyn Command>) {
        command.execute();
        self.history.push(command);
    }
    
    fn undo(&mut self) {
        if let Some(mut command) = self.history.pop() {
            command.undo();
        }
    }
}

// 使用示例
fn use_command() {
    let mut invoker = Invoker::new();
    
    invoker.execute(Box::new(MoveCommand::new(0, 0)));
    invoker.execute(Box::new(MoveCommand::new(10, 10)));
    
    invoker.undo();
    invoker.undo();
}
```

## 最佳实践

### 1. 优先使用类型状态模式

利用 Rust 的类型系统在编译时验证状态转换：

```rust
// 好的做法
impl Door<Locked> {
    fn unlock(self) -> Door<Unlocked> { /* ... */ }
}

// 避免
impl Door {
    fn unlock(&mut self) -> Result<(), String> {
        if self.is_locked {
            self.is_locked = false;
            Ok(())
        } else {
            Err("已解锁".to_string())
        }
    }
}
```

### 2. 使用 match 表达式处理复杂逻辑

```rust
// 好的做法：清晰的模式匹配
match state {
    State::Init => handle_init(),
    State::Running { data } => handle_running(data),
    State::Stopped => handle_stopped(),
}

// 避免：多重 if-else
if state == State::Init {
    handle_init();
} else if matches!(state, State::Running { .. }) {
    // 复杂的解构逻辑
}
```

### 3. 组合小型函数而非大型 match

```rust
// 好的做法：函数组合
fn process(input: &str) -> Option<String> {
    parse(input)
        .and_then(validate)
        .and_then(transform)
}

// 避免：巨大的 match 表达式
fn process(input: &str) -> Option<String> {
    match input {
        // 100+ 行的模式匹配
    }
}
```

## 总结

本文介绍了在 Rust 中实现常见设计模式的方法：

1. **状态机模式**：利用类型系统或枚举管理状态
2. **策略模式**：使用特征或闭包实现策略切换
3. **责任链模式**：通过递归或函数组合传递请求
4. **访问者模式**：使用特征遍历数据结构
5. **命令模式**：封装操作为对象

这些模式充分利用了 Rust 的类型系统、所有权模型和零成本抽象特性。

---

**相关章节**：

- [函数与闭包实践](./01_functions_closures_practice.md)
- [错误处理实践](./02_error_handling_practice.md)
- [高级控制流](../03_advanced/01_advanced_control_flow.md)

---

*最后更新：2025年1月*  
*文档版本：v1.0*  
*Rust 版本：1.90+*
