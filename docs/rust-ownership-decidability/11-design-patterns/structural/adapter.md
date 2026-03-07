# Adapter Pattern in Rust

> **设计模式**: 结构型模式
> **难度**: 🟢 简单
> **应用场景**: 接口兼容性适配

---

## 概念

适配器模式将一个类的接口转换成客户希望的另外一个接口，使得原本由于接口不兼容而不能一起工作的那些类可以一起工作。

---

## 实现方式

### Trait 适配

```rust
// 目标接口
pub trait Target {
    fn request(&self) -> String;
}

// 被适配者 (已有但接口不兼容)
pub struct Adaptee {
    pub value: i32,
}

impl Adaptee {
    pub fn specific_request(&self) -> String {
        format!("Specific: {}", self.value)
    }
}

// 适配器
pub struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    pub fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        // 转换调用
        self.adaptee.specific_request()
    }
}

// 使用
fn client_code(target: &dyn Target) {
    println!("{}", target.request());
}

fn main() {
    let adaptee = Adaptee { value: 42 };
    let adapter = Adapter::new(adaptee);
    client_code(&adapter);
}
```

### 泛型适配器 (零成本)

```rust
pub trait Renderable {
    fn render(&self) -> String;
}

// 第三方库类型 (无法修改)
pub struct ExternalImage {
    pub data: Vec<u8>,
}

impl ExternalImage {
    pub fn draw(&self) -> String {
        format!("Image({} bytes)", self.data.len())
    }
}

// 泛型适配器
pub struct ImageAdapter<T> {
    inner: T,
}

impl<T> ImageAdapter<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
}

impl ImageAdapter<ExternalImage> {
    // 为特定类型实现适配
}

impl Renderable for ImageAdapter<ExternalImage> {
    fn render(&self) -> String {
        self.inner.draw()
    }
}

// 使用泛型避免动态分派
fn display<T: Renderable>(item: &T) {
    println!("{}", item.render());
}
```

---

## 实战: 日志库适配

```rust
// 应用使用的日志 trait
pub trait Logger {
    fn log(&self, level: LogLevel, message: &str);
}

#[derive(Debug, Clone, Copy)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

// 第三方日志库 (log crate)
pub mod external {
    pub struct ExternalLogger;

    impl ExternalLogger {
        pub fn log_debug(&self, msg: &str) {
            println!("[DEBUG] {}", msg);
        }
        pub fn log_info(&self, msg: &str) {
            println!("[INFO] {}", msg);
        }
        pub fn log_warn(&self, msg: &str) {
            println!("[WARN] {}", msg);
        }
        pub fn log_error(&self, msg: &str) {
            println!("[ERROR] {}", msg);
        }
    }
}

use external::ExternalLogger;

// 适配器
pub struct LogAdapter {
    logger: ExternalLogger,
}

impl LogAdapter {
    pub fn new() -> Self {
        Self {
            logger: ExternalLogger,
        }
    }
}

impl Logger for LogAdapter {
    fn log(&self, level: LogLevel, message: &str) {
        match level {
            LogLevel::Debug => self.logger.log_debug(message),
            LogLevel::Info => self.logger.log_info(message),
            LogLevel::Warn => self.logger.log_warn(message),
            LogLevel::Error => self.logger.log_error(message),
        }
    }
}

// 应用代码
pub struct Application {
    logger: Box<dyn Logger>,
}

impl Application {
    pub fn new(logger: Box<dyn Logger>) -> Self {
        Self { logger }
    }

    pub fn run(&self) {
        self.logger.log(LogLevel::Info, "Application started");
    }
}
```

---

## 形式化定义

```
Adapter: Source → Target

其中:
  Source: 已有接口 (不兼容)
  Target: 期望接口

满足:
  ∀s: Source, ∃a: Adapter: a.request() = convert(s.specific_request())
```
