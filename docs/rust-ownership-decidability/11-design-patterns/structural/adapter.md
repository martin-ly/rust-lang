# Adapter Pattern in Rust

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **设计模式**: 结构型模式
> **难度**: 🟢 简单
> **应用场景**: 接口兼容性适配

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Adapter Pattern in Rust](#adapter-pattern-in-rust)
  - [📑 目录](#目录)
  - [概念](#概念)
  - [实现方式](#实现方式)
    - [Trait 适配](#trait-适配)
    - [泛型适配器 (零成本)](#泛型适配器-零成本)
  - [实战: 日志库适配](#实战-日志库适配)
  - [形式化定义](#形式化定义)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引)

## 概念
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

适配器模式将一个类的接口转换成客户希望的另外一个接口，使得原本由于接口不兼容而不能一起工作的那些类可以一起工作。

---

## 实现方式
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### Trait 适配
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

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
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

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
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

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
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
Adapter: Source → Target

其中:
  Source: 已有接口 (不兼容)
  Target: 期望接口

满足:
  ∀s: Source, ∃a: Adapter: a.request() = convert(s.specific_request())
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [structural 目录](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Design Pattern]**

> **[来源: Rust API Guidelines]**

> **[来源: Gang of Four - Design Patterns]**

> **[来源: ACM - Software Design Patterns]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
