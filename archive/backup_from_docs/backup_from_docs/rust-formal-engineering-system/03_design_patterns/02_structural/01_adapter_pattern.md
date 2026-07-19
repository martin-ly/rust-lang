# 适配器模式（Adapter Pattern）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [适配器模式（Adapter Pattern）](#适配器模式adapter-pattern)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [问题场景](#问题场景)
  - [解决方案](#解决方案)
  - [Rust 实现](#rust-实现)
    - [对象适配器](#对象适配器)
    - [类适配器（使用 Trait）](#类适配器使用-trait)
  - [实践示例](#实践示例)
    - [示例 1：数据格式适配器](#示例-1数据格式适配器)
    - [示例 2：HTTP 客户端适配器](#示例-2http-客户端适配器)
  - [优缺点](#优缺点)
    - [优点](#优点)
    - [缺点](#缺点)
  - [参考资料](#参考资料)

---

## 概述

适配器模式（Adapter Pattern）是一种结构型设计模式，它允许接口不兼容的类可以合作无间。适配器模式通过创建一个包装类（适配器）来转换一个类的接口，使其与另一个类兼容。

## 问题场景

假设我们有一个现有的日志系统，它使用特定的接口：

```rust
// 现有的日志接口
trait OldLogger {
    fn log_info(&self, message: &str);
    fn log_error(&self, message: &str);
}

struct OldLoggerImpl;

impl OldLogger for OldLoggerImpl {
    fn log_info(&self, message: &str) {
        println!("[INFO] {}", message);
    }

    fn log_error(&self, message: &str) {
        println!("[ERROR] {}", message);
    }
}
```

现在我们有一个新的日志系统，使用不同的接口：

```rust
// 新的日志接口
trait NewLogger {
    fn info(&self, message: &str);
    fn error(&self, message: &str);
    fn debug(&self, message: &str);
}
```

## 解决方案

使用适配器模式，创建一个适配器将旧接口转换为新接口：

```rust
// 适配器：将 OldLogger 适配为 NewLogger
struct LoggerAdapter {
    old_logger: Box<dyn OldLogger>,
}

impl LoggerAdapter {
    fn new(old_logger: Box<dyn OldLogger>) -> Self {
        LoggerAdapter { old_logger }
    }
}

impl NewLogger for LoggerAdapter {
    fn info(&self, message: &str) {
        self.old_logger.log_info(message);
    }

    fn error(&self, message: &str) {
        self.old_logger.log_error(message);
    }

    fn debug(&self, message: &str) {
        // 旧日志系统不支持 debug，使用 info 代替
        self.old_logger.log_info(&format!("[DEBUG] {}", message));
    }
}
```

## Rust 实现

### 对象适配器

对象适配器使用组合来实现适配：

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 需要适配的类
struct Adaptee {
    value: String,
}

impl Adaptee {
    fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.value)
    }
}

// 适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Adapter {
    fn new(value: String) -> Self {
        Adapter {
            adaptee: Adaptee { value },
        }
    }
}

impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}
```

### 类适配器（使用 Trait）

在 Rust 中，可以使用 Trait 实现类似类适配器的功能：

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 需要适配的 Trait
trait Adaptee {
    fn specific_request(&self) -> String;
}

// 适配器 Trait
trait Adapter: Adaptee {
    fn request(&self) -> String {
        self.specific_request()
    }
}

// 实现
struct ConcreteAdaptee {
    value: String,
}

impl Adaptee for ConcreteAdaptee {
    fn specific_request(&self) -> String {
        format!("Adaptee: {}", self.value)
    }
}

impl Adapter for ConcreteAdaptee {}
```

## 实践示例

### 示例 1：数据格式适配器

```rust
// 旧的数据格式
trait OldDataFormat {
    fn get_data(&self) -> String;
}

struct CSVData {
    data: String,
}

impl OldDataFormat for CSVData {
    fn get_data(&self) -> String {
        self.data.clone()
    }
}

// 新的数据格式
trait NewDataFormat {
    fn get_json(&self) -> String;
}

// 适配器：将 CSV 转换为 JSON
struct CSVToJSONAdapter {
    csv_data: Box<dyn OldDataFormat>,
}

impl CSVToJSONAdapter {
    fn new(csv_data: Box<dyn OldDataFormat>) -> Self {
        CSVToJSONAdapter { csv_data }
    }
}

impl NewDataFormat for CSVToJSONAdapter {
    fn get_json(&self) -> String {
        let csv = self.csv_data.get_data();
        // 简单的 CSV 到 JSON 转换（实际应用中应使用专门的库）
        let lines: Vec<&str> = csv.lines().collect();
        if lines.is_empty() {
            return "[]".to_string();
        }

        let headers: Vec<&str> = lines[0].split(',').collect();
        let mut json_objects = Vec::new();

        for line in lines.iter().skip(1) {
            let values: Vec<&str> = line.split(',').collect();
            let mut obj = String::from("{");
            for (i, header) in headers.iter().enumerate() {
                if i > 0 {
                    obj.push_str(", ");
                }
                obj.push_str(&format!("\"{}\": \"{}\"", header.trim(),
                    values.get(i).unwrap_or(&"").trim()));
            }
            obj.push('}');
            json_objects.push(obj);
        }

        format!("[{}]", json_objects.join(", "))
    }
}
```

### 示例 2：HTTP 客户端适配器

```rust
// 旧的 HTTP 客户端接口
trait OldHttpClient {
    fn get(&self, url: &str) -> Result<String, String>;
}

struct CurlClient;

impl OldHttpClient for CurlClient {
    fn get(&self, url: &str) -> Result<String, String> {
        // 模拟 curl 请求
        Ok(format!("Response from {}", url))
    }
}

// 新的 HTTP 客户端接口
trait NewHttpClient {
    fn fetch(&self, url: &str) -> Result<Response, HttpError>;
}

struct Response {
    body: String,
    status: u16,
}

struct HttpError {
    message: String,
}

// 适配器
struct HttpClientAdapter {
    old_client: Box<dyn OldHttpClient>,
}

impl HttpClientAdapter {
    fn new(old_client: Box<dyn OldHttpClient>) -> Self {
        HttpClientAdapter { old_client }
    }
}

impl NewHttpClient for HttpClientAdapter {
    fn fetch(&self, url: &str) -> Result<Response, HttpError> {
        match self.old_client.get(url) {
            Ok(body) => Ok(Response {
                body,
                status: 200,
            }),
            Err(e) => Err(HttpError { message: e }),
        }
    }
}
```

## 优缺点

### 优点

1. **单一职责原则**：可以将接口转换代码从业务逻辑中分离
2. **开闭原则**：可以在不修改现有代码的情况下引入新的适配器
3. **代码复用**：可以复用现有的类，无需修改其代码

### 缺点

1. **代码复杂度增加**：需要引入新的类和接口
2. **性能开销**：适配器层可能带来轻微的性能开销

## 参考资料

- [设计模式实现](../../../../crates/c09_design_pattern/src/structural/)
- [结构型模式索引](./00_index.md)
- [设计模式总索引](../00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
