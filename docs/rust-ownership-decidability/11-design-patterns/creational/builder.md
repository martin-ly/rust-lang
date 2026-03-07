# Builder Pattern in Rust

> **设计模式**: 创建型模式
> **难度**: 🟡 中等
> **应用场景**: 复杂对象的逐步构建

---

## 概念

构建者模式将复杂对象的构造过程与其表示分离，允许使用相同的构建过程创建不同的表示。

---

## 基础实现

### 标准构建者

```rust
#[derive(Debug, Clone)]
pub struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

pub struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    pub fn new() -> Self {
        Self {
            method: "GET".to_string(),
            url: "/".to_string(),
            headers: Vec::new(),
            body: None,
        }
    }

    pub fn method(mut self, method: &str) -> Self {
        self.method = method.to_string();
        self
    }

    pub fn url(mut self, url: &str) -> Self {
        self.url = url.to_string();
        self
    }

    pub fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }

    pub fn body(mut self, body: &str) -> Self {
        self.body = Some(body.to_string());
        self
    }

    pub fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
        }
    }
}

// 使用
let request = HttpRequestBuilder::new()
    .method("POST")
    .url("/api/users")
    .header("Content-Type", "application/json")
    .body(r#"{"name": "Alice"}"#)
    .build();
```

---

## 高级实现

### Type State 模式 (编译时验证)

```rust
use std::marker::PhantomData;

// 状态标记
struct Incomplete;
struct HasUrl;
struct Complete;

pub struct RequestBuilder<State> {
    method: String,
    url: Option<String>,
    headers: Vec<(String, String)>,
    _state: PhantomData<State>,
}

impl RequestBuilder<Incomplete> {
    pub fn new() -> Self {
        Self {
            method: "GET".to_string(),
            url: None,
            headers: Vec::new(),
            _state: PhantomData,
        }
    }

    pub fn url(self, url: &str) -> RequestBuilder<HasUrl> {
        RequestBuilder {
            method: self.method,
            url: Some(url.to_string()),
            headers: self.headers,
            _state: PhantomData,
        }
    }
}

impl RequestBuilder<HasUrl> {
    pub fn method(mut self, method: &str) -> Self {
        self.method = method.to_string();
        self
    }

    pub fn build(self) -> Request {
        Request {
            method: self.method,
            url: self.url.unwrap(),
            headers: self.headers,
        }
    }
}

pub struct Request {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
}

// 编译错误: 必须先调用 url()
// let req = RequestBuilder::new().build();
```

---

## 形式化定义

### 构建过程的类型理论

```
Builder<T> = Π (fields: Field*). T

其中:
  Field = (name: String, value: Type, optional: Bool)
  T = 目标类型

构建函数类型:
  build: Builder<T> → Result<T, ValidationError>
```

### 不变量

```
Invariant BUILDER_VALID:
  build(b) = Ok(t) ⟹
  ∀f ∈ required_fields(T): f is set in b
```

---

## 实战: 数据库连接配置

```rust
use std::time::Duration;

pub struct DatabaseConfig {
    host: String,
    port: u16,
    database: String,
    username: String,
    password: String,
    pool_size: u32,
    timeout: Duration,
}

pub struct DatabaseConfigBuilder {
    host: String,
    port: u16,
    database: Option<String>,
    username: String,
    password: Option<String>,
    pool_size: u32,
    timeout: Duration,
}

impl DatabaseConfigBuilder {
    pub fn new(host: &str) -> Self {
        Self {
            host: host.to_string(),
            port: 5432,
            database: None,
            username: "postgres".to_string(),
            password: None,
            pool_size: 10,
            timeout: Duration::from_secs(30),
        }
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = port;
        self
    }

    pub fn database(mut self, db: &str) -> Self {
        self.database = Some(db.to_string());
        self
    }

    pub fn credentials(mut self, user: &str, pass: &str) -> Self {
        self.username = user.to_string();
        self.password = Some(pass.to_string());
        self
    }

    pub fn pool_size(mut self, size: u32) -> Self {
        self.pool_size = size;
        self
    }

    pub fn build(self) -> Result<DatabaseConfig, ConfigError> {
        Ok(DatabaseConfig {
            host: self.host,
            port: self.port,
            database: self.database.ok_or(ConfigError::MissingDatabase)?,
            username: self.username,
            password: self.password.ok_or(ConfigError::MissingPassword)?,
            pool_size: self.pool_size,
            timeout: self.timeout,
        })
    }
}

#[derive(Debug)]
pub enum ConfigError {
    MissingDatabase,
    MissingPassword,
}
```

---

## 对比分析

| 实现方式 | 优点 | 缺点 |
|---------|------|------|
| 标准Builder | 简单直观 | 运行时验证 |
| Type State | 编译时安全 | 代码复杂度高 |
| derive_builder | 自动生成 | 额外依赖 |

---

## 推荐 crates

- **derive_builder**: `#[derive(Builder)]`
- **typed-builder**: Type State 自动生成
- **bon**: 现代 Builder 宏
