# C10 Networks - Tier 2: HTTP 客户端开发

> **文档版本**: v1.0.0
> **最后更新**: 2025-12-11
> **Rust 版本**: 1.92.0+
> **预计阅读**: 40 分钟

---

## 📊 目录

- [C10 Networks - Tier 2: HTTP 客户端开发](#c10-networks---tier-2-http-客户端开发)
  - [📊 目录](#-目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
    - [概念矩阵](#概念矩阵)
  - [1. HTTP 基础](#1-http-基础)
    - [1.1 HTTP 请求方法](#11-http-请求方法)
    - [1.2 HTTP 状态码](#12-http-状态码)
  - [2. 使用 reqwest](#2-使用-reqwest)
    - [2.1 基础 GET 请求](#21-基础-get-请求)
    - [2.2 基础 POST 请求](#22-基础-post-请求)
    - [2.3 创建可复用客户端](#23-创建可复用客户端)
  - [3. 请求构建与配置](#3-请求构建与配置)
    - [3.1 请求头设置](#31-请求头设置)
    - [3.2 查询参数](#32-查询参数)
    - [3.3 请求体](#33-请求体)
  - [4. 响应处理](#4-响应处理)
    - [4.1 状态码检查](#41-状态码检查)
    - [4.2 响应头解析](#42-响应头解析)
    - [4.3 响应体解析](#43-响应体解析)
  - [5. 错误处理与重试](#5-错误处理与重试)
    - [5.1 错误类型](#51-错误类型)
    - [5.2 重试策略](#52-重试策略)
  - [6. 高级特性](#6-高级特性)
    - [6.1 Cookie 管理](#61-cookie-管理)
    - [6.2 代理设置](#62-代理设置)
    - [6.3 文件上传](#63-文件上传)
    - [6.4 流式下载](#64-流式下载)
  - [7. 实战案例](#7-实战案例)
    - [7.1 GitHub API 客户端](#71-github-api-客户端)
    - [7.2 并发请求](#72-并发请求)
    - [7.3 RESTful API 封装](#73-restful-api-封装)
  - [8. 总结](#8-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

## 📐 知识结构

### 概念定义

**HTTP 客户端 (HTTP Client)**:

- **定义**: 用于发送 HTTP 请求并接收响应的客户端程序
- **类型**: 网络编程组件
- **范畴**: 网络编程、Web 开发
- **版本**: Rust 1.0+
- **相关概念**: HTTP 协议、RESTful API、网络请求

**HTTP 协议**:

- **定义**: 超文本传输协议，用于在 Web 上传输数据
- **类型**: 应用层协议
- **属性**: 请求-响应、无状态、可扩展
- **关系**: 与 TCP、Web、RESTful API 相关

### 属性特征

**核心属性**:

- **请求方法**: GET、POST、PUT、DELETE 等
- **状态码**: 200、404、500 等响应状态
- **请求头**: 元数据信息
- **请求体**: 传输的数据

**性能特征**:

- **连接复用**: 复用 TCP 连接提升性能
- **并发请求**: 支持并发发送多个请求
- **适用场景**: Web API 调用、数据获取、服务间通信

### 关系连接

**继承关系**:

- HTTP 客户端 --[is-a]--> 网络客户端
- RESTful 客户端 --[is-a]--> HTTP 客户端

**组合关系**:

- HTTP 客户端 --[uses]--> TCP 连接
- HTTP 客户端 --[uses]--> HTTP 协议

**依赖关系**:

- HTTP 客户端 --[depends-on]--> 网络库
- HTTP 客户端 --[depends-on]--> HTTP 协议实现

### 思维导图

```text
HTTP 客户端开发
│
├── HTTP 基础
│   ├── 请求方法
│   └── 状态码
├── 请求构建
│   ├── 请求头
│   ├── 查询参数
│   └── 请求体
├── 响应处理
│   ├── 状态码检查
│   ├── 响应头解析
│   └── 响应体解析
├── 错误处理
│   ├── 错误类型
│   └── 重试策略
└── 高级特性
    ├── Cookie 管理
    ├── 代理设置
    └── 文件上传
```

### 概念矩阵

| HTTP 方法 | 幂等性 | 安全性 | 用途 | 请求体 |
|----------|--------|--------|------|--------|
| GET | ✅ | ✅ | 获取资源 | ❌ |
| POST | ❌ | ❌ | 创建资源 | ✅ |
| PUT | ✅ | ❌ | 更新资源 | ✅ |
| DELETE | ✅ | ❌ | 删除资源 | ❌ |
| PATCH | ❌ | ❌ | 部分更新 | ✅ |

---

## 1. HTTP 基础

### 1.1 HTTP 请求方法

| 方法 | 用途 | 幂等性 | 安全性 |
| --- | --- | --- | --- |
| **GET** | 获取资源 | ✅ | ✅ |
| **POST** | 创建资源 | ❌ | ❌ |
| **PUT** | 更新资源 | ✅ | ❌ |
| **DELETE** | 删除资源 | ✅ | ❌ |
| **PATCH** | 部分更新 | ❌ | ❌ |
| **HEAD** | 获取头部 | ✅ | ✅ |

### 1.2 HTTP 状态码

```rust
// 常见状态码分类
fn interpret_status_code(code: u16) -> &'static str {
    match code {
        200..=299 => "成功",      // 2xx: 成功
        300..=399 => "重定向",    // 3xx: 重定向
        400..=499 => "客户端错误", // 4xx: 客户端错误
        500..=599 => "服务器错误", // 5xx: 服务器错误
        _ => "未知",
    }
}

fn main() {
    println!("200: {}", interpret_status_code(200));
    println!("404: {}", interpret_status_code(404));
    println!("500: {}", interpret_status_code(500));
}
```

---

## 2. 使用 reqwest

### 2.1 基础 GET 请求

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 简单 GET 请求
    let response = reqwest::get("https://httpbin.org/get").await?;

    println!("状态码: {}", response.status());
    println!("头部: {:#?}", response.headers());

    // 获取文本内容
    let body = response.text().await?;
    println!("响应体:\n{}", body);

    Ok(())
}
```

### 2.2 基础 POST 请求

```rust
use reqwest;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();

    // JSON POST 请求
    let response = client
        .post("https://httpbin.org/post")
        .json(&json!({
            "username": "rust_user",
            "password": "secure_password"
        }))
        .send()
        .await?;

    println!("状态码: {}", response.status());

    // 解析 JSON 响应
    let json: serde_json::Value = response.json().await?;
    println!("响应 JSON:\n{:#?}", json);

    Ok(())
}
```

### 2.3 创建可复用客户端

```rust
use reqwest::Client;
use std::time::Duration;

fn create_http_client() -> Client {
    Client::builder()
        .timeout(Duration::from_secs(10))
        .user_agent("my-rust-app/1.0")
        .gzip(true) // 启用 gzip 压缩
        .build()
        .expect("创建客户端失败")
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = create_http_client();

    // 复用客户端发送多个请求
    let response1 = client.get("https://httpbin.org/get").send().await?;
    println!("请求 1: {}", response1.status());

    let response2 = client.get("https://httpbin.org/uuid").send().await?;
    println!("请求 2: {}", response2.status());

    Ok(())
}
```

---

## 3. 请求构建与配置

### 3.1 请求头设置

```rust
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION, CONTENT_TYPE};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut headers = HeaderMap::new();
    headers.insert(AUTHORIZATION, HeaderValue::from_static("Bearer TOKEN123"));
    headers.insert(CONTENT_TYPE, HeaderValue::from_static("application/json"));

    let client = reqwest::Client::builder()
        .default_headers(headers)
        .build()?;

    let response = client
        .get("https://httpbin.org/headers")
        .send()
        .await?;

    println!("{}", response.text().await?);

    Ok(())
}
```

### 3.2 查询参数

```rust
use reqwest::Client;
use serde::Serialize;

#[derive(Serialize)]
struct SearchParams {
    q: String,
    limit: u32,
    offset: u32,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();

    // 方法 1: 手动拼接
    let response = client
        .get("https://httpbin.org/get?foo=bar&baz=qux")
        .send()
        .await?;

    // 方法 2: 使用元组数组
    let response = client
        .get("https://httpbin.org/get")
        .query(&[("foo", "bar"), ("baz", "qux")])
        .send()
        .await?;

    // 方法 3: 使用结构体
    let params = SearchParams {
        q: "rust".to_string(),
        limit: 10,
        offset: 0,
    };
    let response = client
        .get("https://httpbin.org/get")
        .query(&params)
        .send()
        .await?;

    println!("{}", response.text().await?);

    Ok(())
}
```

### 3.3 请求体

```rust
use reqwest::Client;
use serde::{Serialize, Deserialize};

#[derive(Serialize)]
struct User {
    username: String,
    email: String,
    age: u32,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();

    // JSON 请求体
    let user = User {
        username: "rustacean".to_string(),
        email: "user@rust-lang.org".to_string(),
        age: 30,
    };

    let response = client
        .post("https://httpbin.org/post")
        .json(&user)
        .send()
        .await?;

    println!("JSON POST: {}", response.status());

    // 表单请求体
    let form_data = [("name", "Alice"), ("city", "Beijing")];
    let response = client
        .post("https://httpbin.org/post")
        .form(&form_data)
        .send()
        .await?;

    println!("Form POST: {}", response.status());

    // 原始文本请求体
    let response = client
        .post("https://httpbin.org/post")
        .body("Raw text data")
        .send()
        .await?;

    println!("Raw POST: {}", response.status());

    Ok(())
}
```

---

## 4. 响应处理

### 4.1 状态码检查

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let response = reqwest::get("https://httpbin.org/status/404").await?;

    // 方法 1: 检查状态码
    if response.status().is_success() {
        println!("请求成功");
    } else if response.status().is_client_error() {
        println!("客户端错误: {}", response.status());
    } else if response.status().is_server_error() {
        println!("服务器错误: {}", response.status());
    }

    // 方法 2: 自动错误处理
    let response = reqwest::get("https://httpbin.org/status/404")
        .await?
        .error_for_status()?; // 非 2xx 状态码返回错误

    Ok(())
}
```

### 4.2 响应头解析

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let response = reqwest::get("https://httpbin.org/get").await?;

    // 获取单个头部
    if let Some(content_type) = response.headers().get("content-type") {
        println!("Content-Type: {}", content_type.to_str()?);
    }

    // 遍历所有头部
    for (name, value) in response.headers() {
        println!("{}: {}", name, value.to_str().unwrap_or("<非 UTF-8>"));
    }

    Ok(())
}
```

### 4.3 响应体解析

```rust
use reqwest;
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct ApiResponse {
    origin: String,
    url: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 解析为文本
    let text = reqwest::get("https://httpbin.org/get")
        .await?
        .text()
        .await?;
    println!("文本响应: {}", text);

    // 解析为 JSON
    let json: ApiResponse = reqwest::get("https://httpbin.org/get")
        .await?
        .json()
        .await?;
    println!("JSON 响应: {:#?}", json);

    // 解析为字节
    let bytes = reqwest::get("https://httpbin.org/get")
        .await?
        .bytes()
        .await?;
    println!("字节数: {}", bytes.len());

    Ok(())
}
```

---

## 5. 错误处理与重试

### 5.1 错误类型

```rust
use reqwest;

#[tokio::main]
async fn main() {
    match reqwest::get("https://invalid-url-12345.com").await {
        Ok(response) => {
            println!("成功: {}", response.status());
        }
        Err(e) => {
            if e.is_timeout() {
                eprintln!("请求超时");
            } else if e.is_connect() {
                eprintln!("连接失败");
            } else if e.is_status() {
                eprintln!("HTTP 状态错误: {:?}", e.status());
            } else {
                eprintln!("其他错误: {}", e);
            }
        }
    }
}
```

### 5.2 重试策略

```rust
use reqwest::Client;
use std::time::Duration;
use tokio::time::sleep;

async fn fetch_with_retry(
    client: &Client,
    url: &str,
    max_retries: u32,
) -> Result<reqwest::Response, reqwest::Error> {
    let mut attempts = 0;
    let mut delay = Duration::from_millis(100);

    loop {
        match client.get(url).send().await {
            Ok(response) if response.status().is_success() => {
                return Ok(response);
            }
            Ok(response) => {
                eprintln!("非成功状态码: {}", response.status());
            }
            Err(e) if attempts < max_retries => {
                attempts += 1;
                eprintln!("请求失败（尝试 {}/{}）: {}", attempts, max_retries, e);
                sleep(delay).await;
                delay *= 2; // 指数退避
                continue;
            }
            Err(e) => return Err(e),
        }

        if attempts >= max_retries {
            return Err(reqwest::Error::new(
                reqwest::ErrorKind::Request,
                "超过最大重试次数",
            ));
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    let response = fetch_with_retry(&client, "https://httpbin.org/get", 3).await?;
    println!("成功: {}", response.status());
    Ok(())
}
```

---

## 6. 高级特性

### 6.1 Cookie 管理

```rust
use reqwest::Client;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启用 Cookie 存储
    let client = Client::builder()
        .cookie_store(true)
        .build()?;

    // 第一个请求：设置 Cookie
    let response = client.get("https://httpbin.org/cookies/set?foo=bar").send().await?;
    println!("设置 Cookie: {}", response.status());

    // 第二个请求：自动发送 Cookie
    let response = client.get("https://httpbin.org/cookies").send().await?;
    let body = response.text().await?;
    println!("Cookie 内容:\n{}", body);

    Ok(())
}
```

### 6.2 代理设置

```rust
use reqwest::{Client, Proxy};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // HTTP 代理
    let proxy = Proxy::http("http://proxy.example.com:8080")?;

    let client = Client::builder()
        .proxy(proxy)
        .build()?;

    let response = client.get("https://httpbin.org/ip").send().await?;
    println!("{}", response.text().await?);

    Ok(())
}
```

### 6.3 文件上传

```rust
use reqwest::Client;
use reqwest::multipart::{Form, Part};
use tokio::fs::File;
use tokio::io::AsyncReadExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();

    // 读取文件
    let mut file = File::open("example.txt").await?;
    let mut contents = vec![];
    file.read_to_end(&mut contents).await?;

    // 创建 multipart 表单
    let part = Part::bytes(contents)
        .file_name("example.txt")
        .mime_str("text/plain")?;

    let form = Form::new()
        .text("field1", "value1")
        .part("file", part);

    // 上传
    let response = client
        .post("https://httpbin.org/post")
        .multipart(form)
        .send()
        .await?;

    println!("上传成功: {}", response.status());

    Ok(())
}
```

### 6.4 流式下载

```rust
use reqwest::Client;
use tokio::fs::File;
use tokio::io::AsyncWriteExt;
use futures_util::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    let url = "https://httpbin.org/bytes/10240"; // 下载 10KB

    let response = client.get(url).send().await?;
    let mut stream = response.bytes_stream();
    let mut file = File::create("downloaded.bin").await?;

    let mut downloaded = 0;
    while let Some(chunk) = stream.next().await {
        let chunk = chunk?;
        file.write_all(&chunk).await?;
        downloaded += chunk.len();
        println!("已下载: {} 字节", downloaded);
    }

    file.flush().await?;
    println!("下载完成");

    Ok(())
}
```

---

## 7. 实战案例

### 7.1 GitHub API 客户端

```rust
use reqwest::Client;
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct GitHubUser {
    login: String,
    name: Option<String>,
    public_repos: u32,
    followers: u32,
}

struct GitHubClient {
    client: Client,
    base_url: String,
}

impl GitHubClient {
    fn new(token: Option<&str>) -> Self {
        let mut client_builder = Client::builder();

        if let Some(token) = token {
            let mut headers = reqwest::header::HeaderMap::new();
            headers.insert(
                reqwest::header::AUTHORIZATION,
                format!("Bearer {}", token).parse().unwrap(),
            );
            client_builder = client_builder.default_headers(headers);
        }

        Self {
            client: client_builder.build().unwrap(),
            base_url: "https://api.github.com".to_string(),
        }
    }

    async fn get_user(&self, username: &str) -> Result<GitHubUser, reqwest::Error> {
        let url = format!("{}/users/{}", self.base_url, username);
        self.client
            .get(&url)
            .header("User-Agent", "rust-http-client")
            .send()
            .await?
            .json()
            .await
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = GitHubClient::new(None);

    let user = client.get_user("torvalds").await?;
    println!("用户: {:#?}", user);

    Ok(())
}
```

### 7.2 并发请求

```rust
use reqwest::Client;
use tokio::task::JoinSet;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    let urls = vec![
        "https://httpbin.org/delay/1",
        "https://httpbin.org/delay/2",
        "https://httpbin.org/delay/1",
    ];

    let mut tasks = JoinSet::new();

    for url in urls {
        let client = client.clone();
        let url = url.to_string();

        tasks.spawn(async move {
            let start = std::time::Instant::now();
            let response = client.get(&url).send().await;
            let elapsed = start.elapsed();
            (url, response, elapsed)
        });
    }

    while let Some(result) = tasks.join_next().await {
        let (url, response, elapsed) = result?;
        match response {
            Ok(resp) => println!("✅ {} - {} ({:?})", url, resp.status(), elapsed),
            Err(e) => println!("❌ {} - Error: {}", url, e),
        }
    }

    Ok(())
}
```

### 7.3 RESTful API 封装

```rust
use reqwest::{Client, Method, Response};
use serde::{Deserialize, Serialize};

struct ApiClient {
    client: Client,
    base_url: String,
}

impl ApiClient {
    fn new(base_url: impl Into<String>) -> Self {
        Self {
            client: Client::new(),
            base_url: base_url.into(),
        }
    }

    async fn request<T: Serialize>(
        &self,
        method: Method,
        path: &str,
        body: Option<&T>,
    ) -> Result<Response, reqwest::Error> {
        let url = format!("{}{}", self.base_url, path);
        let mut request = self.client.request(method, url);

        if let Some(body) = body {
            request = request.json(body);
        }

        request.send().await
    }

    async fn get(&self, path: &str) -> Result<Response, reqwest::Error> {
        self.request::<()>(Method::GET, path, None).await
    }

    async fn post<T: Serialize>(&self, path: &str, body: &T) -> Result<Response, reqwest::Error> {
        self.request(Method::POST, path, Some(body)).await
    }
}

#[derive(Serialize)]
struct CreateUserRequest {
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let api = ApiClient::new("https://httpbin.org");

    // GET 请求
    let response = api.get("/get").await?;
    println!("GET: {}", response.status());

    // POST 请求
    let user = CreateUserRequest {
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };
    let response = api.post("/post", &user).await?;
    println!("POST: {}", response.status());

    Ok(())
}
```

---

## 8. 总结

### 核心要点

| 特性 | reqwest | 适用场景 |
| --- | --- | --- |
| **异步** | ✅ | 高并发 |
| **同步** | ✅ | 简单脚本 |
| **TLS** | ✅ | HTTPS |
| **Cookie** | ✅ | 会话管理 |
| **代理** | ✅ | 网络隔离 |

### 最佳实践

1. **复用客户端**: `Client` 对象可安全共享
2. **设置超时**: 避免无限等待
3. **错误处理**: 使用 `?` 运算符传播错误
4. **并发控制**: 使用 `tokio::task::JoinSet`
5. **流式处理**: 大文件下载用流式API

---

## 📚 参考资源

- [reqwest 文档](https://docs.rs/reqwest/)
- [HTTP 协议](https://developer.mozilla.org/zh-CN/docs/Web/HTTP)
- [REST API 设计](https://restfulapi.net/)

---

**下一步**: 学习 [WebSocket 实时通信](03_WebSocket实时通信.md)，掌握双向通信技术。
