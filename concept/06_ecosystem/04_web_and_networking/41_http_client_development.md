> **内容分级**: [进阶]
> **代码状态**: ✅ 含可编译示例
>
# HTTP 客户端开发
>
> **EN**: HTTP Client Development in Rust
> **Summary**: Building HTTP clients in Rust with reqwest: request construction, response handling, connection reuse, retries, cookies, proxies, and file uploads.
>
> **受众**: [进阶]
> **层级**: L6 应用主题
> **A/S/P 标记**: **A+P** — Application + Procedure
> **前置概念**: [Async/Await](../../03_advanced/01_async/02_async.md) · [Rust 网络编程](../../03_advanced/06_low_level_patterns/18_network_programming.md) · [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md)
> **后置概念**: [Web Frameworks](27_web_frameworks.md) · [Distributed Systems](18_distributed_systems.md)
>
> **来源**: [reqwest](https://docs.rs/reqwest/) · [hyper](https://hyper.rs/) · [RFC 9110 — HTTP Semantics](https://www.rfc-editor.org/rfc/rfc9110.html)

---

## 1. HTTP 方法语义

| 方法 | 幂等性 | 安全性 | 请求体 | 用途 |
| :--- | :--- | :--- | :--- | :--- |
| GET | ✅ | ✅ | ❌ | 获取资源 |
| HEAD | ✅ | ✅ | ❌ | 获取元数据 |
| POST | ❌ | ❌ | ✅ | 创建资源 |
| PUT | ✅ | ❌ | ✅ | 更新资源 |
| PATCH | ❌ | ❌ | ✅ | 部分更新 |
| DELETE | ✅ | ❌ | ❌ | 删除资源 |

## 2. 使用 reqwest

### 2.1 基础请求

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let response = reqwest::get("https://httpbin.org/get").await?;
    println!("Status: {}", response.status());
    println!("Headers: {:#?}", response.headers());

    let body = response.text().await?;
    println!("{}", body);
    Ok(())
}
```

### 2.2 创建可复用客户端

```rust
use reqwest::Client;
use std::time::Duration;

fn create_client() -> Client {
    Client::builder()
        .timeout(Duration::from_secs(10))
        .user_agent("my-rust-app/1.0")
        .gzip(true)
        .pool_max_idle_per_host(10)
        .build()
        .expect("创建客户端失败")
}
```

### 2.3 POST JSON

```rust
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();
    let response = client
        .post("https://httpbin.org/post")
        .json(&json!({ "name": "rust" }))
        .send()
        .await?;

    let json: serde_json::Value = response.json().await?;
    println!("{:#?}", json);
    Ok(())
}
```

### 2.4 自定义请求头

```rust
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION, CONTENT_TYPE};

fn default_headers() -> HeaderMap {
    let mut headers = HeaderMap::new();
    headers.insert(CONTENT_TYPE, HeaderValue::from_static("application/json"));
    headers.insert(AUTHORIZATION, HeaderValue::from_static("Bearer TOKEN"));
    headers
}
```

## 3. 响应处理

```rust
fn interpret_status(code: u16) -> &'static str {
    match code {
        200..=299 => "成功",
        300..=399 => "重定向",
        400..=499 => "客户端错误",
        500..=599 => "服务器错误",
        _ => "未知",
    }
}
```

## 4. 重试策略

```rust
use tokio::time::{sleep, Duration};

async fn fetch_with_retry(url: &str, max_retries: u32) -> Result<String, reqwest::Error> {
    let client = reqwest::Client::new();
    for attempt in 0..max_retries {
        match client.get(url).send().await {
            Ok(resp) if resp.status().is_success() => return resp.text().await,
            Ok(resp) => eprintln!("服务器错误: {}", resp.status()),
            Err(e) => eprintln!("请求失败: {}", e),
        }
        sleep(Duration::from_millis(500 * 2_u64.pow(attempt))).await;
    }
    Err(reqwest::Error::from(std::io::Error::new(
        std::io::ErrorKind::Other,
        "达到最大重试次数",
    )))
}
```

## 5. 文件上传

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = reqwest::Client::new();
    let file = tokio::fs::read("data.bin").await?;

    let response = client
        .post("https://httpbin.org/post")
        .body(file)
        .send()
        .await?;

    println!("{}", response.status());
    Ok(())
}
```

## 6. 代理与 Cookie

```rust
use reqwest::Proxy;

fn client_with_proxy() -> Result<reqwest::Client, reqwest::Error> {
    reqwest::Client::builder()
        .proxy(Proxy::https("http://proxy.example.com:8080")?)
        .cookie_store(true)
        .build()
}
```

## 7. 最佳实践

- 复用 `Client` 实例以复用连接池。
- 为所有外部请求设置超时。
- 对幂等请求实现指数退避重试。
- 对 4xx/5xx 错误进行分类处理，避免无差别重试。
- 敏感信息（token）不要硬编码，应从环境变量或密钥管理器读取。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

## 相关概念

- [Rust 网络编程](../../03_advanced/06_low_level_patterns/18_network_programming.md)
- [Web 框架对比](27_web_frameworks.md)
- [网络安全](../09_networking/02_network_security.md)

---

> **来源**: [reqwest Documentation](https://docs.rs/reqwest/) · [RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html)
