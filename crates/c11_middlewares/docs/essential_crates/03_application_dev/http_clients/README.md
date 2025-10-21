# HTTP 客户端

> **核心库**: reqwest, surf, ureq  
> **适用场景**: API调用、HTTP请求、文件下载

---

## 📋 核心库对比

| 库 | 异步 | 特点 | 推荐度 |
|-----|------|------|--------|
| **reqwest** | ✅ | 功能全面 | ⭐⭐⭐⭐⭐ |
| **surf** | ✅ | 简洁 | ⭐⭐⭐⭐ |
| **ureq** | ❌ | 同步、轻量 | ⭐⭐⭐⭐ |

---

## 🌐 reqwest - 首选

### 基础用法

```rust
use reqwest;
use serde::{Deserialize, Serialize};

#[derive(Deserialize, Debug)]
struct Post {
    id: u32,
    title: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // GET 请求
    let response = reqwest::get("https://jsonplaceholder.typicode.com/posts/1")
        .await?
        .json::<Post>()
        .await?;
    
    println!("{:?}", response);
    
    // POST 请求
    let client = reqwest::Client::new();
    let res = client.post("https://httpbin.org/post")
        .json(&serde_json::json!({"key": "value"}))
        .send()
        .await?;
    
    println!("Status: {}", res.status());
    Ok(())
}
```

### 高级特性

```rust
use reqwest::{Client, header};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 自定义客户端
    let client = Client::builder()
        .timeout(std::time::Duration::from_secs(10))
        .user_agent("my-app/1.0")
        .build()?;
    
    // 设置请求头
    let res = client.get("https://api.example.com/data")
        .header(header::AUTHORIZATION, "Bearer token")
        .header(header::ACCEPT, "application/json")
        .send()
        .await?;
    
    let body = res.text().await?;
    println!("{}", body);
    
    Ok(())
}
```

### 文件上传/下载

```rust
use reqwest;
use tokio::fs::File;
use tokio::io::AsyncWriteExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 下载文件
    let response = reqwest::get("https://example.com/file.zip").await?;
    let mut file = File::create("downloaded.zip").await?;
    let content = response.bytes().await?;
    file.write_all(&content).await?;
    
    // 上传文件
    let client = reqwest::Client::new();
    let form = reqwest::multipart::Form::new()
        .text("field", "value")
        .file("file", "path/to/file").await?;
    
    let res = client.post("https://httpbin.org/post")
        .multipart(form)
        .send()
        .await?;
    
    Ok(())
}
```

---

## 💡 最佳实践

### 错误处理

```rust
use reqwest;
use thiserror::Error;

#[derive(Error, Debug)]
enum ApiError {
    #[error("HTTP error: {0}")]
    Http(#[from] reqwest::Error),
    
    #[error("Not found")]
    NotFound,
}

async fn fetch_user(id: u32) -> Result<User, ApiError> {
    let res = reqwest::get(format!("https://api.example.com/users/{}", id))
        .await?;
    
    if res.status() == 404 {
        return Err(ApiError::NotFound);
    }
    
    Ok(res.json().await?)
}
```

### 连接池复用

```rust
use reqwest::Client;
use std::sync::Arc;

struct ApiClient {
    client: Arc<Client>,
}

impl ApiClient {
    fn new() -> Self {
        let client = Client::builder()
            .pool_max_idle_per_host(10)
            .build()
            .unwrap();
        
        Self {
            client: Arc::new(client),
        }
    }
    
    async fn get(&self, url: &str) -> Result<String, reqwest::Error> {
        self.client.get(url).send().await?.text().await
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
