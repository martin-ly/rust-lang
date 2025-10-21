# Caching - 缓存解决方案

## 📋 目录

- [Caching - 缓存解决方案](#caching---缓存解决方案)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [内存缓存](#内存缓存)
    - [Moka - 高性能缓存](#moka---高性能缓存)
    - [异步 Moka](#异步-moka)
    - [Cached 宏](#cached-宏)
  - [分布式缓存](#分布式缓存)
    - [Redis 缓存](#redis-缓存)
  - [缓存策略](#缓存策略)
    - [1. 多级缓存](#1-多级缓存)
    - [2. Cache-Aside 模式](#2-cache-aside-模式)
  - [实战示例](#实战示例)
    - [HTTP 响应缓存](#http-响应缓存)
  - [最佳实践](#最佳实践)
    - [1. 缓存键设计](#1-缓存键设计)
    - [2. 缓存穿透保护](#2-缓存穿透保护)
  - [参考资源](#参考资源)

---

## 概述

缓存是提升应用性能的关键技术，通过存储频繁访问的数据来减少计算和I/O开销。

### 核心依赖

```toml
[dependencies]
# 内存缓存
moka = { version = "0.12", features = ["future"] }
cached = "0.46"

# 分布式缓存
redis = { version = "0.24", features = ["tokio-comp", "connection-manager"] }
```

---

## 内存缓存

### Moka - 高性能缓存

```rust
use moka::sync::Cache;
use std::time::Duration;

fn moka_basic() {
    // 创建缓存（最大10000项，TTL 30秒）
    let cache: Cache<String, String> = Cache::builder()
        .max_capacity(10_000)
        .time_to_live(Duration::from_secs(30))
        .build();
    
    // 插入
    cache.insert("key1".to_string(), "value1".to_string());
    
    // 获取
    if let Some(value) = cache.get(&"key1".to_string()) {
        println!("缓存命中: {}", value);
    }
    
    // 获取或插入
    let value = cache.get_with("key2".to_string(), || {
        // 计算昂贵的值
        "computed_value".to_string()
    });
}
```

### 异步 Moka

```rust
use moka::future::Cache;
use std::time::Duration;

async fn moka_async() {
    let cache: Cache<String, String> = Cache::builder()
        .max_capacity(10_000)
        .time_to_live(Duration::from_secs(30))
        .build();
    
    // 异步插入
    cache.insert("key1".to_string(), "value1".to_string()).await;
    
    // 异步获取或插入
    let value = cache
        .get_with("key2".to_string(), async {
            // 异步计算
            tokio::time::sleep(Duration::from_millis(100)).await;
            "async_value".to_string()
        })
        .await;
    
    println!("值: {}", value);
}
```

### Cached 宏

```rust
use cached::proc_macro::cached;

// 自动缓存函数结果
#[cached(size = 100, time = 60)]
fn expensive_computation(n: u32) -> u32 {
    println!("计算 {}", n);
    n * 2
}

fn main() {
    println!("{}", expensive_computation(5)); // 计算
    println!("{}", expensive_computation(5)); // 缓存命中
    println!("{}", expensive_computation(10)); // 计算
}
```

---

## 分布式缓存

### Redis 缓存

```rust
use redis::AsyncCommands;

async fn redis_cache() -> redis::RedisResult<()> {
    // 连接 Redis
    let client = redis::Client::open("redis://127.0.0.1/")?;
    let mut con = client.get_async_connection().await?;
    
    // 设置值（带过期时间）
    con.set_ex("user:1001", "Alice", 3600).await?;
    
    // 获取值
    let value: String = con.get("user:1001").await?;
    println!("用户: {}", value);
    
    // 检查是否存在
    let exists: bool = con.exists("user:1001").await?;
    
    Ok(())
}
```

---

## 缓存策略

### 1. 多级缓存

```rust
use moka::sync::Cache as LocalCache;
use redis::AsyncCommands;
use std::time::Duration;

struct TieredCache {
    local: LocalCache<String, String>,
    redis_client: redis::Client,
}

impl TieredCache {
    async fn get(&self, key: &str) -> Option<String> {
        // L1: 本地缓存
        if let Some(value) = self.local.get(&key.to_string()) {
            return Some(value);
        }
        
        // L2: Redis
        let mut con = self.redis_client.get_async_connection().await.ok()?;
        if let Ok(value) = con.get::<_, String>(key).await {
            // 回填本地缓存
            self.local.insert(key.to_string(), value.clone());
            return Some(value);
        }
        
        None
    }
}
```

### 2. Cache-Aside 模式

```rust
use moka::sync::Cache;

async fn cache_aside_pattern(
    cache: &Cache<u32, String>,
    user_id: u32,
) -> Result<String, Box<dyn std::error::Error>> {
    // 1. 尝试从缓存读取
    if let Some(user) = cache.get(&user_id) {
        return Ok(user);
    }
    
    // 2. 缓存未命中，从数据库读取
    let user = fetch_from_database(user_id).await?;
    
    // 3. 写入缓存
    cache.insert(user_id, user.clone());
    
    Ok(user)
}

async fn fetch_from_database(user_id: u32) -> Result<String, Box<dyn std::error::Error>> {
    Ok(format!("User_{}", user_id))
}
```

---

## 实战示例

### HTTP 响应缓存

```rust
use axum::{
    Router,
    routing::get,
    extract::State,
    http::StatusCode,
};
use moka::future::Cache;
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone)]
struct AppState {
    cache: Arc<Cache<String, String>>,
}

async fn cached_handler(
    State(state): State<AppState>,
) -> Result<String, StatusCode> {
    let cache_key = "api:result";
    
    // 尝试从缓存获取
    if let Some(cached) = state.cache.get(cache_key).await {
        return Ok(cached);
    }
    
    // 计算结果
    let result = expensive_api_call().await;
    
    // 缓存5分钟
    state.cache.insert(
        cache_key.to_string(),
        result.clone(),
    ).await;
    
    Ok(result)
}

async fn expensive_api_call() -> String {
    tokio::time::sleep(Duration::from_secs(2)).await;
    "API Result".to_string()
}

#[tokio::main]
async fn main() {
    let cache = Arc::new(
        Cache::builder()
            .max_capacity(1000)
            .time_to_live(Duration::from_secs(300))
            .build()
    );
    
    let app_state = AppState { cache };
    
    let app = Router::new()
        .route("/", get(cached_handler))
        .with_state(app_state);
    
    println!("服务器运行在 http://127.0.0.1:3000");
}
```

---

## 最佳实践

### 1. 缓存键设计

```rust
fn cache_key_design() {
    // ✅ 好的设计：有命名空间、可读
    let key = format!("user:{}:profile", user_id);
    let key = format!("product:{}:price:USD", product_id);
    
    // ❌ 不好的设计：无结构
    let key = format!("{}{}", user_id, "profile");
}
```

### 2. 缓存穿透保护

```rust
use moka::sync::Cache;

// 使用 Option 缓存空结果
async fn cache_with_null_protection(
    cache: &Cache<u32, Option<String>>,
    user_id: u32,
) -> Option<String> {
    cache.get_with(user_id, || {
        // 即使不存在也缓存 None
        fetch_user_from_db(user_id)
    })
}

fn fetch_user_from_db(user_id: u32) -> Option<String> {
    None // 模拟
}
```

---

## 参考资源

- [Moka GitHub](https://github.com/moka-rs/moka)
- [Cached 文档](https://docs.rs/cached/)
- [Redis Rust 客户端](https://docs.rs/redis/)
