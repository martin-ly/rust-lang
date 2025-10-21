# Session - 会话管理

## 📋 目录

- [Session - 会话管理](#session---会话管理)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [tower-sessions](#tower-sessions)
    - [基础用法](#基础用法)
  - [Cookie-based Sessions](#cookie-based-sessions)
    - [使用 Cookie](#使用-cookie)
  - [Redis Sessions](#redis-sessions)
    - [Redis 存储](#redis-存储)
  - [最佳实践](#最佳实践)
    - [1. 安全的 Session ID](#1-安全的-session-id)
    - [2. Session 过期](#2-session-过期)
  - [参考资源](#参考资源)

---

## 概述

会话（Session）管理用于在多个 HTTP 请求之间保持用户状态。

### 核心依赖

```toml
[dependencies]
# Session 管理
tower-sessions = "0.10"
tower-sessions-redis-store = "0.10"

# Cookie
tower-cookies = "0.10"
```

---

## tower-sessions

### 基础用法

```rust
use axum::{Router, routing::get, extract::State};
use tower_sessions::{Session, MemoryStore, SessionManagerLayer};

async fn set_session(session: Session) -> String {
    session.insert("user_id", 42).await.unwrap();
    "Session 已设置".to_string()
}

async fn get_session(session: Session) -> String {
    let user_id: Option<i32> = session.get("user_id").await.unwrap();
    format!("用户 ID: {:?}", user_id)
}

#[tokio::main]
async fn main() {
    let session_store = MemoryStore::default();
    let session_layer = SessionManagerLayer::new(session_store);
    
    let app = Router::new()
        .route("/set", get(set_session))
        .route("/get", get(get_session))
        .layer(session_layer);
    
    println!("服务器运行中...");
}
```

---

## Cookie-based Sessions

### 使用 Cookie

```rust
use tower_cookies::{Cookie, Cookies, CookieManagerLayer};
use axum::{Router, routing::get};

async fn set_cookie(cookies: Cookies) -> &'static str {
    cookies.add(Cookie::new("user_id", "42"));
    "Cookie 已设置"
}

async fn get_cookie(cookies: Cookies) -> String {
    match cookies.get("user_id") {
        Some(cookie) => format!("用户 ID: {}", cookie.value()),
        None => "未找到 Cookie".to_string(),
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/set", get(set_cookie))
        .route("/get", get(get_cookie))
        .layer(CookieManagerLayer::new());
}
```

---

## Redis Sessions

### Redis 存储

```rust
use tower_sessions::{Session, SessionManagerLayer};
use tower_sessions_redis_store::{RedisStore, fred::prelude::*};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let pool = RedisPool::new(RedisConfig::default(), None, None, None, 6)?;
    pool.connect();
    pool.wait_for_connect().await?;
    
    let session_store = RedisStore::new(pool);
    let session_layer = SessionManagerLayer::new(session_store);
    
    let app = Router::new()
        .route("/", get(handler))
        .layer(session_layer);
    
    Ok(())
}

async fn handler(session: Session) -> String {
    let counter: i32 = session.get("counter").await.unwrap().unwrap_or(0);
    session.insert("counter", counter + 1).await.unwrap();
    format!("访问次数: {}", counter + 1)
}
```

---

## 最佳实践

### 1. 安全的 Session ID

```rust
use tower_sessions::SessionManagerLayer;

let session_layer = SessionManagerLayer::new(store)
    .with_secure(true)  // HTTPS only
    .with_http_only(true)  // 防止 XSS
    .with_same_site(tower_sessions::cookie::SameSite::Strict);  // CSRF 保护
```

### 2. Session 过期

```rust
use std::time::Duration;

let session_layer = SessionManagerLayer::new(store)
    .with_expiry(tower_sessions::Expiry::OnInactivity(
        Duration::from_secs(3600)  // 1小时不活动后过期
    ));
```

---

## 参考资源

- [tower-sessions GitHub](https://github.com/maxcountryman/tower-sessions)
- [tower-cookies 文档](https://docs.rs/tower-cookies/)
