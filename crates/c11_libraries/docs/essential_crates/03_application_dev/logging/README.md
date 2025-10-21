# 日志与追踪

> **核心库**: tracing, log, env_logger, tracing-subscriber  
> **适用场景**: 应用日志、分布式追踪、性能分析

---

## 📋 目录

- [日志与追踪](#日志与追踪)
  - [📋 目录](#-目录)
  - [📋 核心库对比](#-核心库对比)
  - [🔍 tracing - 现代首选](#-tracing---现代首选)
  - [📝 log - 传统日志](#-log---传统日志)
  - [🎨 结构化日志](#-结构化日志)

## 📋 核心库对比

| 库 | 类型 | 异步 | 结构化 | 推荐度 |
|-----|------|------|--------|--------|
| **tracing** | 现代追踪 | ✅ | ✅ | ⭐⭐⭐⭐⭐ |
| **log** | 传统日志 | ❌ | ❌ | ⭐⭐⭐⭐ |
| **env_logger** | log后端 | ❌ | ❌ | ⭐⭐⭐⭐ |

---

## 🔍 tracing - 现代首选

```rust
use tracing::{info, warn, error, debug, span, Level};
use tracing_subscriber;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();
    
    info!("Application started");
    
    let span = span!(Level::INFO, "request", id = 123);
    let _enter = span.enter();
    
    debug!("Processing request");
    process_data(42).await;
    warn!("Warning message");
    
    info!("Request completed");
}

#[tracing::instrument]
async fn process_data(value: i32) {
    info!(value, "Processing");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

---

## 📝 log - 传统日志

```rust
use log::{info, warn, error, debug};
use env_logger;

fn main() {
    env_logger::init();
    
    info!("Application started");
    debug!("Debug info");
    warn!("Warning");
    error!("Error occurred");
}
```

---

## 🎨 结构化日志

```rust
use tracing::{info, info_span};
use tracing_subscriber::fmt;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_target(false)
        .with_thread_ids(true)
        .with_level(true)
        .json()
        .init();
    
    info!(
        user_id = 123,
        action = "login",
        "User logged in"
    );
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
