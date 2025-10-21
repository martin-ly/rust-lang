# Logging - 日志工具

## 📋 目录

- [概述](#概述)
- [日志框架](#日志框架)
- [结构化日志](#结构化日志)

---

## 概述

开发工具链中的日志配置和最佳实践。

---

## 日志框架

### env_logger

```rust
use log::{info, warn, error};

fn main() {
    env_logger::init();
    
    info!("应用启动");
    warn!("警告信息");
    error!("错误信息");
}
```

```bash
# 运行时配置
RUST_LOG=debug cargo run
RUST_LOG=my_app=trace cargo run
```

### tracing

```rust
use tracing::{info, instrument};

#[instrument]
fn process_data(id: u32) {
    info!(id, "处理数据");
}

fn main() {
    tracing_subscriber::fmt::init();
    
    process_data(42);
}
```

---

## 结构化日志

### JSON 输出

```rust
use tracing_subscriber::fmt;

fn main() {
    fmt()
        .json()
        .with_max_level(tracing::Level::INFO)
        .init();
    
    tracing::info!(
        user_id = 123,
        action = "login",
        "用户登录"
    );
}
```

---

## 参考资源

- [log crate 文档](https://docs.rs/log/)
- [tracing 文档](https://docs.rs/tracing/)

