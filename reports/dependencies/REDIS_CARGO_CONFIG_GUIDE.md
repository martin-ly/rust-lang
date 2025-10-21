# Redis Cargo 配置指南

**更新日期**: 2025-10-20  
**Redis 版本**: 1.0.0-rc.2 (最新)

## 📋 项目中的 Redis 使用情况

本项目在以下模块中使用了 Redis：

1. **c06_async** - 异步编程模块（分布式缓存示例）
2. **c11_libraries** - 中间件模块（KV 存储抽象）
3. **Workspace** - 根配置统一版本管理

## 🚀 快速开始

### 1. 基础配置（最简单）

```toml
[dependencies]
redis = "1.0.0-rc.2"
```

### 2. 异步支持（推荐）

```toml
[dependencies]
redis = { version = "1.0.0-rc.2", features = ["tokio-comp"] }
tokio = { version = "1.48", features = ["full"] }
```

### 3. 连接管理（生产环境推荐）

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = ["tokio-comp", "connection-manager"] 
}
tokio = { version = "1.48", features = ["full"] }
```

## 📦 本项目的实际配置

### 配置 1: c06_async 模块 (完整功能)

**文件**: `crates/c06_async/Cargo.toml`

```toml
[dependencies]
# 分布式与微服务（高级案例）
redis = { 
    version = "1.0.0-rc.2",  # ✅ 已更新到最新版本
    features = ["tokio-comp", "connection-manager"] 
}
tokio = { workspace = true }  # 1.48.0，支持 full features
```

**特性说明**:

- ✅ `tokio-comp`: Tokio 异步运行时兼容
- ✅ `connection-manager`: 连接池管理，自动重连

**使用场景**: 异步应用、分布式缓存、微服务

### 配置 2: c11_libraries 模块 (可选特性)

**文件**: `crates/c11_libraries/Cargo.toml`

```toml
[dependencies]
# Key-Value
redis = { 
    version = "1.0.0-rc.2",  # ✅ 已更新到最新版本
    optional = true, 
    default-features = false, 
    features = ["aio", "tokio-comp"] 
}
tokio = { workspace = true, optional = true }

[features]
# 使用 Tokio 运行时
kv-redis = ["redis", "tokio"]

# 使用 Glommio 高性能运行时
kv-redis-glommio = ["redis", "glommio"]

# 完整功能
full = ["kv-redis", ...]
```

**特性说明**:

- ✅ `optional = true`: 作为可选依赖
- ✅ `default-features = false`: 减小二进制大小
- ✅ `aio`: 异步 IO 支持
- ✅ `tokio-comp`: Tokio 兼容层

**使用场景**: 库开发、可选 Redis 支持、最小化依赖

### 配置 3: Workspace 统一版本

**文件**: `Cargo.toml` (根目录)

```toml
[workspace.dependencies]
# redis: Redis客户端库，支持异步操作 - 2025年10月20日最新版本
redis = "1.0.0-rc.2"  # ✅ 已更新到最新版本
```

**好处**:

- ✅ 统一版本管理
- ✅ 减少版本冲突
- ✅ 简化依赖更新

## 🎯 Redis 功能特性详解

### 完整特性列表

| 特性 | 说明 | 用途 |
|------|------|------|
| `aio` | 异步 IO 支持 | 异步应用 |
| `tokio-comp` | Tokio 运行时兼容 | 与 Tokio 集成 |
| `async-std-comp` | async-std 兼容 | 与 async-std 集成 |
| `connection-manager` | 连接池管理 | 生产环境 |
| `cluster` | Redis 集群支持 | 分布式部署 |
| `cluster-async` | 异步集群支持 | 异步集群 |
| `script` | Lua 脚本支持 | 复杂逻辑 |
| `r2d2` | r2d2 连接池 | 同步连接池 |
| `ahash` | ahash 哈希算法 | 性能优化 |
| `tls` | TLS/SSL 支持 | 加密连接 |
| `tls-native-tls` | native-tls 实现 | 系统 TLS |
| `tls-rustls` | rustls 实现 | 纯 Rust TLS |
| `tls-rustls-insecure` | rustls 不验证证书 | 开发测试 |
| `json` | JSON 序列化 | JSON 数据 |
| `sentinel` | Redis Sentinel | 高可用 |

### 推荐配置组合

#### 1. 基础异步应用

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = ["tokio-comp"] 
}
```

**适用**: 简单的异步 Redis 操作

#### 2. 生产环境 Web 应用

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",           # Tokio 支持
        "connection-manager",   # 连接池
        "script",               # Lua 脚本
        "json"                  # JSON 支持
    ] 
}
```

**适用**: Web 服务、API 后端

#### 3. 分布式集群应用

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",
        "connection-manager",
        "cluster-async",        # 集群支持
        "tls-rustls"           # 加密连接
    ] 
}
```

**适用**: 微服务、分布式系统

#### 4. 高安全性应用

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",
        "connection-manager",
        "tls-rustls",           # TLS 加密
        "sentinel"              # 高可用
    ] 
}
```

**适用**: 金融、医疗等高安全场景

#### 5. 高可用部署

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",
        "connection-manager",
        "cluster-async",
        "sentinel",             # Sentinel 支持
        "tls-rustls"
    ] 
}
```

**适用**: 企业级应用

## 💻 代码示例

### 示例 1: 基础连接

```rust
use redis::{Client, Commands};

fn main() -> redis::RedisResult<()> {
    // 创建客户端
    let client = Client::open("redis://127.0.0.1:6379")?;
    let mut con = client.get_connection()?;
    
    // 设置值
    con.set("my_key", "hello")?;
    
    // 获取值
    let value: String = con.get("my_key")?;
    println!("Value: {}", value);
    
    Ok(())
}
```

### 示例 2: 异步连接（Tokio）

```rust
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    // 创建客户端
    let client = redis::Client::open("redis://127.0.0.1:6379")?;
    let mut con = client.get_multiplexed_async_connection().await?;
    
    // 设置值
    con.set("my_key", "hello").await?;
    
    // 获取值
    let value: String = con.get("my_key").await?;
    println!("Value: {}", value);
    
    Ok(())
}
```

### 示例 3: 连接池管理器

```rust
use redis::aio::ConnectionManager;
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    let client = redis::Client::open("redis://127.0.0.1:6379")?;
    
    // 创建连接管理器（自动重连）
    let mut con = ConnectionManager::new(client).await?;
    
    // 使用连接
    con.set("my_key", "hello").await?;
    let value: String = con.get("my_key").await?;
    println!("Value: {}", value);
    
    Ok(())
}
```

### 示例 4: 集群连接

```rust
use redis::cluster::ClusterClient;
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    let nodes = vec!["redis://127.0.0.1:7000/"];
    let client = ClusterClient::new(nodes)?;
    let mut con = client.get_async_connection().await?;
    
    con.set("my_key", "hello").await?;
    let value: String = con.get("my_key").await?;
    println!("Value: {}", value);
    
    Ok(())
}
```

### 示例 5: TLS 加密连接

```rust
use redis::Client;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    // TLS 连接
    let client = Client::open("rediss://127.0.0.1:6380")?;  // 注意是 rediss://
    let mut con = client.get_multiplexed_async_connection().await?;
    
    // 正常使用
    con.set("secure_key", "secure_value").await?;
    
    Ok(())
}
```

### 示例 6: Lua 脚本

```rust
use redis::{Script, AsyncCommands};

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    let client = redis::Client::open("redis://127.0.0.1:6379")?;
    let mut con = client.get_multiplexed_async_connection().await?;
    
    // 创建 Lua 脚本
    let script = Script::new(r"
        redis.call('SET', KEYS[1], ARGV[1])
        return redis.call('GET', KEYS[1])
    ");
    
    // 执行脚本
    let result: String = script
        .key("my_key")
        .arg("my_value")
        .invoke_async(&mut con)
        .await?;
    
    println!("Result: {}", result);
    
    Ok(())
}
```

## 🔧 项目配置示例

### 完整的 Web 应用配置

```toml
[package]
name = "my-web-app"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Redis
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",
        "connection-manager",
        "script",
        "json",
        "tls-rustls"
    ] 
}

# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# Web 框架
axum = "0.8"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"

# 错误处理
anyhow = "1.0"
thiserror = "2.0"

[profile.release]
opt-level = 3
lto = true
```

### 微服务配置

```toml
[package]
name = "my-microservice"
version = "0.1.0"
edition = "2024"

[dependencies]
# Redis 集群
redis = { 
    version = "1.0.0-rc.2", 
    features = [
        "tokio-comp",
        "connection-manager",
        "cluster-async",
        "sentinel",
        "tls-rustls",
        "json"
    ] 
}

# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# 服务发现
consul = "0.4"

# 可观测性
tracing = "0.1"
opentelemetry = "0.31"
```

## 🚀 性能优化建议

### 1. 使用连接池

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = ["tokio-comp", "connection-manager"] 
}
```

### 2. 使用 ahash（更快的哈希）

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = ["tokio-comp", "ahash"] 
}
```

### 3. 使用管道（Pipeline）

```rust
use redis::pipe;

let mut pipe = pipe();
pipe.set("key1", "value1")
    .set("key2", "value2")
    .set("key3", "value3");
pipe.query_async(&mut con).await?;
```

### 4. 最小化特性

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    default-features = false,
    features = ["aio", "tokio-comp"]  # 只启用需要的
}
```

## 🔒 安全性最佳实践

### 1. 使用 TLS

```toml
[dependencies]
redis = { 
    version = "1.0.0-rc.2", 
    features = ["tokio-comp", "tls-rustls"] 
}
```

### 2. 使用环境变量

```rust
use std::env;

let redis_url = env::var("REDIS_URL")
    .unwrap_or_else(|_| "redis://127.0.0.1:6379".to_string());
let client = redis::Client::open(redis_url)?;
```

### 3. 设置超时

```rust
let client = redis::Client::open("redis://127.0.0.1:6379")?
    .set_read_timeout(Some(Duration::from_secs(5)))?
    .set_write_timeout(Some(Duration::from_secs(5)))?;
```

## 📊 版本对比

| 版本 | 发布日期 | 主要特性 | 状态 |
|------|---------|---------|------|
| 1.0.0-rc.2 | 2025-10 | 稳定性改进 | ✅ 最新 |
| 1.0.0-rc.1 | 2025-09 | RC 版本 | 推荐更新 |
| 0.32.7 | 2024 | 稳定版 | 旧版本 |

## 🔄 升级指南

### 从 0.32.7 升级到 1.0.0-rc.2 ✅ 已完成

```toml
# 旧版本 (已升级前)
[dependencies]
redis = { version = "0.32.7", features = ["aio", "tokio-comp"] }

# 新版本 (当前)
[dependencies]
redis = { version = "1.0.0-rc.2", features = ["aio", "tokio-comp"] }
```

**变更说明**:

- ✅ `aio` 特性保持兼容
- ✅ API 完全兼容，无需修改代码
- ✅ 性能和稳定性改进
- ✅ 本项目已全部升级完成

## 📚 相关资源

- **官方文档**: <https://docs.rs/redis/>
- **GitHub**: <https://github.com/redis-rs/redis-rs>
- **Redis 官网**: <https://redis.io/>
- **示例代码**: <https://github.com/redis-rs/redis-rs/tree/main/examples>

## 🤝 项目中的使用

查看项目中的实际使用示例：

```bash
# c06_async 模块示例
cd crates/c06_async
cargo run --example redis_cache

# c11_libraries 模块示例
cd crates/c11_libraries
cargo run --example message_queue --features kv-redis
```

---

**最后更新**: 2025-10-20  
**Redis 版本**: 1.0.0-rc.2  
**Rust 版本**: 1.90+
