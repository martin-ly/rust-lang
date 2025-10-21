# 配置管理 (Configuration Management)

**类别**: 横切关注点  
**重要程度**: ⭐⭐⭐⭐ (应用必备)  
**更新日期**: 2025-10-20

---

## 📋 概述

配置管理是应用程序适应不同环境（开发、测试、生产）的关键。
良好的配置管理遵循**12-Factor App**原则，支持多源配置、类型安全、环境隔离。

---

## 🔧 核心工具

### 1. config (多源配置 ⭐⭐⭐⭐⭐)

**添加依赖**:

```toml
[dependencies]
config = { version = "0.14", features = ["toml", "json", "yaml"] }
serde = { version = "1.0", features = ["derive"] }
```

**用途**: 从多个源（文件、环境变量）加载配置

#### 基础用法

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct AppConfig {
    database_url: String,
    port: u16,
    log_level: String,
    redis: RedisConfig,
}

#[derive(Debug, Deserialize)]
struct RedisConfig {
    host: String,
    port: u16,
}

fn load_config() -> Result<AppConfig, ConfigError> {
    let config = Config::builder()
        // 1. 默认配置
        .add_source(File::with_name("config/default"))
        // 2. 环境特定配置（dev, prod）
        .add_source(
            File::with_name(&format!(
                "config/{}",
                std::env::var("APP_ENV").unwrap_or_else(|_| "dev".into())
            ))
            .required(false)
        )
        // 3. 本地覆盖（不提交到 Git）
        .add_source(File::with_name("config/local").required(false))
        // 4. 环境变量（最高优先级）
        .add_source(Environment::with_prefix("APP").separator("__"))
        .build()?;
    
    config.try_deserialize()
}

fn main() -> Result<(), ConfigError> {
    let config = load_config()?;
    println!("Config: {:?}", config);
    Ok(())
}
```

#### 配置文件示例

**config/default.toml**:

```toml
# 默认配置
database_url = "postgres://localhost/mydb"
port = 3000
log_level = "info"

[redis]
host = "localhost"
port = 6379
```

**config/prod.toml**:

```toml
# 生产环境覆盖
port = 80
log_level = "warn"

[redis]
host = "redis.prod.example.com"
```

#### 环境变量覆盖

```bash
# 环境变量会覆盖文件配置
export APP_PORT=8080
export APP_DATABASE_URL=postgres://prod-db/mydb
export APP__REDIS__HOST=redis.example.com  # 双下划线表示嵌套
```

---

### 2. figment (类型安全配置 ⭐⭐⭐⭐)

**添加依赖**: `cargo add figment`  
**用途**: Rocket 框架配置库，类型安全

```rust
use figment::{Figment, providers::{Env, Format, Toml}};
use serde::Deserialize;

#[derive(Deserialize)]
struct Config {
    port: u16,
    database_url: String,
}

fn load_config() -> Config {
    Figment::new()
        .merge(Toml::file("Config.toml"))
        .merge(Env::prefixed("APP_"))
        .extract()
        .unwrap()
}
```

---

### 3. dotenvy (环境变量 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add dotenvy`  
**用途**: 从 `.env` 文件加载环境变量

#### 基础用法3

```rust
use dotenvy::dotenv;
use std::env;

fn main() {
    // 加载 .env 文件
    dotenv().ok();
    
    let database_url = env::var("DATABASE_URL")
        .expect("DATABASE_URL must be set");
    
    let port: u16 = env::var("PORT")
        .unwrap_or_else(|_| "3000".to_string())
        .parse()
        .expect("PORT must be a number");
    
    println!("Database URL: {}", database_url);
    println!("Port: {}", port);
}
```

**.env 文件**:

```bash
# .env (不提交到 Git)
DATABASE_URL=postgres://localhost/mydb
PORT=3000
SECRET_KEY=my-secret-key
RUST_LOG=debug
```

**.env.example 文件**:

```bash
# .env.example (提交到 Git，作为模板)
DATABASE_URL=postgres://localhost/mydb
PORT=3000
SECRET_KEY=change-me
RUST_LOG=info
```

---

### 4. envy (环境变量反序列化 💡)

**添加依赖**: `cargo add envy`  
**用途**: 直接将环境变量反序列化为结构体

```rust
use serde::Deserialize;

#[derive(Deserialize)]
struct Config {
    database_url: String,
    port: u16,
    log_level: String,
}

fn main() {
    let config: Config = envy::from_env().unwrap();
    println!("{:?}", config);
}
```

---

### 5. clap (CLI 参数 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add clap --features derive`  
**用途**: 命令行参数解析

```rust
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "myapp")]
#[command(about = "My Application", long_about = None)]
struct Cli {
    /// Config file path
    #[arg(short, long, default_value = "config.toml")]
    config: String,
    
    /// Server port
    #[arg(short, long, default_value_t = 3000)]
    port: u16,
    
    /// Log level
    #[arg(short, long, default_value = "info")]
    log_level: String,
    
    /// Enable verbose mode
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let cli = Cli::parse();
    
    println!("Config file: {}", cli.config);
    println!("Port: {}", cli.port);
    println!("Log level: {}", cli.log_level);
    println!("Verbose: {}", cli.verbose);
}
```

---

## 💡 最佳实践

### 1. 配置优先级

```text
优先级（从高到低）：
1. 命令行参数
2. 环境变量
3. 本地配置文件 (config/local.toml)
4. 环境特定配置 (config/prod.toml)
5. 默认配置 (config/default.toml)
```

```rust
use config::{Config, Environment, File};
use clap::Parser;
use serde::Deserialize;

#[derive(Parser)]
struct Cli {
    #[arg(short, long)]
    port: Option<u16>,
}

#[derive(Deserialize)]
struct AppConfig {
    port: u16,
    database_url: String,
}

fn load_config() -> AppConfig {
    let cli = Cli::parse();
    
    let mut builder = Config::builder()
        // 1. 默认配置
        .add_source(File::with_name("config/default"))
        // 2. 环境特定
        .add_source(File::with_name("config/prod").required(false))
        // 3. 环境变量
        .add_source(Environment::with_prefix("APP"));
    
    // 4. CLI 参数（最高优先级）
    if let Some(port) = cli.port {
        builder = builder.set_override("port", port).unwrap();
    }
    
    builder.build().unwrap().try_deserialize().unwrap()
}
```

### 2. 敏感信息管理

```rust
use std::env;

// ❌ 错误：硬编码敏感信息
const API_KEY: &str = "sk-1234567890";

// ✅ 正确：从环境变量读取
fn get_api_key() -> String {
    env::var("API_KEY").expect("API_KEY must be set")
}

// ✅ 更好：提供清晰的错误信息
fn get_api_key_with_help() -> String {
    env::var("API_KEY").unwrap_or_else(|_| {
        eprintln!("Error: API_KEY environment variable is not set");
        eprintln!("Please set it in your .env file or export it:");
        eprintln!("  export API_KEY=your-api-key");
        std::process::exit(1);
    })
}
```

### 3. 配置验证

```rust
use serde::Deserialize;
use thiserror::Error;

#[derive(Debug, Error)]
enum ConfigError {
    #[error("Invalid port: {0}")]
    InvalidPort(u16),
    
    #[error("Invalid database URL: {0}")]
    InvalidDatabaseUrl(String),
}

#[derive(Deserialize)]
struct AppConfig {
    port: u16,
    database_url: String,
}

impl AppConfig {
    fn validate(&self) -> Result<(), ConfigError> {
        // 验证端口
        if self.port < 1024 || self.port > 65535 {
            return Err(ConfigError::InvalidPort(self.port));
        }
        
        // 验证数据库 URL
        if !self.database_url.starts_with("postgres://") {
            return Err(ConfigError::InvalidDatabaseUrl(
                self.database_url.clone()
            ));
        }
        
        Ok(())
    }
}

fn load_config() -> Result<AppConfig, Box<dyn std::error::Error>> {
    let config: AppConfig = config::Config::builder()
        .add_source(config::File::with_name("config/default"))
        .build()?
        .try_deserialize()?;
    
    config.validate()?;
    
    Ok(config)
}
```

### 4. 分层配置结构

```rust
use serde::Deserialize;

#[derive(Deserialize)]
struct AppConfig {
    server: ServerConfig,
    database: DatabaseConfig,
    redis: RedisConfig,
    logging: LoggingConfig,
}

#[derive(Deserialize)]
struct ServerConfig {
    host: String,
    port: u16,
    workers: usize,
}

#[derive(Deserialize)]
struct DatabaseConfig {
    url: String,
    max_connections: u32,
    timeout_seconds: u64,
}

#[derive(Deserialize)]
struct RedisConfig {
    url: String,
    pool_size: usize,
}

#[derive(Deserialize)]
struct LoggingConfig {
    level: String,
    format: String,  // "json" or "text"
}
```

**config/default.toml**:

```toml
[server]
host = "0.0.0.0"
port = 3000
workers = 4

[database]
url = "postgres://localhost/mydb"
max_connections = 10
timeout_seconds = 30

[redis]
url = "redis://localhost:6379"
pool_size = 5

[logging]
level = "info"
format = "text"
```

---

## 📊 工具对比

| 工具 | 多源 | 类型安全 | 易用性 | 推荐场景 |
|------|------|---------|--------|---------|
| **config** | ✅✅ | ✅ | ⭐⭐⭐⭐ | 通用应用 |
| **figment** | ✅✅ | ✅✅ | ⭐⭐⭐⭐ | Rocket 框架 |
| **dotenvy** | ✅ | ❌ | ⭐⭐⭐⭐⭐ | 环境变量 |
| **envy** | ✅ | ✅ | ⭐⭐⭐⭐⭐ | 简单场景 |
| **clap** | ❌ | ✅ | ⭐⭐⭐⭐⭐ | CLI 工具 |

---

## 🎯 实战场景

### 场景1: Web 应用完整配置

```rust
// src/config.rs
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize, Clone)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub redis: RedisConfig,
}

#[derive(Debug, Deserialize, Clone)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
}

#[derive(Debug, Deserialize, Clone)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
}

#[derive(Debug, Deserialize, Clone)]
pub struct RedisConfig {
    pub url: String,
}

impl AppConfig {
    pub fn new() -> Result<Self, ConfigError> {
        let env = std::env::var("APP_ENV").unwrap_or_else(|_| "dev".into());
        
        let config = Config::builder()
            .add_source(File::with_name("config/default"))
            .add_source(File::with_name(&format!("config/{}", env)).required(false))
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?;
        
        config.try_deserialize()
    }
}

// src/main.rs
use crate::config::AppConfig;

#[tokio::main]
async fn main() {
    dotenvy::dotenv().ok();
    
    let config = AppConfig::new().expect("Failed to load config");
    
    println!("Starting server on {}:{}", config.server.host, config.server.port);
    
    // 使用配置启动服务...
}
```

---

## 🔗 相关资源

- [12-Factor App Config](https://12factor.net/config)
- [config-rs Documentation](https://docs.rs/config/)
- [dotenvy Documentation](https://docs.rs/dotenvy/)

---

**导航**: [返回横切关注点](../README.md) | [下一类别：国际化](../i18n/README.md)
