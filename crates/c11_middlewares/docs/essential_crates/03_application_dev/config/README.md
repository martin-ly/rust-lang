# 配置管理 - Rust 应用配置解决方案

> **核心库**: config, figment, dotenvy, envy  
> **适用场景**: 配置文件加载、环境变量管理、多环境配置、配置验证

---

## 📋 目录

- [配置管理 - Rust 应用配置解决方案](#配置管理---rust-应用配置解决方案)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
    - [配置来源](#配置来源)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [config - 多格式配置加载器](#config---多格式配置加载器)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [安装](#安装)
      - [快速开始](#快速开始)
    - [高级特性](#高级特性)
      - [1. 环境特定配置](#1-环境特定配置)
      - [2. 配置验证](#2-配置验证)
      - [3. 动态配置访问](#3-动态配置访问)
  - [figment - 类型安全配置](#figment---类型安全配置)
    - [核心特性1](#核心特性1)
    - [基础用法1](#基础用法1)
      - [安装1](#安装1)
      - [快速开始1](#快速开始1)
    - [配置提供者](#配置提供者)
      - [1. 自定义Provider](#1-自定义provider)
      - [2. 配置Profile](#2-配置profile)
  - [dotenvy - .env 文件管理](#dotenvy---env-文件管理)
    - [核心特性2](#核心特性2)
    - [基础用法2](#基础用法2)
      - [安装2](#安装2)
      - [快速开始2](#快速开始2)
    - [多环境支持](#多环境支持)
      - [1. 环境特定文件](#1-环境特定文件)
      - [2. 从特定路径加载](#2-从特定路径加载)
      - [3. 自定义迭代器](#3-自定义迭代器)
  - [使用场景](#使用场景)
    - [场景1: Web 应用配置](#场景1-web-应用配置)
    - [场景2: 微服务配置中心](#场景2-微服务配置中心)
    - [场景3: CLI 工具配置](#场景3-cli-工具配置)
  - [配置优先级策略](#配置优先级策略)
    - [标准优先级顺序](#标准优先级顺序)
    - [实现示例](#实现示例)
  - [最佳实践](#最佳实践)
    - [1. 敏感信息管理](#1-敏感信息管理)
    - [2. 配置验证2](#2-配置验证2)
    - [3. 配置文件分层](#3-配置文件分层)
    - [4. 结构化配置类型](#4-结构化配置类型)
    - [5. 配置重载支持](#5-配置重载支持)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 环境变量类型转换失败](#️-陷阱1-环境变量类型转换失败)
    - [⚠️ 陷阱2: 配置文件路径问题](#️-陷阱2-配置文件路径问题)
    - [⚠️ 陷阱3: 环境变量覆盖规则不清晰](#️-陷阱3-环境变量覆盖规则不清晰)
    - [⚠️ 陷阱4: 忘记处理配置文件不存在](#️-陷阱4-忘记处理配置文件不存在)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

配置管理是 Rust 应用开发中的关键环节，良好的配置管理能够：

- **环境分离**: 开发、测试、生产环境配置隔离
- **灵活部署**: 无需重新编译即可调整应用行为
- **安全管理**: 敏感信息通过环境变量注入
- **配置验证**: 启动时验证配置完整性和正确性

### 核心概念

```text
配置层次结构：

默认值 (Defaults)
    ↓
配置文件 (config.toml/json/yaml)
    ↓
环境变量 (APP_DATABASE_URL)
    ↓
命令行参数 (--port 8080)
    ↓
最终配置 (Merged Config)

优先级：命令行 > 环境变量 > 配置文件 > 默认值
```

### 配置来源

| 来源 | 优点 | 缺点 | 适用场景 |
|------|------|------|----------|
| **配置文件** | 结构化、易维护 | 需要文件管理 | 复杂配置 |
| **环境变量** | 安全、CI/CD友好 | 类型转换复杂 | 敏感信息 |
| **命令行参数** | 临时覆盖 | 不适合复杂配置 | 调试、快速调整 |
| **默认值** | 代码内置 | 不够灵活 | 合理默认 |

---

## 核心库对比

### 功能矩阵

| 特性 | config | figment | dotenvy | envy |
|------|--------|---------|---------|------|
| **TOML支持** | ✅ | ✅ | ❌ | ✅ |
| **JSON支持** | ✅ | ✅ | ❌ | ✅ |
| **YAML支持** | ✅ | ✅ | ❌ | ✅ |
| **.env支持** | ✅ | ✅ | ✅ | ✅ |
| **配置合并** | ✅ | ✅ | ❌ | ❌ |
| **类型安全** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ |
| **错误提示** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| **性能** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **学习曲线** | 简单 | 中等 | 非常简单 | 简单 |

### 选择指南

| 场景 | 推荐库 | 理由 |
|------|--------|------|
| **复杂多源配置** | config | 支持多种格式和配置合并 |
| **类型安全优先** | figment | Rocket框架同款，错误提示优秀 |
| **简单.env管理** | dotenvy | 轻量、专注.env文件 |
| **环境变量→结构体** | envy | 直接反序列化环境变量 |
| **Rocket应用** | figment | 与Rocket深度集成 |

---

## config - 多格式配置加载器

### 核心特性

- ✅ **多格式支持**: TOML, JSON, YAML, INI, RON, JSON5
- ✅ **配置合并**: 多个来源的配置自动合并
- ✅ **环境覆盖**: 环境变量自动覆盖配置文件
- ✅ **嵌套结构**: 支持复杂嵌套配置
- ✅ **热重载**: 配置文件变化检测（可选）

### 基础用法

#### 安装

```toml
[dependencies]
config = "0.14"
serde = { version = "1.0", features = ["derive"] }
```

#### 快速开始

```rust
use config::{Config, File, Environment};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Database {
    host: String,
    port: u16,
    name: String,
}

#[derive(Debug, Deserialize)]
struct Settings {
    debug: bool,
    database: Database,
    api_key: String,
}

fn main() -> Result<(), config::ConfigError> {
    let settings = Config::builder()
        // 添加默认值
        .set_default("debug", false)?
        .set_default("database.port", 5432)?
        // 添加配置文件（支持多种格式）
        .add_source(File::with_name("config/default"))
        .add_source(File::with_name("config/production").required(false))
        // 添加环境变量（前缀 APP_）
        .add_source(Environment::with_prefix("APP").separator("__"))
        .build()?;

    let app_settings: Settings = settings.try_deserialize()?;
    println!("{:#?}", app_settings);
    
    Ok(())
}
```

**说明**:

- `config/default.toml` 作为基础配置
- `config/production.toml` 覆盖生产环境配置（可选）
- 环境变量 `APP_DATABASE__HOST` 会覆盖 `database.host`

### 高级特性

#### 1. 环境特定配置

```rust
use config::{Config, File, Environment as Env};

fn load_config() -> Result<Config, config::ConfigError> {
    let run_mode = std::env::var("RUN_MODE").unwrap_or_else(|_| "development".into());

    Config::builder()
        .add_source(File::with_name("config/default"))
        .add_source(File::with_name(&format!("config/{}", run_mode)).required(false))
        .add_source(File::with_name("config/local").required(false)) // Git忽略的本地覆盖
        .add_source(Env::with_prefix("APP"))
        .build()
}
```

#### 2. 配置验证

```rust
use serde::Deserialize;
use validator::Validate;

#[derive(Debug, Deserialize, Validate)]
struct Settings {
    #[validate(range(min = 1024, max = 65535))]
    port: u16,
    
    #[validate(url)]
    database_url: String,
    
    #[validate(email)]
    admin_email: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = load_config()?;
    let settings: Settings = config.try_deserialize()?;
    
    // 验证配置
    settings.validate()?;
    
    Ok(())
}
```

#### 3. 动态配置访问

```rust
// 不使用强类型结构体，动态访问
let config = Config::builder()
    .add_source(File::with_name("config"))
    .build()?;

let port: u16 = config.get("server.port")?;
let timeout: u64 = config.get("server.timeout").unwrap_or(30);
```

---

## figment - 类型安全配置

### 核心特性1

- ✅ **类型安全**: 编译时类型检查，优秀的错误提示
- ✅ **配置提供者**: 灵活的Provider系统
- ✅ **配置合并**: 强大的配置合并策略
- ✅ **配置文件**: 支持 TOML, JSON, 环境变量
- ✅ **Rocket集成**: Rocket web框架官方配置库

### 基础用法1

#### 安装1

```toml
[dependencies]
figment = { version = "0.10", features = ["toml", "json", "env"] }
serde = { version = "1.0", features = ["derive"] }
```

#### 快速开始1

```rust
use figment::{Figment, providers::{Format, Toml, Json, Env}};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
struct Config {
    name: String,
    port: u16,
    workers: usize,
}

fn main() -> Result<(), figment::Error> {
    let config: Config = Figment::new()
        .merge(Toml::file("Config.toml"))
        .merge(Json::file("config.json"))
        .merge(Env::prefixed("APP_"))
        .extract()?;

    println!("{:#?}", config);
    Ok(())
}
```

### 配置提供者

#### 1. 自定义Provider

```rust
use figment::{Provider, Metadata, Profile};
use figment::value::{Map, Value};

struct DatabaseProvider {
    url: String,
    max_connections: u32,
}

impl Provider for DatabaseProvider {
    fn metadata(&self) -> Metadata {
        Metadata::named("Database Provider")
    }

    fn data(&self) -> Result<Map<Profile, Map<String, Value>>, figment::Error> {
        let mut map = Map::new();
        map.insert("database_url".into(), self.url.clone().into());
        map.insert("max_connections".into(), self.max_connections.into());
        
        Ok(Map::from([(Profile::Default, map)]))
    }
}

// 使用
let config: Config = Figment::new()
    .merge(DatabaseProvider {
        url: "postgres://localhost/mydb".into(),
        max_connections: 10,
    })
    .extract()?;
```

#### 2. 配置Profile

```rust
use figment::Profile;

// 多环境配置
let config: Config = Figment::new()
    .merge(Toml::file("Config.toml"))
    .merge(Toml::file("Config.toml").nested()) // 嵌套profile
    .select(Profile::from_env_or("APP_PROFILE", "default"))
    .extract()?;
```

**Config.toml**:

```toml
port = 8000

[debug]
port = 8001
log_level = "debug"

[release]
port = 80
log_level = "info"
```

---

## dotenvy - .env 文件管理

### 核心特性2

- ✅ **简单易用**: API简洁，专注.env文件
- ✅ **零依赖**: 轻量级实现
- ✅ **多文件支持**: .env, .env.local, .env.production等
- ✅ **安全**: 不会覆盖已有环境变量
- ✅ **跨平台**: Windows/Linux/macOS一致行为

### 基础用法2

#### 安装2

```toml
[dependencies]
dotenvy = "0.15"
```

#### 快速开始2

```rust
use dotenvy::dotenv;
use std::env;

fn main() {
    // 加载.env文件
    dotenv().ok();

    let database_url = env::var("DATABASE_URL").expect("DATABASE_URL must be set");
    let port: u16 = env::var("PORT")
        .unwrap_or_else(|_| "8080".to_string())
        .parse()
        .expect("PORT must be a number");

    println!("Database: {}", database_url);
    println!("Port: {}", port);
}
```

**.env**:

```bash
DATABASE_URL=postgres://localhost/myapp
PORT=3000
SECRET_KEY=super-secret-key
LOG_LEVEL=debug
```

### 多环境支持

#### 1. 环境特定文件

```rust
use dotenvy::from_filename;

fn main() {
    let env = std::env::var("RUST_ENV").unwrap_or_else(|_| "development".into());
    
    // 优先级：.env.{环境}.local > .env.{环境} > .env.local > .env
    from_filename(&format!(".env.{}.local", env)).ok();
    from_filename(&format!(".env.{}", env)).ok();
    from_filename(".env.local").ok();
    from_filename(".env").ok();

    // 使用环境变量
    let api_key = std::env::var("API_KEY").expect("API_KEY required");
}
```

#### 2. 从特定路径加载

```rust
use dotenvy::from_path;
use std::path::Path;

fn main() {
    // 从指定路径加载
    from_path("/etc/myapp/.env").ok();
    
    // 或从项目根目录
    let mut path = std::env::current_dir().unwrap();
    path.push(".env");
    from_path(path).ok();
}
```

#### 3. 自定义迭代器

```rust
use dotenvy::EnvLoader;

fn main() {
    let loader = EnvLoader::new()
        .sequence_items(".env")
        .sequence_items(".env.local");
    
    for (key, value) in loader.load().unwrap() {
        println!("{} = {}", key, value);
    }
}
```

---

## 使用场景

### 场景1: Web 应用配置

**需求描述**: REST API 需要配置数据库、Redis、日志等多个服务

**推荐方案**:

```rust
use config::{Config, File, Environment};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct AppConfig {
    server: ServerConfig,
    database: DatabaseConfig,
    redis: RedisConfig,
    logging: LogConfig,
}

#[derive(Debug, Deserialize)]
struct ServerConfig {
    host: String,
    port: u16,
    workers: usize,
}

#[derive(Debug, Deserialize)]
struct DatabaseConfig {
    url: String,
    max_connections: u32,
    timeout_seconds: u64,
}

#[derive(Debug, Deserialize)]
struct RedisConfig {
    url: String,
    pool_size: u32,
}

#[derive(Debug, Deserialize)]
struct LogConfig {
    level: String,
    format: String,
}

fn load_config() -> Result<AppConfig, config::ConfigError> {
    let run_mode = std::env::var("RUN_MODE").unwrap_or_else(|_| "development".into());

    let config = Config::builder()
        .add_source(File::with_name("config/default"))
        .add_source(File::with_name(&format!("config/{}", run_mode)).required(false))
        .add_source(Environment::with_prefix("APP").separator("__"))
        .build()?;

    config.try_deserialize()
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = load_config()?;
    
    // 使用配置启动服务器
    let addr = format!("{}:{}", config.server.host, config.server.port);
    println!("Starting server on {}", addr);
    
    Ok(())
}
```

**要点说明**:

- 结构化配置，类型安全
- 支持多环境切换
- 环境变量可覆盖任意配置项

### 场景2: 微服务配置中心

**需求描述**: 微服务需要从配置中心动态获取配置

**推荐方案**:

```rust
use figment::{Figment, Provider};
use reqwest;

// 自定义配置中心Provider
struct ConfigCenterProvider {
    url: String,
    service_name: String,
}

impl Provider for ConfigCenterProvider {
    fn metadata(&self) -> figment::Metadata {
        figment::Metadata::named("Config Center")
    }

    fn data(&self) -> Result<figment::value::Map<figment::Profile, figment::value::Map<String, figment::value::Value>>, figment::Error> {
        // 从配置中心获取配置
        let config_json = reqwest::blocking::get(&format!("{}/config/{}", self.url, self.service_name))
            .map_err(|e| figment::Error::from(e.to_string()))?
            .text()
            .map_err(|e| figment::Error::from(e.to_string()))?;
        
        // 解析并返回配置
        let value: figment::value::Value = serde_json::from_str(&config_json)
            .map_err(|e| figment::Error::from(e.to_string()))?;
        
        Ok(figment::value::Map::from([(figment::Profile::Default, value.into_dict().unwrap())]))
    }
}

fn main() -> Result<(), figment::Error> {
    let config: ServiceConfig = Figment::new()
        // 本地默认配置
        .merge(figment::providers::Toml::file("config.toml"))
        // 配置中心配置（优先级更高）
        .merge(ConfigCenterProvider {
            url: "http://config-center:8080".into(),
            service_name: "my-service".into(),
        })
        // 环境变量最高优先级
        .merge(figment::providers::Env::prefixed("SERVICE_"))
        .extract()?;

    Ok(())
}
```

### 场景3: CLI 工具配置

**需求描述**: 命令行工具需要支持配置文件和命令行参数

**推荐方案**:

```rust
use clap::Parser;
use dotenvy::dotenv;
use serde::Deserialize;
use std::env;

#[derive(Parser, Debug)]
#[command(name = "mytool")]
#[command(about = "A CLI tool with configuration", long_about = None)]
struct Args {
    /// Server host
    #[arg(long, env = "HOST")]
    host: Option<String>,
    
    /// Server port
    #[arg(short, long, env = "PORT")]
    port: Option<u16>,
    
    /// Config file path
    #[arg(short, long, value_name = "FILE")]
    config: Option<String>,
}

#[derive(Debug, Deserialize)]
struct Config {
    host: String,
    port: u16,
    api_key: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 加载.env文件
    dotenv().ok();
    
    // 2. 解析命令行参数
    let args = Args::parse();
    
    // 3. 加载配置文件（如果指定）
    let file_config = if let Some(config_path) = args.config {
        let content = std::fs::read_to_string(config_path)?;
        Some(toml::from_str::<Config>(&content)?)
    } else {
        None
    };
    
    // 4. 合并配置（优先级：命令行 > 环境变量 > 配置文件）
    let host = args.host
        .or_else(|| file_config.as_ref().map(|c| c.host.clone()))
        .unwrap_or_else(|| "localhost".to_string());
    
    let port = args.port
        .or_else(|| file_config.as_ref().map(|c| c.port))
        .unwrap_or(8080);
    
    println!("Running on {}:{}", host, port);
    
    Ok(())
}
```

---

## 配置优先级策略

### 标准优先级顺序

```text
1. 命令行参数 (最高优先级)
   └─ 临时覆盖，适合调试
   
2. 环境变量
   └─ 部署环境特定，CI/CD友好
   
3. 环境特定配置文件 (config.production.toml)
   └─ 生产/测试环境差异
   
4. 本地配置文件 (config.local.toml, git忽略)
   └─ 开发者个人配置
   
5. 基础配置文件 (config.toml)
   └─ 项目默认配置
   
6. 代码默认值 (最低优先级)
   └─ 合理默认值
```

### 实现示例

```rust
use config::{Config, File, Environment};

fn build_config() -> Result<Config, config::ConfigError> {
    let run_mode = std::env::var("RUN_MODE").unwrap_or_else(|_| "development".into());

    Config::builder()
        // 1. 代码默认值
        .set_default("server.host", "127.0.0.1")?
        .set_default("server.port", 8080)?
        .set_default("server.workers", 4)?
        
        // 2. 基础配置文件
        .add_source(File::with_name("config/default").required(false))
        
        // 3. 本地配置（git忽略）
        .add_source(File::with_name("config/local").required(false))
        
        // 4. 环境特定配置
        .add_source(
            File::with_name(&format!("config/{}", run_mode))
                .required(false)
        )
        
        // 5. 环境变量
        .add_source(
            Environment::with_prefix("APP")
                .separator("__")
                .try_parsing(true)
        )
        
        // 6. 命令行参数（通过环境变量注入）
        .build()
}
```

---

## 最佳实践

### 1. 敏感信息管理

**描述**: 永远不要将敏感信息提交到版本控制

✅ **正确做法**:

```rust
// config/default.toml (提交到git)
[database]
host = "localhost"
port = 5432
# 不包含密码！

// .env (git忽略)
DATABASE_URL=postgres://user:password@localhost/mydb
SECRET_KEY=super-secret-key-12345
```

❌ **避免**:

```toml
# config.toml - 不要这样做！
[database]
password = "mypassword123"  # 不要提交密码
```

### 2. 配置验证2

**描述**: 启动时验证配置的完整性

```rust
use serde::Deserialize;
use validator::{Validate, ValidationError};

#[derive(Debug, Deserialize, Validate)]
struct Config {
    #[validate(range(min = 1024, max = 65535))]
    port: u16,
    
    #[validate(url)]
    database_url: String,
    
    #[validate(custom = "validate_log_level")]
    log_level: String,
}

fn validate_log_level(level: &str) -> Result<(), ValidationError> {
    match level {
        "trace" | "debug" | "info" | "warn" | "error" => Ok(()),
        _ => Err(ValidationError::new("invalid_log_level")),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config: Config = load_config()?;
    
    // 验证配置
    config.validate()
        .map_err(|e| format!("Config validation failed: {}", e))?;
    
    Ok(())
}
```

### 3. 配置文件分层

```text
config/
├── default.toml          # 基础配置（提交）
├── development.toml      # 开发环境（提交）
├── test.toml             # 测试环境（提交）
├── production.toml       # 生产环境（提交）
└── local.toml            # 本地覆盖（git忽略）
```

### 4. 结构化配置类型

```rust
// 好的做法：结构化配置
#[derive(Debug, Deserialize)]
struct Config {
    server: ServerConfig,
    database: DatabaseConfig,
    cache: CacheConfig,
}

// 避免：扁平化所有配置
#[derive(Debug, Deserialize)]
struct Config {
    server_host: String,
    server_port: u16,
    database_host: String,
    database_port: u16,
    // ... 难以维护
}
```

### 5. 配置重载支持

```rust
use std::sync::{Arc, RwLock};
use notify::{Watcher, RecursiveMode, watcher};
use std::time::Duration;

struct ConfigManager {
    config: Arc<RwLock<Config>>,
}

impl ConfigManager {
    fn new() -> Self {
        let config = load_config().unwrap();
        Self {
            config: Arc::new(RwLock::new(config)),
        }
    }
    
    fn watch(&self) {
        let config = Arc::clone(&self.config);
        let (tx, rx) = std::sync::mpsc::channel();
        let mut watcher = watcher(tx, Duration::from_secs(2)).unwrap();
        
        watcher.watch("config/", RecursiveMode::Recursive).unwrap();
        
        std::thread::spawn(move || {
            loop {
                match rx.recv() {
                    Ok(_event) => {
                        if let Ok(new_config) = load_config() {
                            *config.write().unwrap() = new_config;
                            println!("Config reloaded");
                        }
                    }
                    Err(e) => println!("Watch error: {:?}", e),
                }
            }
        });
    }
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: 环境变量类型转换失败

**问题描述**: 环境变量都是字符串，自动转换可能失败

❌ **错误示例**:

```bash
# .env
PORT=8080abc  # 包含非数字字符
```

```rust
let port: u16 = env::var("PORT").unwrap().parse().unwrap();  // 崩溃！
```

✅ **正确做法**:

```rust
let port: u16 = env::var("PORT")
    .unwrap_or_else(|_| "8080".to_string())
    .parse()
    .unwrap_or(8080);  // 提供默认值

// 或使用 Result
let port: u16 = env::var("PORT")?
    .parse()
    .map_err(|_| "PORT must be a valid number")?;
```

### ⚠️ 陷阱2: 配置文件路径问题

**问题描述**: 相对路径在不同工作目录下失效

❌ **错误示例**:

```rust
let config = Config::builder()
    .add_source(File::with_name("config/default"))  // 相对路径
    .build()?;
```

✅ **正确做法**:

```rust
use std::path::PathBuf;

fn get_config_path() -> PathBuf {
    // 使用可执行文件目录
    let mut path = std::env::current_exe().unwrap();
    path.pop();
    path.push("config");
    path
}

let config_dir = get_config_path();
let config = Config::builder()
    .add_source(File::from(config_dir.join("default")))
    .build()?;
```

### ⚠️ 陷阱3: 环境变量覆盖规则不清晰

**问题描述**: 嵌套配置的环境变量命名

❌ **错误示例**:

```rust
// 配置文件
database:
  host: localhost
  port: 5432

// 环境变量 - 错误命名
DATABASE_HOST=postgres  // 不会覆盖 database.host
```

✅ **正确做法**:

```rust
// 使用正确的分隔符
let config = Config::builder()
    .add_source(Environment::with_prefix("APP").separator("__"))
    .build()?;

// 环境变量
APP_DATABASE__HOST=postgres  // 正确！会覆盖 database.host
APP_DATABASE__PORT=5433      // 正确！会覆盖 database.port
```

### ⚠️ 陷阱4: 忘记处理配置文件不存在

❌ **错误示例**:

```rust
let config = Config::builder()
    .add_source(File::with_name("config"))  // 文件不存在会崩溃
    .build()?;
```

✅ **正确做法**:

```rust
let config = Config::builder()
    .add_source(File::with_name("config").required(false))  // 文件可选
    .build()?;

// 或明确处理
let config = Config::builder()
    .add_source(
        File::with_name("config/production")
            .format(config::FileFormat::Toml)
            .required(true)  // 生产环境必须存在
    )
    .build()?;
```

---

## 参考资源

### 官方文档

- 📚 [config文档](https://docs.rs/config/)
- 📚 [figment文档](https://docs.rs/figment/)
- 📚 [dotenvy文档](https://docs.rs/dotenvy/)
- 📚 [envy文档](https://docs.rs/envy/)

### 教程与文章

- 📖 [Rust配置管理最佳实践](https://www.shuttle.rs/blog/2024/01/09/getting-started-config-management)
- 📖 [12-Factor App配置原则](https://12factor.net/config)
- 📖 [Figment使用指南](https://rocket.rs/v0.5/guide/configuration/)

### 示例项目

- 💻 [Rocket Web Framework](https://github.com/SergioBenitez/Rocket) - figment使用示例
- 💻 [actix-web-config-example](https://github.com/actix/examples/tree/master/basics/todo) - config使用示例
- 💻 [CLI工具配置示例](https://github.com/rust-cli/config-file-examples)

### 相关文档

- 🔗 [环境变量管理](../../cross_cutting/configuration/README.md)
- 🔗 [CLI工具开发](../cli_tools/README.md)
- 🔗 [Web框架](../web_frameworks/README.md)
- 🔗 [安全最佳实践](../../cross_cutting/security/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区  
**文档长度**: 280+ 行
