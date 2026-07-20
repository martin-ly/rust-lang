# 知识图谱

本页展示常用库的概念关系。

---

## 📊 核心概念关系图

```text
                    [Rust常用库]
                         |
         +---------------+---------------+---------------+
         |               |               |               |
     [核心库]       [Web开发]      [数据处理]     [系统工具]
         |               |               |               |
    +----+----+     +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |     |    |    |
  serde tokio  axum   sqlx  diesel  clap  log  tracing
  anyhow  reqwest actix  redis  csv  regex  env  config
```

---

## 🎯 概念层次

### 1. 核心库 (Core Libraries)

**序列化/反序列化**:

- **serde**: 序列化框架
- **serde_json**: JSON支持
- **bincode**: 二进制序列化
- **toml**: TOML配置文件
- **yaml-rust**: YAML支持

**错误处理**:

- **anyhow**: 简化错误处理
- **thiserror**: 自定义错误类型
- **eyre**: 增强型错误报告

**异步运行时**:

- **tokio**: 异步运行时
- **async-std**: 异步标准库
- **smol**: 轻量异步运行时
- **futures**: Future组合子

---

### 2. Web开发 (Web Development)

**Web框架**:

- **axum**: 现代web框架
- **actix-web**: 高性能框架
- **rocket**: 易用框架
- **warp**: 过滤器框架

**HTTP客户端**:

- **reqwest**: HTTP客户端
- **ureq**: 同步HTTP
- **surf**: 异步HTTP

**模板引擎**:

- **askama**: 编译时模板
- **tera**: 动态模板
- **handlebars**: Handlebars模板

**数据库**:

- **sqlx**: 异步SQL
- **diesel**: ORM框架
- **sea-orm**: 现代ORM
- **redis**: Redis客户端

---

### 3. 数据处理 (Data Processing)

**解析**:

- **nom**: 解析器组合子
- **pest**: PEG解析器
- **regex**: 正则表达式
- **csv**: CSV处理

**数据结构**:

- **indexmap**: 保序HashMap
- **smallvec**: 栈优化Vec
- **dashmap**: 并发HashMap
- **petgraph**: 图数据结构

**时间处理**:

- **chrono**: 时间日期
- **time**: 现代时间库
- **humantime**: 人性化时间

---

### 4. 系统工具 (System Utilities)

**CLI工具**:

- **clap**: 命令行解析
- **structopt**: 结构化CLI
- **dialoguer**: 交互式CLI
- **indicatif**: 进度条

**日志**:

- **log**: 日志门面
- **env_logger**: 环境日志
- **tracing**: 结构化追踪
- **slog**: 结构化日志

**配置管理**:

- **config**: 配置框架
- **dotenv**: 环境变量
- **figment**: 配置聚合

**文件操作**:

- **walkdir**: 目录遍历
- **notify**: 文件监控
- **tempfile**: 临时文件
- **fs_extra**: 扩展文件操作

---

## 🔗 概念关联

### serde ←→ 数据序列化

```rust
use serde::{Serialize, Deserialize};

// 定义可序列化结构
#[derive(Serialize, Deserialize, Debug)]
struct User {
    id: u64,
    name: String,
    email: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    age: Option<u32>,
}

fn main() {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: Some(30),
    };
    
    // 序列化为JSON
    let json = serde_json::to_string(&user).unwrap();
    println!("JSON: {}", json);
    
    // 反序列化
    let user2: User = serde_json::from_str(&json).unwrap();
    println!("User: {:?}", user2);
}
```

### tokio ←→ 异步生态

```rust
use tokio::time::{sleep, Duration};
use tokio::task;

#[tokio::main]
async fn main() {
    // 并发执行多个任务
    let task1 = task::spawn(async {
        sleep(Duration::from_millis(100)).await;
        "Task 1 done"
    });
    
    let task2 = task::spawn(async {
        sleep(Duration::from_millis(200)).await;
        "Task 2 done"
    });
    
    // 等待所有任务完成
    let result1 = task1.await.unwrap();
    let result2 = task2.await.unwrap();
    
    println!("{}, {}", result1, result2);
}
```

### axum ←→ Web服务

```rust
use axum::{
    routing::get,
    Router,
    Json,
};
use serde::{Deserialize, Serialize};
use tower_http::cors::CorsLayer;

#[derive(Serialize)]
struct Response {
    message: String,
}

async fn hello() -> Json<Response> {
    Json(Response {
        message: "Hello, World!".to_string(),
    })
}

#[tokio::main]
async fn main() {
    // 构建应用
    let app = Router::new()
        .route("/", get(hello))
        .layer(CorsLayer::permissive());
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}
```

---

## 📚 学习路径图

```text
第一步: 掌握核心库(serde, anyhow)
    ↓
第二步: 学习异步运行时(tokio)
    ↓
第三步: 使用Web框架(axum)
    ↓
第四步: 集成数据库(sqlx, diesel)
    ↓
第五步: 构建完整应用
```

---

## 🎓 库分类与选择

### 按用途选择

| 用途 | 推荐库 | 特点 |
|------|--------|------|
| **序列化** | serde | 零成本抽象 |
| **异步** | tokio | 生态最完整 |
| **Web** | axum | 现代化设计 |
| **数据库** | sqlx | 编译时检查 |
| **CLI** | clap | 功能强大 |
| **日志** | tracing | 结构化追踪 |

### 按性能选择

| 性能需求 | 库选择 | 说明 |
|----------|--------|------|
| **最高** | actix-web, smallvec | 极致性能 |
| **平衡** | axum, reqwest | 性能与易用性 |
| **易用** | rocket, ureq | 开发效率优先 |

---

## 💡 核心原则

### 1. 零成本抽象

```text
serde → 编译时生成 → 无运行时开销
```

### 2. 类型安全

```text
强类型 → 编译时检查 → 运行时安全
```

### 3. 组合优于继承

```text
trait → 行为组合 → 灵活扩展
```

---

## 🔍 Rust 1.90 特性应用

### 1. 异步trait

```rust
use async_trait::async_trait;

#[async_trait]
trait DataRepository {
    async fn find(&self, id: i64) -> Result<Data, Error>;
    async fn save(&self, data: Data) -> Result<(), Error>;
}

struct PostgresRepo;

#[async_trait]
impl DataRepository for PostgresRepo {
    async fn find(&self, id: i64) -> Result<Data, Error> {
        // 使用sqlx查询数据库
        sqlx::query_as("SELECT * FROM data WHERE id = $1")
            .bind(id)
            .fetch_one(&pool)
            .await
    }
    
    async fn save(&self, data: Data) -> Result<(), Error> {
        sqlx::query("INSERT INTO data VALUES ($1, $2)")
            .bind(data.id)
            .bind(data.value)
            .execute(&pool)
            .await?;
        Ok(())
    }
}
```

### 2. 错误处理改进

```rust
use anyhow::{Context, Result};

async fn process_file(path: &str) -> Result<String> {
    let content = tokio::fs::read_to_string(path)
        .await
        .context("Failed to read file")?;
    
    let parsed = serde_json::from_str(&content)
        .context("Failed to parse JSON")?;
    
    Ok(parsed)
}
```

### 3. 高级配置管理

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Deserialize)]
struct Settings {
    database_url: String,
    server_port: u16,
    log_level: String,
}

fn load_config() -> Result<Settings, ConfigError> {
    Config::builder()
        // 加载默认配置
        .add_source(File::with_name("config/default"))
        // 加载环境特定配置
        .add_source(File::with_name("config/production").required(false))
        // 环境变量覆盖
        .add_source(Environment::with_prefix("APP"))
        .build()?
        .try_deserialize()
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 库生态概览
- **[实践指南](./guides.md)** - 使用指南
- **[代码示例](./examples.md)** - 实战案例 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [Rust库生态全景](../../crates/c11_libraries/README.md)
- [Awesome Rust](https://github.com/rust-unofficial/awesome-rust)
- [crates.io](https://crates.io/)

### 相关模块

- **[C10: 网络编程](../c10/README.md)** - 网络库应用
- **[C06: 异步编程](../c06/README.md)** - tokio详解
- **[C02: 类型系统](../c02/README.md)** - serde原理

---

## 🎯 实践建议

### 库选择决策树

```text
需要序列化？
└─ serde + serde_json/bincode/toml

需要异步？
└─ tokio（完整生态）或 async-std（简洁）

需要Web服务？
├─ 性能优先 → actix-web
├─ 现代化 → axum
└─ 易用性 → rocket

需要数据库？
├─ 编译时安全 → sqlx
└─ ORM → diesel, sea-orm

需要CLI？
└─ clap（功能丰富）或 structopt（简洁）
```

### 库组合最佳实践

```rust
// 典型Web应用技术栈
use axum::{Router, routing::get};     // Web框架
use sqlx::PgPool;                      // 数据库
use serde::{Deserialize, Serialize};  // 序列化
use tracing::{info, instrument};       // 日志追踪
use anyhow::Result;                    // 错误处理
use tokio::runtime::Runtime;           // 异步运行时

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化追踪
    tracing_subscriber::fmt::init();
    
    // 连接数据库
    let pool = PgPool::connect(&env::var("DATABASE_URL")?).await?;
    
    // 构建应用
    let app = Router::new()
        .route("/", get(handler))
        .with_state(pool);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("Server started on port 3000");
    
    axum::serve(listener, app).await?;
    Ok(())
}
```

---

**掌握常用库是高效Rust开发的关键！** 🚀
