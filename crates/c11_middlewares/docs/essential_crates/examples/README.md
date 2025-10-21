# 实战代码示例

## 📋 目录

- [实战代码示例](#实战代码示例)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Web 应用示例](#web-应用示例)
    - [完整的 REST API](#完整的-rest-api)
  - [CLI 工具示例](#cli-工具示例)
    - [文件搜索工具](#文件搜索工具)
  - [异步任务示例](#异步任务示例)
    - [并发下载器](#并发下载器)
  - [数据处理示例](#数据处理示例)
    - [CSV 数据分析](#csv-数据分析)
  - [更多示例](#更多示例)
  - [运行示例](#运行示例)

---

## 概述

这里提供常见场景的完整可运行代码示例。

---

## Web 应用示例

### 完整的 REST API

```rust
// Cargo.toml
// [dependencies]
// axum = "0.7"
// tokio = { version = "1", features = ["full"] }
// serde = { version = "1", features = ["derive"] }
// sqlx = { version = "0.7", features = ["runtime-tokio-rustls", "postgres"] }

use axum::{
    Router,
    routing::{get, post},
    extract::{State, Path},
    Json,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use sqlx::{PgPool, FromRow};
use std::sync::Arc;

#[derive(Debug, Serialize, Deserialize, FromRow)]
struct User {
    id: i32,
    name: String,
    email: String,
}

#[derive(Debug, Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

struct AppState {
    pool: PgPool,
}

async fn list_users(
    State(state): State<Arc<AppState>>,
) -> Result<Json<Vec<User>>, StatusCode> {
    let users = sqlx::query_as!(User, "SELECT id, name, email FROM users")
        .fetch_all(&state.pool)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(users))
}

async fn create_user(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateUser>,
) -> Result<Json<User>, StatusCode> {
    let user = sqlx::query_as!(
        User,
        "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id, name, email",
        payload.name,
        payload.email
    )
    .fetch_one(&state.pool)
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(user))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let pool = PgPool::connect("postgresql://localhost/mydb").await?;
    
    let state = Arc::new(AppState { pool });
    
    let app = Router::new()
        .route("/users", get(list_users).post(create_user))
        .with_state(state);
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
```

---

## CLI 工具示例

### 文件搜索工具

```rust
// Cargo.toml
// [dependencies]
// clap = { version = "4", features = ["derive"] }
// walkdir = "2"
// regex = "1"

use clap::Parser;
use walkdir::WalkDir;
use regex::Regex;
use std::fs;

#[derive(Parser)]
#[command(name = "search")]
#[command(about = "搜索文件中的文本")]
struct Args {
    /// 搜索模式
    pattern: String,
    
    /// 搜索路径
    #[arg(default_value = ".")]
    path: String,
    
    /// 文件扩展名过滤
    #[arg(short, long)]
    ext: Option<String>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let re = Regex::new(&args.pattern)?;
    
    for entry in WalkDir::new(&args.path).into_iter().filter_map(|e| e.ok()) {
        if entry.file_type().is_file() {
            // 检查扩展名
            if let Some(ref ext) = args.ext {
                if !entry.path().extension()
                    .and_then(|s| s.to_str())
                    .map(|s| s == ext)
                    .unwrap_or(false)
                {
                    continue;
                }
            }
            
            // 搜索文件内容
            if let Ok(content) = fs::read_to_string(entry.path()) {
                for (line_no, line) in content.lines().enumerate() {
                    if re.is_match(line) {
                        println!(
                            "{}:{}:{}",
                            entry.path().display(),
                            line_no + 1,
                            line
                        );
                    }
                }
            }
        }
    }
    
    Ok(())
}
```

---

## 异步任务示例

### 并发下载器

```rust
// Cargo.toml
// [dependencies]
// tokio = { version = "1", features = ["full"] }
// reqwest = "0.11"

use tokio::fs::File;
use tokio::io::AsyncWriteExt;
use reqwest;

async fn download_file(url: &str, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let response = reqwest::get(url).await?;
    let bytes = response.bytes().await?;
    
    let mut file = File::create(path).await?;
    file.write_all(&bytes).await?;
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let urls = vec![
        ("https://example.com/file1.txt", "file1.txt"),
        ("https://example.com/file2.txt", "file2.txt"),
        ("https://example.com/file3.txt", "file3.txt"),
    ];
    
    let tasks: Vec<_> = urls
        .into_iter()
        .map(|(url, path)| {
            tokio::spawn(async move {
                match download_file(url, path).await {
                    Ok(_) => println!("下载完成: {}", path),
                    Err(e) => eprintln!("下载失败 {}: {}", path, e),
                }
            })
        })
        .collect();
    
    for task in tasks {
        task.await?;
    }
    
    Ok(())
}
```

---

## 数据处理示例

### CSV 数据分析

```rust
// Cargo.toml
// [dependencies]
// polars = "0.36"
// anyhow = "1.0"

use polars::prelude::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 读取 CSV
    let df = CsvReader::from_path("data.csv")?
        .has_header(true)
        .finish()?;
    
    println!("原始数据:\n{:?}\n", df.head(Some(5)));
    
    // 数据清洗和转换
    let df = df
        .lazy()
        .filter(col("age").gt(lit(18)))
        .select([
            col("name"),
            col("age"),
            col("salary"),
        ])
        .sort("salary", SortOptions::default())
        .collect()?;
    
    println!("过滤后:\n{:?}\n", df);
    
    // 统计信息
    let stats = df
        .lazy()
        .select([
            col("age").mean().alias("avg_age"),
            col("salary").sum().alias("total_salary"),
            col("salary").max().alias("max_salary"),
        ])
        .collect()?;
    
    println!("统计:\n{:?}", stats);
    
    Ok(())
}
```

---

## 更多示例

查看各层目录中的详细示例：

- `01_infrastructure/` - 基础设施示例
- `02_system_programming/` - 系统编程示例
- `03_application_dev/` - 应用开发示例
- `04_domain_specific/` - 领域特定示例

---

## 运行示例

```bash
# 创建新项目
cargo new my-example
cd my-example

# 添加依赖（根据示例需要）
cargo add axum tokio serde

# 复制示例代码到 src/main.rs

# 运行
cargo run
```
