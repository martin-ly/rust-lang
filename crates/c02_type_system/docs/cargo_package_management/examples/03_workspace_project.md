# 实战示例：完整工作空间项目

## 📊 目录

- [实战示例：完整工作空间项目](#实战示例完整工作空间项目)
  - [📊 目录](#-目录)
  - [📋 项目概述](#-项目概述)
  - [📁 项目结构](#-项目结构)
  - [📝 完整代码](#-完整代码)
    - [Cargo.toml (工作空间根)](#cargotoml-工作空间根)
    - [crates/core/Cargo.toml](#cratescorecargotoml)
    - [crates/core/src/lib.rs](#cratescoresrclibrs)
    - [crates/utils/Cargo.toml](#cratesutilscargotoml)
    - [crates/utils/src/lib.rs](#cratesutilssrclibrs)
    - [crates/api/Cargo.toml](#cratesapicargotoml)
    - [crates/api/src/lib.rs](#cratesapisrclibrs)
    - [crates/cli/Cargo.toml](#cratesclicargotoml)
    - [crates/cli/src/main.rs](#cratesclisrcmainrs)
  - [🚀 构建和运行](#-构建和运行)
    - [工作空间级操作](#工作空间级操作)
    - [单独构建成员](#单独构建成员)
    - [发布构建](#发布构建)
  - [🧪 测试](#-测试)
    - [tests/integration.rs](#testsintegrationrs)
  - [📊 依赖分析](#-依赖分析)
  - [🎯 学习要点](#-学习要点)
    - [1. 工作空间配置](#1-工作空间配置)
    - [2. 成员包配置](#2-成员包配置)
    - [3. 发布顺序](#3-发布顺序)
  - [📚 相关资源](#-相关资源)

**难度**: ⭐⭐⭐⭐
**类型**: 工作空间
**创建日期**: 2025-10-19

---

## 📋 项目概述

这是一个完整的工作空间项目示例，展示了：

- 工作空间结构设计
- 依赖继承和共享
- 多包协作
- 统一构建和测试
- 发布流程

---

## 📁 项目结构

```text
workspace-project/
├── Cargo.toml                 # 工作空间配置
├── Cargo.lock                 # 统一依赖锁定
├── .cargo/
│   └── config.toml            # 工作空间级配置
│
├── crates/
│   ├── core/                  # 核心库
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── utils/                 # 工具库
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── api/                   # HTTP API
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   └── cli/                   # CLI 应用
│       ├── Cargo.toml
│       └── src/
│           └── main.rs
│
├── examples/
│   └── demo.rs
│
├── tests/
│   └── integration.rs
│
└── README.md
```

---

## 📝 完整代码

### Cargo.toml (工作空间根)

```toml
[workspace]
resolver = "3"              # 使用 Resolver 3
members = [
    "crates/core",
    "crates/utils",
    "crates/api",
    "crates/cli",
]
default-members = ["crates/cli"]

# 排除目录
exclude = [
    "target",
    "examples/old-*",
]

# 工作空间级包配置
[workspace.package]
version = "0.1.0"
edition = "2024"
rust-version = "1.93"
license = "MIT"
authors = ["Workspace Team <team@example.com>"]
repository = "https://github.com/user/workspace-project"

# 工作空间级依赖
[workspace.dependencies]
# 内部依赖
workspace-core = { path = "crates/core" }
workspace-utils = { path = "crates/utils" }
workspace-api = { path = "crates/api" }

# 外部依赖 - 基础
anyhow = "1.0"
thiserror = "2.0"
log = "0.4"
env_logger = "0.11"

# 外部依赖 - 异步
tokio = { version = "1.48", features = ["full"] }
futures = "0.3"

# 外部依赖 - Web
axum = "0.7"
tower = "0.5"
tower-http = { version = "0.6", features = ["trace"] }

# 外部依赖 - CLI
clap = { version = "4.5", features = ["derive"] }
colored = "2.1"

# 外部依赖 - 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
toml = "0.8"

# 开发依赖
[workspace.dev-dependencies]
tokio-test = "0.4"
criterion = "0.5"

# 工作空间级 Profile
[profile.dev]
opt-level = 1
incremental = true

[profile.release]
opt-level = 3
lto = "thin"           # 工作空间使用 thin LTO
codegen-units = 1
strip = true

# 依赖优化
[profile.dev.package."*"]
opt-level = 2

# 测试优化
[profile.test]
opt-level = 1

# 基准测试
[profile.bench]
inherits = "release"
```

---

### crates/core/Cargo.toml

```toml
[package]
name = "workspace-core"
version.workspace = true
edition.workspace = true
rust-version.workspace = true
license.workspace = true
authors.workspace = true

description = "Core functionality for workspace project"

[dependencies]
thiserror.workspace = true
serde.workspace = true
serde_json.workspace = true

[dev-dependencies]
tokio-test.workspace = true
```

### crates/core/src/lib.rs

```rust
//! 核心功能库
//!
//! 提供工作空间的核心数据结构和业务逻辑。

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 核心错误类型
#[derive(Error, Debug)]
pub enum CoreError {
    #[error("Invalid data: {0}")]
    InvalidData(String),

    #[error("Not found: {0}")]
    NotFound(String),

    #[error("Internal error: {0}")]
    Internal(String),
}

pub type Result<T> = std::result::Result<T, CoreError>;

/// 用户数据模型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub active: bool,
}

impl User {
    /// 创建新用户
    pub fn new(id: u64, name: impl Into<String>, email: impl Into<String>) -> Self {
        Self {
            id,
            name: name.into(),
            email: email.into(),
            active: true,
        }
    }

    /// 验证用户数据
    pub fn validate(&self) -> Result<()> {
        if self.name.is_empty() {
            return Err(CoreError::InvalidData("Name cannot be empty".into()));
        }
        if !self.email.contains('@') {
            return Err(CoreError::InvalidData("Invalid email format".into()));
        }
        Ok(())
    }

    /// 停用用户
    pub fn deactivate(&mut self) {
        self.active = false;
    }
}

/// 用户仓库trait
pub trait UserRepository {
    fn find_by_id(&self, id: u64) -> Result<User>;
    fn save(&mut self, user: User) -> Result<()>;
    fn delete(&mut self, id: u64) -> Result<()>;
    fn list_all(&self) -> Vec<User>;
}

/// 内存用户仓库（示例实现）
#[derive(Default)]
pub struct InMemoryUserRepository {
    users: Vec<User>,
}

impl InMemoryUserRepository {
    pub fn new() -> Self {
        Self::default()
    }
}

impl UserRepository for InMemoryUserRepository {
    fn find_by_id(&self, id: u64) -> Result<User> {
        self.users
            .iter()
            .find(|u| u.id == id)
            .cloned()
            .ok_or_else(|| CoreError::NotFound(format!("User {} not found", id)))
    }

    fn save(&mut self, user: User) -> Result<()> {
        user.validate()?;

        if let Some(existing) = self.users.iter_mut().find(|u| u.id == user.id) {
            *existing = user;
        } else {
            self.users.push(user);
        }
        Ok(())
    }

    fn delete(&mut self, id: u64) -> Result<()> {
        let len_before = self.users.len();
        self.users.retain(|u| u.id != id);

        if self.users.len() == len_before {
            return Err(CoreError::NotFound(format!("User {} not found", id)));
        }
        Ok(())
    }

    fn list_all(&self) -> Vec<User> {
        self.users.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_creation() {
        let user = User::new(1, "Alice", "alice@example.com");
        assert_eq!(user.id, 1);
        assert_eq!(user.name, "Alice");
        assert!(user.active);
    }

    #[test]
    fn test_user_validation() {
        let valid = User::new(1, "Alice", "alice@example.com");
        assert!(valid.validate().is_ok());

        let invalid = User::new(2, "", "invalid");
        assert!(invalid.validate().is_err());
    }

    #[test]
    fn test_repository() {
        let mut repo = InMemoryUserRepository::new();
        let user = User::new(1, "Alice", "alice@example.com");

        // 保存
        assert!(repo.save(user.clone()).is_ok());

        // 查找
        let found = repo.find_by_id(1).unwrap();
        assert_eq!(found.name, "Alice");

        // 删除
        assert!(repo.delete(1).is_ok());
        assert!(repo.find_by_id(1).is_err());
    }
}
```

---

### crates/utils/Cargo.toml

```toml
[package]
name = "workspace-utils"
version.workspace = true
edition.workspace = true
rust-version.workspace = true
license.workspace = true
authors.workspace = true

description = "Utility functions for workspace project"

[dependencies]
workspace-core.workspace = true
log.workspace = true
```

### crates/utils/src/lib.rs

```rust
//! 工具函数库
//!
//! 提供通用工具函数和辅助功能。

use workspace_core::User;

/// ID 生成器
pub struct IdGenerator {
    next_id: u64,
}

impl IdGenerator {
    pub fn new() -> Self {
        Self { next_id: 1 }
    }

    pub fn next(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
}

impl Default for IdGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// 格式化用户信息
pub fn format_user(user: &User) -> String {
    format!(
        "User #{}: {} <{}> [{}]",
        user.id,
        user.name,
        user.email,
        if user.active { "active" } else { "inactive" }
    )
}

/// 用户统计
pub struct UserStats {
    pub total: usize,
    pub active: usize,
    pub inactive: usize,
}

pub fn calculate_stats(users: &[User]) -> UserStats {
    let total = users.len();
    let active = users.iter().filter(|u| u.active).count();
    let inactive = total - active;

    UserStats {
        total,
        active,
        inactive,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_id_generator() {
        let mut gen = IdGenerator::new();
        assert_eq!(gen.next(), 1);
        assert_eq!(gen.next(), 2);
        assert_eq!(gen.next(), 3);
    }

    #[test]
    fn test_format_user() {
        let user = User::new(1, "Alice", "alice@example.com");
        let formatted = format_user(&user);
        assert!(formatted.contains("Alice"));
        assert!(formatted.contains("active"));
    }

    #[test]
    fn test_calculate_stats() {
        let users = vec![
            User::new(1, "Alice", "alice@example.com"),
            User::new(2, "Bob", "bob@example.com"),
        ];

        let stats = calculate_stats(&users);
        assert_eq!(stats.total, 2);
        assert_eq!(stats.active, 2);
    }
}
```

---

### crates/api/Cargo.toml

```toml
[package]
name = "workspace-api"
version.workspace = true
edition.workspace = true
rust-version.workspace = true
license.workspace = true
authors.workspace = true

description = "HTTP API for workspace project"

[dependencies]
workspace-core.workspace = true
workspace-utils.workspace = true

tokio.workspace = true
axum.workspace = true
tower.workspace = true
tower-http.workspace = true
serde.workspace = true
serde_json.workspace = true
anyhow.workspace = true
log.workspace = true

[dev-dependencies]
tokio-test.workspace = true
```

### crates/api/src/lib.rs

```rust
//! HTTP API 库
//!
//! 提供基于 Axum 的 HTTP API。

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::{IntoResponse, Json},
    routing::{get, post, delete},
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex};
use workspace_core::{InMemoryUserRepository, User, UserRepository};

/// API 状态
pub struct AppState {
    repo: Arc<Mutex<InMemoryUserRepository>>,
}

impl AppState {
    pub fn new() -> Self {
        Self {
            repo: Arc::new(Mutex::new(InMemoryUserRepository::new())),
        }
    }
}

impl Default for AppState {
    fn default() -> Self {
        Self::new()
    }
}

/// 创建 API 路由
pub fn create_router() -> Router {
    let state = AppState::new();

    Router::new()
        .route("/", get(root))
        .route("/users", get(list_users))
        .route("/users", post(create_user))
        .route("/users/:id", get(get_user))
        .route("/users/:id", delete(delete_user))
        .with_state(Arc::new(state))
}

/// 根路由
async fn root() -> &'static str {
    "Workspace API v0.1.0"
}

/// 列出所有用户
async fn list_users(State(state): State<Arc<AppState>>) -> Json<Vec<User>> {
    let repo = state.repo.lock().unwrap();
    Json(repo.list_all())
}

#[derive(Deserialize)]
struct CreateUserRequest {
    name: String,
    email: String,
}

/// 创建用户
async fn create_user(
    State(state): State<Arc<AppState>>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), AppError> {
    let mut repo = state.repo.lock().unwrap();

    // 生成新 ID
    let id = repo.list_all().len() as u64 + 1;
    let user = User::new(id, payload.name, payload.email);

    repo.save(user.clone())?;

    Ok((StatusCode::CREATED, Json(user)))
}

/// 获取单个用户
async fn get_user(
    State(state): State<Arc<AppState>>,
    Path(id): Path<u64>,
) -> Result<Json<User>, AppError> {
    let repo = state.repo.lock().unwrap();
    let user = repo.find_by_id(id)?;
    Ok(Json(user))
}

/// 删除用户
async fn delete_user(
    State(state): State<Arc<AppState>>,
    Path(id): Path<u64>,
) -> Result<StatusCode, AppError> {
    let mut repo = state.repo.lock().unwrap();
    repo.delete(id)?;
    Ok(StatusCode::NO_CONTENT)
}

/// API 错误类型
#[derive(Debug)]
struct AppError(workspace_core::CoreError);

impl From<workspace_core::CoreError> for AppError {
    fn from(err: workspace_core::CoreError) -> Self {
        AppError(err)
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        let (status, message) = match self.0 {
            workspace_core::CoreError::NotFound(_) => {
                (StatusCode::NOT_FOUND, self.0.to_string())
            }
            workspace_core::CoreError::InvalidData(_) => {
                (StatusCode::BAD_REQUEST, self.0.to_string())
            }
            _ => (StatusCode::INTERNAL_SERVER_ERROR, self.0.to_string()),
        };

        (status, Json(serde_json::json!({ "error": message }))).into_response()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::Request;
    use tower::ServiceExt;

    #[tokio::test]
    async fn test_root() {
        let app = create_router();
        let response = app
            .oneshot(Request::builder().uri("/").body(String::new()).unwrap())
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}
```

---

### crates/cli/Cargo.toml

```toml
[package]
name = "workspace-cli"
version.workspace = true
edition.workspace = true
rust-version.workspace = true
license.workspace = true
authors.workspace = true

description = "CLI application for workspace project"

[[bin]]
name = "wcli"
path = "src/main.rs"

[dependencies]
workspace-core.workspace = true
workspace-utils.workspace = true

clap.workspace = true
colored.workspace = true
anyhow.workspace = true
serde_json.workspace = true
```

### crates/cli/src/main.rs

```rust
use anyhow::Result;
use clap::{Parser, Subcommand};
use colored::*;
use workspace_core::{InMemoryUserRepository, User, UserRepository};
use workspace_utils::{format_user, calculate_stats};

#[derive(Parser)]
#[command(name = "wcli")]
#[command(version = "0.1.0")]
#[command(about = "Workspace CLI", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 添加用户
    Add {
        #[arg(short, long)]
        name: String,

        #[arg(short, long)]
        email: String,
    },

    /// 列出所有用户
    List,

    /// 显示统计信息
    Stats,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let mut repo = InMemoryUserRepository::new();

    // 添加示例数据
    repo.save(User::new(1, "Alice", "alice@example.com"))?;
    repo.save(User::new(2, "Bob", "bob@example.com"))?;

    match cli.command {
        Commands::Add { name, email } => {
            let id = repo.list_all().len() as u64 + 1;
            let user = User::new(id, name, email);
            repo.save(user.clone())?;

            println!("{} {}", "✓".green().bold(), "User added:");
            println!("  {}", format_user(&user));
        }

        Commands::List => {
            let users = repo.list_all();
            println!("{}", "Users:".green().bold());
            for user in users {
                println!("  {}", format_user(&user));
            }
        }

        Commands::Stats => {
            let users = repo.list_all();
            let stats = calculate_stats(&users);

            println!("{}", "Statistics:".green().bold());
            println!("  Total: {}", stats.total);
            println!("  Active: {}", stats.active.to_string().green());
            println!("  Inactive: {}", stats.inactive.to_string().red());
        }
    }

    Ok(())
}
```

---

## 🚀 构建和运行

### 工作空间级操作

```bash
# 构建所有成员
cargo build --workspace

# 测试所有成员
cargo test --workspace

# 清理
cargo clean
```

### 单独构建成员

```bash
# 构建特定包
cargo build -p workspace-core
cargo build -p workspace-api
cargo build -p workspace-cli

# 运行 CLI
cargo run -p workspace-cli -- list
cargo run -p workspace-cli -- add --name "Charlie" --email "charlie@example.com"
cargo run -p workspace-cli -- stats
```

### 发布构建

```bash
# 发布构建所有包
cargo build --workspace --release

# 运行优化版本
./target/release/wcli list
```

---

## 🧪 测试

### tests/integration.rs

```rust
//! 集成测试

use workspace_core::{User, InMemoryUserRepository, UserRepository};
use workspace_utils::format_user;

#[test]
fn test_full_workflow() {
    let mut repo = InMemoryUserRepository::new();

    // 创建用户
    let user = User::new(1, "Test User", "test@example.com");
    assert!(repo.save(user.clone()).is_ok());

    // 查找用户
    let found = repo.find_by_id(1).unwrap();
    assert_eq!(found.name, "Test User");

    // 格式化
    let formatted = format_user(&found);
    assert!(formatted.contains("Test User"));

    // 删除
    assert!(repo.delete(1).is_ok());
    assert!(repo.find_by_id(1).is_err());
}
```

运行测试：

```bash
cargo test --workspace
cargo test --workspace -- --nocapture
```

---

## 📊 依赖分析

```bash
# 查看工作空间依赖树
cargo tree --workspace

# 查看特定包的依赖
cargo tree -p workspace-cli

# 查看重复依赖
cargo tree --duplicates --workspace
```

---

## 🎯 学习要点

### 1. 工作空间配置

```toml
[workspace]
resolver = "3"
members = ["crates/*"]

[workspace.package]
version = "0.1.0"      # 统一版本
edition = "2024"

[workspace.dependencies]
tokio.workspace = true  # 共享依赖
```

### 2. 成员包配置

```toml
[package]
name = "workspace-core"
version.workspace = true       # 继承版本
edition.workspace = true

[dependencies]
tokio.workspace = true         # 使用共享依赖
workspace-utils.workspace = true  # 内部依赖
```

### 3. 发布顺序

```bash
# 按依赖顺序发布
1. workspace-core   (无内部依赖)
2. workspace-utils  (依赖 core)
3. workspace-api    (依赖 core, utils)
4. workspace-cli    (依赖 core, utils)
```

---

## 📚 相关资源

- [工作空间管理](../05_工作空间管理.md)
- [依赖管理详解](../03_依赖管理详解.md)
- [最佳实践指南](../08_最佳实践指南.md)

---

**项目类型**: 工作空间
**适用场景**: 多包项目、微服务、库生态
**难度等级**: ⭐⭐⭐⭐ 高级

_完整的工作空间示例，展示了真实项目的组织方式！_ 🦀🏗️
