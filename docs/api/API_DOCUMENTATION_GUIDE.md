# 🦀 Rust API文档指南

**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust开发者

---

## 📋 目录

- [🦀 Rust API文档指南](#-rust-api文档指南)
  - [📋 目录](#-目录)
  - [🎯 API文档概述](#-api文档概述)
  - [📝 文档注释规范](#-文档注释规范)
  - [🔧 文档生成工具](#-文档生成工具)
  - [📊 API设计原则](#-api设计原则)
  - [🧪 文档测试](#-文档测试)
  - [📈 文档质量保证](#-文档质量保证)
  - [🚀 文档部署](#-文档部署)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 API文档概述

### 文档目标

1. **清晰性**: 提供清晰、易懂的API说明
2. **完整性**: 覆盖所有公共API接口
3. **准确性**: 确保文档与代码同步
4. **实用性**: 提供实用的示例和用例
5. **可维护性**: 易于维护和更新

### 文档类型

- **API参考**: 详细的API接口说明
- **使用指南**: 如何使用API的指导
- **示例代码**: 实际的使用示例
- **设计文档**: API设计理念和原则
- **变更日志**: API版本变更记录

---

## 📝 文档注释规范

### 基本注释格式

```rust
/// 计算两个数的和
///
/// # 参数
///
/// * `a` - 第一个数
/// * `b` - 第二个数
///
/// # 返回值
///
/// 返回两个数的和
///
/// # 示例
///
/// ```rust
/// use my_crate::add;
///
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
///
/// # 错误
///
/// 如果计算结果溢出，会返回错误
pub fn add(a: i32, b: i32) -> Result<i32> {
    a.checked_add(b).ok_or_else(|| Error::Overflow)
}
```

### 模块级文档

```rust
//! # 用户管理模块
//!
//! 提供用户的基本信息管理功能，包括用户创建、验证和查询。
//!
//! # 功能特性
//!
//! - 用户创建和验证
//! - 用户信息查询
//! - 用户状态管理
//!
//! # 使用示例
//!
//! ```rust
//! use my_crate::user::User;
//!
//! let user = User::new("John Doe".to_string(), "john@example.com".to_string());
//! assert!(user.is_valid());
//! ```
//!
//! # 错误处理
//!
//! 所有函数都返回Result类型，包含详细的错误信息。
```

### 结构体文档

```rust
/// 用户账户信息
///
/// 包含用户的基本信息和状态
///
/// # 示例
///
/// ```rust
/// use my_crate::User;
///
/// let user = User::new("John Doe".to_string(), "john@example.com".to_string());
/// println!("User: {}", user.name);
/// ```
///
/// # 字段
///
/// - `id`: 用户唯一标识符
/// - `name`: 用户姓名
/// - `email`: 用户邮箱地址
/// - `created_at`: 账户创建时间
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    /// 用户唯一标识符
    pub id: u32,

    /// 用户姓名
    pub name: String,

    /// 用户邮箱地址
    pub email: String,

    /// 账户创建时间
    pub created_at: chrono::DateTime<chrono::Utc>,
}
```

### Trait文档

```rust
/// 数据库连接trait
///
/// 提供数据库连接的基本操作接口
///
/// # 实现者
///
/// - `PostgresConnection`: PostgreSQL数据库连接
/// - `SqliteConnection`: SQLite数据库连接
/// - `MockConnection`: 测试用模拟连接
///
/// # 示例
///
/// ```rust
/// use my_crate::{DatabaseConnection, PostgresConnection};
///
/// let mut conn = PostgresConnection::new("postgresql://localhost/db")?;
/// conn.connect()?;
/// let result = conn.query("SELECT * FROM users")?;
/// ```
pub trait DatabaseConnection {
    /// 连接到数据库
    ///
    /// # 返回值
    ///
    /// 如果连接成功返回Ok(())，否则返回错误
    ///
    /// # 示例
    ///
    /// ```rust
    /// use my_crate::{DatabaseConnection, PostgresConnection};
    ///
    /// let mut conn = PostgresConnection::new("postgresql://localhost/db")?;
    /// conn.connect()?;
    /// ```
    fn connect(&mut self) -> Result<()>;

    /// 执行查询
    ///
    /// # 参数
    ///
    /// * `query` - SQL查询语句
    ///
    /// # 返回值
    ///
    /// 返回查询结果
    ///
    /// # 示例
    ///
    /// ```rust
    /// use my_crate::{DatabaseConnection, PostgresConnection};
    ///
    /// let mut conn = PostgresConnection::new("postgresql://localhost/db")?;
    /// conn.connect()?;
    /// let result = conn.query("SELECT * FROM users WHERE id = 1")?;
    /// ```
    fn query(&self, query: &str) -> Result<QueryResult>;
}
```

---

## 🔧 文档生成工具

### Cargo文档生成

```bash
# 生成文档
cargo doc

# 生成文档并打开
cargo doc --open

# 生成所有依赖的文档
cargo doc --all

# 生成文档到指定目录
cargo doc --target-dir docs

# 生成文档时包含私有项
cargo doc --document-private-items
```

### 文档配置

```toml
# Cargo.toml
[package]
# ... 其他配置

[package.metadata.docs.rs]
# 文档生成配置
features = ["std"]
targets = ["x86_64-unknown-linux-gnu"]
rustc-args = ["--cfg", "docsrs"]

# 文档生成特性
[features]
doc = ["documentation"]
documentation = []
```

### 自定义文档主题

```rust
// 在lib.rs或main.rs中添加
#![doc(html_logo_url = "https://example.com/logo.png")]
#![doc(html_favicon_url = "https://example.com/favicon.ico")]
#![doc(html_root_url = "https://docs.rs/my-crate")]
```

---

## 📊 API设计原则

### 设计原则

1. **一致性**: API设计保持一致性
2. **简洁性**: 接口简洁明了
3. **可扩展性**: 支持未来扩展
4. **向后兼容**: 保持向后兼容性
5. **错误处理**: 明确的错误处理

### 命名规范

```rust
// 好的命名
pub fn calculate_user_score(user: &User) -> Result<u32, Error> {
    // 实现
}

// 避免的命名
pub fn calc_usr_score(usr: &User) -> Result<u32, Error> {
    // 实现
}
```

### 错误处理

```rust
use thiserror::Error;

/// API错误类型
#[derive(Error, Debug)]
pub enum ApiError {
    /// 无效输入错误
    #[error("Invalid input: {message}")]
    InvalidInput { message: String },

    /// 网络错误
    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),

    /// 数据库错误
    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),
}

/// API结果类型
pub type ApiResult<T> = Result<T, ApiError>;
```

---

## 🧪 文档测试

### 文档测试配置

```rust
/// 计算阶乘
///
/// # 参数
///
/// * `n` - 要计算阶乘的数
///
/// # 返回值
///
/// 返回n的阶乘
///
/// # 示例
///
/// ```rust
/// use my_crate::factorial;
///
/// assert_eq!(factorial(5), 120);
/// assert_eq!(factorial(0), 1);
/// ```
///
/// # 错误
///
/// 如果n为负数，会返回错误
pub fn factorial(n: i32) -> Result<i64> {
    if n < 0 {
        return Err(Error::InvalidInput {
            message: "Factorial is not defined for negative numbers".to_string(),
        });
    }

    if n == 0 {
        return Ok(1);
    }

    let mut result = 1;
    for i in 1..=n {
        result *= i as i64;
    }

    Ok(result)
}
```

### 文档测试运行

```bash
# 运行文档测试
cargo test --doc

# 运行所有测试包括文档测试
cargo test

# 运行特定模块的文档测试
cargo test --doc my_module
```

---

## 📈 文档质量保证

### 文档检查工具

```bash
# 安装文档检查工具
cargo install cargo-doccheck

# 检查文档完整性
cargo doccheck

# 检查文档链接
cargo doc --document-private-items --no-deps
```

### 文档质量指标

- **覆盖率**: 所有公共API都有文档
- **示例完整性**: 所有函数都有使用示例
- **链接完整性**: 所有链接都有效
- **格式一致性**: 文档格式保持一致

### 文档审查清单

- [ ] 所有公共函数都有文档注释
- [ ] 文档注释包含参数说明
- [ ] 文档注释包含返回值说明
- [ ] 文档注释包含使用示例
- [ ] 文档注释包含错误说明
- [ ] 示例代码可以编译运行
- [ ] 文档格式保持一致
- [ ] 链接都有效

---

## 🚀 文档部署

### GitHub Pages部署

```yaml
# .github/workflows/docs.yml
name: Deploy Documentation

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always

jobs:
  docs:
    name: Build Documentation
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
        override: true

    - name: Build documentation
      run: cargo doc --no-deps --document-private-items

    - name: Deploy to GitHub Pages
      uses: peaceiris/actions-gh-pages@v3
      if: github.ref == 'refs/heads/main'
      with:
        github_token: ${{ secrets.GITHUB_TOKEN }}
        publish_dir: ./target/doc
```

### docs.rs部署

```toml
# Cargo.toml
[package.metadata.docs.rs]
# 文档生成特性
features = ["std"]
# 目标平台
targets = ["x86_64-unknown-linux-gnu"]
# 编译器参数
rustc-args = ["--cfg", "docsrs"]
# 依赖
dependencies = []
# 构建脚本
build-dependencies = []
# 文档生成选项
all-features = false
default-target = "x86_64-unknown-linux-gnu"
rustdoc-args = ["--cfg", "docsrs"]
```

---

## 📝 最佳实践

### 文档编写原则

1. **清晰明了**: 使用简洁明了的语言
2. **完整准确**: 确保文档完整准确
3. **示例丰富**: 提供丰富的使用示例
4. **及时更新**: 及时更新文档内容
5. **格式一致**: 保持文档格式一致

### 文档维护

```bash
#!/bin/bash
# scripts/docs-check.sh

set -e

echo "Checking documentation..."

# 生成文档
cargo doc --no-deps --document-private-items

# 检查文档链接
cargo doccheck

# 运行文档测试
cargo test --doc

echo "Documentation check completed!"
```

### 文档更新流程

1. **代码变更**: 修改代码时同步更新文档
2. **文档审查**: 代码审查时同时审查文档
3. **测试验证**: 确保文档示例可以运行
4. **部署更新**: 及时部署更新的文档

---

-**遵循这些API文档指南，您将能够创建高质量、易维护的Rust API文档！🦀**-
