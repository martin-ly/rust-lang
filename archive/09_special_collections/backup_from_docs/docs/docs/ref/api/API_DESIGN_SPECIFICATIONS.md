# 🦀 Rust API设计规范


## 📊 目录

- [📋 目录](#目录)
- [🎯 API设计概述](#api设计概述)
  - [设计原则](#设计原则)
  - [设计目标](#设计目标)
- [📝 命名规范](#命名规范)
  - [基本命名规则](#基本命名规则)
  - [特殊命名约定](#特殊命名约定)
- [🔧 类型设计](#类型设计)
  - [结构体设计](#结构体设计)
  - [枚举设计](#枚举设计)
  - [Trait设计](#trait设计)
- [⚠️ 错误处理](#️-错误处理)
  - [错误类型设计](#错误类型设计)
  - [错误处理模式](#错误处理模式)
- [🔄 生命周期管理](#生命周期管理)
  - [生命周期参数](#生命周期参数)
  - [生命周期简化](#生命周期简化)
- [📊 性能考虑](#性能考虑)
  - [零成本抽象](#零成本抽象)
  - [内存优化](#内存优化)
- [🧪 测试设计](#测试设计)
  - [单元测试](#单元测试)
  - [集成测试](#集成测试)
- [📈 版本管理](#版本管理)
  - [版本兼容性](#版本兼容性)
  - [向后兼容性](#向后兼容性)
- [📝 最佳实践](#最佳实践)
  - [设计原则1](#设计原则1)
  - [设计检查清单](#设计检查清单)
  - [代码审查要点](#代码审查要点)


**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust API设计者

---

## 📋 目录

- [🦀 Rust API设计规范](#-rust-api设计规范)
  - [📋 目录](#-目录)
  - [🎯 API设计概述](#-api设计概述)
  - [📝 命名规范](#-命名规范)
  - [🔧 类型设计](#-类型设计)
  - [⚠️ 错误处理](#️-错误处理)
  - [🔄 生命周期管理](#-生命周期管理)
  - [📊 性能考虑](#-性能考虑)
  - [🧪 测试设计](#-测试设计)
  - [📈 版本管理](#-版本管理)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 API设计概述

### 设计原则

1. **一致性**: API设计保持一致性
2. **简洁性**: 接口简洁明了
3. **可扩展性**: 支持未来扩展
4. **向后兼容**: 保持向后兼容性
5. **错误处理**: 明确的错误处理

### 设计目标

- **易用性**: 易于理解和使用
- **可维护性**: 易于维护和扩展
- **性能**: 高性能和低开销
- **安全性**: 内存安全和类型安全
- **文档化**: 完整的文档和示例

---

## 📝 命名规范

### 基本命名规则

```rust
// 变量和函数使用snake_case
let user_name = "john_doe";
fn calculate_total_price(items: &[Item]) -> f64;

// 类型和trait使用PascalCase
struct UserAccount {
    id: u32,
    name: String,
}

trait DatabaseConnection {
    fn connect(&self) -> Result<()>;
}

// 常量使用SCREAMING_SNAKE_CASE
const MAX_BUFFER_SIZE: usize = 1024;
const DEFAULT_TIMEOUT: u64 = 30;

// 枚举使用PascalCase
enum HttpStatusCode {
    Ok = 200,
    NotFound = 404,
    InternalServerError = 500,
}
```

### 特殊命名约定

```rust
// 构造函数
impl User {
    pub fn new(name: String, email: String) -> Self {
        Self { name, email }
    }

    pub fn from_json(data: &str) -> Result<Self> {
        // 实现
    }

    pub fn with_config(config: Config) -> Self {
        // 实现
    }
}

// 转换方法
impl User {
    pub fn to_json(&self) -> Result<String> {
        // 实现
    }

    pub fn into_bytes(self) -> Vec<u8> {
        // 实现
    }

    pub fn as_str(&self) -> &str {
        &self.name
    }
}

// 验证方法
impl User {
    pub fn is_valid(&self) -> bool {
        // 实现
    }

    pub fn validate_email(&self) -> Result<()> {
        // 实现
    }
}
```

---

## 🔧 类型设计

### 结构体设计

```rust
/// 用户账户信息
///
/// 包含用户的基本信息和状态
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct User {
    /// 用户唯一标识符
    pub id: u32,

    /// 用户姓名
    pub name: String,

    /// 用户邮箱地址
    pub email: String,

    /// 账户创建时间
    pub created_at: chrono::DateTime<chrono::Utc>,

    /// 账户状态
    pub status: UserStatus,
}

/// 用户状态枚举
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UserStatus {
    /// 活跃状态
    Active,
    /// 暂停状态
    Suspended,
    /// 删除状态
    Deleted,
}

impl User {
    /// 创建新用户
    pub fn new(name: String, email: String) -> Self {
        Self {
            id: 0, // 将由数据库分配
            name,
            email,
            created_at: chrono::Utc::now(),
            status: UserStatus::Active,
        }
    }

    /// 验证用户信息
    pub fn is_valid(&self) -> bool {
        !self.name.is_empty() && self.email.contains('@')
    }
}
```

### 枚举设计

```rust
/// API响应状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApiStatus {
    /// 成功
    Success,
    /// 失败
    Error,
    /// 警告
    Warning,
}

/// API错误类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApiError {
    /// 无效输入
    InvalidInput(String),
    /// 网络错误
    NetworkError(String),
    /// 数据库错误
    DatabaseError(String),
    /// 权限错误
    PermissionError(String),
    /// 内部错误
    InternalError(String),
}

impl std::fmt::Display for ApiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ApiError::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            ApiError::NetworkError(msg) => write!(f, "Network error: {}", msg),
            ApiError::DatabaseError(msg) => write!(f, "Database error: {}", msg),
            ApiError::PermissionError(msg) => write!(f, "Permission error: {}", msg),
            ApiError::InternalError(msg) => write!(f, "Internal error: {}", msg),
        }
    }
}

impl std::error::Error for ApiError {}
```

### Trait设计

```rust
/// 数据库连接trait
pub trait DatabaseConnection {
    /// 连接到数据库
    fn connect(&mut self) -> Result<(), ApiError>;

    /// 断开数据库连接
    fn disconnect(&mut self) -> Result<(), ApiError>;

    /// 执行查询
    fn query(&self, sql: &str) -> Result<QueryResult, ApiError>;

    /// 执行事务
    fn transaction<F, R>(&mut self, f: F) -> Result<R, ApiError>
    where
        F: FnOnce(&mut Self) -> Result<R, ApiError>;
}

/// 查询结果trait
pub trait QueryResult {
    /// 获取行数
    fn row_count(&self) -> usize;

    /// 获取列数
    fn column_count(&self) -> usize;

    /// 获取列名
    fn column_name(&self, index: usize) -> Option<&str>;

    /// 获取值
    fn get_value(&self, row: usize, column: usize) -> Option<&str>;
}
```

---

## ⚠️ 错误处理

### 错误类型设计

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

    /// 序列化错误
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),

    /// 权限错误
    #[error("Permission denied: {reason}")]
    PermissionError { reason: String },

    /// 内部错误
    #[error("Internal error: {0}")]
    InternalError(#[from] anyhow::Error),
}

/// API结果类型
pub type ApiResult<T> = Result<T, ApiError>;

impl ApiError {
    /// 创建无效输入错误
    pub fn invalid_input(message: impl Into<String>) -> Self {
        Self::InvalidInput {
            message: message.into(),
        }
    }

    /// 创建权限错误
    pub fn permission_denied(reason: impl Into<String>) -> Self {
        Self::PermissionError {
            reason: reason.into(),
        }
    }
}
```

### 错误处理模式

```rust
/// 用户服务
pub struct UserService {
    db: Box<dyn DatabaseConnection>,
}

impl UserService {
    /// 创建用户
    pub fn create_user(&mut self, user: User) -> ApiResult<User> {
        // 验证输入
        if !user.is_valid() {
            return Err(ApiError::invalid_input("User data is invalid"));
        }

        // 检查权限
        if !self.has_permission("create_user") {
            return Err(ApiError::permission_denied("Insufficient permissions"));
        }

        // 保存到数据库
        match self.save_user(&user) {
            Ok(saved_user) => Ok(saved_user),
            Err(e) => Err(ApiError::DatabaseError(e.to_string())),
        }
    }

    /// 获取用户
    pub fn get_user(&self, id: u32) -> ApiResult<Option<User>> {
        // 检查权限
        if !self.has_permission("read_user") {
            return Err(ApiError::permission_denied("Insufficient permissions"));
        }

        // 从数据库获取
        match self.load_user(id) {
            Ok(user) => Ok(user),
            Err(e) => Err(ApiError::DatabaseError(e.to_string())),
        }
    }

    /// 检查权限
    fn has_permission(&self, permission: &str) -> bool {
        // 实现权限检查逻辑
        true
    }

    /// 保存用户到数据库
    fn save_user(&mut self, user: &User) -> Result<User, Box<dyn std::error::Error>> {
        // 实现数据库保存逻辑
        Ok(user.clone())
    }

    /// 从数据库加载用户
    fn load_user(&self, id: u32) -> Result<Option<User>, Box<dyn std::error::Error>> {
        // 实现数据库加载逻辑
        Ok(None)
    }
}
```

---

## 🔄 生命周期管理

### 生命周期参数

```rust
/// 文本处理器
pub struct TextProcessor<'a> {
    text: &'a str,
    config: &'a ProcessingConfig,
}

impl<'a> TextProcessor<'a> {
    /// 创建新的文本处理器
    pub fn new(text: &'a str, config: &'a ProcessingConfig) -> Self {
        Self { text, config }
    }

    /// 处理文本
    pub fn process(&self) -> String {
        let mut result = String::new();

        for line in self.text.lines() {
            let processed_line = self.process_line(line);
            result.push_str(&processed_line);
            result.push('\n');
        }

        result
    }

    /// 处理单行文本
    fn process_line(&self, line: &str) -> String {
        if self.config.trim_whitespace {
            line.trim().to_string()
        } else {
            line.to_string()
        }
    }
}

/// 处理配置
#[derive(Debug, Clone)]
pub struct ProcessingConfig {
    pub trim_whitespace: bool,
    pub case_sensitive: bool,
    pub max_length: usize,
}
```

### 生命周期简化

```rust
/// 字符串工具
pub struct StringUtils;

impl StringUtils {
    /// 查找子字符串
    pub fn find<'a>(text: &'a str, pattern: &str) -> Option<&'a str> {
        text.find(pattern).map(|pos| &text[pos..])
    }

    /// 分割字符串
    pub fn split<'a>(text: &'a str, delimiter: &str) -> Vec<&'a str> {
        text.split(delimiter).collect()
    }

    /// 替换字符串
    pub fn replace(text: &str, from: &str, to: &str) -> String {
        text.replace(from, to)
    }
}
```

---

## 📊 性能考虑

### 零成本抽象

```rust
/// 迭代器适配器
pub struct FilterMap<I, F> {
    iter: I,
    f: F,
}

impl<I, F, B> Iterator for FilterMap<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> Option<B>,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some(item) => {
                    if let Some(result) = (self.f)(item) {
                        return Some(result);
                    }
                }
                None => return None,
            }
        }
    }
}

/// 扩展trait
pub trait IteratorExt: Iterator {
    fn filter_map<F, B>(self, f: F) -> FilterMap<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Option<B>,
    {
        FilterMap { iter: self, f }
    }
}

impl<I: Iterator> IteratorExt for I {}
```

### 内存优化

```rust
/// 高效的字符串构建器
pub struct StringBuilder {
    buffer: String,
    capacity: usize,
}

impl StringBuilder {
    /// 创建新的字符串构建器
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
            capacity: 0,
        }
    }

    /// 创建指定容量的字符串构建器
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buffer: String::with_capacity(capacity),
            capacity,
        }
    }

    /// 追加字符串
    pub fn append(&mut self, s: &str) -> &mut Self {
        self.buffer.push_str(s);
        self
    }

    /// 追加字符
    pub fn append_char(&mut self, c: char) -> &mut Self {
        self.buffer.push(c);
        self
    }

    /// 构建最终字符串
    pub fn build(self) -> String {
        self.buffer
    }
}

impl Default for StringBuilder {
    fn default() -> Self {
        Self::new()
    }
}
```

---

## 🧪 测试设计

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_creation() {
        let user = User::new("John Doe".to_string(), "john@example.com".to_string());
        assert_eq!(user.name, "John Doe");
        assert_eq!(user.email, "john@example.com");
        assert_eq!(user.status, UserStatus::Active);
    }

    #[test]
    fn test_user_validation() {
        let valid_user = User::new("John Doe".to_string(), "john@example.com".to_string());
        assert!(valid_user.is_valid());

        let invalid_user = User::new("".to_string(), "invalid-email".to_string());
        assert!(!invalid_user.is_valid());
    }

    #[test]
    fn test_api_error_display() {
        let error = ApiError::invalid_input("Test error");
        assert_eq!(error.to_string(), "Invalid input: Test error");
    }

    #[test]
    fn test_string_builder() {
        let mut builder = StringBuilder::new();
        builder.append("Hello").append(" ").append("World");
        assert_eq!(builder.build(), "Hello World");
    }
}
```

### 集成测试

```rust
// tests/integration_tests.rs
use my_crate::*;

#[test]
fn test_user_service() {
    let mut service = UserService::new();

    let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    let result = service.create_user(user);

    assert!(result.is_ok());
    let created_user = result.unwrap();
    assert_eq!(created_user.name, "John Doe");
}

#[test]
fn test_text_processor() {
    let config = ProcessingConfig {
        trim_whitespace: true,
        case_sensitive: false,
        max_length: 100,
    };

    let text = "  Hello World  \n  Rust Programming  ";
    let processor = TextProcessor::new(text, &config);
    let result = processor.process();

    assert_eq!(result, "Hello World\nRust Programming\n");
}
```

---

## 📈 版本管理

### 版本兼容性

```rust
/// API版本信息
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl ApiVersion {
    /// 创建新版本
    pub fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self { major, minor, patch }
    }

    /// 检查兼容性
    pub fn is_compatible_with(&self, other: &ApiVersion) -> bool {
        self.major == other.major
    }

    /// 转换为字符串
    pub fn to_string(&self) -> String {
        format!("{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// 版本化API
pub trait VersionedApi {
    /// 获取API版本
    fn version() -> ApiVersion;

    /// 检查版本兼容性
    fn is_compatible_with(version: &ApiVersion) -> bool;
}
```

### 向后兼容性

```rust
/// 用户API v1
pub struct UserApiV1;

impl VersionedApi for UserApiV1 {
    fn version() -> ApiVersion {
        ApiVersion::new(1, 0, 0)
    }

    fn is_compatible_with(version: &ApiVersion) -> bool {
        version.major == 1
    }
}

/// 用户API v2
pub struct UserApiV2;

impl VersionedApi for UserApiV2 {
    fn version() -> ApiVersion {
        ApiVersion::new(2, 0, 0)
    }

    fn is_compatible_with(version: &ApiVersion) -> bool {
        version.major == 2
    }
}
```

---

## 📝 最佳实践

### 设计原则1

1. **单一职责**: 每个API只负责一个功能
2. **开闭原则**: 对扩展开放，对修改关闭
3. **里氏替换**: 子类型可以替换父类型
4. **接口隔离**: 使用多个专门的接口
5. **依赖倒置**: 依赖抽象而不是具体实现

### 设计检查清单

- [ ] API命名清晰明了
- [ ] 错误处理完整
- [ ] 生命周期管理正确
- [ ] 性能考虑充分
- [ ] 测试覆盖完整
- [ ] 文档完整准确
- [ ] 版本管理合理
- [ ] 向后兼容性考虑

### 代码审查要点

- [ ] 命名规范遵循
- [ ] 类型设计合理
- [ ] 错误处理完善
- [ ] 生命周期正确
- [ ] 性能优化充分
- [ ] 测试覆盖足够
- [ ] 文档完整准确

---

-**遵循这些API设计规范，您将能够创建高质量、易维护的Rust API！🦀**-
