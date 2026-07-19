# Rust 自定义类型设计准则：包管理与概念组织

## 目录

- [Rust 自定义类型设计准则：包管理与概念组织](#rust-自定义类型设计准则包管理与概念组织)
  - [目录](#目录)
  - [1. 模块结构与命名空间组织](#1-模块结构与命名空间组织)
    - [1.1 按功能领域组织模块](#11-按功能领域组织模块)
    - [1.2 遵循可见性原则](#12-遵循可见性原则)
  - [2. Crate 设计与包管理](#2-crate-设计与包管理)
    - [2.1 Crate 边界设计](#21-crate-边界设计)
    - [2.2 拆分合理的依赖](#22-拆分合理的依赖)
  - [3. API 版本控制与稳定性](#3-api-版本控制与稳定性)
    - [3.1 稳定性注解](#31-稳定性注解)
    - [3.2 版本兼容性策略](#32-版本兼容性策略)
  - [4. 概念一致性与抽象层次](#4-概念一致性与抽象层次)
    - [4.1 保持概念一致性](#41-保持概念一致性)
    - [4.2 遵循共同设计模式](#42-遵循共同设计模式)
  - [5. 再导出与公共 API 设计](#5-再导出与公共-api-设计)
    - [5.1 通过再导出简化 API](#51-通过再导出简化-api)
    - [5.2 预加载常用类型](#52-预加载常用类型)
  - [6. 类型关系与组合策略](#6-类型关系与组合策略)
    - [6.1 类型关系的明确表达](#61-类型关系的明确表达)
    - [6.2 特征与抽象的分层](#62-特征与抽象的分层)
  - [7. 工作区与多包项目组织](#7-工作区与多包项目组织)
    - [7.1 工作区结构](#71-工作区结构)
    - [7.2 包之间的关系设计](#72-包之间的关系设计)
  - [8. 类型内外公开的视图一致性](#8-类型内外公开的视图一致性)
    - [8.1 保持内部和外部视图一致](#81-保持内部和外部视图一致)
    - [8.2 拆分实现与接口](#82-拆分实现与接口)
  - [9. 总结：包管理与概念组织关键准则](#9-总结包管理与概念组织关键准则)

除了基本的类型设计原则外，在 Rust 中组织和管理类型的方式（包括包管理和概念组织）也至关重要。
以下是关于这方面的核心准则和最佳实践：

## 1. 模块结构与命名空间组织

### 1.1 按功能领域组织模块

```rust
// 推荐：按功能领域组织模块
mod users {
    pub struct User { /* ... */ }
    pub struct UserPreferences { /* ... */ }
    
    mod authentication {
        pub struct Credential { /* ... */ }
    }
}

mod products {
    pub struct Product { /* ... */ }
    pub struct Inventory { /* ... */ }
}
```

**准则**：
    将相关的类型、函数和模块按照功能领域或业务概念组织到一起。

### 1.2 遵循可见性原则

```rust
// 推荐：清晰的可见性层次
pub mod api {
    // 公开给外部用户的类型
    pub struct Request { /* ... */ }
    pub struct Response { /* ... */ }
    
    // 内部使用的辅助类型
    struct RequestValidator { /* ... */ }
    
    pub(crate) mod internals {
        // 仅在 crate 内可见的实现细节
        pub(crate) struct ConnectionPool { /* ... */ }
    }
}
```

**准则**：
    使用嵌套模块和可见性修饰符创建清晰的 API 边界。

## 2. Crate 设计与包管理

### 2.1 Crate 边界设计

```toml
# Cargo.toml
[package]
name = "my-library"
version = "0.1.0"
edition = "2021"

# 特性标志定义
[features]
default = ["std"]
std = []
network = ["dep:reqwest"]

# 有条件的依赖
[dependencies]
serde = { version = "1.0", features = ["derive"], optional = true }
reqwest = { version = "0.11", optional = true }
```

**准则**：
    设计合理的 crate 边界和特性标志，允许用户根据需要选择功能。

### 2.2 拆分合理的依赖

```rust
// 推荐：将大型库拆分为多个 crate
// my-core crate
pub struct CoreType { /* ... */ }

// my-derive crate (过程宏)
#[proc_macro_derive(MyDerive)]
pub fn my_derive(/* ... */) { /* ... */ }

// my-library crate (整合其他 crate)
pub use my_core::CoreType;
```

**准则**：
    将大型库拆分为核心功能、可选功能和过程宏等多个独立 crate。

## 3. API 版本控制与稳定性

### 3.1 稳定性注解

```rust
// 推荐：使用稳定性注解
/// Core functionality for handling data processing
/// 
/// # Stability
/// This API is considered stable and will not change in incompatible ways
/// within the same major version.
pub struct Processor { /* ... */ }

/// Experimental feature for advanced processing
/// 
/// # Stability
/// This API is experimental and may change or be removed without notice.
#[doc(hidden)]
pub struct ExperimentalProcessor { /* ... */ }
```

**准则**：
    清晰地标注 API 的稳定性级别，帮助用户了解预期的变化风险。

### 3.2 版本兼容性策略

```rust
// 推荐：保持向后兼容性的接口设计
impl OldInterface {
    // 旧方法保持不变
    pub fn old_method(&self) -> OldResult {
        // 内部可能调用新实现
        self.new_method().into()
    }
    
    // 添加新方法，而不破坏现有代码
    pub fn new_method(&self) -> NewResult {
        /* 新实现 */
    }
}
```

**准则**：
    设计类型时考虑未来的扩展性和向后兼容性。

## 4. 概念一致性与抽象层次

### 4.1 保持概念一致性

```rust
// 推荐：概念一致的抽象层次
// 网络模块
mod network {
    pub struct Request { /* ... */ }
    pub struct Response { /* ... */ }
    pub struct Connection { /* ... */ }
}

// 数据库模块
mod database {
    pub struct Query { /* ... */ }
    pub struct Result { /* ... */ }
    pub struct Connection { /* ... */ }
}
```

**准则**：
    在同一抽象层次上保持概念一致性，避免混合不同抽象级别的概念。

### 4.2 遵循共同设计模式

```rust
// 推荐：跨模块使用一致的设计模式
// 遵循 Builder 模式
pub struct RequestBuilder { /* ... */ }
pub struct QueryBuilder { /* ... */ }

// 遵循 Options 模式
pub struct ServerOptions { /* ... */ }
pub struct DatabaseOptions { /* ... */ }
```

**准则**：
    在整个代码库中使用一致的设计模式和惯用法。

## 5. 再导出与公共 API 设计

### 5.1 通过再导出简化 API

```rust
// lib.rs - 推荐：通过再导出简化公共 API
// 内部模块
mod users;
mod products;
mod orders;

// 公共 API
pub use users::{User, UserBuilder};
pub use products::{Product, ProductBuilder};
// 注意：不是所有 orders 模块中的类型都被再导出
pub use orders::Order;
```

**准则**：
    通过有选择地再导出内部模块的条目，创建简洁清晰的公共 API。

### 5.2 预加载常用类型

```rust
// 推荐：创建 prelude 模块帮助用户导入
pub mod prelude {
    pub use crate::User;
    pub use crate::Product;
    pub use crate::Order;
    pub use crate::traits::{Storable, Loadable};
}

// 用户代码
use my_library::prelude::*;
```

**准则**：
    创建 prelude 模块，包含库中最常用的类型，便于用户导入。

## 6. 类型关系与组合策略

### 6.1 类型关系的明确表达

```rust
// 推荐：清晰表达类型之间的关系
// 通过包含关系表达拥有关系
pub struct User {
    profile: UserProfile,
    settings: UserSettings,
}

// 通过引用表达关联关系
pub struct Order<'a> {
    items: Vec<OrderItem>,
    user: &'a User,  // 订单关联到用户，但不拥有用户
}
```

**准则**：
    通过类型的组织结构明确表达业务概念之间的关系。

### 6.2 特征与抽象的分层

```rust
// 推荐：特征抽象的分层设计
// 基础特征
pub trait Storage {
    fn save(&self, data: &[u8]) -> Result<(), Error>;
    fn load(&self) -> Result<Vec<u8>, Error>;
}

// 扩展特征
pub trait VersionedStorage: Storage {
    fn save_version(&self, version: u32, data: &[u8]) -> Result<(), Error>;
    fn load_version(&self, version: u32) -> Result<Vec<u8>, Error>;
}

// 具体实现
pub struct FileStorage { /* ... */ }
impl Storage for FileStorage { /* ... */ }
impl VersionedStorage for FileStorage { /* ... */ }
```

**准则**：
    创建层次化的特征体系，从基础抽象到高级抽象，允许不同程度的实现。

## 7. 工作区与多包项目组织

### 7.1 工作区结构

```toml
# Cargo.toml (根工作区)
[workspace]
members = [
    "my-library-core",
    "my-library-macros",
    "my-library-client",
    "my-library-server",
]

# 跨包共享的依赖版本
[workspace.dependencies]
serde = "1.0"
tokio = "1.0"
```

**准则**：
    使用工作区组织多包项目，确保版本一致性和构建效率。

### 7.2 包之间的关系设计

```rust
// my-library-core
pub trait Service {
    fn process(&self, input: &[u8]) -> Vec<u8>;
}

// my-library-server
use my_library_core::Service;

pub struct HttpServer<S: Service> {
    service: S,
}
```

**准则**：
    通过依赖关系设计包之间的清晰接口，避免循环依赖。

## 8. 类型内外公开的视图一致性

### 8.1 保持内部和外部视图一致

```rust
// 推荐：内外视图一致
pub struct User {
    pub name: String,
    pub email: String,
    // 私有字段
    password_hash: String,
}

// 公开方法与类型结构一致
impl User {
    pub fn name(&self) -> &str {
        &self.name
    }
    
    pub fn email(&self) -> &str {
        &self.email
    }
    
    // 不直接暴露私有字段
    pub fn verify_password(&self, password: &str) -> bool {
        /* ... */
    }
}
```

**准则**：
    确保类型的公开方法和属性与其概念模型一致，避免混淆。

### 8.2 拆分实现与接口

```rust
// 推荐：拆分实现与接口
// 公共接口
pub trait UserRepository {
    fn find_by_id(&self, id: u64) -> Option<User>;
    fn save(&self, user: &User) -> Result<(), Error>;
}

// 具体实现
mod implementations {
    pub struct PostgresUserRepository {
        pool: Pool,
    }
    
    impl super::UserRepository for PostgresUserRepository {
        /* 实现接口方法 */
    }
}

// 只公开工厂函数
pub fn new_postgres_repository(config: &Config) -> impl UserRepository {
    implementations::PostgresUserRepository::new(config)
}
```

**准则**：
    通过特征和工厂函数分离接口和实现，提高抽象性和可测试性。

## 9. 总结：包管理与概念组织关键准则

1. **功能模块化**：按功能领域组织模块，创建清晰的命名空间
2. **可见性层次**：使用嵌套模块和可见性修饰符创建清晰的 API 边界
3. **合理拆分 Crate**：设计合理的 crate 边界和特性标志
4. **API 稳定性**：明确标注 API 的稳定性级别和版本兼容性策略
5. **概念一致性**：保持同一抽象层次上的概念一致
6. **简化公共 API**：通过再导出和 prelude 模块简化 API 使用
7. **明确类型关系**：通过类型组织表达业务概念之间的关系
8. **工作区管理**：使用工作区组织多包项目
9. **内外视图一致**：确保类型的公开接口与其概念模型一致

这些准则和实践将帮助你在 Rust 中设计结构良好、概念清晰、易于维护和使用的类型系统和库。
通过合理的包管理和概念组织，你可以提高代码的可重用性、可理解性和可维护性，从而构建更加成功的 Rust 项目。
