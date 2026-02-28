# 📦 Rust 模块系统速查卡 {#-rust-模块系统速查卡}

> **快速参考** | [Cargo/包索引](../../../crates/c02_type_system/docs/cargo_package_management/00_INDEX.md) | [Rust 官方模块系统](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | [代码示例](../../../crates/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [📦 Rust 模块系统速查卡 {#-rust-模块系统速查卡}](#-rust-模块系统速查卡--rust-模块系统速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🎯 模块系统概览 {#-模块系统概览}](#-模块系统概览--模块系统概览)
  - [📝 模块声明 {#-模块声明}](#-模块声明--模块声明)
    - [内联模块](#内联模块)
    - [文件模块](#文件模块)
    - [目录模块](#目录模块)
  - [🔒 可见性控制 {#-可见性控制}](#-可见性控制--可见性控制)
    - [pub 关键字](#pub-关键字)
    - [受限可见性](#受限可见性)
    - [结构体可见性](#结构体可见性)
  - [📥 use 语句 {#-use-语句}](#-use-语句--use-语句)
    - [基本用法](#基本用法)
    - [导入项](#导入项)
    - [重命名](#重命名)
    - [嵌套导入](#嵌套导入)
    - [self 和 super](#self-和-super)
  - [🛤️ 路径系统 {#️-路径系统}](#️-路径系统-️-路径系统)
    - [绝对路径](#绝对路径)
    - [相对路径](#相对路径)
    - [路径简写](#路径简写)
  - [📁 文件组织 {#-文件组织}](#-文件组织--文件组织)
    - [单文件模块 {#文件模块-1}](#单文件模块-文件模块-1)
    - [文件模块1](#文件模块1)
    - [目录模块 {#目录模块-1}](#目录模块-目录模块-1)
    - [混合组织](#混合组织)
  - [📦 Crate 系统 {#-crate-系统}](#-crate-系统--crate-系统)
    - [库 Crate](#库-crate)
    - [二进制 Crate](#二进制-crate)
    - [多个二进制文件](#多个二进制文件)
    - [外部 Crate](#外部-crate)
  - [🎯 常用模式 {#-常用模式}](#-常用模式--常用模式)
    - [重导出](#重导出)
    - [条件编译](#条件编译)
    - [模块别名](#模块别名)
    - [私有模块](#私有模块)
    - [模块组织最佳实践](#模块组织最佳实践)
  - [📚 路径规则速查 {#-路径规则速查}](#-路径规则速查--路径规则速查)
    - [模块路径](#模块路径)
    - [use 路径](#use-路径)
  - [🎓 常见模式 {#-常见模式}](#-常见模式--常见模式)
    - [模块初始化](#模块初始化)
    - [模块测试](#模块测试)
    - [特性模块](#特性模块)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 循环引用导致编译失败](#反例-1-循环引用导致编译失败)
    - [反例 2: 在非 pub 项的路径上使用 pub](#反例-2-在非-pub-项的路径上使用-pub)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)
  - [💡 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 分层架构组织](#场景-1-分层架构组织)
    - [场景 2: 特性门控模块](#场景-2-特性门控模块)
    - [场景 3: 私有实现细节](#场景-3-私有实现细节)
  - [⚠️ 边界情况 {#️-边界情况}](#️-边界情况-️-边界情况)
    - [边界 1: 模块可见性陷阱](#边界-1-模块可见性陷阱)
    - [边界 2: 重导出与命名空间](#边界-2-重导出与命名空间)
    - [边界 3: 循环依赖解决](#边界-3-循环依赖解决)
    - [形式化理论](#形式化理论)

---

## 🎯 模块系统概览 {#-模块系统概览}

```text
模块层次结构：

Crate (包)
└── Module (模块)
    ├── Item (项)
    │   ├── Function
    │   ├── Struct
    │   ├── Enum
    │   └── ...
    └── Submodule (子模块)
```

---

## 📝 模块声明 {#-模块声明}

### 内联模块

```rust
// 内联模块定义
mod my_module {
    pub fn public_function() {
        println!("Public function");
    }

    fn private_function() {
        println!("Private function");
    }
}

fn main() {
    my_module::public_function();
    // my_module::private_function(); // ❌ 错误：私有
}
```

### 文件模块

```rust
// src/main.rs
mod my_module; // 声明模块，内容在 my_module.rs

fn main() {
    my_module::public_function();
}
```

```rust
// src/my_module.rs
pub fn public_function() {
    println!("Public function");
}

fn private_function() {
    println!("Private function");
}
```

### 目录模块

```rust
// src/main.rs
mod my_module; // 声明模块，内容在 my_module/mod.rs

fn main() {
    my_module::public_function();
}
```

```rust
// src/my_module/mod.rs
pub fn public_function() {
    println!("Public function");
}

pub mod submodule;
```

```rust
// src/my_module/submodule.rs
pub fn sub_function() {
    println!("Sub function");
}
```

---

## 🔒 可见性控制 {#-可见性控制}

### pub 关键字

```rust
mod my_module {
    // 公开项
    pub fn public_function() {}
    pub struct PublicStruct {}
    pub enum PublicEnum {}

    // 私有项（默认）
    fn private_function() {}
    struct PrivateStruct {}
}
```

### 受限可见性

```rust
mod my_module {
    // 在当前 crate 内可见
    pub(crate) fn crate_visible() {}

    // 在父模块可见
    pub(super) fn super_visible() {}

    // 在指定路径可见
    pub(in crate::parent) fn path_visible() {}

    // 仅在当前模块可见（默认）
    fn private() {}
}
```

### 结构体可见性

```rust
mod my_module {
    // 结构体公开，但字段私有
    pub struct PublicStruct {
        pub public_field: i32,
        private_field: i32,
    }

    impl PublicStruct {
        pub fn new() -> Self {
            PublicStruct {
                public_field: 0,
                private_field: 0,
            }
        }
    }
}
```

---

## 📥 use 语句 {#-use-语句}

### 基本用法

```rust
// 导入模块
use std::collections::HashMap;

// 使用
let map = HashMap::new();
```

### 导入项

```rust
// 导入函数
use std::fs::read_to_string;

// 导入类型
use std::collections::HashMap;
use std::io::Result;

// 导入多个项
use std::collections::{HashMap, HashSet, BTreeMap};

// 导入所有（不推荐）
use std::collections::*;
```

### 重命名

```rust
// 使用 as 重命名
use std::collections::HashMap as Map;

let map = Map::new();
```

### 嵌套导入

```rust
// 导入嵌套路径
use std::{
    collections::HashMap,
    io::{self, Read, Write},
    fs::File,
};
```

### self 和 super

```rust
// 导入当前模块
use self::my_module;

// 导入父模块
use super::parent_module;

// 导入 crate 根
use crate::root_module;
```

---

## 🛤️ 路径系统 {#️-路径系统}

### 绝对路径

```rust
// 从 crate 根开始
use crate::my_module::my_function;

// 从外部 crate 开始
use std::collections::HashMap;
```

### 相对路径

```rust
mod parent {
    mod child {
        fn function() {}
    }

    // 相对路径
    use self::child::function;
    use super::sibling_module;
}
```

### 路径简写

```rust
// 完整路径
use std::collections::hash_map::HashMap;

// 简化路径（推荐）
use std::collections::HashMap;
```

---

## 📁 文件组织 {#-文件组织}

### 单文件模块 {#文件模块-1}

```text
src/
├── main.rs
└── lib.rs
```

```rust
// src/lib.rs
pub mod utils;
pub mod models;
```

### 文件模块1

```text
src/
├── main.rs
├── utils.rs
└── models.rs
```

```rust
// src/main.rs
mod utils;
mod models;

fn main() {
    utils::helper();
    models::User::new();
}
```

### 目录模块 {#目录模块-1}

```text
src/
├── main.rs
├── utils/
│   ├── mod.rs
│   └── helper.rs
└── models/
    ├── mod.rs
    ├── user.rs
    └── post.rs
```

```rust
// src/utils/mod.rs
pub mod helper;

pub fn util_function() {}
```

```rust
// src/utils/helper.rs
pub fn help() {}
```

### 混合组织

```text
src/
├── main.rs
├── config.rs
├── handlers/
│   ├── mod.rs
│   ├── user.rs
│   └── post.rs
└── models/
    ├── mod.rs
    └── user.rs
```

---

## 📦 Crate 系统 {#-crate-系统}

### 库 Crate

```rust
// src/lib.rs
pub mod utils;
pub mod models;

pub fn public_api() {}
```

### 二进制 Crate

```rust
// src/main.rs
use my_crate::utils;

fn main() {
    utils::helper();
}
```

### 多个二进制文件

```text
src/
├── main.rs
├── lib.rs
└── bin/
    ├── tool1.rs
    └── tool2.rs
```

```rust
// src/bin/tool1.rs
use my_crate::utils;

fn main() {
    utils::helper();
}
```

### 外部 Crate

```toml
# Cargo.toml
[dependencies]
serde = "1.0"
tokio = { version = "1", features = ["full"] }
```

```rust
// 使用外部 crate
use serde::{Serialize, Deserialize};
use tokio::runtime::Runtime;
```

---

## 🎯 常用模式 {#-常用模式}

### 重导出

```rust
// src/lib.rs
mod internal {
    pub fn helper() {}
}

// 重导出，简化 API
pub use internal::helper;
```

### 条件编译

```rust
#[cfg(feature = "async")]
pub mod async_utils;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function() {}
}
```

### 模块别名

```rust
// 使用 type 别名
pub type Map<K, V> = std::collections::HashMap<K, V>;

// 使用 use 别名
use std::collections::HashMap as Map;
```

### 私有模块

```rust
// 私有模块（默认）
mod private_module {
    pub fn function() {} // 即使 pub，也只能在父模块访问
}

// 公开模块
pub mod public_module {
    pub fn function() {} // 可以从外部访问
}
```

### 模块组织最佳实践

```rust
// src/lib.rs
// 1. 外部依赖
use std::collections::HashMap;

// 2. 内部模块声明
mod utils;
mod models;
mod handlers;

// 3. 重导出公共 API
pub use models::User;
pub use handlers::handle_request;

// 4. 公共函数
pub fn public_api() {}
```

---

## 📚 路径规则速查 {#-路径规则速查}

### 模块路径

```rust
// 绝对路径（从 crate 根）
crate::module::item

// 相对路径（从当前模块）
self::module::item
super::module::item

// 外部 crate
std::collections::HashMap
```

### use 路径

```rust
// 导入到当前作用域
use std::collections::HashMap;

// 导入并重命名
use std::collections::HashMap as Map;

// 导入多个
use std::collections::{HashMap, HashSet};

// 导入所有
use std::collections::*;
```

---

## 🎓 常见模式 {#-常见模式}

### 模块初始化

```rust
// src/lib.rs
mod config {
    pub fn init() {
        // 初始化配置
    }
}

pub fn setup() {
    config::init();
}
```

### 模块测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function() {
        assert_eq!(function(), expected);
    }
}
```

### 特性模块

```rust
#[cfg(feature = "async")]
mod async_impl {
    pub async fn async_function() {}
}

#[cfg(not(feature = "async"))]
mod sync_impl {
    pub fn sync_function() {}
}
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: 循环引用导致编译失败

**错误示例**:

```rust
// mod_a.rs
use crate::mod_b::B;
pub struct A { pub b: B }

// mod_b.rs
use crate::mod_a::A;  // ❌ 循环依赖
pub struct B { pub a: A }
```

**原因**: 循环依赖导致模块图无法解析。

**修正**: 抽取公共类型到独立模块，或使用 trait 解耦。

---

### 反例 2: 在非 pub 项的路径上使用 pub

**错误示例**:

```rust
mod inner {
    pub fn foo() {}  // pub 但父 mod 是私有的
}
// crate::inner::foo() 仍不可访问
```

**原因**: 父模块私有时，子项 pub 也无法从外部访问。

**修正**: 确保路径上的模块可见：`pub mod inner` 或 `pub use`。

---

## 📚 相关文档 {#-相关文档}

- [项目架构指南](../../07_project/PROJECT_ARCHITECTURE_GUIDE.md)
- [Cargo 包管理与模块索引（项目内）](../../../crates/c02_type_system/docs/cargo_package_management/00_INDEX.md)
- [Workspace 模块示例：控制流与函数模块 README](../../../crates/c03_control_fn/README.md)
- [Workspace 模块示例：线程与并发模块 README](../../../crates/c05_threads/README.md)
- [Workspace 模块示例：类型系统模块 README](../../../crates/c02_type_system/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

这些文件展示了“模块/子模块/导出”的真实组织方式（可直接打开阅读）：

- [C01 crate 根与模块组织](../../../crates/c01_ownership_borrow_scope/src/lib.rs)
- [C02 crate 根与模块组织](../../../crates/c02_type_system/src/lib.rs)
- [C03 crate 根与模块组织](../../../crates/c03_control_fn/src/lib.rs)
- [C05 crate 根与模块组织](../../../crates/c05_threads/src/lib.rs)
- [C10 crate 根与统一 API 组织](../../../crates/c10_networks/src/lib.rs)、[unified_api.rs](../../../crates/c10_networks/src/unified_api.rs)

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 模块系统文档](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)
- [Cargo 文档](https://doc.rust-lang.org/cargo/)

### 项目内部文档

- [Cargo 包管理与模块索引](../../../crates/c02_type_system/docs/cargo_package_management/00_INDEX.md)
- [类型系统速查卡](./type_system.md) - 类型系统与模块的关系
- [Cargo 速查卡](./cargo_cheatsheet.md) - Cargo 包管理
- [字符串与格式化速查卡](./strings_formatting_cheatsheet.md) - 模块中的字符串处理

### 相关速查卡

- [所有权系统速查卡](./ownership_cheatsheet.md) - 模块中的所有权规则
- [错误处理速查卡](./error_handling_cheatsheet.md) - 模块中的错误处理
- [测试速查卡](./testing_cheatsheet.md) - 模块测试

---

## 💡 使用场景 {#-使用场景}

### 场景 1: 分层架构组织

```rust
// src/lib.rs
//! Web 服务器库

pub mod handlers;    // HTTP 请求处理
pub mod models;      // 数据模型
pub mod db;          // 数据库访问层
pub mod middleware;  // 中间件

// 重导出公共 API
pub use handlers::user_handler;
pub use models::User;
```

```rust
// src/handlers/mod.rs
//! HTTP 请求处理器

pub mod user_handler;
pub mod post_handler;

// 公共错误类型
use std::fmt;

#[derive(Debug)]
pub struct HandlerError {
    message: String,
}

impl fmt::Display for HandlerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
```

```rust
// src/handlers/user_handler.rs
//! 用户相关请求处理

use crate::models::User;  // 跨模块引用
use crate::db::Connection;

pub fn get_user(id: u64) -> Option<User> {
    // 实现...
    Some(User { id, name: "Alice".to_string() })
}

pub fn create_user(name: &str) -> User {
    User { id: 1, name: name.to_string() }
}
```

```rust
// src/models/mod.rs
//! 数据模型

pub struct User {
    pub id: u64,
    pub name: String,
}

pub struct Post {
    pub id: u64,
    pub title: String,
    pub content: String,
}
```

### 场景 2: 特性门控模块

```rust
// Cargo.toml
// [features]
// default = ["std"]
// std = []
// async = ["tokio"]
// wasm = ["wasm-bindgen"]

// src/lib.rs
#![cfg_attr(not(feature = "std"), no_std)]

pub mod core;  // 核心功能，始终可用

#[cfg(feature = "std")]
pub mod io;    // 标准 IO，需要 std 特性

#[cfg(feature = "async")]
pub mod async_support;  // 异步支持

#[cfg(feature = "wasm")]
pub mod wasm_bindings;  // WASM 绑定
```

```rust
// src/core/mod.rs
//! 核心功能（无标准库依赖）

pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }
}
```

```rust
// src/io/mod.rs
//! 标准 IO 支持

use std::fs;

pub fn read_file(path: &str) -> Result<String, std::io::Error> {
    fs::read_to_string(path)
}
```

### 场景 3: 私有实现细节

```rust
// src/calculator/mod.rs
//! 计算器模块

// 公开 API
pub struct Calculator;

impl Calculator {
    pub fn new() -> Self {
        Calculator
    }

    pub fn add(&self, a: f64, b: f64) -> f64 {
        internal::precise_add(a, b)
    }

    pub fn divide(&self, a: f64, b: f64) -> Result<f64, &'static str> {
        internal::safe_divide(a, b)
    }
}

// 私有实现模块
mod internal {
    //! 内部实现细节，不对外暴露

    pub fn precise_add(a: f64, b: f64) -> f64 {
        // 使用更高精度算法
        a + b
    }

    pub fn safe_divide(a: f64, b: f64) -> Result<f64, &'static str> {
        if b.abs() < f64::EPSILON {
            return Err("除数不能为零");
        }
        Ok(a / b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculator() {
        let calc = Calculator::new();
        assert_eq!(calc.add(1.0, 2.0), 3.0);
        assert!(calc.divide(10.0, 0.0).is_err());
    }

    // 可以访问内部模块进行测试
    #[test]
    fn test_internal() {
        assert_eq!(internal::precise_add(1.0, 2.0), 3.0);
    }
}
```

---

## ⚠️ 边界情况 {#️-边界情况}

### 边界 1: 模块可见性陷阱

```rust
mod outer {
    // 模块默认私有
    mod inner {
        pub fn public_in_inner() {}
        fn private_in_inner() {}
    }

    // 即使在同一文件，inner 的 pub 项也无法从 outer 外部访问
    pub fn use_inner() {
        inner::public_in_inner(); // OK
    }
}

fn main() {
    outer::use_inner(); // OK
    // outer::inner::public_in_inner(); // ❌ 编译错误：inner 是私有的
}
```

### 边界 2: 重导出与命名空间

```rust
// 使用 pub use 创建清晰的 API 边界

mod internal {
    pub struct ConfigBuilder { /* ... */ }
    pub struct Config { /* ... */ }

    impl ConfigBuilder {
        pub fn new() -> Self { ConfigBuilder {} }
        pub fn build(self) -> Config { Config {} }
    }
}

// 公开 API 只暴露 Config，隐藏 ConfigBuilder
pub use internal::Config;

// 同时提供构建函数
pub fn configure() -> internal::ConfigBuilder {
    internal::ConfigBuilder::new()
}

fn main() {
    // 用户只能看到简洁的 API
    let config = configure().build();
}
```

### 边界 3: 循环依赖解决

```rust
// ❌ 避免这种循环依赖：
// mod a { use crate::b::B; }
// mod b { use crate::a::A; }

// ✅ 解决：提取公共类型到单独模块

// src/types.rs
pub struct UserId(pub u64);
pub struct PostId(pub u64);

// src/user/mod.rs
use crate::types::UserId;
use crate::types::PostId;  // 只使用类型，不依赖 post 模块

pub struct User {
    pub id: UserId,
    pub name: String,
}

// src/post/mod.rs
use crate::types::{UserId, PostId};
// 不直接依赖 user 模块

pub struct Post {
    pub id: PostId,
    pub author_id: UserId,
    pub title: String,
}

fn main() {
    println!("通过类型模块解耦循环依赖");
}
```

### 形式化理论

- [类型系统完备性缺口](../../research_notes/type_theory/00_completeness_gaps.md) — 模块系统与类型可见性的形式化保证
- [所有权模型形式化](../../research_notes/formal_methods/ownership_model.md) — 跨模块边界的所有权规则

---

**最后更新**: 2026-01-27
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.1 更新完成**

🎯 **掌握模块系统，组织清晰代码！**
