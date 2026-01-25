# 实战示例：特性丰富的库

## 📊 目录

- [实战示例：特性丰富的库](#实战示例特性丰富的库)
  - [📊 目录](#-目录)
  - [📋 项目概述](#-项目概述)
  - [📁 项目结构](#-项目结构)
  - [📝 完整代码](#-完整代码)
    - [Cargo.toml](#cargotoml)
    - [src/lib.rs](#srclibrs)
    - [src/sync.rs](#srcsyncrs)
    - [src/async\_impl.rs](#srcasync_implrs)
    - [src/serde\_impl.rs](#srcserde_implrs)
    - [src/crypto.rs](#srccryptors)
    - [src/utils.rs](#srcutilsrs)
    - [examples/basic.rs](#examplesbasicrs)
    - [examples/async\_example.rs](#examplesasync_examplers)
    - [examples/serde\_example.rs](#examplesserde_examplers)
  - [🚀 使用示例](#-使用示例)
    - [基础使用](#基础使用)
    - [使用异步特性](#使用异步特性)
    - [使用 Serde](#使用-serde)
    - [使用全部特性](#使用全部特性)
  - [🧪 测试](#-测试)
  - [📊 性能测试](#-性能测试)
    - [benches/benchmarks.rs](#benchesbenchmarksrs)
  - [📚 文档生成](#-文档生成)
  - [🎯 学习要点](#-学习要点)
    - [1. 特性设计模式](#1-特性设计模式)
    - [2. 条件编译](#2-条件编译)
    - [3. 文档配置](#3-文档配置)
    - [4. 示例特性要求](#4-示例特性要求)
  - [📚 相关资源](#-相关资源)

**难度**: ⭐⭐⭐
**类型**: 库项目
**创建日期**: 2025-10-19

---

## 📋 项目概述

这是一个展示 Cargo 特性系统的库项目，包含：

- 多层次特性设计
- 可选依赖管理
- 条件编译
- 文档集成
- 完整测试

---

## 📁 项目结构

```text
feature-lib/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   ├── sync.rs          # 同步实现
│   ├── async_impl.rs    # 异步实现
│   ├── serde_impl.rs    # Serde 支持
│   └── utils.rs         # 工具函数
├── examples/
│   ├── basic.rs
│   ├── async_example.rs
│   └── serde_example.rs
├── tests/
│   └── integration.rs
├── benches/
│   └── benchmarks.rs
└── README.md
```

---

## 📝 完整代码

### Cargo.toml

```toml
[package]
name = "feature-lib"
version = "0.2.0"
edition = "2024"
rust-version = "1.93"

# 包元数据
description = "A library demonstrating Cargo features"
license = "MIT OR Apache-2.0"
repository = "https://github.com/user/feature-lib"
documentation = "https://docs.rs/feature-lib"
readme = "README.md"
keywords = ["feature", "async", "serde"]
categories = ["development-tools"]

[dependencies]
# 基础依赖（始终需要）
thiserror = "2.0"

# 可选依赖 - 异步支持
tokio = { version = "1.48", features = ["rt", "sync"], optional = true }
futures = { version = "0.3", optional = true }

# 可选依赖 - 序列化支持
serde = { version = "1.0", features = ["derive"], optional = true }
serde_json = { version = "1.0", optional = true }

# 可选依赖 - 加密支持
aes = { version = "0.8", optional = true }
rand = { version = "0.8", optional = true }

[dev-dependencies]
tokio = { version = "1.48", features = ["full", "test-util"] }
criterion = "0.5"
serde_json = "1.0"

[features]
# 默认特性
default = ["std"]

# 标准库支持
std = []

# 仅分配器支持（no_std 兼容）
alloc = []

# 异步支持
async = ["dep:tokio", "dep:futures"]

# 序列化支持
serde-support = ["dep:serde", "dep:serde_json"]

# 加密支持
crypto = ["dep:aes", "dep:rand"]

# 完整功能
full = ["std", "async", "serde-support", "crypto"]

# 精简版本（no_std）
minimal = ["alloc"]

[[example]]
name = "async_example"
required-features = ["async"]

[[example]]
name = "serde_example"
required-features = ["serde-support"]

[[bench]]
name = "benchmarks"
harness = false

[profile.dev]
opt-level = 1

[profile.release]
opt-level = 3
lto = "thin"         # 库使用 thin LTO
codegen-units = 16   # 库保持并行编译

[profile.bench]
inherits = "release"

[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

### src/lib.rs

```rust
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]

//! # Feature Lib
//!
//! 一个展示 Cargo 特性系统的库。
//!
//! ## 特性
//!
//! - `std` (默认): 标准库支持
//! - `alloc`: 分配器支持
//! - `async`: 异步操作支持
//! - `serde-support`: 序列化/反序列化
//! - `crypto`: 加密功能
//! - `full`: 所有特性

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

pub mod sync;

#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub mod async_impl;

#[cfg(feature = "serde-support")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde-support")))]
pub mod serde_impl;

#[cfg(feature = "crypto")]
#[cfg_attr(docsrs, doc(cfg(feature = "crypto")))]
pub mod crypto;

pub mod utils;

// 错误类型
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LibError {
    #[error("Invalid input: {0}")]
    InvalidInput(String),

    #[error("Operation failed: {0}")]
    OperationFailed(String),

    #[cfg(feature = "std")]
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

pub type Result<T> = core::result::Result<T, LibError>;

/// 核心数据结构
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde-support", derive(serde::Serialize, serde::Deserialize))]
pub struct Data {
    pub id: u64,
    pub name: String,
    #[cfg(feature = "std")]
    pub metadata: std::collections::HashMap<String, String>,
}

impl Data {
    /// 创建新的 Data 实例
    pub fn new(id: u64, name: impl Into<String>) -> Self {
        Self {
            id,
            name: name.into(),
            #[cfg(feature = "std")]
            metadata: std::collections::HashMap::new(),
        }
    }

    /// 验证数据
    pub fn validate(&self) -> Result<()> {
        if self.name.is_empty() {
            return Err(LibError::InvalidInput("Name cannot be empty".into()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_creation() {
        let data = Data::new(1, "test");
        assert_eq!(data.id, 1);
        assert_eq!(data.name, "test");
    }

    #[test]
    fn test_validation() {
        let data = Data::new(1, "test");
        assert!(data.validate().is_ok());

        let empty = Data::new(1, "");
        assert!(empty.validate().is_err());
    }
}
```

### src/sync.rs

```rust
//! 同步操作模块

use crate::{Data, Result};

/// 同步处理器
pub struct SyncProcessor;

impl SyncProcessor {
    pub fn new() -> Self {
        Self
    }

    /// 处理数据
    pub fn process(&self, data: &mut Data) -> Result<()> {
        data.validate()?;
        // 处理逻辑
        Ok(())
    }

    /// 批量处理
    #[cfg(feature = "alloc")]
    pub fn process_batch(&self, items: &mut [Data]) -> Result<()> {
        for data in items {
            self.process(data)?;
        }
        Ok(())
    }
}

impl Default for SyncProcessor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_processor() {
        let processor = SyncProcessor::new();
        let mut data = Data::new(1, "test");
        assert!(processor.process(&mut data).is_ok());
    }
}
```

### src/async_impl.rs

```rust
//! 异步操作模块

use crate::{Data, Result};
use tokio::sync::RwLock;
use std::sync::Arc;

/// 异步处理器
pub struct AsyncProcessor {
    data_store: Arc<RwLock<Vec<Data>>>,
}

impl AsyncProcessor {
    pub fn new() -> Self {
        Self {
            data_store: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 异步处理数据
    pub async fn process(&self, mut data: Data) -> Result<()> {
        data.validate()?;
        let mut store = self.data_store.write().await;
        store.push(data);
        Ok(())
    }

    /// 异步获取所有数据
    pub async fn get_all(&self) -> Vec<Data> {
        let store = self.data_store.read().await;
        store.clone()
    }

    /// 异步查找
    pub async fn find_by_id(&self, id: u64) -> Option<Data> {
        let store = self.data_store.read().await;
        store.iter().find(|d| d.id == id).cloned()
    }
}

impl Default for AsyncProcessor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_processor() {
        let processor = AsyncProcessor::new();
        let data = Data::new(1, "test");
        assert!(processor.process(data).await.is_ok());

        let all = processor.get_all().await;
        assert_eq!(all.len(), 1);
    }

    #[tokio::test]
    async fn test_find_by_id() {
        let processor = AsyncProcessor::new();
        let data = Data::new(42, "test");
        processor.process(data).await.unwrap();

        let found = processor.find_by_id(42).await;
        assert!(found.is_some());
        assert_eq!(found.unwrap().id, 42);
    }
}
```

### src/serde_impl.rs

```rust
//! Serde 序列化支持

use crate::Data;
use serde_json::{Result as JsonResult};

/// 序列化为 JSON
pub fn to_json(data: &Data) -> JsonResult<String> {
    serde_json::to_string(data)
}

/// 从 JSON 反序列化
pub fn from_json(json: &str) -> JsonResult<Data> {
    serde_json::from_str(json)
}

/// 美化 JSON
pub fn to_json_pretty(data: &Data) -> JsonResult<String> {
    serde_json::to_string_pretty(data)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serialization() {
        let data = Data::new(1, "test");
        let json = to_json(&data).unwrap();
        assert!(json.contains("\"id\":1"));
        assert!(json.contains("\"name\":\"test\""));
    }

    #[test]
    fn test_deserialization() {
        let json = r#"{"id":42,"name":"test","metadata":{}}"#;
        let data = from_json(json).unwrap();
        assert_eq!(data.id, 42);
        assert_eq!(data.name, "test");
    }

    #[test]
    fn test_roundtrip() {
        let original = Data::new(1, "test");
        let json = to_json(&original).unwrap();
        let parsed = from_json(&json).unwrap();
        assert_eq!(original.id, parsed.id);
        assert_eq!(original.name, parsed.name);
    }
}
```

### src/crypto.rs

```rust
//! 加密功能模块

use aes::Aes128;
use aes::cipher::{BlockEncrypt, BlockDecrypt, KeyInit};
use aes::cipher::generic_array::GenericArray;
use rand::Rng;

/// 简单的加密包装器
pub struct Crypto {
    cipher: Aes128,
}

impl Crypto {
    /// 创建新的加密器（随机密钥）
    pub fn new() -> Self {
        let mut rng = rand::thread_rng();
        let key: [u8; 16] = rng.gen();
        let key_array = GenericArray::from(key);

        Self {
            cipher: Aes128::new(&key_array),
        }
    }

    /// 使用指定密钥创建
    pub fn with_key(key: &[u8; 16]) -> Self {
        let key_array = GenericArray::from(*key);
        Self {
            cipher: Aes128::new(&key_array),
        }
    }

    /// 加密块（16字节）
    pub fn encrypt_block(&self, block: &mut [u8; 16]) {
        let mut block_array = GenericArray::from(*block);
        self.cipher.encrypt_block(&mut block_array);
        *block = block_array.into();
    }

    /// 解密块（16字节）
    pub fn decrypt_block(&self, block: &mut [u8; 16]) {
        let mut block_array = GenericArray::from(*block);
        self.cipher.decrypt_block(&mut block_array);
        *block = block_array.into();
    }
}

impl Default for Crypto {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encrypt_decrypt() {
        let crypto = Crypto::with_key(&[0u8; 16]);
        let mut data = *b"Hello, World!123";
        let original = data;

        crypto.encrypt_block(&mut data);
        assert_ne!(data, original);

        crypto.decrypt_block(&mut data);
        assert_eq!(data, original);
    }
}
```

### src/utils.rs

```rust
//! 工具函数

/// 计算字符串哈希（简单示例）
pub fn simple_hash(s: &str) -> u64 {
    s.bytes().fold(0u64, |acc, b| {
        acc.wrapping_mul(31).wrapping_add(b as u64)
    })
}

/// 验证 ID 范围
pub fn validate_id(id: u64) -> bool {
    id > 0 && id < u64::MAX
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_hash() {
        assert_eq!(simple_hash("test"), simple_hash("test"));
        assert_ne!(simple_hash("test"), simple_hash("test2"));
    }

    #[test]
    fn test_validate_id() {
        assert!(validate_id(1));
        assert!(validate_id(100));
        assert!(!validate_id(0));
    }
}
```

### examples/basic.rs

```rust
use feature_lib::{Data, sync::SyncProcessor};

fn main() {
    let mut data = Data::new(1, "Example Data");

    let processor = SyncProcessor::new();
    match processor.process(&mut data) {
        Ok(_) => println!("✓ Processed: {:?}", data),
        Err(e) => eprintln!("✗ Error: {}", e),
    }
}
```

### examples/async_example.rs

```rust
use feature_lib::{Data, async_impl::AsyncProcessor};

#[tokio::main]
async fn main() {
    let processor = AsyncProcessor::new();

    // 处理数据
    let data1 = Data::new(1, "Async Data 1");
    let data2 = Data::new(2, "Async Data 2");

    processor.process(data1).await.unwrap();
    processor.process(data2).await.unwrap();

    // 获取所有数据
    let all = processor.get_all().await;
    println!("✓ Total items: {}", all.len());

    // 查找特定数据
    if let Some(found) = processor.find_by_id(1).await {
        println!("✓ Found: {:?}", found);
    }
}
```

### examples/serde_example.rs

```rust
use feature_lib::{Data, serde_impl::{to_json_pretty, from_json}};

fn main() {
    let data = Data::new(42, "Serde Example");

    // 序列化
    let json = to_json_pretty(&data).unwrap();
    println!("JSON:\n{}", json);

    // 反序列化
    let parsed = from_json(&json).unwrap();
    println!("\n✓ Parsed: {:?}", parsed);
}
```

---

## 🚀 使用示例

### 基础使用

```bash
cargo run --example basic
```

### 使用异步特性

```bash
cargo run --example async_example --features async
```

### 使用 Serde

```bash
cargo run --example serde_example --features serde-support
```

### 使用全部特性

```bash
cargo run --example async_example --features full
```

---

## 🧪 测试

```bash
# 测试默认特性
cargo test

# 测试所有特性
cargo test --all-features

# 测试特定特性
cargo test --features async
cargo test --features serde-support

# 测试 no_std
cargo test --no-default-features --features minimal
```

---

## 📊 性能测试

### benches/benchmarks.rs

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use feature_lib::{Data, sync::SyncProcessor};

fn benchmark_process(c: &mut Criterion) {
    c.bench_function("process_single", |b| {
        let processor = SyncProcessor::new();
        b.iter(|| {
            let mut data = Data::new(1, "test");
            processor.process(black_box(&mut data)).unwrap()
        });
    });
}

criterion_group!(benches, benchmark_process);
criterion_main!(benches);
```

运行基准测试：

```bash
cargo bench
```

---

## 📚 文档生成

```bash
# 生成文档
cargo doc --all-features --open

# 检查文档链接
cargo doc --all-features --no-deps
```

---

## 🎯 学习要点

### 1. 特性设计模式

```toml
[features]
# 分层特性
default = ["std"]
std = []
alloc = []

# 功能特性
async = ["dep:tokio", "dep:futures"]
serde-support = ["dep:serde"]

# 组合特性
full = ["std", "async", "serde-support"]
```

### 2. 条件编译

```rust
#[cfg(feature = "async")]
pub mod async_impl;

#[cfg_attr(feature = "serde-support", derive(serde::Serialize))]
pub struct Data { ... }
```

### 3. 文档配置

```rust
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub mod async_impl;
```

### 4. 示例特性要求

```toml
[[example]]
name = "async_example"
required-features = ["async"]
```

---

## 📚 相关资源

- [特性系统详解](../04_特性系统详解.md)
- [最佳实践指南](../08_最佳实践指南.md)
- [Cargo Book - Features](https://doc.rust-lang.org/cargo/reference/features.html)

---

**项目类型**: 库
**适用场景**: 可配置的库、多特性库
**难度等级**: ⭐⭐⭐ 中级

*完整的特性系统示例，可直接用作库开发模板！* 🦀📚
