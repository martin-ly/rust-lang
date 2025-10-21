# 测试工具 (Testing Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐⭐ (必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [测试工具 (Testing Tools)](#测试工具-testing-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. cargo test (内置 ⭐⭐⭐⭐⭐)](#1-cargo-test-内置-)
      - [基础用法](#基础用法)
      - [测试示例](#测试示例)
    - [2. cargo-nextest (强烈推荐 🌟)](#2-cargo-nextest-强烈推荐-)
      - [核心优势](#核心优势)
      - [基础用法2](#基础用法2)
      - [.config/nextest.toml 配置](#confignextesttoml-配置)
    - [3. cargo-tarpaulin (代码覆盖率 🌟)](#3-cargo-tarpaulin-代码覆盖率-)
      - [基础用法3](#基础用法3)
      - [tarpaulin.toml 配置](#tarpaulintoml-配置)
    - [4. cargo-llvm-cov (覆盖率 🌟)](#4-cargo-llvm-cov-覆盖率-)
      - [基础用法4](#基础用法4)
    - [5. proptest (属性测试 💡)](#5-proptest-属性测试-)
      - [示例](#示例)
    - [6. mockall (Mock 测试 💡)](#6-mockall-mock-测试-)
      - [示例1](#示例1)
    - [7. insta (快照测试 💡)](#7-insta-快照测试-)
      - [示例2](#示例2)
  - [💡 最佳实践](#-最佳实践)
    - [1. 测试组织结构](#1-测试组织结构)
    - [2. 单元测试模式](#2-单元测试模式)
    - [3. 集成测试](#3-集成测试)
    - [4. CI 配置](#4-ci-配置)
  - [📊 工具对比](#-工具对比)
    - [测试运行器对比](#测试运行器对比)
    - [覆盖率工具对比](#覆盖率工具对比)
  - [🎯 实战工作流](#-实战工作流)
    - [开发阶段](#开发阶段)
    - [提交前检查](#提交前检查)
    - [CI/CD 完整流程](#cicd-完整流程)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

测试是保证代码质量的关键环节。
Rust 生态提供了从单元测试到集成测试、从覆盖率到基准测试的完整工具链。

---

## 🔧 核心工具

### 1. cargo test (内置 ⭐⭐⭐⭐⭐)

**用途**: Rust 内置测试框架

#### 基础用法

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_add
cargo test "test_*"  # 模式匹配

# 显示 println! 输出
cargo test -- --nocapture

# 并行/串行运行
cargo test -- --test-threads=4
cargo test -- --test-threads=1  # 串行

# 只运行忽略的测试
cargo test -- --ignored

# 运行所有测试（包括忽略的）
cargo test -- --include-ignored
```

#### 测试示例

```rust
// src/lib.rs
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 2), 4);
    }

    #[test]
    #[should_panic(expected = "overflow")]
    fn test_overflow() {
        let _ = i32::MAX + 1;  // 应该 panic
    }

    #[test]
    #[ignore]
    fn expensive_test() {
        // 耗时测试，默认不运行
    }

    #[test]
    fn test_result() -> Result<(), String> {
        if add(2, 2) == 4 {
            Ok(())
        } else {
            Err(String::from("2 + 2 != 4"))
        }
    }
}
```

**文档测试**:

```rust
/// 两数相加
///
/// # Examples
///
/// ```
/// use my_crate::add;
/// assert_eq!(add(2, 2), 4);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

---

### 2. cargo-nextest (强烈推荐 🌟)

**安装**: `cargo install cargo-nextest`  
**用途**: 更快的并行测试运行器

#### 核心优势

- ✅ **并行执行**: 真正的并行测试
- ✅ **更快速度**: 比 cargo test 快 3-10x
- ✅ **增强输出**: 彩色、结构化输出
- ✅ **重试机制**: 自动重试失败测试
- ✅ **测试分片**: 支持 CI 分片

#### 基础用法2

```bash
# 运行所有测试
cargo nextest run

# 并行度控制
cargo nextest run -j 16

# 重试失败测试
cargo nextest run --retries 3

# 显示测试输出
cargo nextest run --no-capture

# 只运行特定包
cargo nextest run -p my_crate

# JUnit 输出（CI 集成）
cargo nextest run --profile ci
```

#### .config/nextest.toml 配置

```toml
[profile.default]
# 默认并行度
test-threads = "num-cpus"

# 测试超时
slow-timeout = { period = "60s", terminate-after = 2 }

# 重试设置
retries = 0

# 输出设置
failure-output = "immediate"
success-output = "never"

[profile.ci]
# CI 专用配置
retries = 2
slow-timeout = { period = "120s" }
failure-output = "immediate-final"

# JUnit 输出
junit = { path = "target/nextest/junit.xml" }
```

---

### 3. cargo-tarpaulin (代码覆盖率 🌟)

**安装**: `cargo install cargo-tarpaulin`  
**用途**: 代码覆盖率测试 (Linux only)

#### 基础用法3

```bash
# 生成覆盖率
cargo tarpaulin

# HTML 报告
cargo tarpaulin --out Html

# 多种输出格式
cargo tarpaulin --out Xml --out Html --out Lcov

# 忽略测试代码
cargo tarpaulin --ignore-tests

# 只测试特定包
cargo tarpaulin -p my_crate

# 设置最小覆盖率
cargo tarpaulin --fail-under 80
```

#### tarpaulin.toml 配置

```toml
[coverage]
# 目标覆盖率
target-coverage = 80.0

# 输出格式
output-formats = ["Html", "Lcov", "Xml"]

# 忽略文件
exclude = [
    "tests/*",
    "examples/*",
    "benches/*",
]

# 忽略 panic 代码
exclude-panic-coverage = true
```

---

### 4. cargo-llvm-cov (覆盖率 🌟)

**安装**: `cargo install cargo-llvm-cov`  
**用途**: 基于 LLVM 的覆盖率工具（跨平台）

#### 基础用法4

```bash
# 生成覆盖率
cargo llvm-cov

# HTML 报告
cargo llvm-cov --html
cargo llvm-cov --open  # 生成并打开

# Lcov 格式
cargo llvm-cov --lcov --output-path lcov.info

# 与 nextest 集成
cargo llvm-cov nextest

# 清理缓存
cargo llvm-cov clean
```

---

### 5. proptest (属性测试 💡)

**添加依赖**: `cargo add --dev proptest`  
**用途**: 基于属性的随机测试

#### 示例

```rust
use proptest::prelude::*;

// 测试反转两次等于原值
proptest! {
    #[test]
    fn test_reverse_reverse(s: String) {
        let reversed = s.chars().rev().collect::<String>();
        let back = reversed.chars().rev().collect::<String>();
        prop_assert_eq!(s, back);
    }

    #[test]
    fn test_add_commutative(a: i32, b: i32) {
        prop_assert_eq!(a + b, b + a);
    }
}

// 自定义策略
prop_compose! {
    fn user_strategy()(
        name in "[a-z]{3,10}",
        age in 18u8..100u8,
    ) -> User {
        User { name, age }
    }
}

proptest! {
    #[test]
    fn test_user_validation(user in user_strategy()) {
        prop_assert!(user.is_valid());
    }
}
```

---

### 6. mockall (Mock 测试 💡)

**添加依赖**: `cargo add --dev mockall`  
**用途**: Mock 对象生成

#### 示例1

```rust
use mockall::{automock, predicate::*};

#[automock]
trait Database {
    fn get_user(&self, id: u64) -> Option<User>;
    fn save_user(&mut self, user: User) -> Result<(), Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_service() {
        let mut mock_db = MockDatabase::new();
        
        // 设置期望
        mock_db
            .expect_get_user()
            .with(eq(123))
            .times(1)
            .returning(|_| Some(User { id: 123, name: "Alice".into() }));
        
        let service = UserService::new(mock_db);
        let user = service.find_user(123);
        assert_eq!(user.unwrap().name, "Alice");
    }
}
```

---

### 7. insta (快照测试 💡)

**添加依赖**: `cargo add --dev insta`  
**用途**: 快照测试框架

#### 示例2

```rust
use insta::assert_debug_snapshot;

#[test]
fn test_render() {
    let result = render_template("Hello, {{name}}!", "World");
    assert_debug_snapshot!(result);
}

// 生成 JSON 快照
use insta::assert_json_snapshot;

#[test]
fn test_api_response() {
    let response = api_call();
    assert_json_snapshot!(response);
}
```

---

## 💡 最佳实践

### 1. 测试组织结构

```text
my_project/
├── src/
│   ├── lib.rs           # 单元测试
│   └── module.rs
├── tests/
│   ├── integration_test.rs  # 集成测试
│   └── common/
│       └── mod.rs       # 测试工具
└── benches/
    └── benchmark.rs     # 基准测试
```

### 2. 单元测试模式

```rust
// src/lib.rs
pub fn process(data: &str) -> String {
    // 实现
}

#[cfg(test)]
mod tests {
    use super::*;

    // 测试辅助函数
    fn setup() -> TestContext {
        TestContext::new()
    }

    #[test]
    fn test_normal_case() {
        let ctx = setup();
        assert_eq!(process("input"), "output");
    }

    #[test]
    fn test_edge_case() {
        assert_eq!(process(""), "");
    }

    #[test]
    #[should_panic]
    fn test_invalid_input() {
        process("invalid");
    }
}
```

### 3. 集成测试

```rust
// tests/integration_test.rs
use my_crate::*;

mod common;  // tests/common/mod.rs

#[test]
fn test_full_workflow() {
    let app = common::setup_app();
    let result = app.run("input");
    assert!(result.is_ok());
}
```

### 4. CI 配置

```yaml
# .github/workflows/test.yml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        rust: [stable, beta]
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}
      
      - name: Install nextest
        uses: taiki-e/install-action@nextest
      
      - name: Run tests
        run: cargo nextest run --all-features
      
      - name: Generate coverage
        run: cargo llvm-cov --lcov --output-path lcov.info
      
      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
```

---

## 📊 工具对比

### 测试运行器对比

| 工具 | 速度 | 并行 | 输出 | 覆盖率 | 推荐度 |
|------|------|------|------|--------|--------|
| **cargo test** | ⭐⭐⭐ | ✅ | 基础 | ❌ | 内置 |
| **cargo-nextest** | ⭐⭐⭐⭐⭐ | ✅✅ | 优秀 | ❌ | 🌟强推 |

### 覆盖率工具对比

| 工具 | 平台 | 精度 | 速度 | 输出格式 | 推荐度 |
|------|------|------|------|---------|--------|
| **tarpaulin** | Linux | ⭐⭐⭐⭐ | ⭐⭐⭐ | HTML/Lcov | 🌟 Linux |
| **llvm-cov** | 跨平台 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | HTML/Lcov | 🌟 跨平台 |

---

## 🎯 实战工作流

### 开发阶段

```bash
# 终端1: 自动测试
cargo watch -c -x 'nextest run'

# 终端2: 开发代码
# ...
```

### 提交前检查

```bash
#!/bin/bash
set -e

echo "🧪 Running tests..."
cargo nextest run

echo "📊 Checking coverage..."
cargo llvm-cov --fail-under-lines 80

echo "✅ All checks passed!"
```

### CI/CD 完整流程

```bash
# 1. 单元测试
cargo nextest run --all-features

# 2. 集成测试
cargo test --test '*'

# 3. 文档测试
cargo test --doc

# 4. 代码覆盖率
cargo llvm-cov --lcov > coverage.info

# 5. 基准测试 (可选)
cargo bench --no-run
```

---

## 🔗 相关资源

- [cargo-nextest](https://nexte.st/)
- [cargo-tarpaulin](https://github.com/xd009642/tarpaulin)
- [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov)
- [proptest](https://proptest-rs.github.io/proptest/intro.html)
- [mockall](https://docs.rs/mockall/latest/mockall/)

---

**导航**: [返回工具链层](../README.md) | [下一类别：性能分析](../profiling/README.md)
