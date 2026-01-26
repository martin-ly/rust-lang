# Rust 1.91.1 → 1.92.0 迁移指南（历史记录）

**迁移日期**: 2025-12-11
**最后更新**: 2026-01-26
**Rust版本**: 1.92.0+（历史记录，当前版本为 1.93.0+）
**适用项目**: rust-lang 学习项目
**说明**: 本文档为历史迁移指南，当前项目已更新到 Rust 1.93.0+。最新迁移指南请参考 [Rust 1.93 vs 1.92 对比文档](./docs/toolchain/05_rust_1.93_vs_1.92_comparison.md)

---

## 📋 目录

- [Rust 1.91.1 → 1.92.0 迁移指南（历史记录）](#rust-1911--1920-迁移指南历史记录)
  - [📋 目录](#-目录)
  - [🎯 迁移概述](#-迁移概述)
    - [迁移目标](#迁移目标)
    - [预计时间](#预计时间)
  - [📊 变更摘要](#-变更摘要)
    - [Rust 1.92.0 主要变更](#rust-1920-主要变更)
      - [语言特性 (9项)](#语言特性-9项)
      - [标准库 API (3项)](#标准库-api-3项)
      - [性能优化 (4项)](#性能优化-4项)
  - [1. 版本更新步骤](#1-版本更新步骤)
    - [步骤 1: 更新 Rust 工具链](#步骤-1-更新-rust-工具链)
    - [步骤 2: 更新 Cargo.toml](#步骤-2-更新-cargotoml)
    - [步骤 3: 更新 README 文档](#步骤-3-更新-readme-文档)
  - [2. 新特性使用](#2-新特性使用)
    - [2.1 MaybeUninit 改进](#21-maybeuninit-改进)
    - [2.2 NonZero::div\_ceil](#22-nonzerodiv_ceil)
    - [2.3 rotate\_right](#23-rotate_right)
    - [2.4 Location::file\_as\_c\_str](#24-locationfile_as_c_str)
  - [3. 依赖更新](#3-依赖更新)
    - [3.1 更新依赖版本](#31-更新依赖版本)
    - [3.2 重要依赖更新](#32-重要依赖更新)
    - [3.3 检查兼容性](#33-检查兼容性)
  - [4. 代码迁移](#4-代码迁移)
    - [4.1 编译检查](#41-编译检查)
    - [4.2 测试验证](#42-测试验证)
    - [4.3 代码更新建议](#43-代码更新建议)
      - [使用新 API](#使用新-api)
      - [利用改进的 Lint](#利用改进的-lint)
  - [5. 常见问题](#5-常见问题)
    - [问题1: 编译错误 - 版本不匹配](#问题1-编译错误---版本不匹配)
    - [问题2: 依赖版本冲突](#问题2-依赖版本冲突)
    - [问题3: 新特性不可用](#问题3-新特性不可用)
  - [6. 验证步骤](#6-验证步骤)
    - [步骤 1: 编译验证](#步骤-1-编译验证)
    - [步骤 2: 测试验证](#步骤-2-测试验证)
    - [步骤 3: 构建验证](#步骤-3-构建验证)
    - [步骤 4: 功能验证](#步骤-4-功能验证)
  - [7. 回滚方案](#7-回滚方案)
    - [步骤 1: 安装旧版本](#步骤-1-安装旧版本)
    - [步骤 2: 恢复配置文件](#步骤-2-恢复配置文件)
    - [步骤 3: 恢复依赖](#步骤-3-恢复依赖)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目文档](#项目文档)
  - [✅ 迁移检查清单](#-迁移检查清单)

---

## 🎯 迁移概述

本指南帮助你将项目从 Rust 1.91.1 迁移到 Rust 1.92.0。

### 迁移目标

- ✅ 更新所有配置文件到 Rust 1.92.0
- ✅ 使用 Rust 1.92.0 新特性
- ✅ 更新依赖到兼容版本
- ✅ 验证所有代码正常工作

### 预计时间

- **小型项目**: 1-2 小时
- **中型项目**: 2-4 小时
- **大型项目**: 4-8 小时

---

## 📊 变更摘要

### Rust 1.92.0 主要变更

#### 语言特性 (9项)

1. **MaybeUninit 表示和有效性文档化**
2. **联合体字段的原始引用安全访问**
3. **改进的自动特征和 Sized 边界处理**
4. **零大小数组的优化处理**
5. **#[track_caller] 和 #[no_mangle] 的组合使用**
6. **更严格的 Never 类型 Lint**
7. **关联项的多个边界**
8. **增强的高阶生命周期区域处理**
9. **改进的 unused_must_use Lint 行为**

#### 标准库 API (3项)

1. **NonZero<u{N}>::div_ceil**
2. **Location::file_as_c_str**
3. **<[_]>::rotate_right**

#### 性能优化 (4项)

1. **迭代器方法特化**
2. **简化的元组扩展**
3. **增强的 EncodeWide Debug 信息**
4. **iter::Repeat 中的无限循环 panic**

---

## 1. 版本更新步骤

### 步骤 1: 更新 Rust 工具链

```bash
# 更新 rustup
rustup update stable

# 验证版本
rustc --version  # 应该显示 rustc 1.92.0 或更高
```

### 步骤 2: 更新 Cargo.toml

**根目录 Cargo.toml**:

```toml
[package]
rust-version = "1.92.0"  # 更新这里
```

**Cargo.workspace**:

```toml
[workspace]
target-rust-version = "1.92"  # 更新这里
```

**所有 crate 的 Cargo.toml**:

```toml
[package]
rust-version = "1.92"  # 更新所有 crate
```

### 步骤 3: 更新 README 文档

更新所有 README.md 中的版本引用：

```markdown
**Rust版本**: 1.92.0+（历史记录，当前版本为 1.93.0+）  # 从 1.91.1+ 更新
**最后更新**: 2026-01-26
```

---

## 2. 新特性使用

### 2.1 MaybeUninit 改进

**之前**:

```rust
use std::mem::MaybeUninit;

let mut data: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
```

**现在** (1.92.0):

```rust
use std::mem::MaybeUninit;

// 更清晰的文档和类型表示
let mut data: MaybeUninit<[u8; 1024]> = MaybeUninit::uninit();
// 使用更安全，文档更完善
```

### 2.2 NonZero::div_ceil

**新 API**:

```rust
use std::num::NonZeroU32;

let n = NonZeroU32::new(10).unwrap();
let result = n.div_ceil(NonZeroU32::new(3).unwrap());
assert_eq!(result, 4);
```

### 2.3 rotate_right

**新方法**:

```rust
let mut v = vec![1, 2, 3, 4, 5];
v.rotate_right(2);
assert_eq!(v, vec![4, 5, 1, 2, 3]);
```

### 2.4 Location::file_as_c_str

**新 API**:

```rust
use std::panic::Location;

let location = Location::caller();
let file = location.file_as_c_str();
println!("File: {:?}", file);
```

---

## 3. 依赖更新

### 3.1 更新依赖版本

运行以下命令更新依赖：

```bash
cargo update
```

### 3.2 重要依赖更新

以下依赖已更新到 Rust 1.92.0 兼容版本：

- `http`: 1.3.1 → 1.4.0 (重大版本更新)
- `redis`: 1.0.0-rc.3 → 1.0.1 (RC 到稳定版)
- `actix-web`: 4.12.0 → 4.12.1
- `reqwest`: 0.12.24 → 0.12.25
- `tracing`: 0.1.41 → 0.1.43

### 3.3 检查兼容性

```bash
# 检查依赖兼容性
cargo tree

# 检查过时依赖
cargo outdated
```

---

## 4. 代码迁移

### 4.1 编译检查

```bash
# 检查所有代码
cargo check --workspace

# 检查特定 crate
cargo check --package c01_ownership_borrow_scope
```

### 4.2 测试验证

```bash
# 运行所有测试
cargo test --workspace

# 运行特定测试
cargo test --test rust_192_features_tests
```

### 4.3 代码更新建议

#### 使用新 API

```rust
// 使用新的 rotate_right
let mut data = vec![1, 2, 3, 4, 5];
data.rotate_right(2);

// 使用 NonZero::div_ceil
use std::num::NonZeroU32;
let n = NonZeroU32::new(10).unwrap();
let result = n.div_ceil(NonZeroU32::new(3).unwrap());
```

#### 利用改进的 Lint

```rust
// 改进的 unused_must_use 会更好地检测未使用的 Result
fn returns_result() -> Result<(), Error> {
    Ok(())
}

// 现在会有更好的警告
returns_result();  // 警告：未使用 Result
```

---

## 5. 常见问题

### 问题1: 编译错误 - 版本不匹配

**错误信息**:

```
error: package `xxx` requires rustc 1.91.1 or newer
```

**解决方案**:

```bash
# 更新 rustup
rustup update stable

# 设置默认工具链
rustup default stable
```

### 问题2: 依赖版本冲突

**错误信息**:

```
error: failed to select a version for `xxx`
```

**解决方案**:

```bash
# 更新 Cargo.lock
cargo update

# 如果仍有问题，检查 Cargo.toml 中的版本约束
```

### 问题3: 新特性不可用

**错误信息**:

```
error: `div_ceil` is not a member of trait `NonZeroU32`
```

**解决方案**:

```bash
# 确保使用正确的 Rust 版本
rustc --version  # 应该是 1.93.0+（本文档为历史记录，当前推荐版本为 1.93.0+）

# 清理并重新构建
cargo clean
cargo build
```

---

## 6. 验证步骤

### 步骤 1: 编译验证

```bash
# 检查所有代码
cargo check --workspace --all-targets

# 应该看到: Finished `dev` profile
```

### 步骤 2: 测试验证

```bash
# 运行所有测试
cargo test --workspace

# 应该看到: test result: ok
```

### 步骤 3: 构建验证

```bash
# Release 构建
cargo build --workspace --release

# 应该成功完成
```

### 步骤 4: 功能验证

```bash
# 运行示例
cargo run --example rust_192_features_demo

# 应该正常运行并显示输出
```

---

## 7. 回滚方案

如果迁移遇到问题，可以回滚到 Rust 1.91.1：

### 步骤 1: 安装旧版本

```bash
rustup install 1.91.1
rustup default 1.91.1
```

### 步骤 2: 恢复配置文件

恢复 `Cargo.toml` 中的版本号：

```toml
rust-version = "1.91.1"  # 恢复旧版本
```

### 步骤 3: 恢复依赖

```bash
# 如果有 Cargo.lock 备份，恢复它
# 或者重新生成
cargo update
```

---

## 📚 相关资源

### 官方文档

- [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
- [Rust 1.92.0 特性实现](./crates/c01_ownership_borrow_scope/src/rust_192_features.rs)
- [Rust 1.92.0 示例代码](./crates/c01_ownership_borrow_scope/examples/rust_192_features_demo.rs)

### 项目文档

- [Rust 1.92.0 更新报告](./RUST_192_FINAL_UPDATE_REPORT.md)
- [依赖更新报告](./DEPENDENCY_UPDATE_2025_12_11.md)

---

## ✅ 迁移检查清单

- [ ] Rust 工具链更新到 1.92.0
- [ ] 所有 Cargo.toml 中的 rust-version 更新
- [ ] 所有 README.md 中的版本引用更新
- [ ] 依赖更新完成
- [ ] 代码编译通过
- [ ] 所有测试通过
- [ ] Release 构建成功
- [ ] 功能验证完成

---

**最后更新**: 2026-01-26（历史记录文档）
**维护者**: Rust 学习项目团队
**状态**: ✅ **迁移指南完成**（当前项目已更新到 Rust 1.93.0+）
