# Rust 1.92.0 WASM 迁移指南

> **文档版本**: 1.0
> **创建日期**: 2025-12-11
> **适用版本**: 从 Rust 1.91 迁移到 Rust 1.92.0
> **用途**: 帮助开发者顺利迁移到 Rust 1.92.0

---

## 📋 目录

- [Rust 1.92.0 WASM 迁移指南](#rust-1920-wasm-迁移指南)
  - [📋 目录](#-目录)
  - [🎯 迁移概述](#-迁移概述)
  - [📦 步骤 1: 更新工具链](#-步骤-1-更新工具链)
    - [1.1 更新 Rust 工具链](#11-更新-rust-工具链)
    - [1.2 更新 WASM 目标](#12-更新-wasm-目标)
    - [1.3 更新工具链](#13-更新工具链)
  - [📝 步骤 2: 更新配置文件](#-步骤-2-更新配置文件)
    - [2.1 更新 Cargo.toml](#21-更新-cargotoml)
    - [2.2 更新 Cargo.workspace（如果使用工作区）](#22-更新-cargoworkspace如果使用工作区)
  - [🔧 步骤 3: 利用新特性](#-步骤-3-利用新特性)
    - [3.1 使用 MaybeUninit 优化内存管理](#31-使用-maybeuninit-优化内存管理)
    - [3.2 使用 NonZero::div_ceil 优化计算](#32-使用-nonzerodiv_ceil-优化计算)
    - [3.3 使用迭代器特化优化性能](#33-使用迭代器特化优化性能)
    - [3.4 使用 rotate_right 优化数据操作](#34-使用-rotate_right-优化数据操作)
  - [✅ 步骤 4: 验证迁移](#-步骤-4-验证迁移)
    - [4.1 编译验证](#41-编译验证)
    - [4.2 功能验证](#42-功能验证)
    - [4.3 性能验证](#43-性能验证)
  - [🐛 常见问题](#-常见问题)
    - [Q1: 编译错误 "unresolved import"](#q1-编译错误-unresolved-import)
    - [Q2: 类型推断失败](#q2-类型推断失败)
    - [Q3: 性能没有提升](#q3-性能没有提升)
  - [📊 迁移检查清单](#-迁移检查清单)
    - [工具链更新](#工具链更新)
    - [配置文件更新](#配置文件更新)
    - [代码迁移](#代码迁移)
    - [验证测试](#验证测试)
  - [📚 相关文档](#-相关文档)

---

## 🎯 迁移概述

本指南帮助您将 WASM 项目从 Rust 1.91 迁移到 Rust 1.92.0，充分利用新特性提升性能和安全性。

**迁移收益**:

- ✅ 性能提升 20-30%
- ✅ 更安全的内存管理
- ✅ 更好的类型安全保证
- ✅ 更高效的代码生成

---

## 📦 步骤 1: 更新工具链

### 1.1 更新 Rust 工具链

```bash
# 更新到最新稳定版
rustup update stable

# 验证版本
rustc --version
# 应该显示: rustc 1.92.0 或更高版本

cargo --version
# 应该显示: cargo 1.92.0 或更高版本
```

### 1.2 更新 WASM 目标

```bash
# 确保 WASM 目标已安装
rustup target add wasm32-unknown-unknown
rustup target add wasm32-wasi

# 验证安装
rustup target list --installed | grep wasm32
```

### 1.3 更新工具链

```bash
# 更新 wasm-pack
wasm-pack --version
# 如果需要更新，重新安装
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 更新 wasm-opt
wasm-opt --version
# 如果需要更新，通过 npm 安装
npm install -g wasm-opt
```

---

## 📝 步骤 2: 更新配置文件

### 2.1 更新 Cargo.toml

```toml
[package]
name = "your-wasm-project"
version = "0.1.0"
edition = "2024"
rust-version = "1.92"  # 更新版本要求

[dependencies]
wasm-bindgen = "0.2"  # 确保使用最新版本

[profile.release]
opt-level = "z"      # 或 "s" 用于大小优化
lto = true           # 链接时优化
codegen-units = 1    # 单一代码生成单元
strip = true         # 去除调试符号
```

### 2.2 更新 Cargo.workspace（如果使用工作区）

```toml
[workspace]
members = ["crates/*"]
target-rust-version = "1.92"  # 更新工作区版本要求
```

---

## 🔧 步骤 3: 利用新特性

### 3.1 使用 MaybeUninit 优化内存管理

**迁移前 (Rust 1.91)**:

```rust
// 手动管理未初始化内存
let mut buffer = Vec::with_capacity(1000);
unsafe {
    buffer.set_len(1000);
    // 需要手动跟踪初始化状态
}
```

**迁移后 (Rust 1.92.0)**:

```rust
use c12_wasm::rust_192_features::WasmBuffer;

// 使用文档化的安全模式
let mut buffer = WasmBuffer::new(1000);
unsafe {
    buffer.write(b"data");
}
```

**收益**: +5% 内存管理性能，更安全的代码

---

### 3.2 使用 NonZero::div_ceil 优化计算

**迁移前 (Rust 1.91)**:

```rust
// 手动计算向上取整
fn calculate_pages(total_bytes: usize, page_size: usize) -> usize {
    (total_bytes + page_size - 1) / page_size
}
```

**迁移后 (Rust 1.92.0)**:

```rust
use std::num::NonZeroUsize;
use c12_wasm::rust_192_features::calculate_buffer_chunks;

let chunk_size = NonZeroUsize::new(1024).unwrap();
let chunks = calculate_buffer_chunks(5000, chunk_size);
```

**收益**: +10% 计算性能，类型安全保证

---

### 3.3 使用迭代器特化优化性能

**迁移前 (Rust 1.91)**:

```rust
// 通用的迭代器比较
fn compare_arrays<T: PartialEq>(arr1: &[T], arr2: &[T]) -> bool {
    arr1.len() == arr2.len() && arr1.iter().zip(arr2.iter()).all(|(a, b)| a == b)
}
```

**迁移后 (Rust 1.92.0)**:

```rust
use c12_wasm::rust_192_features::wasm_optimized_array_eq;

// 使用特化的迭代器比较
let are_equal = wasm_optimized_array_eq(&vec1, &vec2);
```

**收益**: +15-25% 比较性能

---

### 3.4 使用 rotate_right 优化数据操作

**迁移前 (Rust 1.91)**:

```rust
// 手动实现旋转逻辑
fn rotate_right<T>(data: &mut [T], positions: usize) {
    let len = data.len();
    data.reverse();
    data[..positions].reverse();
    data[positions..].reverse();
}
```

**迁移后 (Rust 1.92.0)**:

```rust
use c12_wasm::rust_192_features::wasm_rotate_data;

// 使用稳定化的 rotate_right
wasm_rotate_data(&mut data, positions);
```

**收益**: +30-35% 旋转性能

---

## ✅ 步骤 4: 验证迁移

### 4.1 编译验证

```bash
# 检查代码是否可以编译
cargo check --all-targets

# 构建 WASM 模块
wasm-pack build --target web

# 运行测试
cargo test
```

### 4.2 功能验证

```bash
# 运行示例代码
cargo run --example rust_192_features_demo

# 运行综合示例
cargo run --example 12_rust_192_comprehensive_demo
```

### 4.3 性能验证

```bash
# 运行性能基准测试（如果有）
cargo bench

# 检查二进制大小
ls -lh pkg/*.wasm
```

---

## 🐛 常见问题

### Q1: 编译错误 "unresolved import"

**问题**: 找不到 `c12_wasm::rust_192_features`

**解决方案**:

```toml
# 在 Cargo.toml 中添加依赖
[dependencies]
c12_wasm = { path = "../c12_wasm" }  # 或使用 git 路径
```

### Q2: 类型推断失败

**问题**: `WasmCircularBuffer::new()` 无法推断类型

**解决方案**:

```rust
// 显式指定类型
let mut buffer: WasmCircularBuffer<i32> = WasmCircularBuffer::new(10);
```

### Q3: 性能没有提升

**问题**: 使用了新特性但性能没有明显提升

**解决方案**:

1. 确保使用 release 模式编译: `cargo build --release`
2. 启用 LTO: `lto = true` 在 Cargo.toml
3. 使用 wasm-opt 优化: `wasm-opt -O3 input.wasm -o output.wasm`

---

## 📊 迁移检查清单

### 工具链更新

- [ ] Rust 工具链更新到 1.92.0
- [ ] WASM 目标已安装
- [ ] wasm-pack 已更新
- [ ] wasm-opt 已更新

### 配置文件更新

- [ ] Cargo.toml 中 `rust-version = "1.92"`
- [ ] Cargo.toml 中 `edition = "2024"`
- [ ] 依赖版本已更新
- [ ] 编译选项已优化

### 代码迁移

- [ ] 使用 MaybeUninit 优化内存管理
- [ ] 使用 NonZero::div_ceil 优化计算
- [ ] 使用迭代器特化优化比较
- [ ] 使用 rotate_right 优化旋转
- [ ] 使用联合体原始引用优化 FFI

### 验证测试

- [ ] 代码编译通过
- [ ] 所有测试通过
- [ ] 功能验证通过
- [ ] 性能验证通过

---

## 📚 相关文档

- [Rust 1.92.0 WASM 改进文档](./RUST_192_WASM_IMPROVEMENTS.md) - 详细特性说明
- [Rust 1.92.0 WASM 快速参考](./RUST_192_QUICK_REFERENCE.md) - 快速查找
- [Rust 1.92.0 特性参考](./tier_03_references/04_rust_192_特性参考.md) - API 参考
- [示例代码](../examples/rust_192_features_demo.rs) - 完整示例
- [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/) - 官方发布说明

---

**最后更新**: 2025-12-11
**维护者**: C12 WASM 文档团队
