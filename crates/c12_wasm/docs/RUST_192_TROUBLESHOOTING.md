# Rust 1.92.0 WASM 故障排除指南

> **文档版本**: 1.0
> **创建日期**: 2025-12-11
> **适用版本**: Rust 1.92.0+
> **用途**: 解决 Rust 1.92.0 WASM 开发中的常见问题

---

## 📋 目录

- [Rust 1.92.0 WASM 故障排除指南](#rust-1920-wasm-故障排除指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔧 编译问题](#-编译问题)
    - [问题 1: 找不到 rust\_192\_features 模块](#问题-1-找不到-rust_192_features-模块)
    - [问题 2: 类型推断失败](#问题-2-类型推断失败)
    - [问题 3: 编译错误 "unresolved import"](#问题-3-编译错误-unresolved-import)
  - [⚡ 性能问题](#-性能问题)
    - [问题 4: 性能没有提升](#问题-4-性能没有提升)
    - [问题 5: 二进制大小没有减小](#问题-5-二进制大小没有减小)
  - [🛡️ 安全问题](#️-安全问题)
    - [问题 6: unsafe 块警告](#问题-6-unsafe-块警告)
    - [问题 7: 内存安全问题](#问题-7-内存安全问题)
  - [🔗 集成问题](#-集成问题)
    - [问题 8: JavaScript 调用失败](#问题-8-javascript-调用失败)
    - [问题 9: 类型转换错误](#问题-9-类型转换错误)
  - [📚 相关文档](#-相关文档)

---

## 🎯 概述

本文档提供 Rust 1.92.0 WASM 开发中的常见问题解决方案，帮助开发者快速解决问题。

---

## 🔧 编译问题

### 问题 1: 找不到 rust_192_features 模块

**错误信息**:

```
error[E0432]: unresolved import `c12_wasm::rust_192_features`
```

**解决方案**:

1. **检查依赖配置**:

```toml
# Cargo.toml
[dependencies]
c12_wasm = { path = "../c12_wasm" }  # 或使用 git 路径
```

1. **检查模块导出**:

```rust
// 确保 lib.rs 中导出了模块
pub mod rust_192_features;
```

1. **重新构建**:

```bash
cargo clean
cargo build
```

---

### 问题 2: 类型推断失败

**错误信息**:

```
error[E0283]: type annotations needed for `WasmCircularBuffer<_>`
```

**解决方案**:

```rust
// ❌ 错误：类型推断失败
let mut buffer = WasmCircularBuffer::new(10);

// ✅ 正确：显式指定类型
let mut buffer: WasmCircularBuffer<i32> = WasmCircularBuffer::new(10);
```

---

### 问题 3: 编译错误 "unresolved import"

**错误信息**:

```
error[E0432]: unresolved import `std::num::NonZeroUsize`
```

**解决方案**:

```rust
// 确保使用正确的导入
use std::num::NonZeroUsize;

// 检查 Rust 版本
rustc --version  // 应该显示 1.92.0 或更高
```

---

## ⚡ 性能问题

### 问题 4: 性能没有提升

**可能原因**:

1. 使用 debug 模式编译
2. 未启用 LTO
3. 未使用 wasm-opt 优化

**解决方案**:

1. **使用 release 模式**:

```bash
cargo build --release
```

1. **启用 LTO**:

```toml
# Cargo.toml
[profile.release]
lto = true
```

1. **使用 wasm-opt**:

```bash
wasm-opt -O3 input.wasm -o output.wasm
```

1. **验证优化**:

```bash
# 检查二进制大小
ls -lh pkg/*.wasm

# 运行性能测试
cargo bench
```

---

### 问题 5: 二进制大小没有减小

**可能原因**:

1. 未使用大小优化选项
2. 包含未使用的代码
3. 未使用 wasm-opt

**解决方案**:

1. **使用大小优化**:

```toml
# Cargo.toml
[profile.release]
opt-level = "z"  # 或 "s"
lto = true
codegen-units = 1
strip = true
```

1. **使用 wasm-opt**:

```bash
wasm-opt -Oz -o output.wasm input.wasm
```

1. **检查依赖**:

```toml
# 移除未使用的依赖
# 使用 default-features = false
[dependencies]
some-crate = { version = "1.0", default-features = false }
```

---

## 🛡️ 安全问题

### 问题 6: unsafe 块警告

**警告信息**:

```
warning: unnecessary unsafe block
```

**解决方案**:

```rust
// ❌ 错误：不必要的 unsafe
unsafe {
    let value = union.integer;
}

// ✅ 正确：使用安全的访问方法
let value = union.get_integer();
```

---

### 问题 7: 内存安全问题

**问题**: 未初始化内存读取

**解决方案**:

```rust
use c12_wasm::rust_192_features::WasmBuffer;

// ✅ 正确：使用 WasmBuffer 管理内存
let mut buffer = WasmBuffer::new(1000);
unsafe {
    buffer.write(b"data");
    // 确保在读取前已初始化
    let data = buffer.read(4);
}

// ❌ 错误：直接读取未初始化内存
// let mut buffer = Vec::with_capacity(1000);
// unsafe { buffer.set_len(1000); }
// let value = buffer[0]; // 未初始化读取
```

---

## 🔗 集成问题

### 问题 8: JavaScript 调用失败

**错误信息**:

```
TypeError: wasm function is not a function
```

**解决方案**:

1. **确保正确初始化**:

```javascript
// ✅ 正确：先初始化
import init, { add } from "./pkg/c12_wasm.js"

await init()
const result = add(2, 3)

// ❌ 错误：未初始化
import { add } from "./pkg/c12_wasm.js"
const result = add(2, 3) // 错误
```

1. **检查 wasm-bindgen 版本**:

```toml
# Cargo.toml
[dependencies]
wasm-bindgen = "0.2"  # 确保使用最新版本
```

---

### 问题 9: 类型转换错误

**错误信息**:

```
TypeError: Cannot convert undefined to number
```

**解决方案**:

```rust
// ✅ 正确：使用 Option 类型
#[wasm_bindgen]
pub fn get_value() -> Option<i32> {
    Some(42)
}

// JavaScript 端
const value = get_value();
if (value !== undefined) {
    console.log(value);
}
```

---

## 📚 相关文档

- [Rust 1.92.0 WASM 迁移指南](./RUST_192_MIGRATION_GUIDE.md) - 迁移步骤
- [Rust 1.92.0 WASM 最佳实践](./RUST_192_BEST_PRACTICES.md) - 最佳实践
- [常见问题](../tier_01_foundations/04_常见问题.md) - 通用常见问题
- [性能优化指南](./tier_02_guides/04_性能优化指南.md) - 性能优化

---

**最后更新**: 2025-12-11
**维护者**: C12 WASM 文档团队
