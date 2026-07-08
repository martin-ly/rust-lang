# C12 WASM - 最佳实践

> **文档类型**: Tier 3 - 参考层
> **文档定位**: WASM 开发规范和最佳实践
> **项目状态**: ✅ 完整完成
> **相关文档**: [性能优化指南](../tier_02_guides/04_performance_optimization_guide.md) | [API 参考](01_api_reference.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.96.1+ / Edition 2024, WASM 2.0 + WASI 0.2

---

## 📋 目录

- [C12 WASM - 最佳实践](#c12-wasm---最佳实践)
  - [📋 目录](#-目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
  - [🎯 概述](#-概述)
  - [💻 代码实践](#-代码实践)
    - [1. 使用合适的数据类型](#1-使用合适的数据类型)
    - [2. 减少内存分配](#2-减少内存分配)
    - [3. 错误处理](#3-错误处理)
  - [⚡ 性能优化](#-性能优化)
    - [1. 编译优化](#1-编译优化)
    - [2. 使用 wasm-opt](#2-使用-wasm-opt)
    - [3. 减少依赖](#3-减少依赖)
  - [🔐 安全实践](#-安全实践)
    - [1. 输入验证](#1-输入验证)
    - [2. 避免内存泄漏](#2-避免内存泄漏)
  - [📦 项目管理](#-项目管理)
    - [1. 项目结构](#1-项目结构)
    - [2. 版本管理](#2-版本管理)
    - [3. 测试](#3-测试)
  - [📚 相关资源](#-相关资源)

---

## 📐 知识结构

### 概念定义

**WASM 最佳实践 (WASM Best Practices)**:

- **定义**: WASM 开发规范和最佳实践指南
- **类型**: 最佳实践文档
- **范畴**: WebAssembly、开发规范
- **版本**: Rust 1.96.1+, WASM 2.0, WASI 0.2
- **相关概念**: 最佳实践、代码实践、性能优化、安全实践

### 属性特征

**核心属性**:

- **代码实践**: 使用合适的数据类型、减少内存分配、错误处理
- **性能优化**: 编译优化、使用 wasm-opt、减少依赖
- **安全实践**: 输入验证、避免内存泄漏
- **项目管理**: 项目结构、版本管理、测试

**性能特征**:

- **代码质量**: 提高代码可维护性
- **性能优化**: 优化 WASM 性能
- **适用场景**: WASM 开发、生产部署、性能优化

### 关系连接

**组合关系**:

- WASM 最佳实践 --[covers]--> 多种最佳实践
- WASM 应用开发 --[uses]--> WASM 最佳实践

**依赖关系**:

- WASM 最佳实践 --[depends-on]--> WASM 知识
- WASM 开发质量 --[depends-on]--> WASM 最佳实践

### 思维导图

```text
WASM 最佳实践
│
├── 代码实践
│   ├── 数据类型
│   └── 内存分配
├── 性能优化
│   ├── 编译优化
│   └── wasm-opt
├── 安全实践
│   └── 输入验证
└── 项目管理
    └── 项目结构
```

---

## 🎯 概述

本文档提供 WASM 开发的最佳实践和规范。

---

## 💻 代码实践

### 1. 使用合适的数据类型

```rust
// ✅ 好：使用原始类型
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// ❌ 避免：过度使用 String
#[wasm_bindgen]
pub fn add_bad(a: String, b: String) -> String {
    format!("{}", a.parse::<i32>().unwrap() + b.parse::<i32>().unwrap())
}
```

### 2. 减少内存分配

```rust
// ✅ 好：重用缓冲区
thread_local! {
    static BUFFER: RefCell<Vec<u8>> = RefCell::new(Vec::new());
}

// ❌ 避免：频繁分配
pub fn process(data: &[u8]) -> Vec<u8> {
    // 每次都分配新 Vec
    data.to_vec()
}
```

### 3. 错误处理

```rust
// ✅ 好：使用 Result
#[wasm_bindgen]
pub fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}
```

---

## ⚡ 性能优化

### 1. 编译优化

```toml
[profile.release]
opt-level = "z"      # 优化大小
lto = true           # 链接时优化
codegen-units = 1    # 单一代码生成单元
```

### 2. 使用 wasm-opt

```bash
wasm-opt -Oz -o output.wasm input.wasm
```

### 3. 减少依赖

```toml
[dependencies]
some-crate = { version = "1.0", default-features = false }
```

---

## 🔐 安全实践

### 1. 输入验证

```rust
#[wasm_bindgen]
pub fn process_input(input: &str) -> Result<String, String> {
    if input.len() > 1000 {
        return Err("Input too long".to_string());
    }
    // 处理输入
    Ok(input.to_uppercase())
}
```

### 2. 避免内存泄漏

```rust
// ✅ 好：及时释放资源
{
    let data = expensive_operation();
    // 使用 data
} // data 在这里自动释放
```

---

## 📦 项目管理

### 1. 项目结构

```text
project/
├── Cargo.toml
├── src/
│   └── lib.rs
├── pkg/          # wasm-pack 输出
├── www/          # Web 前端
└── tests/        # 测试
```

### 2. 版本管理

```toml
[package]
version = "0.1.0"
```

### 3. 测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }
}
```

---

## 📚 相关资源

- [性能优化指南](../tier_02_guides/04_performance_optimization_guide.md) - 深入学习优化
- [API 参考](01_api_reference.md) - API 文档
- [常见问题](../tier_01_foundations/04_faq.md) - FAQ

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-30
**适用版本**: Rust 1.96.1+ / Edition 2024, WASM 2.0 + WASI 0.2

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
