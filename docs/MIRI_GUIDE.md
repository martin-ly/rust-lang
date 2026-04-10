# Miri 使用指南

本文档介绍如何在项目中使用 Miri 进行内存安全测试。

## 目录

- [Miri 使用指南](#miri-使用指南)
  - [目录](#目录)
  - [什么是 Miri](#什么是-miri)
  - [安装 Miri](#安装-miri)
  - [运行 Miri 测试](#运行-miri-测试)
    - [使用脚本运行](#使用脚本运行)
    - [手动运行](#手动运行)
  - [Tree Borrows vs Stacked Borrows](#tree-borrows-vs-stacked-borrows)
    - [Stacked Borrows (默认)](#stacked-borrows-默认)
    - [Tree Borrows (推荐)](#tree-borrows-推荐)
    - [关键区别示例](#关键区别示例)
  - [配置 Miri](#配置-miri)
    - [项目配置](#项目配置)
    - [Miri 环境变量](#miri-环境变量)
    - [常用 Miri 选项](#常用-miri-选项)
  - [常见错误类型](#常见错误类型)
    - [Use-after-free](#use-after-free)
    - [数据竞争](#数据竞争)
    - [越界访问](#越界访问)
    - [未初始化内存](#未初始化内存)
  - [Miri 测试结构](#miri-测试结构)
    - [测试文件位置](#测试文件位置)
    - [测试模块声明](#测试模块声明)
    - [测试组织](#测试组织)
    - [标记 Miri 专用测试](#标记-miri-专用测试)
  - [最佳实践](#最佳实践)
  - [更多资源](#更多资源)

## 什么是 Miri

Miri (Mid-level Intermediate Representation Interpreter) 是 Rust 的官方解释器，用于检测代码中的**未定义行为 (Undefined Behavior, UB)**。

Miri 可以检测的问题：

- **内存安全**: Use-after-free, double-free, 内存泄漏
- **数据竞争**: 线程间不安全的数据访问
- **无效内存访问**: 空指针解引用, 越界访问
- **对齐违规**: 未对齐的内存访问
- **未初始化内存**: 读取未初始化的值
- **类型违规**: 违反 Rust 类型系统的操作

## 安装 Miri

```bash
# 添加 Miri 组件
rustup component add miri

# 初始化 Miri
cargo miri setup
```

## 运行 Miri 测试

### 使用脚本运行

```bash
# Linux/macOS
./scripts/run-miri.sh

# Windows
scripts\run-miri.bat
```

### 手动运行

```bash
# 运行所有 Miri 测试
cargo miri test --workspace -- miri_tests

# 运行特定 crate 的 Miri 测试
cargo miri test -p c01_ownership_borrow_scope -- miri_tests

# 使用 Tree Borrows 模型
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 禁用隔离（允许文件系统/网络访问）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

## Tree Borrows vs Stacked Borrows

Miri 支持两种别名模型来检查内存访问的有效性：

### Stacked Borrows (默认)

- 更严格的模型
- 基于栈的借用跟踪
- 与某些合法的 unsafe 模式不兼容

### Tree Borrows (推荐)

- 更灵活的模型
- 基于树的借用关系
- 更符合实际 unsafe 代码的使用模式

**推荐使用 Tree Borrows**: 它在保持安全性的同时，对合法的 unsafe 代码更友好。

```bash
# 启用 Tree Borrows
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

### 关键区别示例

```rust
let mut x = 0;
let y = &mut x;      // 创建可变借用
let z = &mut *y;     // 重新借用

*z = 1;              // 通过子借用写入
*y = 2;              // 通过父借用写入（Tree Borrows: OK, Stacked Borrows: UB）
```

在 Tree Borrows 中，重新借用创建的是**父子关系**，使用父引用是允许的。而在 Stacked Borrows 中，这会破坏借用栈。

## 配置 Miri

### 项目配置

项目的 `.cargo/config.toml` 已配置 Miri 支持：

```toml
[target.x86_64-unknown-linux-gnu.miri]
runner = "miri"

[target.x86_64-pc-windows-msvc.miri]
runner = "miri"

[env.miri]
MIRIFLAGS = { value = "-Zmiri-tree-borrows -Zmiri-disable-isolation", force = false }
```

### Miri 环境变量

| 变量 | 说明 | 示例 |
|------|------|------|
| `MIRIFLAGS` | Miri 选项 | `-Zmiri-tree-borrows` |
| `MIRI_BACKTRACE` | 完整 backtrace | `1` |
| `MIRI_LOG` | 日志级别 | `info` |

### 常用 Miri 选项

```bash
# Tree Borrows 模型
-Zmiri-tree-borrows

# 标记裸指针
-Zmiri-tag-raw-pointers

# 禁用隔离（允许文件系统/网络）
-Zmiri-disable-isolation

# 检查内存泄漏
-Zmiri-ignore-leaks

# 控制地址空间布局随机化
-Zmiri-disable-address-space-layout-randomization
```

## 常见错误类型

### Use-after-free

```rust
let ptr = {
    let x = Box::new(42);
    &*x as *const i32
}; // x 在这里被释放

unsafe {
    let _ = *ptr; // 错误: use-after-free!
}
```

### 数据竞争

```rust
static mut COUNTER: i32 = 0;

// 线程 1
thread::spawn(|| unsafe {
    COUNTER += 1; // 数据竞争!
});

// 线程 2
unsafe {
    COUNTER += 1; // 数据竞争!
}
```

### 越界访问

```rust
let arr = [1, 2, 3];
unsafe {
    let ptr = arr.as_ptr();
    let _ = *ptr.offset(10); // 越界访问!
}
```

### 未初始化内存

```rust
let x: i32;
let _ = x; // 错误: 使用未初始化的值
```

## Miri 测试结构

### 测试文件位置

每个 crate 的 Miri 测试位于 `src/miri_tests.rs`：

```
crates/
├── c01_ownership_borrow_scope/src/miri_tests.rs
├── c02_type_system/src/miri_tests.rs
├── c03_control_fn/src/miri_tests.rs
└── ...
```

### 测试模块声明

在 `lib.rs` 中添加：

```rust
#[cfg(test)]
pub mod miri_tests;
```

### 测试组织

```rust
//! Miri 测试模块

// ==================== 基础测试 ====================

#[test]
fn test_basic_memory_safety() {
    // Miri 会检测此测试中的内存问题
    let x = 42;
    let r = &x;
    assert_eq!(*r, 42);
}

// ==================== Unsafe 代码测试 ====================

#[test]
fn test_unsafe_operations() {
    unsafe {
        // 安全的裸指针操作
        let mut x = 0;
        let ptr = &mut x as *mut i32;
        *ptr = 42;
        assert_eq!(x, 42);
    }
}

// ==================== 应该失败的测试 ====================

#[test]
#[ignore = "This test should fail with UB"]
fn test_use_after_free() {
    // 这个测试应该被 Miri 检测出错误
    let ptr = {
        let x = Box::new(42);
        &*x as *const i32
    };

    unsafe {
        let _ = *ptr; // UB!
    }
}
```

### 标记 Miri 专用测试

```rust
#[cfg(miri)]
mod miri_only_tests {
    // 这些测试只在 Miri 下运行
    #[test]
    fn test_miri_specific() {
        // ...
    }
}

#[cfg(not(miri))]
mod non_miri_tests {
    // 这些测试在 Miri 之外运行
}
```

## 最佳实践

1. **为所有 unsafe 代码编写 Miri 测试**
   - 确保 unsafe 块的安全性
   - 验证原始指针操作

2. **使用 Tree Borrows 模型**
   - 更友好的 unsafe 代码支持
   - 减少误报

3. **在 CI 中运行 Miri**
   - 定期检查内存安全
   - 捕获回归问题

4. **区分 Miri 专用测试**
   - 使用 `#[cfg(miri)]` 标记
   - 避免不必要的 Miri 运行

5. **处理 Miri 限制**
   - Miri 不支持所有系统调用
   - 某些代码可能需要 `#[cfg(not(miri))]`

## 更多资源

- [Miri 官方文档](https://github.com/rust-lang/miri)
- [Tree Borrows 论文](https://arxiv.org/abs/2206.00986)
- [Stacked Borrows 论文](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [Rustonomicon - 不安全代码指南](https://doc.rust-lang.org/nomicon/)
