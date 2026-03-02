# Miri 使用教程：检测Rust未定义行为

> Miri（Mid-level IR Interpreter）是Rust的MIR解释器，用于检测unsafe代码中的未定义行为（UB）。

---

## 目录

- [Miri 使用教程：检测Rust未定义行为](#miri-使用教程检测rust未定义行为)
  - [目录](#目录)
  - [1. 安装与配置](#1-安装与配置)
    - [1.1 安装 Miri](#11-安装-miri)
    - [1.2 更新 Miri](#12-更新-miri)
    - [1.3 验证安装](#13-验证安装)
  - [2. 基础使用](#2-基础使用)
    - [2.1 运行单个文件](#21-运行单个文件)
    - [2.2 运行 Cargo 项目](#22-运行-cargo-项目)
    - [2.3 运行测试](#23-运行测试)
  - [3. 检测的未定义行为](#3-检测的未定义行为)
    - [3.1 内存访问错误](#31-内存访问错误)
    - [3.2 借用规则违规](#32-借用规则违规)
    - [3.3 并发问题](#33-并发问题)
  - [4. 别名模型](#4-别名模型)
    - [4.1 Stacked Borrows](#41-stacked-borrows)
    - [4.2 Tree Borrows](#42-tree-borrows)
  - [5. 高级用法](#5-高级用法)
    - [5.1 环境变量](#51-环境变量)
    - [5.2 跳过某些检查](#52-跳过某些检查)
    - [5.3 外部函数调用](#53-外部函数调用)
  - [6. 实际案例](#6-实际案例)
    - [6.1 检测 use-after-free](#61-检测-use-after-free)
    - [6.2 检测数据竞争](#62-检测数据竞争)
    - [6.3 检测内存泄漏](#63-检测内存泄漏)
  - [7. 故障排除](#7-故障排除)
    - [常见问题](#常见问题)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 CI/CD 集成](#81-cicd-集成)
    - [8.2 测试策略](#82-测试策略)
    - [8.3 文档和注释](#83-文档和注释)
  - [参考资源](#参考资源)

---

## 1. 安装与配置

### 1.1 安装 Miri

```bash
# 安装 Miri（需要 rustup）
rustup component add miri

# 如果 Miri 需要特定工具链
rustup run nightly rustup component add miri
```

### 1.2 更新 Miri

```bash
rustup update
rustup component add miri --force
```

### 1.3 验证安装

```bash
# 检查 Miri 版本
miri --version

# 运行简单测试
miri run --bin hello
```

---

## 2. 基础使用

### 2.1 运行单个文件

```bash
# 解释执行单个 Rust 文件
miri run file.rs

# 示例
miri run --edition 2021 example.rs
```

### 2.2 运行 Cargo 项目

```bash
# 在项目根目录下
cargo miri run              # 运行主程序
cargo miri run --bin app    # 运行特定 binary
cargo miri run --example ex # 运行示例

# 带参数运行
cargo miri run -- arg1 arg2
```

### 2.3 运行测试

```bash
# 运行所有测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 运行特定模块的测试
cargo miri test module_name
```

---

## 3. 检测的未定义行为

### 3.1 内存访问错误

| 错误类型 | 描述 | 示例 |
|----------|------|------|
| **Use after free** | 使用已释放内存 | 悬垂指针解引用 |
| **Out-of-bounds** | 越界访问 | 数组/切片越界 |
| **Unaligned access** | 未对齐访问 | 未对齐指针解引用 |
| **Invalid pointer** | 无效指针 | 空指针解引用 |

**示例 - Use after free：**

```rust
// test_ub.rs
unsafe fn use_after_free() {
    let ptr = Box::into_raw(Box::new(42));
    drop(Box::from_raw(ptr));  // 释放内存
    let _ = *ptr;  // ❌ UB: 使用已释放内存
}

fn main() {
    unsafe { use_after_free(); }
}
```

```bash
$ miri run test_ub.rs
error: Undefined Behavior: pointer to alloc1374 was dereferenced after this allocation got freed
```

### 3.2 借用规则违规

**Stacked Borrows / Tree Borrows 违规：**

```rust
// test_borrow.rs
unsafe fn stacked_borrows_violation() {
    let mut x = 5;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;

    *r1 = 10;  // 写入
    *r2 = 20;  // 另一个写入 - 可能违反别名规则
}

fn main() {
    unsafe { stacked_borrows_violation(); }
}
```

### 3.3 并发问题

| 错误类型 | 描述 |
|----------|------|
| **Data race** | 非同步的读写竞争 |
| **Unsync access** | 非线程安全类型的跨线程访问 |

---

## 4. 别名模型

### 4.1 Stacked Borrows

**默认别名模型**，基于栈结构跟踪借用：

```bash
# 使用 Stacked Borrows（默认）
MIRIFLAGS="-Zmiri-stacked-borrows" cargo miri run
```

**特点：**

- 更严格的别名检查
- 发现更多潜在的UB
- 可能误报某些合法代码

### 4.2 Tree Borrows

**新的别名模型**，基于树结构：

```bash
# 使用 Tree Borrows
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run
```

**特点：**

- 更精确的别名分析
- 支持更多合法模式
- 推荐用于新项目

**对比：**

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| 精确度 | 较保守 | 更精确 |
| 误报率 | 较高 | 较低 |
| 性能 | 快 | 稍慢 |
| 推荐 | 兼容性测试 | 新项目 |

---

## 5. 高级用法

### 5.1 环境变量

```bash
# 启用详细输出
MIRIFLAGS="-Zmiri-backtrace=full" cargo miri run

# 设置种子（用于随机化测试）
MIRIFLAGS="-Zmiri-seed=1234" cargo miri test

# 禁用隔离（允许文件系统访问）
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri run

# 跟踪特定内存分配
MIRIFLAGS="-Zmiri-track-alloc-id=123" cargo miri run
```

### 5.2 跳过某些检查

```bash
# 跳过栈对齐检查
MIRIFLAGS="-Zmiri-check-number-validity=no" cargo miri run

# 允许未对齐访问
MIRIFLAGS="-Zmiri-symbolic-alignment-check" cargo miri run
```

### 5.3 外部函数调用

Miri 默认不支持外部函数调用（FFI）：

```bash
# 允许特定的外部函数
MIRIFLAGS="-Zmiri-allow-ffi" cargo miri run
```

---

## 6. 实际案例

### 6.1 检测 use-after-free

```rust
// 不安全的链表实现
unsafe fn dangling_pointer() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;  // ptr指向局部变量
    }  // x在此处被释放

    println!("{}", *ptr);  // ❌ use-after-free
}
```

```bash
$ cargo miri run
error: Undefined Behavior: using stack memory after returning to caller
```

**修复：**

```rust
fn safe_version() {
    let x = 42;
    let ptr: *const i32 = &x;
    println!("{}", unsafe { *ptr });  // ✅ 在x的生命周期内使用
}
```

### 6.2 检测数据竞争

```rust
use std::thread;

fn data_race() {
    let mut data = 0;
    let ptr = &mut data as *mut i32;

    thread::scope(|s| {
        s.spawn(|| unsafe {
            *ptr = 1;  // 线程1写入
        });

        s.spawn(|| unsafe {
            *ptr = 2;  // 线程2写入 - 数据竞争！
        });
    });
}
```

```bash
$ cargo miri run
error: Undefined Behavior: Data race detected
```

**修复：**

```rust
use std::sync::{Arc, Mutex};

fn no_race() {
    let data = Arc::new(Mutex::new(0));

    thread::scope(|s| {
        let d1 = Arc::clone(&data);
        s.spawn(move || {
            *d1.lock().unwrap() = 1;  // ✅ 使用Mutex同步
        });

        let d2 = Arc::clone(&data);
        s.spawn(move || {
            *d2.lock().unwrap() = 2;
        });
    });
}
```

### 6.3 检测内存泄漏

```rust
fn memory_leak() {
    let data = Box::new([0u8; 1024 * 1024]);  // 1MB
    let _ptr = Box::into_raw(data);
    // ptr 被丢弃但没有 drop，内存泄漏
}
```

```bash
MIRIFLAGS="-Zmiri-ignore-leaks" cargo miri run  # 忽略泄漏
cargo miri run  # 默认会报告泄漏
```

---

## 7. 故障排除

### 常见问题

**问题1：Miri 太慢**

```bash
# 解决方案：只测试关键代码
# 使用条件编译
#[cfg(miri)]
mod miri_tests {
    // Miri 专用测试
}
```

**问题2：某些代码 Miri 无法运行**

```bash
# 跳过 Miri 测试
#[test]
#[cfg(not(miri))]  // 不在 Miri 下运行
fn test_native_only() {
    // 使用平台特定功能的测试
}
```

**问题3：Tree Borrows vs Stacked Borrows 差异**

```rust
// 某些代码在 Stacked Borrows 下报错但在 Tree Borrows 下通过
// 这通常是 Stacked Borrows 的误报
// 建议：使用 Tree Borrows 验证
```

---

## 8. 最佳实践

### 8.1 CI/CD 集成

```yaml
# .github/workflows/miri.yml
name: Miri

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Miri
        run: |
          rustup component add miri
          cargo miri setup
      - name: Test with Miri
        run: cargo miri test
```

### 8.2 测试策略

```rust
// tests/miri_tests.rs

#[test]
fn test_safe_abstraction() {
    // 测试 unsafe 封装的安全性
}

#[test]
fn test_complex_lifetimes() {
    // 测试复杂生命周期场景
}

#[test]
#[cfg_attr(miri, ignore)]  // Miri 下忽略
fn test_performance() {
    // 性能测试不需要 Miri
}
```

### 8.3 文档和注释

```rust
/// # Safety
///
/// 调用者必须保证：
/// - ptr 是有效的非空指针
/// - ptr 指向的内存已正确初始化
/// - ptr 的生命周期至少与返回值相同
///
/// Miri 验证：
/// ```
/// # cargo miri test
/// ```
unsafe fn dangerous_function(ptr: *const i32) -> i32 {
    *ptr
}
```

---

## 参考资源

- [Miri GitHub](https://github.com/rust-lang/miri)
- [Tree Borrows Paper](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)
- [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)

---

*通过 Miri 检测，可以确保 unsafe 代码的内存安全性，是 Rust 开发中不可或缺的工具。*
