# 调试工具 (Debugging Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐  
**更新日期**: 2025-10-20

---

## 📋 目录

- [调试工具 (Debugging Tools)](#调试工具-debugging-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. rust-gdb / rust-lldb (必备 ⭐⭐⭐⭐⭐)](#1-rust-gdb--rust-lldb-必备-)
      - [基础用法](#基础用法)
      - [GDB 常用命令](#gdb-常用命令)
      - [调试技巧](#调试技巧)
    - [2. cargo-expand (宏展开 🌟)](#2-cargo-expand-宏展开-)
      - [基础用法2](#基础用法2)
      - [示例](#示例)
    - [3. dbg! 宏 (内置)](#3-dbg-宏-内置)
    - [4. cargo-llvm-lines (代码膨胀分析)](#4-cargo-llvm-lines-代码膨胀分析)
    - [5. rust-analyzer 调试功能](#5-rust-analyzer-调试功能)
      - [VSCode 配置 (launch.json)](#vscode-配置-launchjson)
    - [6. tracing / log (运行时调试)](#6-tracing--log-运行时调试)
      - [使用示例](#使用示例)
    - [7. assert 系列宏](#7-assert-系列宏)
    - [8. 内存调试](#8-内存调试)
      - [AddressSanitizer (ASan)](#addresssanitizer-asan)
      - [ThreadSanitizer (TSan)](#threadsanitizer-tsan)
      - [MemorySanitizer (MSan)](#memorysanitizer-msan)
  - [💡 最佳实践](#-最佳实践)
    - [1. 调试构建配置](#1-调试构建配置)
    - [2. 条件编译调试代码](#2-条件编译调试代码)
    - [3. 日志级别控制](#3-日志级别控制)
    - [4. 调试宏](#4-调试宏)
  - [📊 调试策略](#-调试策略)
    - [调试流程](#调试流程)
    - [常见问题调试](#常见问题调试)
  - [🎯 实战技巧](#-实战技巧)
    - [技巧1: 交互式调试](#技巧1-交互式调试)
    - [技巧2: 条件日志](#技巧2-条件日志)
    - [技巧3: 断点注入](#技巧3-断点注入)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

Rust 的调试工具生态从简单的打印调试到高级的交互式调试器，从宏展开到 LLVM IR 查看，提供了全方位的调试支持。

---

## 🔧 核心工具

### 1. rust-gdb / rust-lldb (必备 ⭐⭐⭐⭐⭐)

**安装**: Rust 安装时自带  
**用途**: Rust 专用的 GDB/LLDB 包装器

#### 基础用法

```bash
# 使用 rust-gdb (Linux)
rust-gdb ./target/debug/my_app

# 使用 rust-lldb (macOS/Linux)
rust-lldb ./target/debug/my_app

# 带参数运行
rust-gdb --args ./target/debug/my_app arg1 arg2
```

#### GDB 常用命令

```gdb
# 运行
(gdb) run
(gdb) r

# 设置断点
(gdb) break main
(gdb) b src/main.rs:42
(gdb) b my_function

# 条件断点
(gdb) b main.rs:42 if x > 10

# 查看代码
(gdb) list
(gdb) l main.rs:40

# 单步执行
(gdb) step       # 进入函数
(gdb) next       # 下一行
(gdb) finish     # 执行到返回

# 查看变量
(gdb) print x
(gdb) p x
(gdb) p/x x      # 十六进制
(gdb) info locals

# 查看栈
(gdb) backtrace
(gdb) bt
(gdb) frame 2

# 查看类型
(gdb) ptype x
(gdb) whatis x

# 查看内存
(gdb) x/10x 0x7fffffffe000
```

#### 调试技巧

```rust
// 在代码中设置断点
#[inline(never)]
fn debug_point() {
    // GDB: break debug_point
}

fn main() {
    debug_point();  // 断点
    // 其他代码
}
```

---

### 2. cargo-expand (宏展开 🌟)

**安装**: `cargo install cargo-expand`  
**用途**: 展开宏，查看生成的代码

#### 基础用法2

```bash
# 展开整个 crate
cargo expand

# 展开特定模块
cargo expand module_name

# 展开特定项
cargo expand ::my_macro

# 美化输出
cargo expand | rustfmt
```

#### 示例

```rust
// 原始代码
#[derive(Debug, Clone)]
struct User {
    name: String,
    age: u32,
}

// cargo expand 后
impl ::core::fmt::Debug for User {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::debug_struct_field2_finish(
            f,
            "User",
            "name",
            &&self.name,
            "age",
            &&self.age,
        )
    }
}

impl ::core::clone::Clone for User {
    fn clone(&self) -> Self {
        Self {
            name: ::core::clone::Clone::clone(&self.name),
            age: ::core::clone::Clone::clone(&self.age),
        }
    }
}
```

---

### 3. dbg! 宏 (内置)

**用途**: 快速打印调试

```rust
fn main() {
    let x = 5;
    let y = 10;
    
    // 打印变量
    dbg!(x);  // [src/main.rs:4] x = 5
    
    // 打印表达式
    dbg!(x + y);  // [src/main.rs:7] x + y = 15
    
    // 链式调用中使用
    let result = vec![1, 2, 3]
        .iter()
        .map(|x| dbg!(x * 2))
        .collect::<Vec<_>>();
    
    // 打印多个值
    dbg!(x, y, x + y);
}
```

---

### 4. cargo-llvm-lines (代码膨胀分析)

**安装**: `cargo install cargo-llvm-lines`  
**用途**: 分析编译后的代码大小

```bash
# 分析 LLVM IR 行数
cargo llvm-lines

# 输出示例
  Lines        Copies         Function name
  -----        ------         -------------
  30737 (100%)   1107 (100%)  (TOTAL)
    1395 (4.5%)     83 (7.5%)  core::fmt::Formatter::pad
     915 (3.0%)      2 (0.2%)  alloc::slice::merge_sort
     855 (2.8%)      2 (0.2%)  alloc::raw_vec::RawVec<T,A>::reserve_for_push
```

---

### 5. rust-analyzer 调试功能

**用途**: IDE 集成调试

#### VSCode 配置 (launch.json)

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug executable",
      "cargo": {
        "args": ["build", "--bin=my_app", "--package=my_crate"]
      },
      "args": [],
      "cwd": "${workspaceFolder}"
    },
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug unit tests",
      "cargo": {
        "args": ["test", "--no-run", "--lib", "--package=my_crate"]
      },
      "args": [],
      "cwd": "${workspaceFolder}"
    }
  ]
}
```

---

### 6. tracing / log (运行时调试)

**添加依赖**:

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
```

#### 使用示例

```rust
use tracing::{debug, error, info, trace, warn};
use tracing_subscriber;

fn main() {
    // 初始化
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    info!("Application started");
    
    let user_id = 123;
    debug!("Processing user: {}", user_id);
    
    if let Err(e) = process_user(user_id) {
        error!("Failed to process user {}: {}", user_id, e);
    }
}

#[tracing::instrument]
fn process_user(user_id: u64) -> Result<(), Error> {
    info!("Fetching user data");
    // ...
    Ok(())
}
```

---

### 7. assert 系列宏

```rust
fn main() {
    // 基本断言
    assert!(x > 0);
    assert_eq!(x, 42);
    assert_ne!(x, 0);
    
    // 带消息
    assert!(x > 0, "x must be positive, got {}", x);
    
    // Debug 专用
    debug_assert!(expensive_check());
    debug_assert_eq!(x, y);
}
```

---

### 8. 内存调试

#### AddressSanitizer (ASan)

```bash
# 安装
rustup component add rust-src

# 使用 ASan
RUSTFLAGS="-Z sanitizer=address" \
cargo +nightly run --target x86_64-unknown-linux-gnu
```

#### ThreadSanitizer (TSan)

```bash
# 检测数据竞争
RUSTFLAGS="-Z sanitizer=thread" \
cargo +nightly run --target x86_64-unknown-linux-gnu
```

#### MemorySanitizer (MSan)

```bash
# 检测未初始化内存读取
RUSTFLAGS="-Z sanitizer=memory" \
cargo +nightly run --target x86_64-unknown-linux-gnu
```

---

## 💡 最佳实践

### 1. 调试构建配置

```toml
# Cargo.toml
[profile.dev]
opt-level = 0      # 不优化，便于调试
debug = true       # 包含调试信息
overflow-checks = true
lto = false

[profile.debug-optimized]
inherits = "dev"
opt-level = 1      # 轻微优化，保留可调试性
```

### 2. 条件编译调试代码

```rust
// 只在 debug 模式下编译
#[cfg(debug_assertions)]
fn debug_info() {
    println!("Debug build");
}

// 只在 test 模式下编译
#[cfg(test)]
mod tests {
    // 测试代码
}

// 自定义 feature
#[cfg(feature = "debug-utils")]
fn extra_debug() {
    // 额外的调试功能
}
```

### 3. 日志级别控制

```bash
# 设置日志级别
RUST_LOG=debug cargo run

# 模块级别控制
RUST_LOG=my_app=debug,my_lib=trace cargo run

# 复杂过滤
RUST_LOG="warn,my_app::module=debug" cargo run
```

### 4. 调试宏

```rust
// 自定义调试宏
macro_rules! debug_println {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        println!($($arg)*);
    };
}

// 使用
debug_println!("x = {}", x);  // 只在 debug 模式输出
```

---

## 📊 调试策略

### 调试流程

```text
1. 重现问题
   ├─ 编写最小复现用例
   └─ 确定输入和预期输出

2. 缩小范围
   ├─ 使用 dbg! 宏定位
   ├─ 添加日志输出
   └─ 二分查找问题代码

3. 深入调试
   ├─ 使用 GDB/LLDB 断点
   ├─ 查看变量状态
   └─ 分析调用栈

4. 理解原因
   ├─ 检查宏展开 (cargo expand)
   ├─ 查看生成的汇编 (cargo asm)
   └─ 分析类型推导

5. 验证修复
   ├─ 添加单元测试
   ├─ 回归测试
   └─ 代码审查
```

### 常见问题调试

**生命周期错误**:

```bash
# 1. 使用 rust-analyzer 查看推导的生命周期
# 2. 简化代码，逐步添加复杂度
# 3. 使用 `'static` 或 `Arc` 绕过
```

**trait 边界问题**:

```bash
# 1. cargo expand 查看展开的代码
# 2. 检查 trait 实现
# 3. 使用 where 子句明确约束
```

**性能问题**:

```bash
# 1. cargo flamegraph 找热点
# 2. cargo bench 对比优化
# 3. 使用 perf 深入分析
```

---

## 🎯 实战技巧

### 技巧1: 交互式调试

```gdb
# .gdbinit
set print pretty on
set pagination off
set confirm off

# 自定义命令
define pv
    print $arg0
    print *$arg0
end

# 使用
(gdb) pv my_variable
```

### 技巧2: 条件日志

```rust
use tracing::{info, debug};

#[tracing::instrument(level = "debug")]
fn process_item(item: &Item) -> Result<()> {
    if item.is_complex() {
        debug!("Processing complex item: {:?}", item);
    }
    // ...
    Ok(())
}
```

### 技巧3: 断点注入

```rust
#[cfg(debug_assertions)]
macro_rules! breakpoint {
    () => {
        #[allow(unused_unsafe)]
        unsafe {
            ::std::arch::asm!("int3");  // x86/x64
        }
    };
}

fn debug_this() {
    breakpoint!();  // 触发调试器断点
}
```

---

## 🔗 相关资源

- [GDB Manual](https://sourceware.org/gdb/documentation/)
- [LLDB Tutorial](https://lldb.llvm.org/use/tutorial.html)
- [cargo-expand](https://github.com/dtolnay/cargo-expand)
- [tracing Documentation](https://docs.rs/tracing/latest/tracing/)
- [Sanitizers in Rust](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html)

---

**导航**: [返回工具链层](../README.md) | [下一类别：文档工具](../documentation/README.md)
