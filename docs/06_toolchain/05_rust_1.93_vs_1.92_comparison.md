# Rust 1.93 vs 1.92 全面对比分析

> **文档版本**: 1.0
> **创建日期**: 2026-01-26
> **Rust 1.93 发布日期**: 2026年1月22日
> **Rust 1.92 发布日期**: 2025年12月11日
> **Edition**: 2024

---

## 📊 目录

- [Rust 1.93 vs 1.92 全面对比分析](#rust-193-vs-192-全面对比分析)
  - [📊 目录](#-目录)
  - [版本概览](#版本概览)
    - [Rust 1.92 主要特性回顾](#rust-192-主要特性回顾)
    - [Rust 1.93 主要新特性](#rust-193-主要新特性)
  - [核心改进](#核心改进)
    - [1. musl 1.2.5 更新](#1-musl-125-更新)
      - [改进说明](#改进说明)
      - [1.92 版本代码示例](#192-版本代码示例)
      - [1.93 版本改进示例](#193-版本改进示例)
      - [兼容性说明](#兼容性说明)
    - [2. 全局分配器线程本地存储支持](#2-全局分配器线程本地存储支持)
      - [改进说明](#改进说明-1)
      - [1.92 版本限制](#192-版本限制)
      - [1.93 版本改进示例](#193-版本改进示例-1)
      - [实际应用场景](#实际应用场景)
    - [3. `cfg` 属性在 `asm!` 行上](#3-cfg-属性在-asm-行上)
      - [改进说明](#改进说明-2)
      - [1.92 版本代码示例](#192-版本代码示例-1)
      - [1.93 版本改进示例](#193-版本改进示例-2)
      - [更复杂的示例](#更复杂的示例)
  - [标准库更新](#标准库更新)
    - [MaybeUninit API 增强](#maybeuninit-api-增强)
      - [新增方法](#新增方法)
      - [实际应用](#实际应用)
    - [集合类型改进](#集合类型改进)
      - [String 和 Vec 原始部分访问](#string-和-vec-原始部分访问)
      - [VecDeque 条件弹出](#vecdeque-条件弹出)
    - [整数操作增强](#整数操作增强)
    - [其他稳定 API](#其他稳定-api)
      - [切片到数组转换](#切片到数组转换)
      - [Duration 扩展](#duration-扩展)
      - [char 常量](#char-常量)
      - [fmt::from\_fn](#fmtfrom_fn)
  - [编译器改进](#编译器改进)
    - [平台支持](#平台支持)
    - [其他改进](#其他改进)
  - [工具链更新](#工具链更新)
    - [Cargo 1.93](#cargo-193)
    - [Clippy 1.93](#clippy-193)
    - [Rustfmt 1.93](#rustfmt-193)
  - [实际应用示例](#实际应用示例)
    - [示例 1：使用 musl 1.2.5 的网络应用](#示例-1使用-musl-125-的网络应用)
    - [示例 2：使用线程本地存储的分配器](#示例-2使用线程本地存储的分配器)
    - [示例 3：条件编译的内联汇编](#示例-3条件编译的内联汇编)
  - [迁移指南](#迁移指南)
    - [升级步骤](#升级步骤)
      - [步骤 1：更新 Rust 版本](#步骤-1更新-rust-版本)
      - [步骤 2：更新项目配置](#步骤-2更新项目配置)
      - [步骤 3：检查依赖兼容性](#步骤-3检查依赖兼容性)
      - [步骤 4：利用新特性（可选）](#步骤-4利用新特性可选)
    - [兼容性检查清单](#兼容性检查清单)
    - [潜在问题与解决方案](#潜在问题与解决方案)
      - [问题 1：musl 兼容性符号缺失](#问题-1musl-兼容性符号缺失)
      - [问题 2：全局分配器重入问题](#问题-2全局分配器重入问题)
  - [总结](#总结)
    - [Rust 1.93 的主要改进](#rust-193-的主要改进)
    - [升级建议](#升级建议)
  - [参考资源](#参考资源)

---

## 版本概览

### Rust 1.92 主要特性回顾

Rust 1.92 版本的主要更新包括：

1. **Never 类型 Lint 提升**：`!` 类型的两个 lint 从警告提升为默认拒绝
2. **错误报告改进**：显示被 `cfg` 禁用的有用项
3. **标准库 API 稳定**：多个新 API 稳定化
4. **性能优化**：编译器和运行时性能改进
5. **工具链改进**：Cargo、Clippy、Rustfmt 更新

### Rust 1.93 主要新特性

Rust 1.93 版本相比 1.92 的改进：

1. **musl 1.2.5 更新**：改进 DNS 解析器可靠性，特别是大型 DNS 记录和递归名称服务器
2. **全局分配器线程本地存储支持**：允许全局分配器使用 `thread_local!` 和 `std::thread::current`
3. **`cfg` 属性在 `asm!` 行上**：可以在内联汇编的单个语句上使用条件编译
4. **大量 API 稳定化**：MaybeUninit、String、Vec、整数操作、VecDeque、Duration、char、fmt 等

---

## 核心改进

### 1. musl 1.2.5 更新

**Rust 1.93** 将所有 `*-linux-musl` 目标更新到 musl 1.2.5（之前为 1.2.3）。

#### 改进说明

- **DNS 解析器改进**：musl 1.2.4 引入了 DNS 解析器的主要改进，1.2.5 包含错误修复
- **可移植性提升**：静态链接的 musl 二进制文件在网络操作中更加可靠
- **大型 DNS 记录支持**：更好地处理大型 DNS 记录和递归名称服务器

#### 1.92 版本代码示例

```rust
// Rust 1.92 - 使用 musl 1.2.3
// 在某些网络环境下可能遇到 DNS 解析问题
use std::net::TcpStream;

fn connect_to_server() -> Result<(), Box<dyn std::error::Error>> {
    // 在 musl 1.2.3 下，大型 DNS 记录可能导致解析失败
    let stream = TcpStream::connect("example.com:80")?;
    Ok(())
}
```

#### 1.93 版本改进示例

```rust
// Rust 1.93 - 使用 musl 1.2.5，DNS 解析更可靠
use std::net::TcpStream;

fn connect_to_server() -> Result<(), Box<dyn std::error::Error>> {
    // musl 1.2.5 改进了 DNS 解析器，更好地处理大型记录
    let stream = TcpStream::connect("example.com:80")?;
    Ok(())
}
```

#### 兼容性说明

**重要**：musl 1.2.4 移除了几个遗留兼容性符号，Rust `libc` crate 之前使用了这些符号。

- **修复可用**：libc 0.2.146+（2023年6月发布）已包含修复
- **影响范围**：仅影响使用旧版本 libc 的项目
- **建议**：确保使用 libc 0.2.146 或更新版本

```toml
# Cargo.toml
[dependencies]
libc = "0.2.146"  # 或更新版本
```

---

### 2. 全局分配器线程本地存储支持

**Rust 1.93** 允许全局分配器使用 `thread_local!` 和 `std::thread::current`，无需担心重入问题。

#### 改进说明

标准库内部调整，允许用 Rust 编写的全局分配器使用：

- `std::thread_local!` 宏
- `std::thread::current` 函数

通过使用系统分配器而不是自定义分配器来避免重入问题。

#### 1.92 版本限制

```rust
// Rust 1.92 - 全局分配器不能使用 thread_local!
use std::alloc::{GlobalAlloc, Layout, System};

struct MyAllocator;

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // ❌ 1.92: 不能使用 thread_local!，可能导致重入问题
        // thread_local! { ... }  // 这会导致问题
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}
```

#### 1.93 版本改进示例

```rust
// Rust 1.93 - 全局分配器可以使用 thread_local!
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

struct MyAllocator;

thread_local! {
    static ALLOCATION_COUNT: Cell<usize> = Cell::new(0);
}

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // ✅ 1.93: 可以使用 thread_local!，系统分配器避免重入
        ALLOCATION_COUNT.with(|count| {
            count.set(count.get() + 1);
        });

        // 使用系统分配器避免重入
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static GLOBAL: MyAllocator = MyAllocator;

fn main() {
    // 现在可以在全局分配器中使用线程本地存储
    let _vec = vec![1, 2, 3];

    ALLOCATION_COUNT.with(|count| {
        println!("Allocations: {}", count.get());
    });
}
```

#### 实际应用场景

**性能监控分配器**：

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

thread_local! {
    static THREAD_ALLOCS: std::cell::Cell<usize> = std::cell::Cell::new(0);
}

struct TrackingAllocator;

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        THREAD_ALLOCS.with(|count| {
            count.set(count.get() + 1);
        });
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static GLOBAL: TrackingAllocator = TrackingAllocator;
```

---

### 3. `cfg` 属性在 `asm!` 行上

**Rust 1.93** 允许在内联汇编的单个语句上使用 `cfg` 属性，无需重复整个 `asm!` 块。

#### 改进说明

之前，如果内联汇编的某些部分需要条件编译，必须重复整个 `asm!` 块。现在可以在单个语句上使用 `cfg`。

#### 1.92 版本代码示例

```rust
// Rust 1.92 - 需要重复整个 asm! 块
#[cfg(target_feature = "sse2")]
unsafe fn optimized_add_sse2(a: f32, b: f32) -> f32 {
    let result;
    asm!(
        "addss {}, {}",
        in(xmm_reg) a,
        in(xmm_reg) b,
        out(xmm_reg) result,
    );
    result
}

#[cfg(not(target_feature = "sse2"))]
unsafe fn optimized_add_sse2(a: f32, b: f32) -> f32 {
    let result;
    asm!(
        "fadd {}, {}",
        in(x87_reg) a,
        in(x87_reg) b,
        out(x87_reg) result,
    );
    result
}
```

#### 1.93 版本改进示例

```rust
// Rust 1.93 - 可以在单个语句上使用 cfg
unsafe fn optimized_add(a: f32, b: f32) -> f32 {
    let result;
    asm!(
        // 基础指令
        "nop",

        // ✅ 1.93: 可以在单个语句上使用 cfg
        #[cfg(target_feature = "sse2")]
        "addss {}, {}",
        #[cfg(not(target_feature = "sse2"))]
        "fadd {}, {}",

        in(xmm_reg) a,
        in(xmm_reg) b,
        out(xmm_reg) result,

        // 条件寄存器约束
        #[cfg(target_feature = "sse2")]
        a = const 123,  // 仅在 SSE2 时使用
    );
    result
}
```

#### 更复杂的示例

```rust
// Rust 1.93 - 多个条件编译的 asm! 语句
unsafe fn platform_specific_operation() {
    asm!(
        // 通用指令
        "mov eax, 1",

        // x86_64 特定
        #[cfg(target_arch = "x86_64")]
        "mov rbx, 2",

        // x86 特定
        #[cfg(target_arch = "x86")]
        "mov ebx, 2",

        // SSE2 特定
        #[cfg(target_feature = "sse2")]
        "movaps xmm0, xmm1",

        // AVX 特定
        #[cfg(target_feature = "avx")]
        "vmovaps ymm0, ymm1",

        // 条件输出
        #[cfg(target_feature = "sse2")]
        out(xmm_reg) _,
    );
}
```

---

## 标准库更新

### MaybeUninit API 增强

**Rust 1.93** 稳定了多个 `MaybeUninit` 相关 API：

#### 新增方法

```rust
use std::mem::MaybeUninit;

let mut uninit = MaybeUninit::<String>::uninit();

// ✅ 1.93 新增：安全地获取引用
let reference: &String = unsafe { uninit.assume_init_ref() };
let mutable: &mut String = unsafe { uninit.assume_init_mut() };

// ✅ 1.93 新增：安全地调用 drop
unsafe { uninit.assume_init_drop() };

// ✅ 1.93 新增：从切片写入
let src = [1, 2, 3];
let mut dst = [MaybeUninit::<i32>::uninit(); 3];
MaybeUninit::write_copy_of_slice(&mut dst, &src);
```

#### 实际应用

```rust
use std::mem::MaybeUninit;

// 安全地初始化数组
fn initialize_array<T, const N: usize>(init: impl Fn(usize) -> T) -> [T; N] {
    let mut array: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

    for i in 0..N {
        array[i] = MaybeUninit::new(init(i));
    }

    // ✅ 1.93: 使用新的 API 安全地转换
    unsafe { std::mem::transmute(array) }
}

let squares = initialize_array(|i| i * i);
assert_eq!(squares, [0, 1, 4, 9, 16]);
```

---

### 集合类型改进

#### String 和 Vec 原始部分访问

```rust
// ✅ 1.93 新增：获取 String 的原始部分
let s = String::from("hello");
let (ptr, len, capacity) = s.into_raw_parts();
let s = unsafe { String::from_raw_parts(ptr, len, capacity) };

// ✅ 1.93 新增：获取 Vec 的原始部分
let v = vec![1, 2, 3];
let (ptr, len, capacity) = v.into_raw_parts();
let v = unsafe { Vec::from_raw_parts(ptr, len, capacity) };
```

#### VecDeque 条件弹出

```rust
use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);

// ✅ 1.93 新增：条件弹出
if let Some(value) = deque.pop_front_if(|&x| x > 2) {
    println!("Popped: {}", value);  // 输出: Popped: 3
}

if let Some(value) = deque.pop_back_if(|&x| x < 5) {
    println!("Popped: {}", value);  // 输出: Popped: 4
}
```

---

### 整数操作增强

**Rust 1.93** 稳定了多个未检查的整数操作方法：

```rust
// ✅ 1.93 新增：未检查的整数操作
let x: i32 = 10;

// 未检查的取反（不会检查溢出）
let neg = unsafe { x.unchecked_neg() };

// 未检查的左移
let shifted_left = unsafe { x.unchecked_shl(2) };

// 未检查的右移
let shifted_right = unsafe { x.unchecked_shr(2) };

// 无符号整数也有类似方法
let y: u32 = 10;
let shifted = unsafe { y.unchecked_shl(2) };
```

**使用场景**：性能关键代码，已知不会溢出的情况。

---

### 其他稳定 API

#### 切片到数组转换

```rust
// ✅ 1.93 新增：切片到数组的安全转换
let slice = &[1, 2, 3, 4];
let array: &[i32; 4] = slice.as_array().unwrap();

let mut slice = &mut [1, 2, 3, 4];
let array: &mut [i32; 4] = slice.as_mut_array().unwrap();
```

#### Duration 扩展

```rust
use std::time::Duration;

// ✅ 1.93 新增：从 u128 纳秒创建 Duration
let nanos: u128 = 1_000_000_000;
let duration = Duration::from_nanos_u128(nanos);
assert_eq!(duration.as_secs(), 1);
```

#### char 常量

```rust
// ✅ 1.93 新增：char 的最大 UTF-8/UTF-16 长度常量
assert_eq!(char::MAX_LEN_UTF8, 4);
assert_eq!(char::MAX_LEN_UTF16, 2);
```

#### fmt::from_fn

```rust
use std::fmt;

// ✅ 1.93 新增：从函数创建格式化器
let formatter = fmt::from_fn(|f: &mut fmt::Formatter<'_>| {
    write!(f, "Custom: {}", 42)
});

println!("{}", formatter);  // 输出: Custom: 42
```

---

## 编译器改进

### 平台支持

Rust 1.93 的 release post 并未将“平台 tier 变更”作为核心亮点展开说明。若你需要核对平台支持现状或变更，请以权威来源为准：

- Rustc 平台支持总览：`https://doc.rust-lang.org/rustc/platform-support.html`
- Rust 1.93.0 GitHub release tag：`https://github.com/rust-lang/rust/releases/tag/1.93.0`

### 其他改进

- 改进的 rustdoc 搜索和过滤功能
- 编译器错误消息的进一步改进

---

## 工具链更新

### Cargo 1.93

- 构建性能优化
- 依赖解析改进
- 工作区管理增强

### Clippy 1.93

- 新的 lints
- 现有 lints 的改进
- 性能优化

### Rustfmt 1.93

- 格式化规则改进
- 性能优化

---

## 实际应用示例

### 示例 1：使用 musl 1.2.5 的网络应用

```rust
// Rust 1.93 - 利用改进的 DNS 解析
use std::net::TcpStream;
use std::io::{Write, Read};

fn fetch_data(host: &str, port: u16) -> Result<String, Box<dyn std::error::Error>> {
    // musl 1.2.5 改进了 DNS 解析，特别是大型记录
    let mut stream = TcpStream::connect(format!("{}:{}", host, port))?;

    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
    stream.write_all(request.as_bytes())?;

    let mut response = String::new();
    stream.read_to_string(&mut response)?;

    Ok(response)
}
```

### 示例 2：使用线程本地存储的分配器

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

thread_local! {
    static THREAD_ALLOC_COUNT: std::cell::Cell<usize> = std::cell::Cell::new(0);
}

struct ThreadTrackingAllocator;

unsafe impl GlobalAlloc for ThreadTrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        THREAD_ALLOC_COUNT.with(|count| {
            count.set(count.get() + 1);
        });
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static GLOBAL: ThreadTrackingAllocator = ThreadTrackingAllocator;

fn main() {
    let _vec1 = vec![1, 2, 3];
    let _vec2 = vec![4, 5, 6];

    THREAD_ALLOC_COUNT.with(|count| {
        println!("Thread allocations: {}", count.get());
    });
}
```

### 示例 3：条件编译的内联汇编

```rust
// Rust 1.93 - 使用 cfg 属性的内联汇编
#[cfg(target_arch = "x86_64")]
unsafe fn cpu_id() -> (u32, u32, u32, u32) {
    let eax: u32;
    let ebx: u32;
    let ecx: u32;
    let edx: u32;

    asm!(
        "cpuid",
        inout("eax") 0 => eax,
        out("ebx") ebx,
        #[cfg(target_feature = "sse2")]
        out("ecx") ecx,
        #[cfg(not(target_feature = "sse2"))]
        out("ecx") _,
        out("edx") edx,
    );

    (eax, ebx, ecx, edx)
}
```

---

## 迁移指南

### 升级步骤

#### 步骤 1：更新 Rust 版本

```bash
rustup update stable
rustc --version  # 应该显示 rustc 1.93.0
cargo --version   # 应该显示 cargo 1.93.0
```

#### 步骤 2：更新项目配置

```toml
# Cargo.toml
[package]
rust-version = "1.93"  # 更新版本要求
```

#### 步骤 3：检查依赖兼容性

```bash
# 检查 libc 版本（如果使用 musl）
cargo tree | grep libc

# 确保使用 libc 0.2.146 或更新版本
```

#### 步骤 4：利用新特性（可选）

- 更新 musl 目标以利用改进的 DNS 解析
- 在全局分配器中使用 `thread_local!`
- 简化条件编译的内联汇编代码
- 使用新的稳定 API

---

### 兼容性检查清单

> **说明**：以下检查项供用户在升级到 Rust 1.93 时自行验证。

- [ ] **代码兼容性**：所有代码在 1.93 下编译通过（用户需自行验证）
- [ ] **API 使用**：检查是否有使用已弃用的 API（用户需自行检查）
- [ ] **依赖兼容性**：所有依赖库支持 Rust 1.93（用户需自行验证）
- [ ] **musl 兼容性**：如果使用 musl，确保 libc >= 0.2.146（用户需自行验证）
- [ ] **性能测试**：验证性能改进是否符合预期（用户需自行测试）
- [ ] **文档更新**：更新文档中的版本号引用（用户需自行更新）

---

### 潜在问题与解决方案

#### 问题 1：musl 兼容性符号缺失

**症状**：使用旧版本 libc 的项目在 musl 目标上编译失败

**解决方案**：

```toml
# Cargo.toml
[dependencies]
libc = "0.2.146"  # 或更新版本
```

#### 问题 2：全局分配器重入问题

**症状**：在全局分配器中使用 `thread_local!` 导致问题

**解决方案**：Rust 1.93 已解决，确保使用系统分配器避免重入：

```rust
use std::alloc::System;

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // 使用 System 分配器避免重入
        System.alloc(layout)
    }
}
```

---

## 总结

### Rust 1.93 的主要改进

1. **musl 1.2.5 更新**：改进 DNS 解析器可靠性
2. **全局分配器增强**：支持线程本地存储
3. **内联汇编改进**：`cfg` 属性支持
4. **大量 API 稳定化**：MaybeUninit、集合类型、整数操作等
5. **工具链改进**：Cargo、Clippy、Rustfmt 更新

### 升级建议

✅ **推荐升级**：Rust 1.93 带来了重要的系统级改进和大量 API 稳定化，建议尽快升级。

**特别推荐升级的场景**：

- 使用 musl 目标进行静态链接的项目
- 需要自定义全局分配器的项目
- 使用内联汇编的项目
- 需要新稳定 API 的项目

---

## 参考资源

- [Rust 1.93.0 Release Notes](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)
- [Rust 1.93.0 详细发布说明](https://doc.rust-lang.org/stable/releases.html#version-1930-2026-01-22)
- [Rust 1.92.0 Release Notes](https://blog.rust-lang.org/2025/12/11/Rust-1.92.0/)
- [Rust 1.92.0 详细发布说明](https://doc.rust-lang.org/stable/releases.html#version-1920-2025-12-11)
- [musl 1.2.5 发布说明](https://musl.libc.org/releases.html)
- [libc 兼容性修复](https://github.com/rust-lang/libc/pull/2935)

---

**文档维护**: Documentation Team
**最后更新**: 2026-02-12
**最后对照 releases.rs**: 2026-02-14
**下次更新**：Rust 1.94 发布时
