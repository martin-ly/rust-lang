# FFI 实战指南

> **创建日期**: 2025-12-11
> **最后更新**: 2026-03-17
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成

**FFI (Foreign Function Interface)** 是 Rust 与外部代码交互的核心机制。本指南涵盖从 C 到 Rust、Rust 到 C、以及 Rust 到 WebAssembly 的完整实践方案，适用于生产环境开发。

---

## 目录

- [FFI 实战指南](#ffi-实战指南)
  - [目录](#目录)
  - [1. FFI 基础概念](#1-ffi-基础概念)
    - [1.1 什么是 FFI](#11-什么是-ffi)
    - [1.2 FFI 安全边界](#12-ffi-安全边界)
    - [1.3 ABI 与调用约定](#13-abi-与调用约定)
  - [2. bindgen - C/C++ → Rust](#2-bindgen---cc--rust)
    - [2.1 安装与配置](#21-安装与配置)
    - [2.2 基础绑定生成](#22-基础绑定生成)
    - [2.3 build.rs 配置详解](#23-buildrs-配置详解)
    - [2.4 处理结构体和回调](#24-处理结构体和回调)
    - [2.5 C++ 支持](#25-c-支持)
    - [2.6 常见问题](#26-常见问题)
    - [2.7 实战：SQLite 绑定](#27-实战sqlite-绑定)
  - [3. cbindgen - Rust → C/C++](#3-cbindgen---rust--cc)
    - [3.1 安装与配置](#31-安装与配置)
    - [3.2 生成 C 头文件](#32-生成-c-头文件)
    - [3.3 cbindgen.toml 配置详解](#33-cbindgentoml-配置详解)
    - [3.4 不透明指针模式](#34-不透明指针模式)
    - [3.5 常见问题](#35-常见问题)
    - [3.6 实战：Rust 库供 C 调用](#36-实战rust-库供-c-调用)
  - [4. wasm-bindgen - Rust → Web](#4-wasm-bindgen---rust--web)
    - [4.1 安装与配置](#41-安装与配置)
    - [4.2 基础设置](#42-基础设置)
    - [4.3 类型映射](#43-类型映射)
    - [4.4 与 Web API 集成](#44-与-web-api-集成)
    - [4.5 常见问题](#45-常见问题)
    - [4.6 实战：WASM 图像处理模块](#46-实战wasm-图像处理模块)
  - [5. 内存管理最佳实践](#5-内存管理最佳实践)
    - [5.1 内存所有权规则](#51-内存所有权规则)
    - [5.2 内存管理模式](#52-内存管理模式)
    - [5.3 字符串处理](#53-字符串处理)
    - [5.4 生命周期管理](#54-生命周期管理)
  - [6. 错误处理策略](#6-错误处理策略)
    - [6.1 错误码设计](#61-错误码设计)
    - [6.2 错误传播模式](#62-错误传播模式)
    - [6.3 Panic 安全](#63-panic-安全)
  - [7. 线程安全考虑](#7-线程安全考虑)
    - [7.1 Send 和 Sync](#71-send-和-sync)
    - [7.2 线程安全模式](#72-线程安全模式)
    - [7.3 跨线程数据传递](#73-跨线程数据传递)
  - [8. 完整项目示例](#8-完整项目示例)
    - [8.1 项目概述](#81-项目概述)
    - [8.2 Rust 核心库](#82-rust-核心库)
    - [8.3 C 绑定](#83-c-绑定)
    - [8.4 Python 绑定](#84-python-绑定)
    - [8.5 构建系统](#85-构建系统)
  - [9. 调试与测试](#9-调试与测试)
    - [9.1 Miri 验证](#91-miri-验证)
    - [9.2 Valgrind](#92-valgrind)
    - [9.3 AddressSanitizer](#93-addresssanitizer)
  - [10. C/C++ 互操作最佳实践](#10-cc-互操作最佳实践)
    - [10.1 类型安全](#101-类型安全)
    - [10.2 设计模式](#102-设计模式)
    - [10.3 性能优化](#103-性能优化)
  - [工具对比表](#工具对比表)
  - [安全注意事项清单](#安全注意事项清单)
    - [FFI 函数设计](#ffi-函数设计)
    - [内存安全](#内存安全)
    - [类型安全](#类型安全)
    - [线程安全](#线程安全)
  - [参考资源](#参考资源)
  - [Rust 1.94 在 FFI 开发中的应用](#rust-194-在-ffi-开发中的应用)
    - [LazyLock 在 C 库句柄管理中的应用](#lazylock-在-c-库句柄管理中的应用)
    - [ControlFlow 在错误处理转换中的应用](#controlflow-在错误处理转换中的应用)

---

## 1. FFI 基础概念

### 1.1 什么是 FFI

FFI (Foreign Function Interface) 允许 Rust 代码与其他语言编写的代码进行交互。最常见的场景是与 C/C++ 代码互操作，因为 C 的 ABI 是大多数系统的标准。

```
┌─────────────────────────────────────────────────────────────────┐
│                     FFI 架构概览                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   ┌──────────────┐         ┌──────────────┐                    │
│   │   Rust 代码   │ ←────→ │  FFI 边界层   │ ←────→ C/C++ 代码  │
│   │              │         │              │                    │
│   │ • 安全抽象    │         │ • unsafe 块   │                    │
│   │ • 所有权管理  │         │ • 类型转换    │                    │
│   │ • 错误处理    │         │ • 内存管理    │                    │
│   └──────────────┘         └──────────────┘                    │
│         ↑                          ↑                           │
│         │                          │                           │
│   bindgen (C→Rust)           cbindgen (Rust→C)                 │
│   wasm-bindgen (Rust→JS)                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 FFI 安全边界

当 Rust 与外部代码交互时，编译器的安全保证不再适用。理解这个边界对编写正确的 FFI 代码至关重要：

```rust
// 在 Safe Rust 中，以下情况不可能发生
fn safe_rust() {
    let x = vec![1, 2, 3];
    // 编译器防止 use-after-free、double-free 等问题
}

// 在 FFI 边界，必须手动保证安全性
/// # Safety
/// - ptr 必须是非空且正确对齐的有效指针
/// - ptr 必须由 create_data 分配且未被释放
/// - 调用后 ptr 无效，不可再次使用
#[no_mangle]
pub unsafe extern "C" fn free_data(ptr: *mut Data) {
    if !ptr.is_null() {
        // SAFETY: 调用者保证 ptr 的有效性
        unsafe { drop(Box::from_raw(ptr)); }
    }
}
```

### 1.3 ABI 与调用约定

ABI (Application Binary Interface) 定义了函数调用时参数传递、返回值处理、栈管理等规则。

| 调用约定 | Rust 语法 | 适用平台 |
|---------|----------|---------|
| C 标准 | `extern "C"` | 所有平台（推荐） |
| Windows | `extern "stdcall"` | Windows 32-bit |
| Windows 64 | `extern "win64"` | Windows 64-bit |
| System V | `extern "sysv64"` | Linux/macOS x86_64 |
| 向量调用 | `extern "vectorcall"` | Windows |

```rust
// 标准 C 调用约定 - 最常用，跨平台兼容
#[no_mangle]
pub extern "C" fn process_data(data: *const u8, len: usize) -> i32 {
    // ...
}

// C++ 名称修饰（用于 C++ 互操作）
#[no_mangle]
pub extern "C++" fn cpp_function(x: i32) -> i32 {
    // ...
}
```

---

## 2. bindgen - C/C++ → Rust

**bindgen** 自动生成 Rust FFI 绑定，从 C/C++ 头文件创建 Rust 接口。

### 2.1 安装与配置

```bash
# 安装 bindgen CLI 工具
cargo install bindgen-cli

# 需要 LLVM/Clang 支持
# Ubuntu/Debian
sudo apt-get install libclang-dev

# macOS
brew install llvm

# Windows (使用 Chocolatey)
choco install llvm
```

**Cargo.toml 配置：**

```toml
[package]
name = "my-ffi-project"
version = "0.1.0"
edition = "2021"

[dependencies]
libc = "0.2"
thiserror = "1.0"

[build-dependencies]
bindgen = "0.69"
cc = "1.0"  # 用于编译 C 代码
```

### 2.2 基础绑定生成

```bash
# 基础生成命令
bindgen wrapper.h -o src/bindings.rs

# 包含 C++ 支持
bindgen wrapper.hpp --enable-cxx-namespaces -o src/bindings.rs

# 使用特定 clang 参数
bindgen wrapper.h --clang-arg="-I/usr/local/include" --clang-arg="-std=c99"
```

### 2.3 build.rs 配置详解

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // 1. 链接 C 库配置
    println!("cargo:rustc-link-lib=mylib");
    println!("cargo:rustc-link-search=native=/usr/local/lib");

    // 2. 重新构建触发条件
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=/usr/local/lib/libmylib.a");
    println!("cargo:rerun-if-changed=build.rs");

    // 3. 生成绑定配置
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // C++ 支持（如果需要）
        .clang_arg("-x")
        .clang_arg("c++")
        .clang_arg("-std=c++17")
        // 系统头文件路径
        .clang_arg("-I/usr/local/include")
        .clang_arg("-I/usr/include")
        // 类型配置
        .size_t_is_usize(true)
        .translate_enum_integer_types(true)
        // 黑名单（排除不需要的项）
        .blocklist_item("__.*")  // 排除双下划线开头的内部项
        .blocklist_function(".*_internal")  // 排除内部函数
        .blocklist_file(".*stdint.h")
        // 白名单（只包含需要的项）
        .allowlist_function("mylib_.*")
        .allowlist_type("mylib_.*")
        .allowlist_var("MYLIB_.*")
        // 生成选项
        .derive_debug(true)
        .derive_default(true)
        .impl_debug(true)
        .impl_partialeq(true)
        .generate_comments(true)
        // 布局测试（CI 中很有用）
        .layout_tests(cfg!(feature = "layout-tests"))
        // C++ 命名空间支持
        .enable_cxx_namespaces()
        // 生成绑定
        .generate()
        .expect("Unable to generate bindings");

    // 4. 写入绑定文件
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

**wrapper.h 示例：**

```c
#ifndef WRAPPER_H
#define WRAPPER_H

// 只包含需要暴露的接口
#include <mylib/core.h>
#include <mylib/utils.h>

// 排除不需要的部分
#undef MYLIB_INTERNAL_API

#endif // WRAPPER_H
```

**lib.rs 中使用：**

```rust
// src/lib.rs
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

// 包含生成的绑定
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// 安全包装模块
pub mod safe {
    use super::*;
    use std::ffi::{CStr, CString};
    use std::os::raw::c_char;

    /// 安全获取版本字符串
    pub fn get_version() -> String {
        unsafe {
            let ptr = mylib_get_version();
            CStr::from_ptr(ptr)
                .to_string_lossy()
                .into_owned()
        }
    }
}
```

### 2.4 处理结构体和回调

**C 头文件定义：**

```c
// mylib.h
typedef struct {
    const char* name;
    int age;
    void* user_data;
} person_t;

typedef void (*progress_cb)(int percent, void* user_data);

typedef struct {
    int (*read)(void* buf, size_t len, void* user_data);
    int (*write)(const void* buf, size_t len, void* user_data);
    void* user_data;
} io_callbacks_t;

int process_persons(
    const person_t* persons,
    size_t count,
    progress_cb callback,
    void* user_data
);
```

**Rust 安全封装：**

```rust
use std::ffi::{c_char, c_int, c_void, CStr, CString};

/// 安全的人结构体
#[derive(Debug)]
pub struct Person<'a> {
    pub name: &'a str,
    pub age: i32,
}

/// 进度回调类型
pub type ProgressFn = Box<dyn FnMut(i32) + Send>;

/// 用户数据包装
struct CallbackData {
    callback: ProgressFn,
}

/// 从 C 调用的 trampoline 函数
unsafe extern "C" fn progress_trampoline(
    percent: c_int,
    user_data: *mut c_void,
) {
    let data = &mut *(user_data as *mut CallbackData);
    (data.callback)(percent);
}

/// 安全的人处理函数
pub fn process_persons_safe<F>(
    persons: &[Person],
    mut progress: F,
) -> Result<(), String>
where
    F: FnMut(i32) + Send + 'static,
{
    // 转换 Rust 结构体为 C 结构体
    let c_strings: Vec<CString> = persons
        .iter()
        .map(|p| CString::new(p.name).expect("invalid name"))
        .collect();

    let c_persons: Vec<bindings::person_t> = c_strings
        .iter()
        .zip(persons.iter())
        .map(|(name, p)| bindings::person_t {
            name: name.as_ptr(),
            age: p.age,
            user_data: std::ptr::null_mut(),
        })
        .collect();

    // 准备回调
    let mut callback_data = CallbackData {
        callback: Box::new(progress),
    };

    let result = unsafe {
        bindings::process_persons(
            c_persons.as_ptr(),
            c_persons.len(),
            Some(progress_trampoline),
            &mut callback_data as *mut _ as *mut c_void,
        )
    };

    if result == 0 {
        Ok(())
    } else {
        Err(format!("process failed: {}", result))
    }
}
```

### 2.5 C++ 支持

```rust
// build.rs
let bindings = bindgen::Builder::default()
    .header("wrapper.hpp")
    .clang_arg("-x")
    .clang_arg("c++")
    .clang_arg("-std=c++17")
    // 命名空间支持
    .enable_cxx_namespaces()
    // 类模板支持
    .whitelist_type("MyTemplate.*")
    // 虚函数表支持
    .vtable_generation(true)
    // 生成 C++ 方法
    .generate_inline_functions(true)
    .generate()
    .expect("Failed to generate C++ bindings");
```

### 2.6 常见问题

**问题 1: 找不到头文件**

```rust
// 解决方案：指定 include 路径
.clang_arg("-I/path/to/includes")
.clang_arg("-I/usr/local/include")
```

**问题 2: 宏定义未展开**

```rust
// 解决方案：定义预处理宏
.clang_arg("-DMYLIB_EXPORT")
.clang_arg("-DAPI_VERSION=2")
```

**问题 3: 平台特定代码**

```rust
// 解决方案：条件编译
#[cfg(target_os = "linux")]
let bindings = bindgen::Builder::default()
    .clang_arg("-D__linux__")
    // ...
    .generate();
```

**问题 4: 绑定文件过大**

```rust
// 解决方案：使用白名单过滤
.allowlist_function("mylib_.*")
.allowlist_type("mylib_.*")
.blocklist_item("std::.*")  // 排除标准库
```

### 2.7 实战：SQLite 绑定

**项目结构：**

```text
sqlite-rs/
├── Cargo.toml
├── build.rs
├── wrapper.h
├── sqlite3/
│   ├── sqlite3.c
│   └── sqlite3.h
└── src/
    └── lib.rs
```

**Cargo.toml：**

```toml
[package]
name = "sqlite-rs"
version = "0.1.0"
edition = "2021"

[dependencies]
libc = "0.2"
thiserror = "1.0"

[build-dependencies]
bindgen = "0.69"
cc = "1.0"

[features]
default = ["bundled"]
bundled = []
```

**build.rs：**

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let sqlite_dir = PathBuf::from("sqlite3");

    // 编译 SQLite
    cc::Build::new()
        .file(sqlite_dir.join("sqlite3.c"))
        .include(&sqlite_dir)
        .flag("-DSQLITE_ENABLE_FTS5")
        .flag("-DSQLITE_ENABLE_JSON1")
        .flag("-DSQLITE_THREADSAFE=1")
        .compile("sqlite3");

    // 生成绑定
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg(format!("-I{}", sqlite_dir.display()))
        .allowlist_function("sqlite3_.*")
        .allowlist_type("sqlite3.*")
        .allowlist_var("SQLITE_.*")
        .translate_enum_integer_types(true)
        .generate()
        .expect("Failed to generate bindings");

    bindings
        .write_to_file(out_dir.join("bindings.rs"))
        .expect("Failed to write bindings");

    println!("cargo:rustc-link-lib=static=sqlite3");
}
```

---

## 3. cbindgen - Rust → C/C++

**cbindgen** 从 Rust 代码生成 C/C++ 头文件，使 Rust 库可被其他语言调用。

### 3.1 安装与配置

```bash
cargo install cbindgen
```

**Cargo.toml：**

```toml
[package]
name = "mylib"
version = "0.1.0"
edition = "2021"
crate-type = ["cdylib", "staticlib"]  # 关键：编译为 C 库

[dependencies]

[build-dependencies]
cbindgen = "0.26"
```

### 3.2 生成 C 头文件

**build.rs：**

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let output_file = PathBuf::from(&crate_dir)
        .join("include")
        .join("mylib.h");

    cbindgen::Builder::new()
        .with_crate(crate_dir)
        .with_config(cbindgen::Config::from_file("cbindgen.toml").unwrap())
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(output_file);
}
```

### 3.3 cbindgen.toml 配置详解

```toml
# 语言设置: C 或 C++
language = "C"
# language = "C++"

# 输出配置
header = "/* Auto-generated header - DO NOT EDIT */"
autogen_warning = "/* Warning: auto-generated by cbindgen */"
include_guard = "MYLIB_H"
pragma_once = true
namespaces = ["mylib"]

# 样式设置
braces = "SameLine"
line_length = 100
tab_width = 4
documentation = true
documentation_style = "auto"

# 函数前缀
prefix = "mylib_"

# 导出配置
[export]
include = ["MyStruct", "my_function"]
exclude = ["PrivateStruct"]
prefix = "MyLib"
item_types = [
    "globals", "enums", "structs", "unions", "typedefs",
    "opaque", "functions", "constants"
]

[export.rename]
"MyStruct" = "mylib_struct_t"
"MyEnum" = "mylib_enum_t"

[fn]
rename_args = "CamelCase"
args = "auto"
sort_by = "Name"

[struct]
rename_fields = "CamelCase"

[enum]
rename_variants = "ScreamingSnakeCase"

[parse]
parse_deps = false

[parse.expand]
crates = ["mylib"]
features = ["c_api"]

# C++ 特定配置
[cpp]
namespace = "mylib"
```

### 3.4 不透明指针模式

不透明指针是 FFI 中最安全的模式之一，隐藏实现细节：

```rust
// 内部实现（不公开）
pub struct DataProcessor {
    buffer: Vec<u8>,
    metadata: HashMap<String, String>,
}

// 公开的不透明类型
pub type MyLibProcessor = c_void;

/// 创建处理器
#[no_mangle]
pub extern "C" fn mylib_processor_new(name: *const c_char) -> *mut MyLibProcessor {
    if name.is_null() {
        return ptr::null_mut();
    }

    let name_str = unsafe {
        match CStr::from_ptr(name).to_str() {
            Ok(s) => s.to_string(),
            Err(_) => return ptr::null_mut(),
        }
    };

    let processor = Box::new(DataProcessor {
        buffer: Vec::new(),
        metadata: HashMap::new(),
    });

    Box::into_raw(processor) as *mut MyLibProcessor
}

/// 释放处理器
#[no_mangle]
pub extern "C" fn mylib_processor_free(ptr: *mut MyLibProcessor) {
    if !ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(ptr as *mut DataProcessor);
        }
    }
}
```

### 3.5 常见问题

**问题 1: 泛型不支持**

```rust
// 错误：泛型不会出现在生成的头文件中
pub struct Container<T> {
    data: T,
}

// 解决：使用具体类型或宏
pub struct ContainerU32 {
    data: u32,
}
```

**问题 2: 复杂类型映射**

```rust
// 问题：Rust String 不能直接映射
pub fn get_string() -> String;

// 解决：使用 C 兼容类型
#[no_mangle]
pub extern "C" fn get_string() -> *mut c_char {
    CString::new("hello").unwrap().into_raw()
}
```

**问题 3: 特征对象**

```rust
// 问题：trait 对象不能直接导出
pub trait Processor { }

// 解决：使用不透明指针包装
pub struct ProcessorHandle {
    inner: Box<dyn Processor>,
}
```

### 3.6 实战：Rust 库供 C 调用

**Rust 代码 (src/lib.rs)：**

```rust
//! Rust 库 C API 示例

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int, c_void};
use std::ptr;
use std::sync::Arc;

// ========== 错误处理 ==========

/// 错误码
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum MyLibError {
    Ok = 0,
    NullPointer = -1,
    InvalidUtf8 = -2,
    AllocationFailed = -3,
    InvalidHandle = -4,
    IoError = -5,
}

/// 获取错误描述
#[no_mangle]
pub extern "C" fn mylib_error_string(code: MyLibError) -> *const c_char {
    let msg = match code {
        MyLibError::Ok => "Success",
        MyLibError::NullPointer => "Null pointer",
        MyLibError::InvalidUtf8 => "Invalid UTF-8",
        MyLibError::AllocationFailed => "Allocation failed",
        MyLibError::InvalidHandle => "Invalid handle",
        MyLibError::IoError => "IO error",
    };
    concat!(msg, "\0").as_ptr() as *const c_char
}

// ========== 简单类型 ==========

/// 两数相加
#[no_mangle]
pub extern "C" fn mylib_add(a: c_int, b: c_int) -> c_int {
    a + b
}

/// 处理字符串
#[no_mangle]
pub extern "C" fn mylib_process_string(
    input: *const c_char,
    output: *mut c_char,
    output_len: usize,
) -> MyLibError {
    if input.is_null() || output.is_null() {
        return MyLibError::NullPointer;
    }

    let input_str = unsafe {
        match CStr::from_ptr(input).to_str() {
            Ok(s) => s,
            Err(_) => return MyLibError::InvalidUtf8,
        }
    };

    let processed = format!("Processed: {}", input_str.to_uppercase());

    let output_slice = unsafe {
        std::slice::from_raw_parts_mut(output as *mut u8, output_len)
    };

    let bytes = processed.as_bytes();
    if bytes.len() >= output_len {
        return MyLibError::AllocationFailed;
    }

    output_slice[..bytes.len()].copy_from_slice(bytes);
    output_slice[bytes.len()] = 0; // null 终止

    MyLibError::Ok
}

// ========== 不透明指针模式 ==========

/// 不透明的数据处理器
pub struct DataProcessor {
    data: Vec<u8>,
    name: String,
}

pub type MyLibProcessor = c_void;

/// 创建处理器
#[no_mangle]
pub extern "C" fn mylib_processor_new(name: *const c_char) -> *mut MyLibProcessor {
    if name.is_null() {
        return ptr::null_mut();
    }

    let name_str = unsafe {
        match CStr::from_ptr(name).to_str() {
            Ok(s) => s.to_string(),
            Err(_) => return ptr::null_mut(),
        }
    };

    let processor = Box::new(DataProcessor {
        data: Vec::new(),
        name: name_str,
    });

    Box::into_raw(processor) as *mut MyLibProcessor
}

/// 释放处理器
#[no_mangle]
pub extern "C" fn mylib_processor_free(ptr: *mut MyLibProcessor) {
    if !ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(ptr as *mut DataProcessor);
        }
    }
}

/// 添加数据
#[no_mangle]
pub extern "C" fn mylib_processor_append(
    ptr: *mut MyLibProcessor,
    data: *const u8,
    len: usize,
) -> MyLibError {
    if ptr.is_null() || data.is_null() {
        return MyLibError::NullPointer;
    }

    let processor = unsafe { &mut *(ptr as *mut DataProcessor) };
    let slice = unsafe { std::slice::from_raw_parts(data, len) };

    processor.data.extend_from_slice(slice);
    MyLibError::Ok
}

/// 获取数据大小
#[no_mangle]
pub extern "C" fn mylib_processor_len(ptr: *const MyLibProcessor) -> usize {
    if ptr.is_null() {
        return 0;
    }

    let processor = unsafe { &*(ptr as *const DataProcessor) };
    processor.data.len()
}

// ========== 线程安全 ==========

use std::sync::Mutex;

pub struct SharedCounter {
    count: Mutex<i64>,
}

pub type MyLibCounter = c_void;

#[no_mangle]
pub extern "C" fn mylib_counter_new() -> *mut MyLibCounter {
    let counter = Box::new(SharedCounter {
        count: Mutex::new(0),
    });
    Box::into_raw(counter) as *mut MyLibCounter
}

#[no_mangle]
pub extern "C" fn mylib_counter_free(ptr: *mut MyLibCounter) {
    if !ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(ptr as *mut SharedCounter);
        }
    }
}

#[no_mangle]
pub extern "C" fn mylib_counter_increment(ptr: *mut MyLibCounter) -> i64 {
    if ptr.is_null() {
        return -1;
    }

    let counter = unsafe { &*(ptr as *mut SharedCounter) };
    let mut guard = counter.count.lock().unwrap();
    *guard += 1;
    *guard
}

// ========== Panic 处理 ==========

use std::panic;

/// 初始化 panic 处理（在库加载时调用）
#[no_mangle]
pub extern "C" fn mylib_init() {
    panic::set_hook(Box::new(|info| {
        eprintln!("Rust panic: {}", info);
    }));
}
```

**生成的 C 头文件 (include/mylib.h)：**

```c
/* Auto-generated header - DO NOT EDIT */
/* Warning: this file is auto-generated by cbindgen */

#ifndef MYLIB_H
#define MYLIB_H

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * Error codes
 */
typedef enum {
    MYLIB_OK = 0,
    MYLIB_NULL_POINTER = -1,
    MYLIB_INVALID_UTF8 = -2,
    MYLIB_ALLOCATION_FAILED = -3,
    MYLIB_INVALID_HANDLE = -4,
    MYLIB_IO_ERROR = -5,
} MyLibError;

typedef void MyLibCounter;
typedef void MyLibProcessor;

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize panic handling (call when loading library)
 */
void mylib_init(void);

/**
 * Add two integers
 */
int32_t mylib_add(int32_t a, int32_t b);

/**
 * Create processor
 */
MyLibProcessor *mylib_processor_new(const char *name);

/**
 * Free processor
 */
void mylib_processor_free(MyLibProcessor *ptr);

/**
 * Get data size
 */
size_t mylib_processor_len(const MyLibProcessor *ptr);

/**
 * Create counter
 */
MyLibCounter *mylib_counter_new(void);

/**
 * Free counter
 */
void mylib_counter_free(MyLibCounter *ptr);

/**
 * Increment counter
 */
int64_t mylib_counter_increment(MyLibCounter *ptr);

#ifdef __cplusplus
}
#endif

#endif /* MYLIB_H */
```

**C 使用示例：**

```c
#include <stdio.h>
#include "mylib.h"

int main() {
    // 初始化
    mylib_init();

    // 简单函数
    int result = mylib_add(5, 3);
    printf("5 + 3 = %d\n", result);

    // 使用处理器（不透明指针）
    MyLibProcessor *proc = mylib_processor_new("test_processor");
    if (proc) {
        uint8_t data[] = {1, 2, 3, 4, 5};
        mylib_processor_append(proc, data, sizeof(data));
        printf("Data size: %zu\n", mylib_processor_len(proc));
        mylib_processor_free(proc);
    }

    // 线程安全计数器
    MyLibCounter *counter = mylib_counter_new();
    for (int i = 0; i < 10; i++) {
        mylib_counter_increment(counter);
    }
    printf("Counter: %lld\n", (long long)mylib_counter_get(counter));
    mylib_counter_free(counter);

    return 0;
}
```

---

## 4. wasm-bindgen - Rust → Web

**wasm-bindgen** 让 Rust 与 JavaScript 无缝互操作，编译为 WebAssembly。

### 4.1 安装与配置

```bash
# 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 添加 WASM 目标
rustup target add wasm32-unknown-unknown
```

### 4.2 基础设置

**项目结构：**

```text
wasm-project/
├── Cargo.toml
├── src/lib.rs
├── pkg/          # 生成的包
└── www/          # 前端代码
    ├── index.html
    └── index.js
```

**Cargo.toml：**

```toml
[package]
name = "wasm-project"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
wasm-bindgen = "0.2"
serde = { version = "1.0", features = ["derive"] }
serde-wasm-bindgen = "0.6"

# Web API 访问
js-sys = "0.3"
web-sys = { version = "0.3", features = [
    "console",
    "Document",
    "Element",
    "Window",
] }

[dependencies.wasm-bindgen-futures]
version = "0.4"

[profile.release]
opt-level = 3
lto = true
```

### 4.3 类型映射

```rust
use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};

// 基本类型
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 字符串
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

// 字节数组
#[wasm_bindgen]
pub fn process_bytes(data: &[u8]) -> Vec<u8> {
    data.iter().map(|b| b * 2).collect()
}

// 结构体
#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct Point {
    x: f64,
    y: f64,
}

#[wasm_bindgen]
impl Point {
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    #[wasm_bindgen(getter)]
    pub fn x(&self) -> f64 { self.x }

    #[wasm_bindgen(getter)]
    pub fn y(&self) -> f64 { self.y }

    pub fn distance(&self, other: &Point) -> f64 {
        ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
    }
}

// 复杂类型（使用 serde）
#[derive(Serialize, Deserialize)]
pub struct User {
    id: u64,
    name: String,
    email: Option<String>,
}

#[wasm_bindgen]
pub fn parse_user(json: &str) -> Result<JsValue, JsValue> {
    let user: User = serde_json::from_str(json)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;
    serde_wasm_bindgen::to_value(&user)
        .map_err(|e| JsValue::from_str(&e.to_string()))
}
```

### 4.4 与 Web API 集成

```rust
use wasm_bindgen::prelude::*;
use web_sys::{console, Document, Window};

#[wasm_bindgen(start)]
pub fn main() {
    console::log_1(&"WASM module loaded".into());
}

/// DOM 操作
#[wasm_bindgen]
pub struct DomManipulator {
    document: Document,
}

#[wasm_bindgen]
impl DomManipulator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<DomManipulator, JsValue> {
        let window = web_sys::window().ok_or("no window")?;
        let document = window.document().ok_or("no document")?;
        Ok(Self { document })
    }

    pub fn create_element(&self, tag: &str, content: &str) -> Result<(), JsValue> {
        let elem = self.document.create_element(tag)?;
        elem.set_text_content(Some(content));
        let body = self.document.body().ok_or("no body")?;
        body.append_child(&elem)?;
        Ok(())
    }
}

/// 异步操作
#[wasm_bindgen]
pub async fn fetch_data(url: String) -> Result<String, JsValue> {
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_str(&url)).await?;
    let resp: Response = resp_value.dyn_into()?;
    let text = JsFuture::from(resp.text()?).await?;
    Ok(text.as_string().unwrap_or_default())
}
```

### 4.5 常见问题

**问题 1: 线程不支持**

```rust
// 错误：WASM 不支持标准线程
use std::thread;

// 解决：使用 wasm-bindgen-futures
use wasm_bindgen_futures::spawn_local;
spawn_local(async { /* ... */ });
```

**问题 2: 文件系统访问**

```rust
// 错误：WASM 没有文件系统
std::fs::read("file.txt");

// 解决：使用 Web API
let file_input = document.get_element_by_id("file-input");
```

**问题 3: 随机数生成**

```toml
# Cargo.toml
[dependencies]
getrandom = { version = "0.2", features = ["js"] }
```

### 4.6 实战：WASM 图像处理模块

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct ImageProcessor;

#[wasm_bindgen]
impl ImageProcessor {
    /// 灰度化
    pub fn grayscale(data: &[u8]) -> Vec<u8> {
        let mut result = data.to_vec();
        for chunk in result.chunks_exact_mut(4) {
            let gray = ((chunk[0] as u16 * 299 +
                        chunk[1] as u16 * 587 +
                        chunk[2] as u16 * 114) / 1000) as u8;
            chunk[0] = gray;
            chunk[1] = gray;
            chunk[2] = gray;
        }
        result
    }

    /// 调整亮度
    pub fn adjust_brightness(data: &[u8], factor: f32) -> Vec<u8> {
        data.iter()
            .map(|&p| (p as f32 * factor).clamp(0.0, 255.0) as u8)
            .collect()
    }
}

/// 数据压缩
#[wasm_bindgen]
pub fn compress_data(data: &[u8]) -> Result<Vec<u8>, JsValue> {
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use std::io::Write;

    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;
    encoder.finish()
        .map_err(|e| JsValue::from_str(&e.to_string()))
}
```

---

## 5. 内存管理最佳实践

### 5.1 内存所有权规则

```
┌─────────────────────────────────────────────────────────────┐
│                   FFI 内存所有权规则                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  规则 1: Rust 分配 → Rust 释放                               │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐             │
│  │  Rust   │ ──→  │   Box   │ ──→  │  into_raw│ → C        │
│  │         │ ←──  │ from_raw│ ←──  │  caller   │ ← free     │
│  └─────────┘      └─────────┘      └─────────┘             │
│                                                             │
│  规则 2: C 分配 → C 释放                                     │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐             │
│  │    C    │ ──→  │ malloc  │ ──→  │ Rust使用 │             │
│  │         │ ←──  │  free   │ ←──  │  return  │             │
│  └─────────┘      └─────────┘      └─────────┘             │
│                                                             │
│  永远不要混用分配器！                                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 内存管理模式

**模式 1: Rust 拥有内存**

```rust
/// Rust 分配，返回不透明指针给 C
#[no_mangle]
pub extern "C" fn datastore_new() -> *mut DataStore {
    let store = Box::new(DataStore::new());
    Box::into_raw(store)
}

/// C 调用此函数释放内存
#[no_mangle]
pub unsafe extern "C" fn datastore_free(ptr: *mut DataStore) {
    if !ptr.is_null() {
        unsafe { drop(Box::from_raw(ptr)); }
    }
}
```

**模式 2: C 拥有内存**

```rust
/// 填充 C 预分配的缓冲区
#[no_mangle]
pub unsafe extern "C" fn fill_buffer(
    buffer: *mut c_char,
    buffer_len: usize,
) -> isize {
    if buffer.is_null() || buffer_len == 0 {
        return -1;
    }

    let data = b"Hello from Rust!";
    let to_write = data.len().min(buffer_len - 1);

    unsafe {
        std::ptr::copy_nonoverlapping(
            data.as_ptr(),
            buffer as *mut u8,
            to_write
        );
        *buffer.add(to_write) = 0; // null 终止
    }

    to_write as isize
}
```

**模式 3: 共享所有权（引用计数）**

```rust
use std::sync::Arc;

pub struct SharedData {
    inner: Arc<Mutex<Data>>,
}

#[no_mangle]
pub extern "C" fn shared_data_clone(handle: *const SharedData) -> *mut SharedData {
    if handle.is_null() { return std::ptr::null_mut(); }

    let handle = unsafe { &*handle };
    let new_handle = Box::new(SharedData {
        inner: Arc::clone(&handle.inner),
    });
    Box::into_raw(new_handle)
}
```

### 5.3 字符串处理

```rust
use std::ffi::{CStr, CString};

/// Rust String → C 字符串（调用者负责释放）
#[no_mangle]
pub extern "C" fn rust_string_new(rust_str: *const c_char) -> *mut c_char {
    if rust_str.is_null() { return std::ptr::null_mut(); }

    unsafe {
        let c_str = CStr::from_ptr(rust_str);
        match CString::new(c_str.to_bytes()) {
            Ok(s) => s.into_raw(),
            Err(_) => std::ptr::null_mut(),
        }
    }
}

/// 释放 Rust 分配的字符串
#[no_mangle]
pub unsafe extern "C" fn rust_string_free(ptr: *mut c_char) {
    if !ptr.is_null() {
        unsafe { drop(CString::from_raw(ptr)); }
    }
}

/// 安全地复制 C 字符串到 Rust
pub unsafe fn c_to_rust_string(ptr: *const c_char) -> Option<String> {
    if ptr.is_null() { return None; }
    unsafe {
        CStr::from_ptr(ptr).to_str().ok().map(|s| s.to_string())
    }
}
```

### 5.4 生命周期管理

```rust
use std::marker::PhantomData;

/// 带生命周期标记的缓冲区
pub struct CBuffer<'a> {
    ptr: *mut u8,
    len: usize,
    _marker: PhantomData<&'a mut [u8]>,
}

impl<'a> CBuffer<'a> {
    pub fn from_mut_slice(slice: &'a mut [u8]) -> Self {
        Self {
            ptr: slice.as_mut_ptr(),
            len: slice.len(),
            _marker: PhantomData,
        }
    }
}

/// 作用域 API 确保生命周期安全
pub fn with_c_string<F, R>(s: &str, f: F) -> R
where
    F: FnOnce(*const c_char) -> R,
{
    let cstr = CString::new(s).expect("invalid string");
    f(cstr.as_ptr())
    // cstr 在这里自动释放
}
```

---

## 6. 错误处理策略

### 6.1 错误码设计

```rust
/// FFI 错误码设计
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FfiErrorCode {
    Success = 0,
    NullPointer = 1,
    InvalidUtf8 = 2,
    BufferTooSmall = 3,
    AllocationFailed = 4,
    IoError = 5,
    InvalidArgument = 6,
    InternalError = 99,
}

/// 详细的错误信息
#[repr(C)]
pub struct FfiError {
    code: FfiErrorCode,
    message: *const c_char,
}

impl FfiError {
    pub fn success() -> Self {
        Self {
            code: FfiErrorCode::Success,
            message: std::ptr::null(),
        }
    }

    pub fn new(code: FfiErrorCode, message: &str) -> Self {
        let cmsg = CString::new(message).unwrap_or_default();
        Self {
            code,
            message: cmsg.into_raw(),
        }
    }
}

impl Drop for FfiError {
    fn drop(&mut self) {
        if !self.message.is_null() {
            unsafe {
                let _ = CString::from_raw(self.message as *mut c_char);
            }
        }
    }
}
```

### 6.2 错误传播模式

```rust
/// 使用宏简化错误处理
#[macro_export]
macro_rules! ffi_check_null {
    ($ptr:expr) => {
        if $ptr.is_null() {
            return FfiError::new(
                FfiErrorCode::NullPointer,
                concat!(stringify!($ptr), " is null")
            );
        }
    };
}

#[macro_export]
macro_rules! ffi_try {
    ($expr:expr, $err_msg:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => {
                return FfiError::new(
                    FfiErrorCode::InternalError,
                    &format!("{}: {}", $err_msg, e)
                );
            }
        }
    };
}

/// 使用示例
#[no_mangle]
pub extern "C" fn process_data(
    input: *const c_char,
    output: *mut c_char,
    output_len: usize,
) -> FfiError {
    ffi_check_null!(input);
    ffi_check_null!(output);

    if output_len == 0 {
        return FfiError::new(
            FfiErrorCode::BufferTooSmall,
            "output buffer size is 0"
        );
    }

    let input_str = ffi_try!(
        unsafe { CStr::from_ptr(input).to_str() },
        "invalid UTF-8"
    );

    // ... 处理逻辑

    FfiError::success()
}
```

### 6.3 Panic 安全

```rust
use std::panic;

/// 设置 panic 钩子，防止跨 FFI 边界展开
pub fn setup_panic_handler() {
    panic::set_hook(Box::new(|info| {
        eprintln!("Panic in FFI code: {}", info);
        // 记录到日志系统
    }));
}

/// 捕获 panic 的包装宏
#[macro_export]
macro_rules! ffi_catch_panic {
    ($default:expr, $body:expr) => {{
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| $body)) {
            Ok(result) => result,
            Err(_) => {
                eprintln!("Caught panic in FFI function");
                $default
            }
        }
    }};
}

/// 使用示例
#[no_mangle]
pub extern "C" fn panic_safe_operation(input: i32) -> i32 {
    ffi_catch_panic!(-1, {
        if input < 0 {
            panic!("negative input");
        }
        input * 2
    })
}
```

---

## 7. 线程安全考虑

### 7.1 Send 和 Sync

```rust
/// 明确标记线程安全
pub struct ThreadSafeHandle {
    inner: *mut c_void,
}

// 如果底层 C 库是线程安全的
unsafe impl Send for ThreadSafeHandle {}
unsafe impl Sync for ThreadSafeHandle {}

/// 如果不是线程安全的，需要包装
pub struct NonThreadSafeHandle {
    inner: *mut c_void,
}

// 不实现 Send 和 Sync
// 这样 Rust 编译器会阻止跨线程使用
```

### 7.2 线程安全模式

```rust
use std::sync::Mutex;

/// 线程安全的计数器
pub struct SharedCounter {
    count: Mutex<i64>,
}

pub type MyLibCounter = c_void;

#[no_mangle]
pub extern "C" fn mylib_counter_new() -> *mut MyLibCounter {
    let counter = Box::new(SharedCounter {
        count: Mutex::new(0),
    });
    Box::into_raw(counter) as *mut MyLibCounter
}

#[no_mangle]
pub extern "C" fn mylib_counter_increment(ptr: *mut MyLibCounter) -> i64 {
    if ptr.is_null() { return -1; }

    let counter = unsafe { &*(ptr as *mut SharedCounter) };
    let mut guard = counter.count.lock().unwrap();
    *guard += 1;
    *guard
}
```

### 7.3 跨线程数据传递

```rust
use std::sync::mpsc;
use std::thread;

/// 跨线程处理数据
#[no_mangle]
pub extern "C" fn process_in_thread(
    data: *const u8,
    len: usize,
    callback: extern "C" fn(*const u8, usize),
) {
    if data.is_null() || len == 0 { return; }

    let data = unsafe {
        std::slice::from_raw_parts(data, len).to_vec()
    };

    thread::spawn(move || {
        // 在后台线程处理
        let processed = expensive_operation(&data);
        callback(processed.as_ptr(), processed.len());
    });
}
```

---

## 8. 完整项目示例

### 8.1 项目概述

创建一个多语言绑定的图像处理库：

```text
image-processor/
├── Cargo.toml              # Rust 主库
├── build.rs                # 构建脚本
├── cbindgen.toml           # C 头文件生成配置
├── include/                # 生成的 C 头文件
│   └── image_processor.h
├── src/
│   ├── lib.rs             # Rust 库入口
│   ├── processor.rs       # 核心处理逻辑
│   └── ffi/               # FFI 绑定代码
│       ├── mod.rs
│       ├── c_api.rs       # C API
│       └── python_api.rs  # Python API (PyO3)
├── c-example/             # C 使用示例
│   ├── main.c
│   └── Makefile
├── python-example/        # Python 使用示例
│   └── test.py
└── tests/                 # Rust 测试
    └── integration_tests.rs
```

### 8.2 Rust 核心库

**Cargo.toml：**

```toml
[package]
name = "image-processor"
version = "0.1.0"
edition = "2021"

[lib]
name = "image_processor"
crate-type = ["cdylib", "staticlib", "rlib"]

[dependencies]
libc = "0.2"
thiserror = "1.0"
image = "0.24"

[dependencies.pyo3]
version = "0.20"
features = ["extension-module"]
optional = true

[build-dependencies]
cbindgen = "0.26"

[features]
default = ["c-api"]
c-api = []
python-api = ["pyo3"]
```

**src/processor.rs：**

```rust
//! 核心图像处理逻辑

use image::{DynamicImage, GenericImageView, ImageBuffer, Rgba};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProcessorError {
    #[error("Invalid image format")]
    InvalidFormat,
    #[error("Processing failed: {0}")]
    ProcessingFailed(String),
}

pub type Result<T> = std::result::Result<T, ProcessorError>;

pub struct ImageProcessor;

impl ImageProcessor {
    /// 灰度化处理
    pub fn grayscale(image: DynamicImage) -> DynamicImage {
        DynamicImage::ImageLuma8(image.to_luma8())
    }

    /// 调整大小
    pub fn resize(
        image: &DynamicImage,
        width: u32,
        height: u32,
    ) -> DynamicImage {
        image.resize_exact(width, height, image::imageops::Lanczos3)
    }

    /// 旋转
    pub fn rotate90(image: DynamicImage) -> DynamicImage {
        DynamicImage::ImageRgba8(image::imageops::rotate90(&image.to_rgba8()))
    }
}
```

### 8.3 C 绑定

**src/ffi/c_api.rs：**

```rust
//! C FFI API

use crate::processor::*;
use image::load_from_memory;
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::os::raw;
use std::ptr;

/// 错误码
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub enum ImgProcError {
    Success = 0,
    NullPointer = 1,
    InvalidImage = 2,
    ProcessingFailed = 3,
    AllocationFailed = 4,
}

/// 不透明的图像句柄
pub type ImgProcImage = c_void;

/// 加载图像
#[no_mangle]
pub extern "C" fn imgproc_load(data: *const u8, len: usize) -> *mut ImgProcImage {
    if data.is_null() || len == 0 {
        return ptr::null_mut();
    }

    let bytes = unsafe { std::slice::from_raw_parts(data, len) };

    match load_from_memory(bytes) {
        Ok(image) => {
            let boxed = Box::new(image);
            Box::into_raw(boxed) as *mut ImgProcImage
        }
        Err(_) => ptr::null_mut(),
    }
}

/// 释放图像
#[no_mangle]
pub unsafe extern "C" fn imgproc_free(image: *mut ImgProcImage) {
    if !image.is_null() {
        unsafe {
            let _ = Box::from_raw(image as *mut DynamicImage);
        }
    }
}

/// 获取图像尺寸
#[no_mangle]
pub unsafe extern "C" fn imgproc_get_size(
    image: *const ImgProcImage,
    width: *mut u32,
    height: *mut u32,
) -> ImgProcError {
    if image.is_null() || width.is_null() || height.is_null() {
        return ImgProcError::NullPointer;
    }

    let img = unsafe { &*(image as *const DynamicImage) };
    let (w, h) = img.dimensions();

    unsafe {
        *width = w;
        *height = h;
    }

    ImgProcError::Success
}

/// 灰度化处理
#[no_mangle]
pub unsafe extern "C" fn imgproc_grayscale(
    image: *mut ImgProcImage,
) -> *mut ImgProcImage {
    if image.is_null() {
        return ptr::null_mut();
    }

    let img = unsafe { &*(image as *mut DynamicImage) };
    let processed = ImageProcessor::grayscale(img.clone());

    Box::into_raw(Box::new(processed)) as *mut ImgProcImage
}

/// 导出为 PNG
#[no_mangle]
pub unsafe extern "C" fn imgproc_to_png(
    image: *const ImgProcImage,
    out_data: *mut *mut u8,
    out_len: *mut usize,
) -> ImgProcError {
    if image.is_null() || out_data.is_null() || out_len.is_null() {
        return ImgProcError::NullPointer;
    }

    let img = unsafe { &*(image as *const DynamicImage) };

    let mut buffer = Vec::new();
    if let Err(_) = img.write_to(&mut std::io::Cursor::new(&mut buffer), image::ImageOutputFormat::Png) {
        return ImgProcError::ProcessingFailed;
    }

    let ptr = buffer.as_mut_ptr();
    let len = buffer.len();
    std::mem::forget(buffer);

    unsafe {
        *out_data = ptr;
        *out_len = len;
    }

    ImgProcError::Success
}

/// 释放 Rust 分配的缓冲区
#[no_mangle]
pub unsafe extern "C" fn imgproc_free_buffer(data: *mut u8, len: usize) {
    if !data.is_null() && len > 0 {
        unsafe {
            let _ = Vec::from_raw_parts(data, len, len);
        }
    }
}
```

### 8.4 Python 绑定

**src/ffi/python_api.rs：**

```rust
//! Python API using PyO3

use crate::processor::*;
use image::load_from_memory;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

#[pyclass]
struct PyImageProcessor;

#[pymethods]
impl PyImageProcessor {
    #[new]
    fn new() -> Self {
        Self
    }

    /// 灰度化处理
    fn grayscale<'py>(
        &self,
        py: Python<'py>,
        data: &[u8],
    ) -> PyResult<&'py PyBytes> {
        let image = load_from_memory(data)
            .map_err(|e| PyErr::new::<pyo3::exceptions::PyValueError, _>(
                format!("Invalid image: {}", e)
            ))?;

        let processed = ImageProcessor::grayscale(image);

        let mut buffer = Vec::new();
        processed.write_to(&mut std::io::Cursor::new(&mut buffer), image::ImageOutputFormat::Png)
            .map_err(|e| PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(
                format!("Processing failed: {}", e)
            ))?;

        Ok(PyBytes::new(py, &buffer))
    }
}

#[pymodule]
fn image_processor(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<PyImageProcessor>()?;
    Ok(())
}
```

### 8.5 构建系统

**build.rs：**

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    // 生成 C 头文件
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let output_file = PathBuf::from(&crate_dir).join("include/image_processor.h");

    cbindgen::Builder::new()
        .with_crate(crate_dir)
        .with_config(cbindgen::Config::from_file("cbindgen.toml").unwrap())
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(output_file);
}
```

**cbindgen.toml：**

```toml
language = "C"
header = "/* Auto-generated header - DO NOT EDIT */"
include_guard = "IMAGE_PROCESSOR_H"
pragma_once = true

[export]
include = ["imgproc_.*"]
prefix = "ImgProc"

[fn]
rename_args = "CamelCase"
```

---

## 9. 调试与测试

### 9.1 Miri 验证

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 检查 FFI 安全性
cargo miri run --example ffi_example
```

### 9.2 Valgrind

```bash
# 内存泄漏检测
valgrind --leak-check=full --show-leak-kinds=all ./target/debug/my_program

# 详细错误报告
valgrind --leak-check=full --track-origins=yes ./target/debug/my_program
```

### 9.3 AddressSanitizer

```bash
# 设置环境变量
export RUSTFLAGS="-Z sanitizer=address"

# 运行测试
cargo test --target x86_64-unknown-linux-gnu

# 使用 ThreadSanitizer
export RUSTFLAGS="-Z sanitizer=thread"
cargo test --target x86_64-unknown-linux-gnu
```

---

## 10. C/C++ 互操作最佳实践

### 10.1 类型安全

```rust
// 使用固定大小整数
#[repr(C)]
pub struct Data {
    pub count: u32,      // 明确 32 位
    pub offset: usize,   // 平台相关大小
}

// 使用 #[repr(C)] 确保布局兼容
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

// 枚举使用显式值
#[repr(C)]
#[derive(Clone, Copy)]
pub enum Status {
    Ok = 0,
    Error = 1,
    Invalid = 2,
}
```

### 10.2 设计模式

**不透明指针模式：**

```rust
// 隐藏实现细节
pub struct InternalState { /* ... */ }
pub type Handle = c_void;

#[no_mangle]
pub extern "C" fn create() -> *mut Handle {
    Box::into_raw(Box::new(InternalState::new())) as *mut Handle
}
```

**Builder 模式：**

```rust
#[repr(C)]
pub struct Config {
    pub width: u32,
    pub height: u32,
    pub quality: u8,
}

#[no_mangle]
pub extern "C" fn process_with_config(data: *const u8, len: usize, config: *const Config) {
    // 使用配置处理数据
}
```

### 10.3 性能优化

```rust
// 使用零拷贝
pub fn process_slice(data: &[u8]) {
    // 直接操作 slice，不复制数据
}

// 批量处理
#[no_mangle]
pub extern "C" fn process_batch(
    items: *const *const u8,
    lengths: *const usize,
    count: usize,
) {
    // 一次处理多个项目，减少 FFI 调用开销
}

// 预分配缓冲区
pub fn process_into_buffer(input: &[u8], output: &mut [u8]) {
    // 使用调用者提供的缓冲区，避免分配
}
```

---

## 工具对比表

| 工具 | 用途 | 适用场景 | 性能开销 | 学习曲线 |
|------|------|----------|----------|----------|
| **bindgen** | C → Rust | 使用 C/C++ 库 | 编译时 | 中等 |
| **cbindgen** | Rust → C | 创建 C 兼容库 | 编译时 | 中等 |
| **wasm-bindgen** | Rust → JS | WebAssembly 开发 | 运行时低 | 低 |
| **Miri** | UB 检测 | 开发期验证 | 高（10-100x） | 中等 |
| **Valgrind** | 内存检测 | Linux 调试 | 高（5-20x） | 中等 |
| **ASan** | 内存错误检测 | CI/测试 | 中等（2-3x） | 低 |
| **TSan** | 数据竞争检测 | 并发调试 | 高（5-15x） | 中等 |

---

## 安全注意事项清单

### FFI 函数设计

- [ ] 所有指针参数都进行空指针检查
- [ ] 缓冲区大小参数与指针配对使用
- [ ] 返回值明确表示成功/失败
- [ ] 使用 `#[no_mangle]` 和 `extern "C"`
- [ ] 提供对称的创建/销毁函数

### 内存安全

- [ ] 明确内存所有权归属
- [ ] 不混用不同来源的分配器
- [ ] 文档说明调用方/被调方的内存责任
- [ ] 使用 `std::panic::catch_unwind` 保护 FFI 边界

### 类型安全

- [ ] 使用 `#[repr(C)]` 标记跨 FFI 的结构体
- [ ] 固定大小整数类型（`c_int`, `c_long` 等）
- [ ] 谨慎处理字符串编码（UTF-8 vs 系统编码）

### 线程安全

- [ ] 明确标记 `Send` 和 `Sync`
- [ ] 使用线程安全的类型包装 C 数据
- [ ] 文档说明线程限制

---

## 参考资源

- [Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/) - FFI 示例大全
- [The Rustonomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html) - 官方 FFI 指南
- [bindgen 文档](https://rust-lang.github.io/rust-bindgen/) - bindgen 用户指南
- [cbindgen 文档](https://github.com/mozilla/cbindgen) - cbindgen 项目文档
- [wasm-bindgen 指南](https://rustwasm.github.io/wasm-bindgen/) - WebAssembly 开发指南
- [The Rust FFI Guide](https://michael-f-bryan.github.io/rust-ffi-guide/) - FFI 最佳实践
- [CXX](https://cxx.rs/) - 安全的 C++ 互操作库

---

## Rust 1.94 在 FFI 开发中的应用

> **适用版本**: Rust 1.94.0+

### LazyLock 在 C 库句柄管理中的应用

```rust
use std::sync::LazyLock;

/// C 库句柄单例（延迟初始化）
static CLIB_HANDLE: LazyLock<CLibHandle> = LazyLock::new(|| {
    CLibHandle::init().expect("Failed to initialize C library")
});

/// 快速检查 C 库是否已初始化
pub fn is_clib_ready() -> bool {
    LazyLock::get(&CLIB_HANDLE).is_some()
}
```

### ControlFlow 在错误处理转换中的应用

```rust
use std::ops::ControlFlow;

/// 将 C 错误码转换为 Rust 错误，支持提前终止
fn check_c_errors(results: &[c_int]) -> ControlFlow<FFIError, ()> {
    for &code in results {
        if code < 0 {
            return ControlFlow::Break(FFIError::from_code(code));
        }
    }
    ControlFlow::Continue(())
}
```

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 深度整合完成
**最后更新**: 2026-03-17
