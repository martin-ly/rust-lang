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
  - [2. bindgen - C/C++ → Rust](#2-bindgen---cc--rust)
  - [3. cbindgen - Rust → C/C++](#3-cbindgen---rust--cc)
  - [4. wasm-bindgen - Rust → Web](#4-wasm-bindgen---rust--web)
  - [5. 内存管理最佳实践](#5-内存管理最佳实践)
  - [6. 错误处理策略](#6-错误处理策略)
  - [7. 线程安全考虑](#7-线程安全考虑)
  - [8. 完整项目示例](#8-完整项目示例)
  - [9. 调试与测试](#9-调试与测试)
  - [10. C/C++ 互操作最佳实践](#10-cc-互操作最佳实践)
  - [工具对比表](#工具对比表)
  - [安全注意事项清单](#安全注意事项清单)
  - [参考资源](#参考资源)
  - [Rust 1.94 在 FFI 开发中的应用](#rust-194-在-ffi-开发中的应用)

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
