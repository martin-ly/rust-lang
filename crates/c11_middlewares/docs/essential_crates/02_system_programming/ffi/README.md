# FFI 与互操作 - Rust C/C++ 互操作指南

> **核心库**: libc, bindgen, cc, cbindgen, cxx  
> **适用场景**: C/C++集成、系统调用、遗留代码复用、跨语言库

---

## 📋 目录

- [FFI 与互操作 - Rust C/C++ 互操作指南](#ffi-与互操作---rust-cc-互操作指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
    - [FFI使用场景](#ffi使用场景)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [libc - C标准库绑定](#libc---c标准库绑定)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [安装](#安装)
      - [快速开始](#快速开始)
    - [高级特性](#高级特性)
      - [1. 文件操作](#1-文件操作)
      - [2. 内存操作](#2-内存操作)
      - [3. 信号处理](#3-信号处理)
  - [bindgen - 自动绑定生成](#bindgen---自动绑定生成)
    - [核心特性1](#核心特性1)
    - [基础用法1](#基础用法1)
      - [安装1](#安装1)
      - [快速开始1](#快速开始1)
    - [高级配置](#高级配置)
      - [1. 选择性绑定](#1-选择性绑定)
      - [2. 类型映射](#2-类型映射)
  - [cc - 编译C/C++代码](#cc---编译cc代码)
    - [核心特性2](#核心特性2)
    - [基础用法2](#基础用法2)
      - [安装2](#安装2)
      - [快速开始2](#快速开始2)
    - [高级配置2](#高级配置2)
      - [1. C++项目](#1-c项目)
      - [2. 链接外部库](#2-链接外部库)
  - [cbindgen - 导出C头文件](#cbindgen---导出c头文件)
    - [核心特性3](#核心特性3)
    - [基础用法3](#基础用法3)
  - [cxx - 现代C++互操作](#cxx---现代c互操作)
    - [核心特性4](#核心特性4)
    - [基础用法4](#基础用法4)
  - [使用场景](#使用场景)
    - [场景1: 集成现有C库](#场景1-集成现有c库)
    - [场景2: 导出Rust库给C使用](#场景2-导出rust库给c使用)
    - [场景3: C++互操作](#场景3-c互操作)
  - [内存安全指南](#内存安全指南)
    - [1. 所有权管理](#1-所有权管理)
    - [2. 生命周期](#2-生命周期)
    - [3. 空指针检查](#3-空指针检查)
  - [最佳实践](#最佳实践)
    - [1. 安全封装](#1-安全封装)
    - [2. 错误处理](#2-错误处理)
    - [3. 文档和注释](#3-文档和注释)
    - [4. 测试策略](#4-测试策略)
    - [5. ABI稳定性](#5-abi稳定性)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 内存泄漏](#️-陷阱1-内存泄漏)
    - [⚠️ 陷阱2: 悬垂指针](#️-陷阱2-悬垂指针)
    - [⚠️ 陷阱3: 数据竞争](#️-陷阱3-数据竞争)
    - [⚠️ 陷阱4: ABI不兼容](#️-陷阱4-abi不兼容)
    - [⚠️ 陷阱5: 未定义行为](#️-陷阱5-未定义行为)
    - [⚠️ 陷阱6: 字符串处理](#️-陷阱6-字符串处理)
    - [⚠️ 陷阱7: 回调函数生命周期](#️-陷阱7-回调函数生命周期)
    - [⚠️ 陷阱8: 平台差异](#️-陷阱8-平台差异)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

FFI (Foreign Function Interface) 是Rust与其他语言互操作的桥梁，主要用于与C/C++代码集成。Rust的FFI设计追求零成本抽象，同时保持内存安全。

**FFI的核心价值**:

- **代码复用**: 利用现有C/C++库和生态
- **渐进迁移**: 逐步将C/C++代码迁移到Rust
- **系统调用**: 直接调用操作系统API
- **性能优化**: 对特定场景使用C/C++优化

### 核心概念

```text
Rust FFI 层次结构：

┌─────────────────────────────────────┐
│     Rust 应用代码 (Safe)             │
│     高级抽象、所有权、借用检查        │
└──────────────┬──────────────────────┘
               │
               ↓
┌─────────────────────────────────────┐
│     Rust FFI 绑定 (Unsafe)          │
│     extern "C" { ... }              │
│     #[repr(C)] struct               │
└──────────────┬──────────────────────┘
               │
               ↓ ABI 边界 (C ABI)
               │
┌─────────────────────────────────────┐
│     C/C++ 代码                      │
│     .c/.cpp 文件                    │
└─────────────────────────────────────┘

关键概念：
- ABI (Application Binary Interface): 二进制接口约定
- repr(C): Rust结构体使用C内存布局
- extern "C": 使用C调用约定
- unsafe: 绕过Rust安全检查
```

### FFI使用场景

| 场景 | 描述 | 典型工具 |
|------|------|----------|
| **调用C库** | Rust调用现有C库 | bindgen + cc |
| **导出C API** | Rust库提供C接口 | cbindgen |
| **C++互操作** | Rust与C++双向调用 | cxx |
| **系统调用** | 直接调用OS API | libc |
| **嵌入Rust** | 在C/C++项目中嵌入Rust | cbindgen + cargo build |

---

## 核心库对比

### 功能矩阵

| 特性 | libc | bindgen | cc | cbindgen | cxx |
|------|------|---------|-----|----------|-----|
| **C标准库** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **自动生成绑定** | ❌ | ✅ | ❌ | ✅ | ✅ |
| **编译C代码** | ❌ | ❌ | ✅ | ❌ | ✅ |
| **导出C头文件** | ❌ | ❌ | ❌ | ✅ | ❌ |
| **C++支持** | ❌ | ⭐⭐ | ✅ | ❌ | ⭐⭐⭐⭐⭐ |
| **类型安全** | ⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **学习曲线** | 简单 | 中等 | 简单 | 简单 | 中等 |
| **文档质量** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |

### 选择指南

| 场景 | 推荐库 | 理由 |
|------|--------|------|
| **系统调用** | libc | 标准C库，跨平台 |
| **调用C库** | bindgen + cc | 自动生成绑定 |
| **导出给C** | cbindgen | 自动生成头文件 |
| **C++互操作** | cxx | 安全的C++绑定 |
| **简单集成** | cc | 快速编译C代码 |
| **遗留C代码** | bindgen | 处理复杂头文件 |

---

## libc - C标准库绑定

### 核心特性

- ✅ **跨平台**: Windows, Linux, macOS统一接口
- ✅ **标准C库**: 完整的C标准库绑定
- ✅ **系统调用**: 直接访问OS API
- ✅ **零依赖**: 无外部依赖
- ✅ **底层控制**: 精细的系统资源控制

### 基础用法

#### 安装

```toml
[dependencies]
libc = "0.2"
```

#### 快速开始

```rust
use libc::{getpid, getuid, printf};
use std::ffi::CString;

fn main() {
    unsafe {
        // 获取进程ID
        let pid = getpid();
        println!("Process ID: {}", pid);

        // 获取用户ID
        let uid = getuid();
        println!("User ID: {}", uid);

        // 使用C的printf
        let msg = CString::new("Hello from libc!\n").unwrap();
        printf(msg.as_ptr());
    }
}
```

### 高级特性

#### 1. 文件操作

```rust
use libc::{open, close, read, write, O_RDWR, O_CREAT};
use std::ffi::CString;

fn main() {
    unsafe {
        // 打开文件
        let path = CString::new("/tmp/test.txt").unwrap();
        let fd = open(path.as_ptr(), O_RDWR | O_CREAT, 0o644);
        
        if fd < 0 {
            panic!("Failed to open file");
        }

        // 写入数据
        let data = b"Hello, World!";
        let written = write(fd, data.as_ptr() as *const _, data.len());
        println!("Written {} bytes", written);

        // 读取数据
        let mut buffer = [0u8; 100];
        let read_bytes = read(fd, buffer.as_mut_ptr() as *mut _, buffer.len());
        println!("Read {} bytes", read_bytes);

        // 关闭文件
        close(fd);
    }
}
```

#### 2. 内存操作

```rust
use libc::{malloc, free, memcpy, memset};
use std::ptr;

fn main() {
    unsafe {
        // 分配内存
        let size = 1024;
        let ptr = malloc(size) as *mut u8;
        
        if ptr.is_null() {
            panic!("Memory allocation failed");
        }

        // 初始化内存
        memset(ptr as *mut _, 0, size);

        // 复制数据
        let data = b"Test data";
        memcpy(ptr as *mut _, data.as_ptr() as *const _, data.len());

        // 使用内存...
        let slice = std::slice::from_raw_parts(ptr, data.len());
        println!("Data: {:?}", slice);

        // 释放内存
        free(ptr as *mut _);
    }
}
```

#### 3. 信号处理

```rust
use libc::{signal, SIGINT, SIG_DFL};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

static mut RUNNING: AtomicBool = AtomicBool::new(true);

extern "C" fn handle_sigint(_: i32) {
    unsafe {
        RUNNING.store(false, Ordering::SeqCst);
    }
}

fn main() {
    unsafe {
        // 注册信号处理器
        signal(SIGINT, handle_sigint as usize);
    }

    println!("Press Ctrl+C to exit...");
    
    while unsafe { RUNNING.load(Ordering::SeqCst) } {
        std::thread::sleep(std::time::Duration::from_secs(1));
    }

    println!("Exiting...");
}
```

---

## bindgen - 自动绑定生成

### 核心特性1

- ✅ **自动化**: 从C头文件自动生成Rust绑定
- ✅ **复杂类型**: 处理结构体、联合体、函数指针
- ✅ **宏展开**: 支持C预处理器宏
- ✅ **可配置**: 灵活的生成选项
- ✅ **增量构建**: 支持增量绑定生成

### 基础用法1

#### 安装1

```toml
[build-dependencies]
bindgen = "0.69"
```

#### 快速开始1

**wrapper.h**:

```c
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int x;
    int y;
} Point;

Point* create_point(int x, int y);
void free_point(Point* p);
void print_point(Point* p);
```

**build.rs**:

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉cargo在wrapper.h变化时重新构建
    println!("cargo:rerun-if-changed=wrapper.h");

    // 生成绑定
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // 告诉bindgen我们想要生成哪些类型
        .allowlist_function("create_point")
        .allowlist_function("free_point")
        .allowlist_function("print_point")
        .allowlist_type("Point")
        // 生成绑定
        .generate()
        .expect("Unable to generate bindings");

    // 写入绑定到$OUT_DIR/bindings.rs
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

**src/lib.rs**:

```rust
// 包含生成的绑定
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point() {
        unsafe {
            let p = create_point(10, 20);
            assert!(!p.is_null());
            
            print_point(p);
            
            free_point(p);
        }
    }
}
```

### 高级配置

#### 1. 选择性绑定

```rust
let bindings = bindgen::Builder::default()
    .header("wrapper.h")
    // 只绑定特定函数
    .allowlist_function("foo_.*")  // 正则表达式
    // 排除某些函数
    .blocklist_function("internal_.*")
    // 只绑定特定类型
    .allowlist_type("MyStruct")
    // 生成Debug trait
    .derive_debug(true)
    // 生成Default trait
    .derive_default(true)
    .generate()
    .expect("Unable to generate bindings");
```

#### 2. 类型映射

```rust
let bindings = bindgen::Builder::default()
    .header("wrapper.h")
    // 将C类型映射到Rust类型
    .raw_line("use std::os::raw::{c_char, c_int};")
    // 使用ctypes
    .ctypes_prefix("libc")
    // 处理不透明类型
    .opaque_type("OpaqueThing")
    .generate()
    .unwrap();
```

---

## cc - 编译C/C++代码

### 核心特性2

- ✅ **编译C/C++**: 在构建时编译C/C++代码
- ✅ **跨平台**: 自动检测编译器(GCC/Clang/MSVC)
- ✅ **灵活配置**: 编译选项、链接库
- ✅ **并行编译**: 多线程编译
- ✅ **缓存支持**: 增量编译

### 基础用法2

#### 安装2

```toml
[build-dependencies]
cc = "1.0"
```

#### 快速开始2

**helper.c**:

```c
#include <stdio.h>

int add(int a, int b) {
    return a + b;
}

void print_hello() {
    printf("Hello from C!\n");
}
```

**build.rs**:

```rust
fn main() {
    cc::Build::new()
        .file("src/helper.c")
        .compile("helper");
    
    println!("cargo:rerun-if-changed=src/helper.c");
}
```

**src/lib.rs**:

```rust
extern "C" {
    fn add(a: i32, b: i32) -> i32;
    fn print_hello();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        unsafe {
            assert_eq!(add(2, 3), 5);
            print_hello();
        }
    }
}
```

### 高级配置2

#### 1. C++项目

**math.cpp**:

```cpp
#include <iostream>

extern "C" {
    int multiply(int a, int b) {
        return a * b;
    }

    void print_message(const char* msg) {
        std::cout << "Message: " << msg << std::endl;
    }
}
```

**build.rs**:

```rust
fn main() {
    cc::Build::new()
        .cpp(true)  // 启用C++模式
        .file("src/math.cpp")
        .flag("-std=c++17")  // C++17标准
        .compile("mathlib");
}
```

#### 2. 链接外部库

```rust
fn main() {
    cc::Build::new()
        .file("src/helper.c")
        // 添加include路径
        .include("/usr/local/include")
        // 添加编译标志
        .flag("-O3")
        .flag("-march=native")
        // 定义宏
        .define("DEBUG", "1")
        .compile("helper");

    // 链接外部库
    println!("cargo:rustc-link-lib=static=mylib");
    println!("cargo:rustc-link-search=native=/usr/local/lib");
}
```

---

## cbindgen - 导出C头文件

### 核心特性3

- ✅ **自动生成**: 从Rust代码生成C/C++头文件
- ✅ **C/C++兼容**: 同时支持C和C++
- ✅ **文档注释**: 保留Rust文档注释
- ✅ **可配置**: 灵活的生成选项

### 基础用法3

**src/lib.rs**:

```rust
#[repr(C)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

/// Create a new point
#[no_mangle]
pub extern "C" fn point_new(x: i32, y: i32) -> *mut Point {
    Box::into_raw(Box::new(Point { x, y }))
}

/// Free a point
#[no_mangle]
pub extern "C" fn point_free(ptr: *mut Point) {
    if !ptr.is_null() {
        unsafe { Box::from_raw(ptr) };
    }
}

/// Get x coordinate
#[no_mangle]
pub extern "C" fn point_get_x(ptr: *const Point) -> i32 {
    unsafe { (*ptr).x }
}
```

**cbindgen.toml**:

```toml
language = "C"

[export]
include = ["Point"]
```

**生成头文件**:

```bash
cbindgen --config cbindgen.toml --crate my-crate --output point.h
```

**生成的 point.h**:

```c
#ifndef MY_CRATE_H
#define MY_CRATE_H

#include <stdint.h>

typedef struct Point {
    int32_t x;
    int32_t y;
} Point;

/**
 * Create a new point
 */
Point* point_new(int32_t x, int32_t y);

/**
 * Free a point
 */
void point_free(Point* ptr);

/**
 * Get x coordinate
 */
int32_t point_get_x(const Point* ptr);

#endif /* MY_CRATE_H */
```

---

## cxx - 现代C++互操作

### 核心特性4

- ✅ **安全C++绑定**: 类型安全的C++互操作
- ✅ **双向调用**: Rust↔C++双向调用
- ✅ **零成本抽象**: 无运行时开销
- ✅ **现代C++**: 支持C++11/14/17特性
- ✅ **异常安全**: 自动处理C++异常

### 基础用法4

**src/main.rs**:

```rust
#[cxx::bridge]
mod ffi {
    // C++类型和函数声明
    unsafe extern "C++" {
        include!("mylib.h");

        type MyClass;

        fn create_myclass(value: i32) -> UniquePtr<MyClass>;
        fn get_value(self: &MyClass) -> i32;
        fn set_value(self: Pin<&mut MyClass>, value: i32);
    }

    // Rust函数导出给C++
    extern "Rust" {
        fn rust_callback(x: i32) -> i32;
    }
}

fn rust_callback(x: i32) -> i32 {
    x * 2
}

fn main() {
    let mut obj = ffi::create_myclass(42);
    println!("Value: {}", obj.get_value());
    obj.pin_mut().set_value(100);
    println!("New value: {}", obj.get_value());
}
```

**include/mylib.h**:

```cpp
#pragma once
#include <memory>

class MyClass {
public:
    MyClass(int value) : value_(value) {}
    int get_value() const { return value_; }
    void set_value(int value) { value_ = value; }

private:
    int value_;
};

std::unique_ptr<MyClass> create_myclass(int value) {
    return std::make_unique<MyClass>(value);
}
```

---

## 使用场景

### 场景1: 集成现有C库

**需求描述**: 使用现有的图像处理C库

**推荐方案**: bindgen + cc

```rust
// build.rs
fn main() {
    // 编译C库
    cc::Build::new()
        .file("vendor/imagelib.c")
        .include("vendor/include")
        .compile("imagelib");

    // 生成绑定
    let bindings = bindgen::Builder::default()
        .header("vendor/include/imagelib.h")
        .generate()
        .unwrap();

    let out_path = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    bindings.write_to_file(out_path.join("bindings.rs")).unwrap();
}
```

```rust
// src/lib.rs
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub struct Image {
    inner: *mut ImageHandle,
}

impl Image {
    pub fn load(path: &str) -> Result<Self, String> {
        let c_path = std::ffi::CString::new(path).unwrap();
        let handle = unsafe { image_load(c_path.as_ptr()) };
        
        if handle.is_null() {
            Err("Failed to load image".to_string())
        } else {
            Ok(Image { inner: handle })
        }
    }

    pub fn width(&self) -> u32 {
        unsafe { image_get_width(self.inner) as u32 }
    }
}

impl Drop for Image {
    fn drop(&mut self) {
        unsafe { image_free(self.inner) };
    }
}
```

### 场景2: 导出Rust库给C使用

**需求描述**: 将Rust库提供给C项目使用

**推荐方案**: cbindgen

```rust
// src/lib.rs
#[repr(C)]
pub struct Config {
    pub timeout: u32,
    pub max_connections: u32,
}

#[no_mangle]
pub extern "C" fn config_default() -> Config {
    Config {
        timeout: 30,
        max_connections: 100,
    }
}

#[no_mangle]
pub extern "C" fn server_start(config: *const Config) -> bool {
    if config.is_null() {
        return false;
    }
    
    let config = unsafe { &*config };
    // 启动服务器...
    true
}
```

**使用cbindgen生成头文件**:

```bash
cbindgen --output server.h
```

**C代码使用**:

```c
#include "server.h"

int main() {
    Config config = config_default();
    config.timeout = 60;
    
    if (server_start(&config)) {
        printf("Server started\n");
    }
    
    return 0;
}
```

### 场景3: C++互操作

**需求描述**: Rust与C++项目互调

**推荐方案**: cxx

```rust
#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        include!("logger.h");
        
        type Logger;
        
        fn create_logger(name: &str) -> UniquePtr<Logger>;
        fn log_info(self: &Logger, msg: &str);
        fn log_error(self: &Logger, msg: &str);
    }
    
    extern "Rust" {
        fn process_data(data: Vec<u8>) -> Result<String>;
    }
}

fn process_data(data: Vec<u8>) -> Result<String, Box<dyn std::error::Error>> {
    // Rust处理逻辑
    Ok(String::from_utf8(data)?)
}
```

---

## 内存安全指南

### 1. 所有权管理

**描述**: 明确内存所有权归属

✅ **正确做法**:

```rust
// Rust拥有所有权
#[no_mangle]
pub extern "C" fn create_object() -> *mut MyObject {
    Box::into_raw(Box::new(MyObject::new()))
}

// C释放所有权
#[no_mangle]
pub extern "C" fn free_object(ptr: *mut MyObject) {
    if !ptr.is_null() {
        unsafe { Box::from_raw(ptr) };  // 自动释放
    }
}

// Rust借用，不转移所有权
#[no_mangle]
pub extern "C" fn use_object(ptr: *const MyObject) {
    unsafe {
        let obj = &*ptr;  // 借用
        // 使用obj...
    }  // obj生命周期结束，但不释放
}
```

### 2. 生命周期

```rust
// 错误：返回的引用生命周期不明确
// pub extern "C" fn get_data(ptr: *const MyObject) -> *const u8

// 正确：明确说明调用者不应持有返回的指针太久
/// # Safety
/// 返回的指针仅在ptr有效期内有效
#[no_mangle]
pub unsafe extern "C" fn get_data(ptr: *const MyObject) -> *const u8 {
    (*ptr).data.as_ptr()
}
```

### 3. 空指针检查

✅ **总是检查空指针**:

```rust
#[no_mangle]
pub extern "C" fn process(ptr: *const Data) -> bool {
    if ptr.is_null() {
        return false;
    }
    
    unsafe {
        let data = &*ptr;
        // 处理数据...
        true
    }
}
```

---

## 最佳实践

### 1. 安全封装

**描述**: 为unsafe FFI提供安全的Rust接口

✅ **正确做法**:

```rust
// 底层unsafe绑定
mod ffi {
    extern "C" {
        pub fn c_create_image(width: u32, height: u32) -> *mut std::ffi::c_void;
        pub fn c_free_image(ptr: *mut std::ffi::c_void);
        pub fn c_get_pixel(ptr: *mut std::ffi::c_void, x: u32, y: u32) -> u32;
    }
}

// 安全的Rust封装
pub struct Image {
    ptr: *mut std::ffi::c_void,
    width: u32,
    height: u32,
}

impl Image {
    pub fn new(width: u32, height: u32) -> Result<Self, String> {
        let ptr = unsafe { ffi::c_create_image(width, height) };
        if ptr.is_null() {
            Err("Failed to create image".to_string())
        } else {
            Ok(Image { ptr, width, height })
        }
    }

    pub fn get_pixel(&self, x: u32, y: u32) -> Option<u32> {
        if x >= self.width || y >= self.height {
            return None;
        }
        Some(unsafe { ffi::c_get_pixel(self.ptr, x, y) })
    }
}

impl Drop for Image {
    fn drop(&mut self) {
        unsafe { ffi::c_free_image(self.ptr) };
    }
}

// 用户代码完全安全
fn main() {
    let img = Image::new(800, 600).unwrap();
    if let Some(color) = img.get_pixel(10, 10) {
        println!("Pixel: {:06x}", color);
    }
}
```

### 2. 错误处理

```rust
// 将C错误码转换为Rust Result
#[no_mangle]
pub extern "C" fn do_operation(
    ptr: *const Data,
    out_error: *mut i32,
) -> bool {
    match do_operation_impl(ptr) {
        Ok(()) => {
            if !out_error.is_null() {
                unsafe { *out_error = 0 };
            }
            true
        }
        Err(e) => {
            if !out_error.is_null() {
                unsafe { *out_error = e.code() };
            }
            false
        }
    }
}

fn do_operation_impl(ptr: *const Data) -> Result<(), MyError> {
    // 实际逻辑...
    Ok(())
}
```

### 3. 文档和注释

```rust
/// 创建新对象
///
/// # Safety
///
/// 调用者必须：
/// - 使用 `free_object` 释放返回的指针
/// - 不能在多个线程中同时访问对象
///
/// # Returns
///
/// 成功返回非空指针，失败返回null
#[no_mangle]
pub unsafe extern "C" fn create_object() -> *mut MyObject {
    // ...
}
```

### 4. 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ffi_lifecycle() {
        unsafe {
            // 创建
            let ptr = create_object();
            assert!(!ptr.is_null());

            // 使用
            assert!(use_object(ptr));

            // 释放
            free_object(ptr);
        }
    }

    #[test]
    fn test_null_pointer_handling() {
        unsafe {
            assert!(!use_object(std::ptr::null()));
            free_object(std::ptr::null());  // 不应崩溃
        }
    }
}
```

### 5. ABI稳定性

```rust
// 使用#[repr(C)]确保内存布局稳定
#[repr(C)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

// 使用#[no_mangle]确保函数名不被修改
#[no_mangle]
pub extern "C" fn point_create() -> Point {
    Point { x: 0, y: 0 }
}

// 文档化ABI版本
/// ABI Version: 1.0.0
#[no_mangle]
pub extern "C" fn get_abi_version() -> u32 {
    0x01_00_00
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: 内存泄漏

**问题描述**: C分配的内存未释放

❌ **错误示例**:

```rust
extern "C" {
    fn c_create() -> *mut Data;
}

fn main() {
    let ptr = unsafe { c_create() };
    // 忘记释放！内存泄漏
}
```

✅ **正确做法**:

```rust
struct DataHandle(*mut Data);

impl Drop for DataHandle {
    fn drop(&mut self) {
        unsafe { c_free(self.0) };
    }
}

fn main() {
    let handle = DataHandle(unsafe { c_create() });
    // 自动释放
}
```

### ⚠️ 陷阱2: 悬垂指针

**问题描述**: 使用已释放的内存

❌ **错误示例**:

```rust
let data: Vec<u8> = vec![1, 2, 3];
let ptr = data.as_ptr();
drop(data);  // data被释放
unsafe { c_process(ptr) };  // 悬垂指针！未定义行为
```

✅ **正确做法**:

```rust
let data: Vec<u8> = vec![1, 2, 3];
unsafe { c_process(data.as_ptr()) };
// data在此之后才被释放
```

### ⚠️ 陷阱3: 数据竞争

**问题描述**: 多线程访问共享数据

❌ **错误示例**:

```rust
static mut GLOBAL_DATA: *mut Data = std::ptr::null_mut();

// 线程A
unsafe { GLOBAL_DATA = create_data() };

// 线程B
unsafe { use_data(GLOBAL_DATA) };  // 数据竞争！
```

✅ **正确做法**:

```rust
use std::sync::Mutex;

static GLOBAL_DATA: Mutex<Option<*mut Data>> = Mutex::new(None);

// 线程安全访问
let mut data = GLOBAL_DATA.lock().unwrap();
*data = Some(unsafe { create_data() });
```

### ⚠️ 陷阱4: ABI不兼容

❌ **错误示例**:

```rust
// Rust默认布局（不稳定）
pub struct Point {
    pub x: i32,
    pub y: i32,
}
```

✅ **正确做法**:

```rust
// 使用C布局
#[repr(C)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}
```

### ⚠️ 陷阱5: 未定义行为

❌ **错误示例**:

```rust
// 解引用空指针
unsafe {
    let x = *std::ptr::null::<i32>();  // UB!
}

// 数据竞争
unsafe {
    *ptr = 42;  // 同时有其他线程访问ptr
}
```

### ⚠️ 陷阱6: 字符串处理

❌ **错误示例**:

```rust
// 忘记null终止符
let s = CString::new("Hello").unwrap();
unsafe { c_print(s.as_ptr()) };
// s被drop，悬垂指针
```

✅ **正确做法**:

```rust
let s = CString::new("Hello").unwrap();
unsafe { c_print(s.as_ptr()) };
drop(s);  // 显式drop，确保生命周期
```

### ⚠️ 陷阱7: 回调函数生命周期

❌ **错误示例**:

```rust
let data = vec![1, 2, 3];
let callback = || {
    data.len()  // 捕获data
};
unsafe { c_register_callback(&callback as *const _ as *const _) };
drop(data);  // data被释放，callback悬垂
```

### ⚠️ 陷阱8: 平台差异

```rust
// 类型大小在不同平台可能不同
#[repr(C)]
pub struct Data {
    pub ptr: usize,  // 32位: 4字节, 64位: 8字节
}

// 使用固定大小类型
#[repr(C)]
pub struct Data {
    pub ptr: *mut std::ffi::c_void,  // 平台无关
}
```

---

## 参考资源

### 官方文档

- 📚 [Rust FFI指南](https://doc.rust-lang.org/nomicon/ffi.html)
- 📚 [libc文档](https://docs.rs/libc/)
- 📚 [bindgen文档](https://rust-lang.github.io/rust-bindgen/)
- 📚 [cc文档](https://docs.rs/cc/)
- 📚 [cbindgen文档](https://github.com/eqrion/cbindgen/blob/master/docs.md)
- 📚 [cxx文档](https://cxx.rs/)

### 教程与文章

- 📖 [Rust FFI Omnibus](http://jakegoulding.com/rust-ffi-omnibus/)
- 📖 [The Rust FFI Guide](https://michael-f-bryan.github.io/rust-ffi-guide/)
- 📖 [Unsafe Rust指南](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)

### 示例项目

- 💻 [rust-ffi-examples](https://github.com/alexcrichton/rust-ffi-examples)
- 💻 [bindgen examples](https://github.com/rust-lang/rust-bindgen/tree/master/bindgen-integration)
- 💻 [cxx examples](https://github.com/dtolnay/cxx/tree/master/demo)

### 相关文档

- 🔗 [Unsafe Rust](../unsafe/README.md)
- 🔗 [内存管理](../memory/README.md)
- 🔗 [系统编程](../process_system/README.md)
- 🔗 [跨平台开发](../../cross_cutting/cross_platform/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区  
**文档长度**: 1000+ 行
