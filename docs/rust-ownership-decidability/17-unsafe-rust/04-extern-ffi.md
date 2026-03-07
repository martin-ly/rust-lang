# FFI 与外部代码交互

> **权威来源**: The Rustonomicon (FFI), The Rust Reference
> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: Unsafe Rust, Data Layout

---

## 目录

- [FFI 与外部代码交互](#ffi-与外部代码交互)
  - [目录](#目录)
  - [1. FFI 基础](#1-ffi-基础)
    - [1.1 什么是 FFI](#11-什么是-ffi)
    - [1.2 ABI 类型](#12-abi-类型)
  - [2. 调用 C 代码](#2-调用-c-代码)
    - [2.1 基本示例](#21-基本示例)
    - [2.2 字符串处理](#22-字符串处理)
    - [2.3 结构体传递](#23-结构体传递)
  - [3. 被 C 调用](#3-被-c-调用)
    - [3.1 创建 C 兼容库](#31-创建-c-兼容库)
    - [3.2 C 头文件](#32-c-头文件)
  - [4. 类型映射](#4-类型映射)
    - [4.1 基本类型](#41-基本类型)
    - [4.2 字符串类型](#42-字符串类型)
  - [5. 内存管理](#5-内存管理)
    - [5.1 所有权规则](#51-所有权规则)
    - [5.2 安全包装示例](#52-安全包装示例)
  - [6. 常见模式与陷阱](#6-常见模式与陷阱)
    - [6.1 Panic 安全](#61-panic-安全)
    - [6.2 空指针检查](#62-空指针检查)
    - [6.3 线程安全](#63-线程安全)
  - [参考](#参考)

---

## 1. FFI 基础

### 1.1 什么是 FFI

FFI (Foreign Function Interface) 允许 Rust 代码与其他语言（主要是 C）交互。

```rust
// 声明外部函数
extern "C" {
    fn sqrt(x: f64) -> f64;
    fn strlen(s: *const c_char) -> usize;
}

// 使用
unsafe {
    let r = sqrt(2.0);
}
```

### 1.2 ABI 类型

```rust
// 不同的调用约定
extern "C" {           // C 标准调用约定
    fn c_function();
}

extern "system" {      // 系统默认 (Windows 上是 stdcall)
    fn system_function();
}

extern "C-unwind" {    // 支持栈展开 (Rust 1.71+)
    fn may_panic();
}
```

---

## 2. 调用 C 代码

### 2.1 基本示例

```c
// mathlib.c
int add(int a, int b) {
    return a + b;
}
```

```rust
// main.rs
use std::os::raw::c_int;

#[link(name = "mathlib")]
extern "C" {
    fn add(a: c_int, b: c_int) -> c_int;
}

fn main() {
    unsafe {
        let result = add(2, 3);
        println!("2 + 3 = {}", result);
    }
}
```

### 2.2 字符串处理

```rust
use std::ffi::{CString, CStr};
use std::os::raw::c_char;

extern "C" {
    fn process_string(s: *const c_char) -> *mut c_char;
    fn free_string(s: *mut c_char);
}

fn call_c_function(input: &str) -> String {
    // Rust String -> C 字符串
    let c_input = CString::new(input).unwrap();

    unsafe {
        let c_output = process_string(c_input.as_ptr());

        // C 字符串 -> Rust String
        let result = CStr::from_ptr(c_output)
            .to_string_lossy()
            .into_owned();

        // 释放 C 分配的内存
        free_string(c_output);

        result
    }
}
```

### 2.3 结构体传递

```c
// point.h
typedef struct {
    double x;
    double y;
} Point;

double point_distance(Point p1, Point p2);
```

```rust
use std::os::raw::c_double;

#[repr(C)]  // 关键！确保 C 兼容布局
pub struct Point {
    x: c_double,
    y: c_double,
}

#[link(name = "geometry")]
extern "C" {
    fn point_distance(p1: Point, p2: Point) -> c_double;
}

fn main() {
    let p1 = Point { x: 0.0, y: 0.0 };
    let p2 = Point { x: 3.0, y: 4.0 };

    unsafe {
        let dist = point_distance(p1, p2);
        assert_eq!(dist, 5.0);
    }
}
```

---

## 3. 被 C 调用

### 3.1 创建 C 兼容库

```rust
// lib.rs - 编译为动态库
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};

/// 暴露给 C 的函数
///
/// # Safety
/// - name 必须是有效的 UTF-8 C 字符串
#[no_mangle]  // 防止名称修饰
pub extern "C" fn rust_greet(name: *const c_char) -> *mut c_char {
    // 安全检查
    if name.is_null() {
        return std::ptr::null_mut();
    }

    let name_str = unsafe {
        match CStr::from_ptr(name).to_str() {
            Ok(s) => s,
            Err(_) => return std::ptr::null_mut(),
        }
    };

    let greeting = format!("Hello, {}!", name_str);

    // 返回 C 兼容的字符串（调用者负责释放）
    match CString::new(greeting) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// 释放 Rust 分配的字符串
#[no_mangle]
pub extern "C" fn rust_free_string(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            let _ = CString::from_raw(s);  // 获取所有权并 drop
        }
    }
}
```

### 3.2 C 头文件

```c
// rustlib.h
#ifndef RUSTLIB_H
#define RUSTLIB_H

#ifdef __cplusplus
extern "C" {
#endif

// 创建问候语
// 返回的字符串必须使用 rust_free_string 释放
char* rust_greet(const char* name);

// 释放 Rust 分配的字符串
void rust_free_string(char* s);

#ifdef __cplusplus
}
#endif

#endif
```

---

## 4. 类型映射

### 4.1 基本类型

| C 类型 | Rust 类型 | 说明 |
|--------|----------|------|
| `int` | `c_int` | `std::os::raw::c_int` |
| `unsigned int` | `c_uint` | - |
| `long` | `c_long` | - |
| `size_t` | `usize` | - |
| `void*` | `*mut c_void` | - |
| `char*` | `*mut c_char` | 注意：C char 是有符号的 |
| `bool` (C99) | `bool` | 布局可能不同 |

### 4.2 字符串类型

```rust
// C 字符串 ↔ Rust String

// &str / String -> *const c_char
let cstr = CString::new("hello").unwrap();
let ptr: *const c_char = cstr.as_ptr();

// *const c_char -> &str
let cstr = unsafe { CStr::from_ptr(ptr) };
let rstr: &str = cstr.to_str()?;
```

---

## 5. 内存管理

### 5.1 所有权规则

```
┌─────────────────────────────────────────────────────────┐
│                    FFI 内存所有权                        │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Rust 分配 → Rust 释放                                  │
│  C 分配 → C 释放                                        │
│  混合 = 内存泄漏或 Use-after-free                       │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 5.2 安全包装示例

```rust
pub struct CVector {
    ptr: *mut f64,
    len: usize,
}

extern "C" {
    fn vec_create(len: usize) -> *mut f64;
    fn vec_free(vec: *mut f64);
}

impl CVector {
    pub fn new(len: usize) -> Option<Self> {
        let ptr = unsafe { vec_create(len) };
        if ptr.is_null() {
            return None;
        }
        Some(Self { ptr, len })
    }

    pub fn as_slice(&self) -> &[f64] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [f64] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

impl Drop for CVector {
    fn drop(&mut self) {
        unsafe { vec_free(self.ptr); }
    }
}
```

---

## 6. 常见模式与陷阱

### 6.1 Panic 安全

```rust
// ❌ 危险：panic 跨越 FFI 边界是 UB
#[no_mangle]
pub extern "C" fn may_panic() {
    panic!("oops");  // UB!
}

// ✅ 正确：捕获 panic
#[no_mangle]
pub extern "C" fn safe_function() -> c_int {
    match std::panic::catch_unwind(|| {
        // 可能 panic 的代码
        risky_operation()
    }) {
        Ok(result) => result,
        Err(_) => -1,  // 错误码
    }
}
```

### 6.2 空指针检查

```rust
// ❌ 危险：可能空指针解引用
#[no_mangle]
pub extern "C" fn unsafe_func(ptr: *const c_char) {
    let s = unsafe { CStr::from_ptr(ptr) };  // UB if null!
}

// ✅ 正确：检查空指针
#[no_mangle]
pub extern "C" fn safe_func(ptr: *const c_char) -> c_int {
    if ptr.is_null() {
        return -1;
    }
    // 现在安全
    0
}
```

### 6.3 线程安全

```rust
// ❌ 危险：非线程安全函数
static mut GLOBAL: i32 = 0;

#[no_mangle]
pub extern "C" fn increment() {
    unsafe { GLOBAL += 1; }  // 数据竞争！
}

// ✅ 正确：使用原子操作
use std::sync::atomic::{AtomicI32, Ordering};

static GLOBAL: AtomicI32 = AtomicI32::new(0);

#[no_mangle]
pub extern "C" fn increment() {
    GLOBAL.fetch_add(1, Ordering::SeqCst);
}
```

---

## 参考

- [The Rustonomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html)
- [bindgen](https://github.com/rust-lang/rust-bindgen) - 自动生成 FFI 绑定
- [cbindgen](https://github.com/mozilla/cbindgen) - 生成 C 头文件

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
