# FFI/ABI 与 repr 完整指南

**版本**: Rust 1.90  
**创建日期**: 2025-10-19  
**文档状态**: ✅ 完整

---

## 📋 目录

- [FFI/ABI 与 repr 完整指南](#ffiabi-与-repr-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
  - [repr 属性详解](#repr-属性详解)
    - [repr(Rust) - 默认布局](#reprrust---默认布局)
    - [repr(C) - C 兼容布局 ✅](#reprc---c-兼容布局-)
    - [repr(transparent) - 透明包装](#reprtransparent---透明包装)
    - [repr(packed) - 紧凑布局](#reprpacked---紧凑布局)
    - [repr(align(N)) - 指定对齐](#repralignn---指定对齐)
  - [FFI 基础](#ffi-基础)
    - [extern "C" 声明](#extern-c-声明)
    - [导出 Rust 函数到 C](#导出-rust-函数到-c)
    - [ABI 选择](#abi-选择)
  - [数据类型映射](#数据类型映射)
    - [基本类型映射](#基本类型映射)
    - [指针类型](#指针类型)
    - [结构体映射](#结构体映射)
    - [枚举映射](#枚举映射)
    - [字符串映射](#字符串映射)
  - [所有权与生命周期](#所有权与生命周期)
    - [跨边界传递所有权](#跨边界传递所有权)
    - [借用检查](#借用检查)
  - [错误处理](#错误处理)
    - [方法 1: 返回错误码](#方法-1-返回错误码)
    - [方法 2: 使用 `Option<Box<T>>`](#方法-2-使用-optionboxt)
    - [方法 3: 使用线程局部错误](#方法-3-使用线程局部错误)
  - [回调函数](#回调函数)
    - [C 回调到 Rust](#c-回调到-rust)
    - [带状态的回调](#带状态的回调)
  - [最佳实践](#最佳实践)
    - [1. 类型安全封装](#1-类型安全封装)
    - [2. 使用 newtype 模式](#2-使用-newtype-模式)
    - [3. 自动资源管理](#3-自动资源管理)
  - [实战示例](#实战示例)
    - [示例 1: 完整的 C 库绑定](#示例-1-完整的-c-库绑定)
    - [示例 2: Rust 库供 C 使用](#示例-2-rust-库供-c-使用)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [工具推荐](#工具推荐)
    - [相关文档](#相关文档)

---

## 概述

**FFI (Foreign Function Interface)** 允许 Rust 代码与其他语言（主要是 C/C++）进行互操作。
正确的内存布局（通过 `repr` 属性）和调用约定（通过 `extern`）是 FFI 安全性的关键。

### 核心概念

- **repr**: 控制类型的内存布局
- **extern**: 指定函数的调用约定（ABI）
- **FFI Safe**: 可以安全地跨语言边界传递的类型

---

## repr 属性详解

### repr(Rust) - 默认布局

```rust
// 默认布局，编译器可自由优化
struct MyStruct {
    a: u8,
    b: u32,
    c: u16,
}

// ⚠️ 布局未定义，不同编译可能不同
// ❌ 不能用于 FFI
```

**特点**:

- 编译器可以重排字段顺序
- 可以添加任意填充
- 优化空间占用
- **不保证稳定性**

### repr(C) - C 兼容布局 ✅

```rust
// C 兼容布局
#[repr(C)]
struct CStruct {
    a: u8,
    // padding: 3 bytes
    b: u32,
    c: u16,
    // padding: 2 bytes
}

// ✅ 布局保证与 C 兼容
// ✅ 字段顺序固定
// ✅ 可用于 FFI
```

**特点**:

- 与 C 结构体布局完全一致
- 字段按声明顺序排列
- 遵循 C 的对齐规则
- **跨语言边界安全**

**C 等价**:

```c
struct CStruct {
    uint8_t a;
    uint32_t b;
    uint16_t c;
};
```

### repr(transparent) - 透明包装

```rust
// 透明包装：与内部类型布局完全相同
#[repr(transparent)]
struct Wrapper(u32);

// ✅ 与 u32 布局完全相同
// ✅ 可以安全地转换
assert_eq!(
    std::mem::size_of::<Wrapper>(),
    std::mem::size_of::<u32>()
);
```

**使用场景**:

```rust
// 新类型模式 + FFI
#[repr(transparent)]
struct FileDescriptor(i32);

extern "C" {
    fn close(fd: i32) -> i32;
}

impl FileDescriptor {
    fn close(self) -> Result<(), std::io::Error> {
        unsafe {
            if close(self.0) == -1 {
                Err(std::io::Error::last_os_error())
            } else {
                Ok(())
            }
        }
    }
}
```

**限制**:

- 只能有一个非零大小字段
- 可以有多个零大小字段（PhantomData）

```rust
use std::marker::PhantomData;

// ✅ 合法
#[repr(transparent)]
struct Wrapper<T> {
    value: i32,
    _marker: PhantomData<T>,
}

// ❌ 非法：多个非零大小字段
#[repr(transparent)]
struct Invalid {
    a: i32,
    b: i32,  // 错误！
}
```

### repr(packed) - 紧凑布局

```rust
// 移除所有填充
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32,  // 未对齐！
    c: u16,
}

// ⚠️ 总大小：7 bytes（无填充）
// ⚠️ 未对齐引用是 UB
```

**详见**: [repr(packed) 安全注意事项](./04_ffi_safety.md)

### repr(align(N)) - 指定对齐

```rust
// 指定最小对齐
#[repr(align(16))]
struct Aligned {
    data: [u8; 12],
}

// ✅ 对齐到 16 字节边界
assert_eq!(std::mem::align_of::<Aligned>(), 16);
assert_eq!(std::mem::size_of::<Aligned>(), 16);
```

**使用场景**:

- SIMD 优化
- 缓存行对齐
- 硬件要求

```rust
// 缓存行对齐（64 字节）
#[repr(align(64))]
struct CacheAligned {
    data: [u64; 4],
}
```

---

## FFI 基础

### extern "C" 声明

```rust
// 调用 C 函数
extern "C" {
    // 标准 C 库函数
    fn strlen(s: *const i8) -> usize;
    fn malloc(size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
    
    // 自定义 C 函数
    fn custom_function(a: i32, b: i32) -> i32;
}

// 使用
fn use_c_functions() {
    unsafe {
        let s = b"Hello\0";
        let len = strlen(s.as_ptr() as *const i8);
        println!("Length: {}", len);
        
        let ptr = malloc(100);
        if !ptr.is_null() {
            free(ptr);
        }
    }
}
```

### 导出 Rust 函数到 C

```rust
// 导出函数给 C 调用
#[no_mangle]
pub extern "C" fn rust_add(a: i32, b: i32) -> i32 {
    a + b
}

#[no_mangle]
pub extern "C" fn rust_process_data(
    data: *const u8,
    len: usize,
) -> i32 {
    if data.is_null() {
        return -1;
    }
    
    unsafe {
        let slice = std::slice::from_raw_parts(data, len);
        // 处理数据
        slice.len() as i32
    }
}
```

**C 头文件**:

```c
// rust_lib.h
#ifdef __cplusplus
extern "C" {
#endif

int32_t rust_add(int32_t a, int32_t b);
int32_t rust_process_data(const uint8_t* data, size_t len);

#ifdef __cplusplus
}
#endif
```

### ABI 选择

```rust
// C ABI（最常用）
extern "C" fn c_abi() {}

// System ABI（平台默认）
extern "system" fn system_abi() {}

// Rust ABI（默认，不稳定）
extern "Rust" fn rust_abi() {}  // 等同于不加 extern

// Win64 ABI
extern "win64" fn win64_abi() {}

// x86_64 平台特定
extern "sysv64" fn sysv64_abi() {}
```

---

## 数据类型映射

### 基本类型映射

| Rust 类型 | C 类型 | 大小 | 对齐 |
|-----------|--------|------|------|
| `i8` | `int8_t` / `char` | 1 | 1 |
| `u8` | `uint8_t` / `unsigned char` | 1 | 1 |
| `i16` | `int16_t` / `short` | 2 | 2 |
| `u16` | `uint16_t` / `unsigned short` | 2 | 2 |
| `i32` | `int32_t` / `int` | 4 | 4 |
| `u32` | `uint32_t` / `unsigned int` | 4 | 4 |
| `i64` | `int64_t` / `long long` | 8 | 8 |
| `u64` | `uint64_t` / `unsigned long long` | 8 | 8 |
| `isize` | `intptr_t` / `ptrdiff_t` | 平台相关 | 平台相关 |
| `usize` | `uintptr_t` / `size_t` | 平台相关 | 平台相关 |
| `f32` | `float` | 4 | 4 |
| `f64` | `double` | 8 | 8 |

### 指针类型

```rust
// Rust → C
*const T    // const T*
*mut T      // T*
&T          // const T* (生命周期内有效)
&mut T      // T* (生命周期内有效)

// 示例
extern "C" {
    fn process_const(data: *const u8, len: usize);
    fn process_mut(data: *mut u8, len: usize);
}

fn use_pointers() {
    let data = vec![1, 2, 3, 4, 5];
    
    unsafe {
        // 只读访问
        process_const(data.as_ptr(), data.len());
        
        // 可写访问（需要 mut）
        let mut data_mut = data.clone();
        process_mut(data_mut.as_mut_ptr(), data_mut.len());
    }
}
```

### 结构体映射

```rust
// Rust 结构体
#[repr(C)]
struct Point {
    x: f64,
    y: f64,
}

#[repr(C)]
struct Rectangle {
    top_left: Point,
    bottom_right: Point,
}

// 对应的 C 结构体
/*
struct Point {
    double x;
    double y;
};

struct Rectangle {
    struct Point top_left;
    struct Point bottom_right;
};
*/

extern "C" {
    fn calculate_area(rect: *const Rectangle) -> f64;
}

fn use_rect() {
    let rect = Rectangle {
        top_left: Point { x: 0.0, y: 10.0 },
        bottom_right: Point { x: 10.0, y: 0.0 },
    };
    
    unsafe {
        let area = calculate_area(&rect);
        println!("Area: {}", area);
    }
}
```

### 枚举映射

```rust
// C 风格枚举
#[repr(C)]
enum Status {
    Success = 0,
    Error = 1,
    Pending = 2,
}

// C 等价
/*
enum Status {
    SUCCESS = 0,
    ERROR = 1,
    PENDING = 2,
};
*/

// ⚠️ Rust 枚举与 C 枚举不同！
// Rust 枚举可能有关联数据
#[repr(C)]
enum Result {
    Ok,
    Err(i32),  // ⚠️ C 没有对应概念
}
```

**安全的枚举映射**:

```rust
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq)]
enum CStatus {
    Success = 0,
    ErrorInvalidInput = 1,
    ErrorOutOfMemory = 2,
    ErrorUnknown = 3,
}

impl From<i32> for CStatus {
    fn from(code: i32) -> Self {
        match code {
            0 => CStatus::Success,
            1 => CStatus::ErrorInvalidInput,
            2 => CStatus::ErrorOutOfMemory,
            _ => CStatus::ErrorUnknown,
        }
    }
}
```

### 字符串映射

```rust
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

// C 字符串（以 null 结尾）
extern "C" {
    fn process_string(s: *const c_char) -> i32;
    fn get_string() -> *const c_char;
}

// Rust → C
fn rust_to_c_string() {
    let rust_str = "Hello, C!";
    
    // 方法 1: CString（拥有所有权）
    let c_string = CString::new(rust_str).expect("CString::new failed");
    unsafe {
        process_string(c_string.as_ptr());
    }
    // c_string 离开作用域时自动释放
    
    // 方法 2: 手动添加 null 字节
    let bytes = b"Hello\0";
    unsafe {
        process_string(bytes.as_ptr() as *const c_char);
    }
}

// C → Rust
fn c_to_rust_string() {
    unsafe {
        let c_ptr = get_string();
        
        if c_ptr.is_null() {
            println!("Got null pointer");
            return;
        }
        
        // 借用 C 字符串（不拥有所有权）
        let c_str = CStr::from_ptr(c_ptr);
        
        // 转换为 Rust 字符串
        match c_str.to_str() {
            Ok(rust_str) => println!("Got: {}", rust_str),
            Err(e) => println!("Invalid UTF-8: {}", e),
        }
    }
}
```

---

## 所有权与生命周期

### 跨边界传递所有权

```rust
use std::boxed::Box;

// ✅ Rust 创建，C 使用，Rust 释放
#[no_mangle]
pub extern "C" fn create_data() -> *mut Data {
    let data = Box::new(Data::new());
    Box::into_raw(data)
}

#[no_mangle]
pub extern "C" fn free_data(ptr: *mut Data) {
    if !ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(ptr);
            // Box 离开作用域时自动释放
        }
    }
}

#[repr(C)]
pub struct Data {
    value: i32,
}

impl Data {
    fn new() -> Self {
        Data { value: 42 }
    }
}
```

**C 使用示例**:

```c
// C 代码
Data* data = create_data();
// 使用 data
printf("%d\n", data->value);
// 释放
free_data(data);
```

### 借用检查

```rust
// ❌ 错误：悬垂引用
#[no_mangle]
pub extern "C" fn get_string() -> *const u8 {
    let s = String::from("Hello");
    s.as_ptr()  // ❌ s 离开作用域后被释放
}

// ✅ 正确：使用静态生命周期
#[no_mangle]
pub extern "C" fn get_static_string() -> *const u8 {
    const S: &str = "Hello";
    S.as_ptr()
}

// ✅ 正确：转移所有权
#[no_mangle]
pub extern "C" fn create_string() -> *mut u8 {
    let s = String::from("Hello");
    let boxed = s.into_boxed_str();
    Box::into_raw(boxed) as *mut u8
}

#[no_mangle]
pub extern "C" fn free_string(ptr: *mut u8, len: usize) {
    unsafe {
        let _ = Box::from_raw(std::slice::from_raw_parts_mut(ptr, len));
    }
}
```

---

## 错误处理

### 方法 1: 返回错误码

```rust
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub enum ErrorCode {
    Success = 0,
    InvalidInput = 1,
    OutOfMemory = 2,
    IoError = 3,
}

#[no_mangle]
pub extern "C" fn process_data(
    data: *const u8,
    len: usize,
    result: *mut i32,
) -> ErrorCode {
    // 参数验证
    if data.is_null() || result.is_null() {
        return ErrorCode::InvalidInput;
    }
    
    // 处理数据
    let slice = unsafe { std::slice::from_raw_parts(data, len) };
    
    match do_processing(slice) {
        Ok(value) => {
            unsafe { *result = value; }
            ErrorCode::Success
        }
        Err(_) => ErrorCode::IoError,
    }
}

fn do_processing(data: &[u8]) -> Result<i32, std::io::Error> {
    // 实际处理逻辑
    Ok(data.len() as i32)
}
```

### 方法 2: 使用 `Option<Box<T>>`

```rust
#[no_mangle]
pub extern "C" fn try_create_data() -> *mut Data {
    match Data::try_new() {
        Some(data) => Box::into_raw(Box::new(data)),
        None => std::ptr::null_mut(),  // 表示失败
    }
}

#[repr(C)]
pub struct Data {
    value: i32,
}

impl Data {
    fn try_new() -> Option<Self> {
        Some(Data { value: 42 })
    }
}
```

### 方法 3: 使用线程局部错误

```rust
use std::cell::RefCell;

thread_local! {
    static LAST_ERROR: RefCell<Option<String>> = RefCell::new(None);
}

fn set_last_error(err: String) {
    LAST_ERROR.with(|e| *e.borrow_mut() = Some(err));
}

#[no_mangle]
pub extern "C" fn get_last_error() -> *const c_char {
    LAST_ERROR.with(|e| {
        match &*e.borrow() {
            Some(err) => {
                let c_str = CString::new(err.clone()).unwrap();
                c_str.into_raw()
            }
            None => std::ptr::null(),
        }
    })
}

#[no_mangle]
pub extern "C" fn free_error_string(ptr: *mut c_char) {
    if !ptr.is_null() {
        unsafe { let _ = CString::from_raw(ptr); }
    }
}
```

---

## 回调函数

### C 回调到 Rust

```rust
// 回调函数类型
type Callback = extern "C" fn(i32) -> i32;

// 接受回调
#[no_mangle]
pub extern "C" fn register_callback(cb: Callback) {
    // 调用回调
    let result = cb(42);
    println!("Callback returned: {}", result);
}

// Rust 端回调实现
extern "C" fn my_callback(value: i32) -> i32 {
    println!("Received: {}", value);
    value * 2
}

fn use_callback() {
    unsafe {
        register_callback(my_callback);
    }
}
```

### 带状态的回调

```rust
use std::os::raw::c_void;

// 回调函数带 userdata
type CallbackWithData = extern "C" fn(*mut c_void, i32) -> i32;

#[no_mangle]
pub extern "C" fn process_with_callback(
    cb: CallbackWithData,
    userdata: *mut c_void,
) {
    unsafe {
        let result = cb(userdata, 42);
        println!("Result: {}", result);
    }
}

// 使用示例
struct CallbackState {
    multiplier: i32,
}

extern "C" fn callback_with_state(
    userdata: *mut c_void,
    value: i32,
) -> i32 {
    unsafe {
        let state = &mut *(userdata as *mut CallbackState);
        value * state.multiplier
    }
}

fn use_callback_with_state() {
    let mut state = CallbackState { multiplier: 3 };
    
    unsafe {
        process_with_callback(
            callback_with_state,
            &mut state as *mut _ as *mut c_void,
        );
    }
}
```

---

## 最佳实践

### 1. 类型安全封装

```rust
// 隐藏不安全的 FFI 细节
mod ffi {
    use super::*;
    
    extern "C" {
        pub(super) fn c_process_data(
            data: *const u8,
            len: usize,
        ) -> i32;
    }
}

// 提供安全的 Rust API
pub fn process_data(data: &[u8]) -> Result<i32, std::io::Error> {
    let result = unsafe {
        ffi::c_process_data(data.as_ptr(), data.len())
    };
    
    if result >= 0 {
        Ok(result)
    } else {
        Err(std::io::Error::last_os_error())
    }
}
```

### 2. 使用 newtype 模式

```rust
#[repr(transparent)]
pub struct Handle(usize);

impl Handle {
    pub fn new(value: usize) -> Self {
        Handle(value)
    }
    
    pub fn as_raw(&self) -> usize {
        self.0
    }
}

// 类型安全的 API
extern "C" {
    fn create_handle() -> usize;
    fn use_handle(handle: usize);
}

pub fn create() -> Handle {
    Handle(unsafe { create_handle() })
}

pub fn use_handle_safe(handle: &Handle) {
    unsafe { use_handle(handle.as_raw()) }
}
```

### 3. 自动资源管理

```rust
pub struct Resource {
    handle: *mut c_void,
}

impl Resource {
    pub fn new() -> Option<Self> {
        let handle = unsafe { ffi_create_resource() };
        if handle.is_null() {
            None
        } else {
            Some(Resource { handle })
        }
    }
}

impl Drop for Resource {
    fn drop(&mut self) {
        unsafe {
            ffi_destroy_resource(self.handle);
        }
    }
}

extern "C" {
    fn ffi_create_resource() -> *mut c_void;
    fn ffi_destroy_resource(handle: *mut c_void);
}
```

---

## 实战示例

### 示例 1: 完整的 C 库绑定

```rust
// lib.rs - Safe Rust wrapper for C library

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};

mod ffi {
    use super::*;
    
    #[repr(C)]
    pub struct CContext {
        _private: [u8; 0],
    }
    
    extern "C" {
        pub fn context_create() -> *mut CContext;
        pub fn context_destroy(ctx: *mut CContext);
        pub fn context_process(
            ctx: *mut CContext,
            input: *const c_char,
            output: *mut c_char,
            output_len: usize,
        ) -> c_int;
    }
}

pub struct Context {
    raw: *mut ffi::CContext,
}

impl Context {
    pub fn new() -> Option<Self> {
        let raw = unsafe { ffi::context_create() };
        if raw.is_null() {
            None
        } else {
            Some(Context { raw })
        }
    }
    
    pub fn process(&mut self, input: &str) -> Result<String, String> {
        let c_input = CString::new(input)
            .map_err(|e| format!("Invalid input: {}", e))?;
        
        let mut output = vec![0u8; 1024];
        
        let result = unsafe {
            ffi::context_process(
                self.raw,
                c_input.as_ptr(),
                output.as_mut_ptr() as *mut c_char,
                output.len(),
            )
        };
        
        if result == 0 {
            let c_str = unsafe { CStr::from_ptr(output.as_ptr() as *const c_char) };
            Ok(c_str.to_string_lossy().into_owned())
        } else {
            Err(format!("Processing failed with code {}", result))
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            ffi::context_destroy(self.raw);
        }
    }
}

unsafe impl Send for Context {}
unsafe impl Sync for Context {}
```

### 示例 2: Rust 库供 C 使用

```rust
// lib.rs - Rust library for C

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::panic;

#[repr(C)]
pub struct RustContext {
    data: Vec<u8>,
    counter: usize,
}

#[no_mangle]
pub extern "C" fn rust_context_new() -> *mut RustContext {
    let ctx = Box::new(RustContext {
        data: Vec::new(),
        counter: 0,
    });
    Box::into_raw(ctx)
}

#[no_mangle]
pub extern "C" fn rust_context_free(ctx: *mut RustContext) {
    if !ctx.is_null() {
        unsafe { let _ = Box::from_raw(ctx); }
    }
}

#[no_mangle]
pub extern "C" fn rust_context_add_data(
    ctx: *mut RustContext,
    data: *const u8,
    len: usize,
) -> i32 {
    if ctx.is_null() || data.is_null() {
        return -1;
    }
    
    let result = panic::catch_unwind(|| {
        unsafe {
            let ctx = &mut *ctx;
            let slice = std::slice::from_raw_parts(data, len);
            ctx.data.extend_from_slice(slice);
            ctx.counter += 1;
        }
    });
    
    match result {
        Ok(_) => 0,
        Err(_) => -2,
    }
}

#[no_mangle]
pub extern "C" fn rust_context_get_count(ctx: *const RustContext) -> usize {
    if ctx.is_null() {
        return 0;
    }
    unsafe { (*ctx).counter }
}
```

**对应的 C 头文件**:

```c
// rust_lib.h
#ifndef RUST_LIB_H
#define RUST_LIB_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct RustContext RustContext;

RustContext* rust_context_new(void);
void rust_context_free(RustContext* ctx);
int32_t rust_context_add_data(
    RustContext* ctx,
    const uint8_t* data,
    size_t len
);
size_t rust_context_get_count(const RustContext* ctx);

#ifdef __cplusplus
}
#endif

#endif // RUST_LIB_H
```

---

## 🔗 相关资源

### 官方文档

- [Rust FFI Omnibus](http://jakegoulding.com/rust-ffi-omnibus/)
- [Rust Reference - FFI](https://doc.rust-lang.org/reference/items/external-blocks.html)
- [Rustonomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html)

### 工具推荐

- [bindgen](https://github.com/rust-lang/rust-bindgen) - 自动生成 C 绑定
- [cbindgen](https://github.com/eqrion/cbindgen) - 为 Rust 生成 C 头文件
- [safer-ffi](https://github.com/getditto/safer-ffi) - 安全的 FFI 工具

### 相关文档

- [内存安全](./01_memory_safety.md)
- [repr(packed) 安全](./04_ffi_safety.md)
- [类型安全](./02_type_safety.md)

---

**维护状态**: 🟢 活跃维护中  
**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

*示例与测试：见 `examples/ffi_abi_repr.rs` 与 `tests/ffi_abi_repr_tests.rs`* 🦀
