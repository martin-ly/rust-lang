# FFI 绑定实战指南

> **FFI (Foreign Function Interface)** 是 Rust 与外部代码交互的核心机制。本指南涵盖从 C 到 Rust、Rust 到 C、以及 Rust 到 WebAssembly 的完整实践方案。

---

## 📋 目录

- [bindgen - C 到 Rust](#1-bindgen---c-到-rust)
- [cbindgen - Rust 到 C](#2-cbindgen---rust-到-c)
- [wasm-bindgen - Rust 到 JS](#3-wasm-bindgen---rust-到-js)
- [FFI 安全模式](#4-ffi-安全模式)
- [调试工具](#5-调试工具)
- [工具对比表](#工具对比表)

---

## 1. bindgen - C 到 Rust

**bindgen** 自动生成 Rust FFI 绑定，从 C/C++ 头文件创建安全的 Rust 接口。

### 1.1 基础绑定生成

```bash
# 安装 bindgen CLI
cargo install bindgen-cli

# 基础生成
bindgen wrapper.h -o src/bindings.rs
```

**Cargo.toml 配置：**

```toml
[dependencies]
# 运行时支持
libc = "0.2"

[build-dependencies]
bindgen = "0.69"
```

### 1.2 build.rs 配置

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉 Cargo 链接 C 库
    println!("cargo:rustc-link-lib=mylib");
    println!("cargo:rustc-link-search=native=/usr/local/lib");
    
    // 重新构建触发条件
    println!("cargo:rerun-if-changed=wrapper.h");
    println!("cargo:rerun-if-changed=/usr/local/lib/libmylib.a");
    
    // 生成绑定
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // C++ 支持
        .clang_arg("-x")
        .clang_arg("c++")
        .clang_arg("-std=c++17")
        // 系统头文件路径
        .clang_arg("-I/usr/local/include")
        // 黑名单（不生成绑定的项）
        .blocklist_item("__.*")
        .blocklist_function(".*_internal")
        // 类型配置
        .size_t_is_usize(true)
        // 布局测试
        .layout_tests(false)
        // 生成选项
        .derive_debug(true)
        .derive_default(true)
        .impl_debug(true)
        // 命名空间处理（C++）
        .enable_cxx_namespaces()
        .generate()
        .expect("无法生成绑定");
    
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("无法写入绑定文件");
}
```

**wrapper.h 示例：**

```c
#ifndef WRAPPER_H
#define WRAPPER_H

#include <mylib.h>

// 只暴露需要的接口
#endif
```

**库中使用：**

```rust
// src/lib.rs
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

// 包含生成的绑定
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// 包装为安全 API
pub mod safe {
    use super::*;
    use std::ffi::{CStr, CString};
    use std::os::raw::c_char;
    
    /// 安全的字符串处理包装
    pub fn get_version() -> String {
        unsafe {
            let ptr = mylib_get_version();
            CStr::from_ptr(ptr)
                .to_string_lossy()
                .into_owned()
        }
    }
    
    /// 带错误处理的数据库连接
    pub struct Database {
        ptr: *mut mylib_db_t,
    }
    
    impl Database {
        pub fn open(path: &str) -> Result<Self, String> {
            let c_path = CString::new(path)
                .map_err(|_| "无效路径".to_string())?;
            
            let mut ptr = std::ptr::null_mut();
            let result = unsafe {
                mylib_db_open(c_path.as_ptr(), &mut ptr)
            };
            
            if result == 0 {
                Ok(Self { ptr })
            } else {
                Err(format!("打开数据库失败: {}", result))
            }
        }
        
        pub fn query(&self, sql: &str) -> Result<Vec<Row>, String> {
            // 安全封装...
            todo!()
        }
    }
    
    impl Drop for Database {
        fn drop(&mut self) {
            unsafe {
                mylib_db_close(self.ptr);
            }
        }
    }
    
    unsafe impl Send for Database {}
    unsafe impl Sync for Database {}
}
```

### 1.3 处理结构体和回调

**C 结构体定义：**

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

**Rust 回调封装：**

```rust
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::os::raw::{c_int, c_void};

/// 安全的人结构体包装
#[derive(Debug)]
pub struct Person<'a> {
    pub name: &'a str,
    pub age: i32,
}

/// 进度回调类型
pub type ProgressFn = Box<dyn FnMut(i32) + Send>;

/// 用户数据包装，用于传递闭包
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
    let c_persons: Vec<bindings::person_t> = persons
        .iter()
        .map(|p| {
            let name = CString::new(p.name)
                .expect("无效名称");
            bindings::person_t {
                name: name.into_raw(), // 注意：需要管理内存
                age: p.age,
                user_data: std::ptr::null_mut(),
            }
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
    
    // 清理 CString 内存
    for p in c_persons {
        unsafe {
            let _ = CString::from_raw(p.name as *mut c_char);
        }
    }
    
    if result == 0 {
        Ok(())
    } else {
        Err(format!("处理失败: {}", result))
    }
}

/// IO 回调 trait
pub trait IoCallbacks {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ()>;
    fn write(&mut self, buf: &[u8]) -> Result<usize, ()>;
}

/// IO 回调包装结构体
pub struct IoWrapper<T: IoCallbacks> {
    inner: T,
}

impl<T: IoCallbacks> IoWrapper<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
    
    /// 生成 C 兼容的回调结构体
    pub fn as_c_callbacks(&mut self) -> bindings::io_callbacks_t {
        bindings::io_callbacks_t {
            read: Some(Self::read_trampoline),
            write: Some(Self::write_trampoline),
            user_data: self as *mut _ as *mut c_void,
        }
    }
    
    unsafe extern "C" fn read_trampoline(
        buf: *mut c_void,
        len: usize,
        user_data: *mut c_void,
    ) -> c_int {
        let wrapper = &mut *(user_data as *mut Self);
        let slice = std::slice::from_raw_parts_mut(buf as *mut u8, len);
        
        match wrapper.inner.read(slice) {
            Ok(n) => n as c_int,
            Err(()) => -1,
        }
    }
    
    unsafe extern "C" fn write_trampoline(
        buf: *const c_void,
        len: usize,
        user_data: *mut c_void,
    ) -> c_int {
        let wrapper = &mut *(user_data as *mut Self);
        let slice = std::slice::from_raw_parts(buf as *const u8, len);
        
        match wrapper.inner.write(slice) {
            Ok(n) => n as c_int,
            Err(()) => -1,
        }
    }
}
```

### 1.4 实战：SQLite 绑定

**项目结构：**

```
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
bundled = []  # 使用捆绑的 SQLite
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
        // SQLite 特定配置
        .blocklist_function("sqlite3_.*_v2")  // 使用 v1 版本
        .allowlist_function("sqlite3_.*")
        .allowlist_type("sqlite3.*")
        .allowlist_var("SQLITE_.*")
        // 类型映射
        .translate_enum_integer_types(true)
        .generate()
        .expect("生成绑定失败");
    
    bindings
        .write_to_file(out_dir.join("bindings.rs"))
        .expect("写入绑定失败");
    
    println!("cargo:rustc-link-lib=static=sqlite3");
    println!("cargo:rustc-link-search=native={}", out_dir.display());
}
```

**wrapper.h：**

```c
#ifndef SQLITE_WRAPPER_H
#define SQLITE_WRAPPER_H

#include "sqlite3/sqlite3.h"

#endif
```

**安全封装 (src/lib.rs)：**

```rust
#![allow(non_camel_case_types, non_snake_case)]

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int, c_void};
use std::ptr;
use thiserror::Error;

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[derive(Error, Debug)]
pub enum SqliteError {
    #[error("数据库错误 {code}: {message}")]
    DatabaseError { code: i32, message: String },
    
    #[error("无效 UTF-8")]
    InvalidUtf8,
    
    #[error("空指针")]
    NullPointer,
}

pub type Result<T> = std::result::Result<T, SqliteError>;

/// 数据库连接
pub struct Connection {
    ptr: *mut sqlite3,
}

impl Connection {
    pub fn open(path: &str) -> Result<Self> {
        let c_path = CString::new(path).map_err(|_| SqliteError::InvalidUtf8)?;
        let mut ptr = ptr::null_mut();
        
        let rc = unsafe { sqlite3_open(c_path.as_ptr(), &mut ptr) };
        
        if rc != SQLITE_OK {
            let msg = unsafe {
                CStr::from_ptr(sqlite3_errmsg(ptr))
                    .to_string_lossy()
                    .into_owned()
            };
            unsafe { sqlite3_close(ptr) };
            return Err(SqliteError::DatabaseError {
                code: rc,
                message: msg,
            });
        }
        
        Ok(Self { ptr })
    }
    
    pub fn execute(&self, sql: &str) -> Result<()> {
        let c_sql = CString::new(sql).map_err(|_| SqliteError::InvalidUtf8)?;
        let mut err_msg = ptr::null_mut();
        
        let rc = unsafe {
            sqlite3_exec(
                self.ptr,
                c_sql.as_ptr(),
                None,
                ptr::null_mut(),
                &mut err_msg,
            )
        };
        
        if rc != SQLITE_OK {
            let msg = unsafe {
                CStr::from_ptr(err_msg)
                    .to_string_lossy()
                    .into_owned()
            };
            unsafe { sqlite3_free(err_msg as *mut c_void) };
            return Err(SqliteError::DatabaseError {
                code: rc,
                message: msg,
            });
        }
        
        Ok(())
    }
    
    pub fn prepare(&self, sql: &str) -> Result<Statement> {
        let c_sql = CString::new(sql).map_err(|_| SqliteError::InvalidUtf8)?;
        let mut stmt = ptr::null_mut();
        
        let rc = unsafe {
            sqlite3_prepare_v2(
                self.ptr,
                c_sql.as_ptr(),
                -1,
                &mut stmt,
                ptr::null_mut(),
            )
        };
        
        if rc != SQLITE_OK {
            return Err(self.last_error());
        }
        
        Ok(Statement { ptr: stmt })
    }
    
    fn last_error(&self) -> SqliteError {
        let code = unsafe { sqlite3_errcode(self.ptr) };
        let msg = unsafe {
            CStr::from_ptr(sqlite3_errmsg(self.ptr))
                .to_string_lossy()
                .into_owned()
        };
        SqliteError::DatabaseError { code, message: msg }
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        unsafe {
            sqlite3_close(self.ptr);
        }
    }
}

unsafe impl Send for Connection {}
unsafe impl Sync for Connection {}

/// 预编译语句
pub struct Statement {
    ptr: *mut sqlite3_stmt,
}

impl Statement {
    pub fn bind_text(&self, index: i32, value: &str) -> Result<()> {
        let c_value = CString::new(value).map_err(|_| SqliteError::InvalidUtf8)?;
        let rc = unsafe {
            sqlite3_bind_text(
                self.ptr,
                index,
                c_value.as_ptr(),
                -1,
                Some(sqlite3_transient_destructor),
            )
        };
        
        if rc != SQLITE_OK {
            return Err(SqliteError::DatabaseError {
                code: rc,
                message: "绑定失败".to_string(),
            });
        }
        
        Ok(())
    }
    
    pub fn bind_int(&self, index: i32, value: i32) -> Result<()> {
        let rc = unsafe { sqlite3_bind_int(self.ptr, index, value) };
        if rc != SQLITE_OK {
            return Err(SqliteError::DatabaseError {
                code: rc,
                message: "绑定失败".to_string(),
            });
        }
        Ok(())
    }
    
    pub fn step(&self) -> Result<bool> {
        let rc = unsafe { sqlite3_step(self.ptr) };
        match rc {
            SQLITE_ROW => Ok(true),
            SQLITE_DONE => Ok(false),
            _ => Err(SqliteError::DatabaseError {
                code: rc,
                message: "执行失败".to_string(),
            }),
        }
    }
    
    pub fn column_text(&self, col: i32) -> Option<String> {
        let ptr = unsafe { sqlite3_column_text(self.ptr, col) };
        if ptr.is_null() {
            None
        } else {
            Some(unsafe {
                CStr::from_ptr(ptr as *const c_char)
                    .to_string_lossy()
                    .into_owned()
            })
        }
    }
    
    pub fn column_int(&self, col: i32) -> i32 {
        unsafe { sqlite3_column_int(self.ptr, col) }
    }
    
    pub fn reset(&self) -> Result<()> {
        let rc = unsafe { sqlite3_reset(self.ptr) };
        if rc != SQLITE_OK {
            return Err(SqliteError::DatabaseError {
                code: rc,
                message: "重置失败".to_string(),
            });
        }
        Ok(())
    }
}

impl Drop for Statement {
    fn drop(&mut self) {
        unsafe {
            sqlite3_finalize(self.ptr);
        }
    }
}

unsafe impl Send for Statement {}
unsafe impl Sync for Statement {}

// 使用示例
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_basic_operations() {
        let conn = Connection::open(":memory:").unwrap();
        
        conn.execute(r#"
            CREATE TABLE users (
                id INTEGER PRIMARY KEY,
                name TEXT NOT NULL
            )
        "#).unwrap();
        
        let stmt = conn.prepare("INSERT INTO users (name) VALUES (?)").unwrap();
        stmt.bind_text(1, "Alice").unwrap();
        stmt.step().unwrap();
        stmt.reset().unwrap();
        
        stmt.bind_text(1, "Bob").unwrap();
        stmt.step().unwrap();
        
        let query = conn.prepare("SELECT id, name FROM users").unwrap();
        let mut count = 0;
        while query.step().unwrap() {
            let id = query.column_int(0);
            let name = query.column_text(1).unwrap();
            println!("User {}: {}", id, name);
            count += 1;
        }
        
        assert_eq!(count, 2);
    }
}
```

---

## 2. cbindgen - Rust 到 C

**cbindgen** 从 Rust 代码生成 C/C++ 头文件，使 Rust 库可被其他语言调用。

### 2.1 生成 C 头文件

**安装：**

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
        .expect("无法生成绑定")
        .write_to_file(output_file);
}
```

### 2.2 cbindgen.toml 配置

```toml
# 语言设置
language = "C"
# 或 language = "C++"

# 输出配置
header = "/* 自动生成的头文件 - 请勿手动修改 */"
autogen_warning = "/* 警告：此文件由 cbindgen 自动生成 */"
include_guard = "MYLIB_H"
pragma_once = true
namespaces = ["mylib"]

# 样式
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
item_types = ["globals", "enums", "structs", "unions", "typedefs", 
              "opaque", "functions", "constants"]

[export.rename]
"MyStruct" = "mylib_struct_t"
"MyEnum" = "mylib_enum_t"

[fn]
rename_args = "CamelCase"
# 或 rename_args = "SnakeCase"
args = "auto"
sort_by = "Name"

[struct]
rename_fields = "CamelCase"

[enum]
rename_variants = "ScreamingSnakeCase"
add_sentinel = false

[parse]
parse_deps = false
# include = ["dep1", "dep2"]
# exclude = ["private_dep"]

[parse.expand]
crates = ["mylib"]
features = ["c_api"]

# C++ 特定配置
[cpp]
namespace = "mylib"

# 文档注释
[documentation]
license = "MIT"
repository = "https://github.com/example/mylib"
homepage = "https://example.com/mylib"
```

### 2.3 实战：Rust 库供 C 调用

**Rust 库代码 (src/lib.rs)：**

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
    // 注意：返回静态字符串指针
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
    
    let processed = format!("处理结果: {}", input_str.to_uppercase());
    
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

/// Opaque handle type
pub type MyLibProcessor = c_void;

/// 创建处理器
#[no_mangle]
pub extern "C" fn mylib_processor_new(
    name: *const c_char,
) -> *mut MyLibProcessor {
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

/// 获取处理器名称
#[no_mangle]
pub extern "C" fn mylib_processor_get_name(
    ptr: *const MyLibProcessor,
) -> *const c_char {
    if ptr.is_null() {
        return ptr::null();
    }
    
    let processor = unsafe { &*(ptr as *const DataProcessor) };
    
    // 注意：这里返回的指针只在 processor 存在时有效
    // 更好的做法是让调用者提供缓冲区
    match CString::new(processor.name.clone()) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => ptr::null(),
    }
}

/// 释放字符串（与 get_name 配对使用）
#[no_mangle]
pub extern "C" fn mylib_string_free(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            let _ = CString::from_raw(s);
        }
    }
}

// ========== 回调 ==========

/// 数据回调类型
pub type DataCallback = extern "C" fn(data: *const u8, len: usize, user_data: *mut c_void);

/// 枚举数据
#[no_mangle]
pub extern "C" fn mylib_processor_foreach(
    ptr: *const MyLibProcessor,
    callback: Option<DataCallback>,
    user_data: *mut c_void,
) -> MyLibError {
    if ptr.is_null() {
        return MyLibError::NullPointer;
    }
    
    let callback = match callback {
        Some(cb) => cb,
        None => return MyLibError::NullPointer,
    };
    
    let processor = unsafe { &*(ptr as *const DataProcessor) };
    
    // 分块回调
    for chunk in processor.data.chunks(1024) {
        callback(chunk.as_ptr(), chunk.len(), user_data);
    }
    
    MyLibError::Ok
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

#[no_mangle]
pub extern "C" fn mylib_counter_get(ptr: *const MyLibCounter) -> i64 {
    if ptr.is_null() {
        return -1;
    }
    
    let counter = unsafe { &*(ptr as *const SharedCounter) };
    *counter.count.lock().unwrap()
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
/* 自动生成的头文件 - 请勿手动修改 */
/* 警告：此文件由 cbindgen 自动生成 */

#ifndef MYLIB_H
#define MYLIB_H

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * 错误码
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

/**
 * 数据回调类型
 */
typedef void (*DataCallback)(const uint8_t *data, size_t len, void *user_data);

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * 两数相加
 */
int32_t mylib_add(int32_t a, int32_t b);

/**
 * 获取错误描述
 */
const char *mylib_error_string(MyLibError code);

/**
 * 初始化 panic 处理（在库加载时调用）
 */
void mylib_init(void);

/**
 * 释放字符串（与 get_name 配对使用）
 */
void mylib_string_free(char *s);

/**
 * 释放处理器
 */
void mylib_processor_free(MyLibProcessor *ptr);

/**
 * 获取处理器名称
 */
const char *mylib_processor_get_name(const MyLibProcessor *ptr);

/**
 * 获取数据大小
 */
size_t mylib_processor_len(const MyLibProcessor *ptr);

/**
 * 创建处理器
 */
MyLibProcessor *mylib_processor_new(const char *name);

/**
 * 添加数据
 */
MyLibError mylib_processor_append(MyLibProcessor *ptr,
                                  const uint8_t *data,
                                  size_t len);

/**
 * 枚举数据
 */
MyLibError mylib_processor_foreach(const MyLibProcessor *ptr,
                                   DataCallback callback,
                                   void *user_data);

/**
 * 处理字符串
 */
MyLibError mylib_process_string(const char *input, char *output, size_t output_len);

/**
 * 释放计数器
 */
void mylib_counter_free(MyLibCounter *ptr);

/**
 * 获取当前值
 */
int64_t mylib_counter_get(const MyLibCounter *ptr);

/**
 * 增加计数器
 */
int64_t mylib_counter_increment(MyLibCounter *ptr);

/**
 * 创建计数器
 */
MyLibCounter *mylib_counter_new(void);

#ifdef __cplusplus
} // extern "C"
#endif // __cplusplus

#endif /* MYLIB_H */
```

**C 使用示例：**

```c
#include <stdio.h>
#include <string.h>
#include "mylib.h"

// 回调函数
void on_data_chunk(const uint8_t *data, size_t len, void *user_data) {
    int *total = (int*)user_data;
    *total += len;
    printf("收到数据块: %zu 字节\n", len);
}

int main() {
    // 初始化
    mylib_init();
    
    // 简单函数
    int result = mylib_add(5, 3);
    printf("5 + 3 = %d\n", result);
    
    // 字符串处理
    char output[256];
    MyLibError err = mylib_process_string("hello", output, sizeof(output));
    if (err == MYLIB_OK) {
        printf("结果: %s\n", output);
    }
    
    // 使用处理器（不透明指针）
    MyLibProcessor *proc = mylib_processor_new("test_processor");
    if (proc) {
        uint8_t data[] = {1, 2, 3, 4, 5};
        mylib_processor_append(proc, data, sizeof(data));
        
        printf("数据大小: %zu\n", mylib_processor_len(proc));
        
        // 使用回调
        int total = 0;
        mylib_processor_foreach(proc, on_data_chunk, &total);
        printf("总数据量: %d\n", total);
        
        // 获取名称
        const char *name = mylib_processor_get_name(proc);
        printf("处理器名称: %s\n", name);
        mylib_string_free((char*)name);  // 释放字符串
        
        mylib_processor_free(proc);
    }
    
    // 线程安全计数器
    MyLibCounter *counter = mylib_counter_new();
    for (int i = 0; i < 10; i++) {
        mylib_counter_increment(counter);
    }
    printf("计数器: %lld\n", (long long)mylib_counter_get(counter));
    mylib_counter_free(counter);
    
    return 0;
}
```

**编译和使用：**

```bash
# 构建 Rust 库
cargo build --release

# 编译 C 程序
gcc -o test_app test.c -L target/release -lmylib -lpthread -ldl

# 运行
LD_LIBRARY_PATH=target/release ./test_app
```

---

## 3. wasm-bindgen - Rust 到 JS

**wasm-bindgen** 让 Rust 与 JavaScript 无缝互操作，编译为 WebAssembly。

### 3.1 基础设置

**安装工具链：**

```bash
# 安装 wasm-pack
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

# 添加 WASM 目标
rustup target add wasm32-unknown-unknown
```

**项目结构：**

```
wasm-project/
├── Cargo.toml
├── src/lib.rs
├── pkg/          # 生成的包
└── www/          # 前端代码
    ├── index.html
    ├── index.js
    └── package.json
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

# 可选：用于 Web API 访问
js-sys = "0.3"
web-sys = { version = "0.3", features = [
    "console",
    "Document",
    "Element",
    "HtmlElement",
    "Window",
    "MouseEvent",
    "EventTarget",
] }

[dependencies.wasm-bindgen-futures]
version = "0.4"

[dependencies.getrandom]
version = "0.2"
features = ["js"]

[profile.release]
opt-level = 3
lto = true
```

### 3.2 类型映射

```rust
use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};

// ========== 基本类型 ==========

/// 导出函数到 JS
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 字符串处理
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

/// 字节数组
#[wasm_bindgen]
pub fn process_bytes(data: &[u8]) -> Vec<u8> {
    data.iter().map(|b| b * 2).collect()
}

// ========== 结构体 ==========

/// 导出结构体
#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct Point {
    x: f64,
    y: f64,
}

#[wasm_bindgen]
impl Point {
    /// 构造函数
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }
    
    /// Getter
    #[wasm_bindgen(getter)]
    pub fn x(&self) -> f64 {
        self.x
    }
    
    #[wasm_bindgen(getter)]
    pub fn y(&self) -> f64 {
        self.y
    }
    
    /// Setter
    #[wasm_bindgen(setter)]
    pub fn set_x(&mut self, x: f64) {
        self.x = x;
    }
    
    /// 方法
    pub fn distance(&self, other: &Point) -> f64 {
        ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
    }
    
    /// 静态方法
    pub fn origin() -> Point {
        Self { x: 0.0, y: 0.0 }
    }
}

// ========== 复杂类型（使用 serde） ==========

#[derive(Serialize, Deserialize)]
pub struct User {
    id: u64,
    name: String,
    email: Option<String>,
    roles: Vec<String>,
}

#[wasm_bindgen]
pub fn parse_user(json: &str) -> Result<JsValue, JsValue> {
    let user: User = serde_json::from_str(json)
        .map_err(|e| JsValue::from_str(&e.to_string()))?;
    
    serde_wasm_bindgen::to_value(&user)
        .map_err(|e| JsValue::from_str(&e.to_string()))
}

#[wasm_bindgen]
pub fn create_user(name: &str) -> JsValue {
    let user = User {
        id: 1,
        name: name.to_string(),
        email: Some("user@example.com".to_string()),
        roles: vec!["user".to_string()],
    };
    
    serde_wasm_bindgen::to_value(&user).unwrap()
}

// ========== 错误处理 ==========

#[wasm_bindgen]
#[derive(Debug)]
pub struct CalculationError {
    message: String,
}

#[wasm_bindgen]
impl CalculationError {
    #[wasm_bindgen(getter)]
    pub fn message(&self) -> String {
        self.message.clone()
    }
}

impl std::fmt::Display for CalculationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for CalculationError {}

#[wasm_bindgen]
pub fn divide(a: f64, b: f64) -> Result<f64, JsValue> {
    if b == 0.0 {
        let err = CalculationError {
            message: "Cannot divide by zero".to_string(),
        };
        return Err(JsValue::from(err));
    }
    Ok(a / b)
}

// ========== 异步 ==========

use wasm_bindgen_futures::JsFuture;
use web_sys::Response;

#[wasm_bindgen]
pub async fn fetch_data(url: String) -> Result<String, JsValue> {
    let window = web_sys::window().unwrap();
    let resp_value = JsFuture::from(window.fetch_with_str(&url)).await?;
    
    let resp: Response = resp_value.dyn_into()?;
    let json = JsFuture::from(resp.json()?).await?;
    
    // 转换为字符串
    Ok(JSON::stringify(&json)?.as_string().unwrap_or_default())
}
```

### 3.3 与 Web API 集成

```rust
use wasm_bindgen::prelude::*;
use web_sys::{console, Document, Element, HtmlElement, Window, MouseEvent};

/// 日志宏
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
    
    #[wasm_bindgen(js_namespace = console, js_name = log)]
    fn log_u32(a: u32);
    
    #[wasm_bindgen(js_namespace = console, js_name = log)]
    fn log_many(a: &str, b: &str);
}

#[wasm_bindgen(start)]
pub fn main() {
    console::log_1(&"WASM 模块已加载".into());
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
    
    /// 创建元素
    pub fn create_element(&self, tag: &str, content: &str) -> Result<(), JsValue> {
        let elem = self.document.create_element(tag)?;
        elem.set_text_content(Some(content));
        
        let body = self.document.body().ok_or("no body")?;
        body.append_child(&elem)?;
        
        Ok(())
    }
    
    /// 修改样式
    pub fn set_style(&self, id: &str, property: &str, value: &str) -> Result<(), JsValue> {
        let elem = self.document
            .get_element_by_id(id)
            .ok_or("element not found")?;
        
        let html_elem: HtmlElement = elem.dyn_into()?;
        html_elem.style().set_property(property, value)?;
        
        Ok(())
    }
    
    /// 添加事件监听
    pub fn add_click_listener(&self, id: &str) -> Result<(), JsValue> {
        let elem = self.document
            .get_element_by_id(id)
            .ok_or("element not found")?;
        
        let closure = Closure::wrap(Box::new(move |event: MouseEvent| {
            console::log_1(&format!("点击位置: ({}, {})", event.client_x(), event.client_y()).into());
        }) as Box<dyn FnMut(_)>);
        
        elem.add_event_listener_with_callback("click", closure.as_ref().unchecked_ref())?;
        closure.forget(); // 避免闭包被释放
        
        Ok(())
    }
}

/// Canvas 绘图
#[wasm_bindgen]
pub struct CanvasRenderer {
    context: web_sys::CanvasRenderingContext2d,
}

#[wasm_bindgen]
impl CanvasRenderer {
    #[wasm_bindgen(constructor)]
    pub fn new(canvas_id: &str) -> Result<CanvasRenderer, JsValue> {
        let window = web_sys::window().unwrap();
        let document = window.document().unwrap();
        let canvas = document
            .get_element_by_id(canvas_id)
            .ok_or("Canvas not found")?;
        
        let canvas: web_sys::HtmlCanvasElement = canvas.dyn_into()?;
        let context = canvas
            .get_context("2d")?
            .ok_or("Could not get 2d context")?
            .dyn_into()?;
        
        Ok(Self { context })
    }
    
    pub fn draw_rect(&self, x: f64, y: f64, width: f64, height: f64) {
        self.context.fill_rect(x, y, width, height);
    }
    
    pub fn set_fill_color(&self, color: &str) {
        self.context.set_fill_style(&color.into());
    }
    
    pub fn clear(&self) {
        let canvas = self.context.canvas().unwrap();
        self.context.clear_rect(
            0.0, 0.0, 
            canvas.width() as f64, 
            canvas.height() as f64
        );
    }
}

/// 使用 requestAnimationFrame
#[wasm_bindgen]
pub struct AnimationLoop {
    callback: Closure<dyn FnMut()>,
}

#[wasm_bindgen]
impl AnimationLoop {
    pub fn new<F>(mut f: F) -> AnimationLoop
    where
        F: FnMut() + 'static,
    {
        let closure = Closure::wrap(Box::new(move || {
            f();
        }) as Box<dyn FnMut()>);
        
        AnimationLoop { callback: closure }
    }
    
    pub fn start(&self) {
        let window = web_sys::window().unwrap();
        window
            .request_animation_frame(self.callback.as_ref().unchecked_ref())
            .unwrap();
    }
}
```

### 3.4 实战：WASM 模块

**加密工具模块：**

```rust
use wasm_bindgen::prelude::*;
use sha2::{Sha256, Digest};
use base64::{Engine as _, engine::general_purpose};

#[wasm_bindgen]
pub struct CryptoUtils;

#[wasm_bindgen]
impl CryptoUtils {
    /// SHA256 哈希
    pub fn sha256(input: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(input.as_bytes());
        let result = hasher.finalize();
        format!("{:x}", result)
    }
    
    /// Base64 编码
    pub fn base64_encode(input: &[u8]) -> String {
        general_purpose::STANDARD.encode(input)
    }
    
    /// Base64 解码
    pub fn base64_decode(input: &str) -> Result<Vec<u8>, JsValue> {
        general_purpose::STANDARD.decode(input)
            .map_err(|e| JsValue::from_str(&e.to_string()))
    }
}

/// 图像处理
#[wasm_bindgen]
pub struct ImageProcessor;

#[wasm_bindgen]
impl ImageProcessor {
    /// 灰度化
    pub fn grayscale(data: &[u8]) -> Vec<u8> {
        let mut result = data.to_vec();
        
        // 假设 RGBA 格式
        for chunk in result.chunks_exact_mut(4) {
            let gray = ((chunk[0] as u16 * 299 + 
                        chunk[1] as u16 * 587 + 
                        chunk[2] as u16 * 114) / 1000) as u8;
            chunk[0] = gray;
            chunk[1] = gray;
            chunk[2] = gray;
            // chunk[3] 保持 alpha 不变
        }
        
        result
    }
    
    /// 调整亮度
    pub fn adjust_brightness(data: &[u8], factor: f32) -> Vec<u8> {
        data.iter()
            .map(|&p| {
                let adjusted = (p as f32 * factor).clamp(0.0, 255.0) as u8;
                adjusted
            })
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

**前端使用：**

```html
<!-- www/index.html -->
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>WASM Demo</title>
</head>
<body>
    <h1>WASM 加密工具</h1>
    <input type="text" id="input" placeholder="输入文本">
    <button id="hash-btn">计算 SHA256</button>
    <p id="result"></p>
    
    <canvas id="canvas" width="400" height="300"></canvas>
    
    <script type="module">
        import init, { CryptoUtils, CanvasRenderer } from './pkg/wasm_project.js';
        
        async function run() {
            await init();
            
            // 加密功能
            document.getElementById('hash-btn').addEventListener('click', () => {
                const input = document.getElementById('input').value;
                const hash = CryptoUtils.sha256(input);
                document.getElementById('result').textContent = hash;
            });
            
            // Canvas 绘图
            const renderer = new CanvasRenderer('canvas');
            renderer.set_fill_color('#FF5733');
            renderer.draw_rect(50, 50, 100, 100);
        }
        
        run();
    </script>
</body>
</html>
```

**构建和运行：**

```bash
# 构建 WASM 包
wasm-pack build --target web --out-dir pkg

# 启动开发服务器
cd pkg && python3 -m http.server 8000
# 或使用 npx serve
npx serve pkg
```

---

## 4. FFI 安全模式

### 4.1 生命周期管理

```rust
use std::ffi::CString;
use std::marker::PhantomData;
use std::os::raw::c_char;
use std::ptr::NonNull;

/// 安全的 C 字符串包装，自动管理生命周期
pub struct CStrWrap {
    ptr: NonNull<c_char>,
}

impl CStrWrap {
    pub fn new(s: &str) -> Option<Self> {
        CString::new(s).ok().map(|cstr| {
            let ptr = cstr.into_raw();
            Self {
                ptr: NonNull::new(ptr).unwrap(),
            }
        })
    }
    
    pub fn as_ptr(&self) -> *const c_char {
        self.ptr.as_ptr()
    }
}

impl Drop for CStrWrap {
    fn drop(&mut self) {
        unsafe {
            let _ = CString::from_raw(self.ptr.as_ptr());
        }
    }
}

/// 带生命周期标记的缓冲区
pub struct CBuffer<'a> {
    ptr: *mut u8,
    len: usize,
    _marker: PhantomData<&'a mut [u8]>,
}

impl<'a> CBuffer<'a> {
    /// 从可变切片创建
    pub fn from_mut_slice(slice: &'a mut [u8]) -> Self {
        Self {
            ptr: slice.as_mut_ptr(),
            len: slice.len(),
            _marker: PhantomData,
        }
    }
    
    /// 安全地访问缓冲区
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
    
    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
    
    pub fn len(&self) -> usize {
        self.len
    }
    
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// 借用检查器无法跟踪时使用的作用域 API
pub fn with_c_string<F, R>(s: &str, f: F) -> R
where
    F: FnOnce(*const c_char) -> R,
{
    let cstr = CString::new(s).expect("invalid string");
    f(cstr.as_ptr())
    // cstr 在这里自动释放
}

/// 作用域内的 FFI 调用
pub fn with_ffi_buffer<F, R>(size: usize, f: F) -> R
where
    F: FnOnce(*mut u8, usize) -> R,
{
    let mut buf = vec![0u8; size];
    let result = f(buf.as_mut_ptr(), buf.len());
    // 缓冲区在返回前有效
    result
}
```

### 4.2 内存所有权

```rust
use std::ffi::c_void;
use std::ptr::NonNull;
use std::alloc::{self, Layout};

/// FFI 内存分配器 trait
pub trait FfiAllocator {
    unsafe fn allocate(&self, size: usize) -> *mut c_void;
    unsafe fn deallocate(&self, ptr: *mut c_void);
    unsafe fn reallocate(&self, ptr: *mut c_void, old_size: usize, new_size: usize) -> *mut c_void;
}

/// C 标准库分配器
pub struct CAllocator;

impl FfiAllocator for CAllocator {
    unsafe fn allocate(&self, size: usize) -> *mut c_void {
        libc::malloc(size)
    }
    
    unsafe fn deallocate(&self, ptr: *mut c_void) {
        libc::free(ptr);
    }
    
    unsafe fn reallocate(&self, ptr: *mut c_void, _old_size: usize, new_size: usize) -> *mut c_void {
        libc::realloc(ptr, new_size)
    }
}

/// 拥有 C 库分配的内存
pub struct FfiBox<T> {
    ptr: NonNull<T>,
    allocator: Box<dyn FfiAllocator>,
}

impl<T> FfiBox<T> {
    pub unsafe fn from_raw(
        ptr: *mut T,
        allocator: Box<dyn FfiAllocator>,
    ) -> Option<Self> {
        NonNull::new(ptr).map(|nn| Self {
            ptr: nn,
            allocator,
        })
    }
    
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }
    
    pub fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
    
    pub fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for FfiBox<T> {
    fn drop(&mut self) {
        unsafe {
            self.allocator.deallocate(self.ptr.as_ptr() as *mut c_void);
        }
    }
}

/// 跨边界内存规则：
/// 1. Rust 分配，Rust 释放
/// 2. C 分配，C 释放
/// 3. 永远不要混用分配器

/// 安全的字符串传递
pub struct StringTransfer {
    /// Rust 字符串转 C 字符串（临时借用）
    pub fn rust_to_c_temp(s: &str) -> Option<CString> {
        CString::new(s).ok()
    }
    
    /// C 字符串转 Rust（复制）
    pub unsafe fn c_to_rust_copy(ptr: *const c_char) -> Option<String> {
        if ptr.is_null() {
            return None;
        }
        CStr::from_ptr(ptr).to_str().ok().map(|s| s.to_string())
    }
}

/// 零拷贝视图（不安全但高效）
pub struct CStrView<'a> {
    ptr: *const c_char,
    _marker: PhantomData<&'a ()>,
}

impl<'a> CStrView<'a> {
    /// 必须在 ptr 有效期间使用
    pub unsafe fn new(ptr: *const c_char) -> Option<Self> {
        if ptr.is_null() {
            None
        } else {
            Some(Self {
                ptr,
                _marker: PhantomData,
            })
        }
    }
    
    pub fn to_str(&self) -> Option<&str> {
        unsafe {
            CStr::from_ptr(self.ptr).to_str().ok()
        }
    }
}
```

### 4.3 错误处理

```rust
use std::ffi::{c_char, CStr, CString};
use std::ptr;

/// FFI 错误码
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FfiErrorCode {
    Success = 0,
    NullPointer = 1,
    InvalidUtf8 = 2,
    BufferTooSmall = 3,
    AllocationFailed = 4,
    IoError = 5,
    Unknown = 99,
}

/// 错误信息结构体
#[repr(C)]
pub struct FfiError {
    code: FfiErrorCode,
    message: *const c_char,
}

impl FfiError {
    pub fn new(code: FfiErrorCode, message: &str) -> Self {
        let cmsg = CString::new(message).unwrap_or_default();
        Self {
            code,
            message: cmsg.into_raw(),
        }
    }
    
    pub fn success() -> Self {
        Self {
            code: FfiErrorCode::Success,
            message: ptr::null(),
        }
    }
    
    pub fn code(&self) -> FfiErrorCode {
        self.code
    }
    
    pub unsafe fn message(&self) -> Option<&str> {
        if self.message.is_null() {
            None
        } else {
            CStr::from_ptr(self.message).to_str().ok()
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

/// 结果类型宏
#[macro_export]
macro_rules! ffi_result {
    ($expr:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => {
                return FfiError::new(
                    FfiErrorCode::Unknown,
                    &e.to_string()
                );
            }
        }
    };
}

/// 空指针检查宏
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

/// 使用示例
#[no_mangle]
pub extern "C" fn safe_operation(
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
    
    let input_str = unsafe {
        match CStr::from_ptr(input).to_str() {
            Ok(s) => s,
            Err(_) => {
                return FfiError::new(
                    FfiErrorCode::InvalidUtf8,
                    "input is not valid UTF-8"
                );
            }
        }
    };
    
    let result = format!("处理结果: {}", input_str);
    
    if result.len() >= output_len {
        return FfiError::new(
            FfiErrorCode::BufferTooSmall,
            "output buffer too small"
        );
    }
    
    let output_slice = unsafe {
        std::slice::from_raw_parts_mut(output as *mut u8, output_len)
    };
    
    output_slice[..result.len()].copy_from_slice(result.as_bytes());
    output_slice[result.len()] = 0;
    
    FfiError::success()
}

/// 错误传播模式
pub type FfiResult<T> = Result<T, FfiError>;

pub fn ffi_try<T>(result: Result<T, impl std::fmt::Display>) -> FfiResult<T> {
    result.map_err(|e| FfiError::new(FfiErrorCode::Unknown, &e.to_string()))
}
```

### 4.4 Panic 安全

```rust
use std::ffi::c_void;
use std::panic;
use std::process::abort;

/// 设置 panic 钩子，防止跨 FFI 边界展开
pub fn setup_panic_handler() {
    panic::set_hook(Box::new(|info| {
        eprintln!("Panic in FFI code: {}", info);
        // 记录到日志或通知系统
        // 不要在这里做复杂操作
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

/// 安全的 panic 边界
pub struct PanicGuard<T> {
    value: Option<T>,
    default: T,
}

impl<T: Clone> PanicGuard<T> {
    pub fn new(default: T) -> Self {
        Self {
            value: None,
            default,
        }
    }
    
    pub fn run<F>(&mut self, f: F) -> T
    where
        F: FnOnce() -> T + panic::UnwindSafe,
    {
        match panic::catch_unwind(f) {
            Ok(v) => v,
            Err(_) => {
                eprintln!("Operation panicked, returning default");
                self.default.clone()
            }
        }
    }
}

/// 中止模式（更严重的情况）
pub fn abort_on_panic() {
    panic::set_hook(Box::new(|_| {
        abort();
    }));
}

/// 实际使用示例
#[no_mangle]
pub extern "C" fn panic_safe_operation(input: i32) -> i32 {
    ffi_catch_panic!(-1, {
        if input < 0 {
            panic!("negative input");
        }
        input * 2
    })
}

/// 复杂类型的 panic 安全
#[no_mangle]
pub extern "C" fn process_data_safe(
    data: *const u8,
    len: usize,
    callback: extern "C" fn(*const u8, usize),
) {
    ffi_catch_panic!((), {
        if data.is_null() {
            return;
        }
        
        let slice = unsafe { std::slice::from_raw_parts(data, len) };
        let processed = expensive_operation(slice);
        
        // 确保回调也受保护
        let _ = panic::catch_unwind(|| {
            callback(processed.as_ptr(), processed.len());
        });
    });
}

fn expensive_operation(data: &[u8]) -> Vec<u8> {
    data.to_vec()
}

/// 初始化函数（库加载时调用）
#[no_mangle]
pub extern "C" fn mylib_init() {
    setup_panic_handler();
}
```

---

## 5. 调试工具

### 5.1 Miri 验证

**安装和使用：**

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 运行特定示例
cargo miri run --example ffi_example
```

**Miri 检测的不安全行为：**

```rust
// ❌ 错误：使用未初始化内存
pub unsafe fn bad_uninit() -> i32 {
    let x: i32 = std::mem::uninitialized();
    x
}

// ❌ 错误：数据竞争
static mut COUNTER: i32 = 0;

pub unsafe fn race_condition() {
    COUNTER += 1;  // 多线程不安全
}

// ❌ 错误：越界访问
pub unsafe fn out_of_bounds() -> u8 {
    let arr = [1, 2, 3];
    *arr.get_unchecked(10)
}

// ✅ 正确：使用 MaybeUninit
pub fn good_uninit() -> i32 {
    use std::mem::MaybeUninit;
    
    let mut x = MaybeUninit::<i32>::uninit();
    unsafe {
        x.as_mut_ptr().write(42);
        x.assume_init()
    }
}

// ✅ 正确：使用原子类型
use std::sync::atomic::{AtomicI32, Ordering};

static COUNTER_SAFE: AtomicI32 = AtomicI32::new(0);

pub fn safe_increment() {
    COUNTER_SAFE.fetch_add(1, Ordering::SeqCst);
}
```

**FFI 特定的 Miri 检查：**

```rust
/// 测试 FFI 边界
#[cfg(miri)]
mod miri_tests {
    use super::*;
    
    #[test]
    fn test_ffi_safety() {
        // Miri 会检查：
        // 1. 指针有效性
        // 2. 内存对齐
        // 3. 生命周期
        // 4. 数据竞争
        
        let mut buf = vec![0u8; 100];
        
        // 模拟 FFI 调用
        unsafe {
            // 假设这是 C 函数
            simulate_c_write(buf.as_mut_ptr(), buf.len());
        }
    }
    
    // Miri 提供的 FFI 辅助函数
    extern "C" fn simulate_c_write(ptr: *mut u8, len: usize) {
        unsafe {
            std::ptr::write_bytes(ptr, 0, len);
        }
    }
}
```

### 5.2 Valgrind

**安装：**

```bash
# Ubuntu/Debian
sudo apt-get install valgrind

# macOS
brew install valgrind  # 仅限 Intel Mac
```

**使用 Valgrind 检测内存问题：**

```bash
# 基本内存检查
valgrind --leak-check=full --show-leak-kinds=all \
    ./target/debug/my_program

# 详细错误报告
valgrind --leak-check=full --track-origins=yes \
    --show-leak-kinds=all --verbose \
    ./target/debug/my_program

# 检测非法内存访问
valgrind --tool=memcheck --track-origins=yes \
    ./target/debug/my_program
```

**FFI 内存泄漏示例：**

```rust
// ❌ 错误：内存泄漏
#[no_mangle]
pub extern "C" fn leaky_function() -> *mut c_char {
    let s = CString::new("leak").unwrap();
    s.into_raw()  // 调用者需要释放，但经常被遗忘
}

// ✅ 正确：提供配对函数
#[no_mangle]
pub extern "C" fn mylib_string_create(s: *const c_char) -> *mut c_char {
    unsafe {
        let input = CStr::from_ptr(s).to_str().unwrap();
        CString::new(input.to_uppercase()).unwrap().into_raw()
    }
}

#[no_mangle]
pub extern "C" fn mylib_string_free(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            let _ = CString::from_raw(s);
        }
    }
}
```

**Valgrind 抑制文件：**

```
# valgrind.supp
# 抑制已知的非问题警告
{
    rust_alloc
    Memcheck:Leak
    match-leak-kinds: possible
    ...
    fun:__rust_alloc
    ...
}

{
    cargo_jemalloc
    Memcheck:Leak
    ...
    fun:je_
    ...
}
```

使用：

```bash
valgrind --suppressions=valgrind.supp ./target/debug/my_program
```

### 5.3 AddressSanitizer

**使用 ASan：**

```bash
# 设置环境变量
export RUSTFLAGS="-Z sanitizer=address"

# 运行测试
cargo test --target x86_64-unknown-linux-gnu

# 运行程序
cargo run --target x86_64-unknown-linux-gnu
```

**检测的问题类型：**

```rust
// ❌ 堆缓冲区溢出
pub fn heap_overflow() {
    let mut vec = vec![0u8; 10];
    unsafe {
        *vec.as_mut_ptr().add(100) = 1;  // 越界写入
    }
}

// ❌ 栈缓冲区溢出
pub fn stack_overflow() {
    let mut arr = [0u8; 10];
    unsafe {
        std::ptr::write(arr.as_mut_ptr().add(20), 1);
    }
}

// ❌ 使用已释放内存
pub fn use_after_free() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        let _ = Box::from_raw(ptr);  // 释放
        println!("{}", *ptr);  // 错误：使用已释放内存
    }
}

// ❌ 双重释放
pub fn double_free() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        let _ = Box::from_raw(ptr);
        let _ = Box::from_raw(ptr);  // 错误：双重释放
    }
}
```

**交叉编译使用 Sanitizer：**

```bash
# 安装目标
rustup target add x86_64-unknown-linux-gnu

# 使用 ASan 构建
cargo build --target x86_64-unknown-linux-gnu \
    -Z build-std \
    --target x86_64-unknown-linux-gnu

# 使用 TSan (Thread Sanitizer)
export RUSTFLAGS="-Z sanitizer=thread"
cargo test --target x86_64-unknown-linux-gnu
```

**组合调试：**

```rust
/// 安全的 FFI 调试模式
#[cfg(feature = "debug-ffi")]
mod debug {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    pub struct DebugAllocator;
    
    static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
    static FREED: AtomicUsize = AtomicUsize::new(0);
    
    unsafe impl GlobalAlloc for DebugAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
            System.alloc(layout)
        }
        
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            FREED.fetch_add(layout.size(), Ordering::SeqCst);
            System.dealloc(ptr, layout);
        }
    }
    
    #[global_allocator]
    static ALLOCATOR: DebugAllocator = DebugAllocator;
    
    pub fn print_stats() {
        println!(
            "Allocated: {}, Freed: {}, Leaked: {}",
            ALLOCATED.load(Ordering::SeqCst),
            FREED.load(Ordering::SeqCst),
            ALLOCATED.load(Ordering::SeqCst) - FREED.load(Ordering::SeqCst)
        );
    }
}
```

---

## 工具对比表

| 工具 | 用途 | 适用场景 | 性能开销 | 学习曲线 |
|------|------|----------|----------|----------|
| **bindgen** | C → Rust | 使用 C/C++ 库 | 编译时 | 中等 |
| **cbindgen** | Rust → C/C++ | 创建 C 兼容库 | 编译时 | 中等 |
| **wasm-bindgen** | Rust → JS | WebAssembly 开发 | 运行时低 | 低 |
| **Miri** | 未定义行为检测 | 开发期验证 | 高（10-100x） | 中等 |
| **Valgrind** | 内存问题检测 | Linux 调试 | 高（5-20x） | 中等 |
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

- [Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/)
- [nomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html)
- [bindgen 文档](https://rust-lang.github.io/rust-bindgen/)
- [cbindgen 文档](https://github.com/mozilla/cbindgen)
- [wasm-bindgen 指南](https://rustwasm.github.io/wasm-bindgen/)
- [The Rust FFI Guide](https://michael-f-bryan.github.io/rust-ffi-guide/)

---

> **总结**：FFI 是 Rust 与外部世界交互的桥梁。正确的模式（不透明指针、作用域 API、错误处理）和充分的测试（Miri、Valgrind、ASan）是确保 FFI 安全的关键。
