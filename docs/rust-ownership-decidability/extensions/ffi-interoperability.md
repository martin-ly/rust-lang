# FFI 互操作性

Foreign Function Interface (FFI) 是 Rust 与外部代码交互的核心机制。本章节深入探讨如何使用 Rust 调用 C/C++ 库，以及如何用 Rust 编写可以被其他语言调用的库。

## 目录

- [FFI 互操作性](#ffi-互操作性)
  - [目录](#目录)
  - [基础概念](#基础概念)
    - [什么是 FFI](#什么是-ffi)
    - [ABI 兼容性](#abi-兼容性)
    - [不透明类型](#不透明类型)
  - [C 语言绑定](#c-语言绑定)
    - [基本绑定示例](#基本绑定示例)
    - [使用 Bindgen 自动生成绑定](#使用-bindgen-自动生成绑定)
  - [Python 绑定](#python-绑定)
  - [回调函数处理](#回调函数处理)
  - [复杂数据结构](#复杂数据结构)
  - [线程安全与 FFI](#线程安全与-ffi)
  - [内存管理](#内存管理)
  - [最佳实践](#最佳实践)
    - [1. 类型安全封装](#1-类型安全封装)
    - [2. 文档和不变式](#2-文档和不变式)
    - [3. 测试策略](#3-测试策略)
    - [4. 错误处理模式](#4-错误处理模式)
    - [5. 持续集成配置](#5-持续集成配置)

## 基础概念

### 什么是 FFI

FFI 允许一种编程语言调用另一种语言的函数和使用其数据结构。Rust 通过 `extern` 关键字和 `#[link]` 属性提供了强大的 FFI 支持。

### ABI 兼容性

Application Binary Interface (ABI) 定义了函数调用的底层约定：

```rust
// 使用 C ABI
extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}

// 可用的 ABI 字符串
extern "C"          // 标准 C ABI
extern "system"     // 平台默认 ABI (Windows: stdcall, 其他: C)
extern "stdcall"    // Windows API
extern "fastcall"   // fastcall 约定
extern "vectorcall" // Windows vectorcall
extern "thiscall"   // C++ thiscall
extern "aapcs"      // ARM 架构
extern "win64"      // Windows x86_64
extern "sysv64"     // System V AMD64 ABI
```

### 不透明类型

处理 C 库中不透明的结构体指针：

```rust
// C 头文件中的不透明类型
// typedef struct sqlite3 sqlite3;

// Rust 中的表示
#[repr(C)]
pub struct sqlite3 {
    _private: [u8; 0],  // 零大小数组，阻止直接实例化
}

// 使用方式
pub type Sqlite3Handle = *mut sqlite3;
```

## C 语言绑定

### 基本绑定示例

创建一个完整的 SQLite 绑定示例：

**Cargo.toml:**

```toml
[package]
name = "sqlite-ffi-demo"
version = "0.1.0"
edition = "2021"

[dependencies]
libc = "0.2"

[build-dependencies]
pkg-config = "0.3"
```

**build.rs:**

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    // 使用 pkg-config 查找 SQLite
    let lib = pkg_config::probe_library("sqlite3").unwrap();

    // 或者手动链接
    println!("cargo:rustc-link-lib=sqlite3");
    println!("cargo:rustc-link-search=/usr/lib");

    // 重新运行条件
    println!("cargo:rerun-if-changed=build.rs");
}
```

**src/lib.rs:**

```rust
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int, c_void};
use std::ptr;

// SQLite 错误码
pub const SQLITE_OK: c_int = 0;
pub const SQLITE_ROW: c_int = 100;
pub const SQLITE_DONE: c_int = 101;
pub const SQLITE_BUSY: c_int = 5;
pub const SQLITE_LOCKED: c_int = 6;

// SQLite 类型定义
#[repr(C)]
pub struct sqlite3 {
    _private: [u8; 0],
}

#[repr(C)]
pub struct sqlite3_stmt {
    _private: [u8; 0],
}

// 外部函数声明
#[link(name = "sqlite3")]
extern "C" {
    pub fn sqlite3_open(filename: *const c_char, ppDb: *mut *mut sqlite3) -> c_int;
    pub fn sqlite3_close(pDb: *mut sqlite3) -> c_int;
    pub fn sqlite3_exec(
        pDb: *mut sqlite3,
        sql: *const c_char,
        callback: Option<extern "C" fn(*mut c_void, c_int, *mut *mut c_char, *mut *mut c_char) -> c_int>,
        pArg: *mut c_void,
        errmsg: *mut *mut c_char,
    ) -> c_int;
    pub fn sqlite3_prepare_v2(
        pDb: *mut sqlite3,
        zSql: *const c_char,
        nByte: c_int,
        ppStmt: *mut *mut sqlite3_stmt,
        pzTail: *mut *const c_char,
    ) -> c_int;
    pub fn sqlite3_step(pStmt: *mut sqlite3_stmt) -> c_int;
    pub fn sqlite3_finalize(pStmt: *mut sqlite3_stmt) -> c_int;
    pub fn sqlite3_column_count(pStmt: *mut sqlite3_stmt) -> c_int;
    pub fn sqlite3_column_name(pStmt: *mut sqlite3_stmt, N: c_int) -> *const c_char;
    pub fn sqlite3_column_text(pStmt: *mut sqlite3_stmt, iCol: c_int) -> *const c_char;
    pub fn sqlite3_column_int(pStmt: *mut sqlite3_stmt, iCol: c_int) -> c_int;
    pub fn sqlite3_column_double(pStmt: *mut sqlite3_stmt, iCol: c_int) -> f64;
    pub fn sqlite3_errmsg(pDb: *mut sqlite3) -> *const c_char;
    pub fn sqlite3_free(p: *mut c_void);
}

// 安全的 Rust 包装器
pub struct Database {
    raw: *mut sqlite3,
}

pub struct Statement<'db> {
    raw: *mut sqlite3_stmt,
    _phantom: std::marker::PhantomData<&'db Database>,
}

pub struct Row<'stmt> {
    stmt: &'stmt Statement<'stmt>,
}

impl Database {
    pub fn open(path: &str) -> Result<Self, SqliteError> {
        let c_path = CString::new(path).map_err(|_| SqliteError::InvalidPath)?;
        let mut raw = ptr::null_mut();

        unsafe {
            let result = sqlite3_open(c_path.as_ptr(), &mut raw);
            if result != SQLITE_OK {
                return Err(SqliteError::OpenFailed(result));
            }
            Ok(Database { raw })
        }
    }

    pub fn execute(&self, sql: &str) -> Result<(), SqliteError> {
        let c_sql = CString::new(sql).map_err(|_| SqliteError::InvalidSql)?;

        unsafe {
            let result = sqlite3_exec(
                self.raw,
                c_sql.as_ptr(),
                None,
                ptr::null_mut(),
                ptr::null_mut(),
            );

            if result != SQLITE_OK {
                return Err(SqliteError::ExecFailed(result));
            }
            Ok(())
        }
    }

    pub fn prepare(&self, sql: &str) -> Result<Statement, SqliteError> {
        let c_sql = CString::new(sql).map_err(|_| SqliteError::InvalidSql)?;
        let mut raw = ptr::null_mut();

        unsafe {
            let result = sqlite3_prepare_v2(
                self.raw,
                c_sql.as_ptr(),
                -1,  // 读取到 null 终止符
                &mut raw,
                ptr::null_mut(),
            );

            if result != SQLITE_OK {
                return Err(SqliteError::PrepareFailed(result));
            }

            Ok(Statement {
                raw,
                _phantom: std::marker::PhantomData,
            })
        }
    }

    pub fn last_error(&self) -> String {
        unsafe {
            let msg = sqlite3_errmsg(self.raw);
            CStr::from_ptr(msg).to_string_lossy().into_owned()
        }
    }
}

impl Drop for Database {
    fn drop(&mut self) {
        unsafe {
            let _ = sqlite3_close(self.raw);
        }
    }
}

// 禁止跨线程共享（SQLite 默认非线程安全）
impl !Send for Database {}
impl !Sync for Database {}

impl<'db> Statement<'db> {
    pub fn step(&self) -> Result<bool, SqliteError> {
        unsafe {
            match sqlite3_step(self.raw) {
                SQLITE_ROW => Ok(true),
                SQLITE_DONE => Ok(false),
                code => Err(SqliteError::StepFailed(code)),
            }
        }
    }

    pub fn column_count(&self) -> i32 {
        unsafe { sqlite3_column_count(self.raw) }
    }

    pub fn column_name(&self, idx: i32) -> Option<&str> {
        unsafe {
            let ptr = sqlite3_column_name(self.raw, idx);
            if ptr.is_null() {
                None
            } else {
                Some(CStr::from_ptr(ptr).to_str().ok()?)
            }
        }
    }

    pub fn get_text(&self, idx: i32) -> Option<&str> {
        unsafe {
            let ptr = sqlite3_column_text(self.raw, idx);
            if ptr.is_null() {
                None
            } else {
                Some(CStr::from_ptr(ptr as *const c_char).to_str().ok()?)
            }
        }
    }

    pub fn get_int(&self, idx: i32) -> i32 {
        unsafe { sqlite3_column_int(self.raw, idx) }
    }

    pub fn get_double(&self, idx: i32) -> f64 {
        unsafe { sqlite3_column_double(self.raw, idx) }
    }
}

impl<'db> Drop for Statement<'db> {
    fn drop(&mut self) {
        unsafe {
            let _ = sqlite3_finalize(self.raw);
        }
    }
}

#[derive(Debug)]
pub enum SqliteError {
    InvalidPath,
    InvalidSql,
    OpenFailed(c_int),
    ExecFailed(c_int),
    PrepareFailed(c_int),
    StepFailed(c_int),
}

impl std::fmt::Display for SqliteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SqliteError::InvalidPath => write!(f, "Invalid database path"),
            SqliteError::InvalidSql => write!(f, "Invalid SQL statement"),
            SqliteError::OpenFailed(code) => write!(f, "Failed to open database: {}", code),
            SqliteError::ExecFailed(code) => write!(f, "Failed to execute SQL: {}", code),
            SqliteError::PrepareFailed(code) => write!(f, "Failed to prepare statement: {}", code),
            SqliteError::StepFailed(code) => write!(f, "Failed to step: {}", code),
        }
    }
}

impl std::error::Error for SqliteError {}
```

### 使用 Bindgen 自动生成绑定

对于大型 C 库，手动编写绑定是不现实的。`bindgen` 可以自动生成 Rust 绑定：

**Cargo.toml:**

```toml
[package]
name = "bindgen-demo"
version = "0.1.0"
edition = "2021"

[dependencies]

[build-dependencies]
bindgen = "0.69"
```

**build.rs:**

```rust
use std::env;
use std::path::PathBuf;

fn main() {
    // 告诉 cargo 在库变化时重新构建
    println!("cargo:rerun-if-changed=wrapper.h");

    // 使用 bindgen 生成绑定
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg("-I/usr/include")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        // 白名单配置
        .allowlist_function("sqlite3_.*")
        .allowlist_type("sqlite3.*")
        .allowlist_var("SQLITE_.*")
        // 生成选项
        .size_t_is_usize(true)
        .generate_comments(true)
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // 链接 SQLite
    println!("cargo:rustc-link-lib=sqlite3");
}
```

**wrapper.h:**

```c
#include <sqlite3.h>
```

**src/lib.rs:**

```rust
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
```

## Python 绑定

使用 PyO3 创建 Python 扩展模块：

**Cargo.toml:**

```toml
[package]
name = "my-rust-lib"
version = "0.1.0"
edition = "2021"

[lib]
name = "my_rust_lib"
crate-type = ["cdylib"]

[dependencies]
pyo3 = { version = "0.20", features = ["extension-module"] }

[features]
default = ["pyo3/extension-module"]
```

**src/lib.rs:**

```rust
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyList;

/// 高性能计算模块示例

/// 计算斐波那契数列（使用矩阵快速幂）
#[pyfunction]
fn fibonacci(n: u64) -> PyResult<u64> {
    if n > 93 {
        return Err(PyValueError::new_err(
            "n is too large, would overflow u64"
        ));
    }

    fn mat_mult(a: [[u64; 2]; 2], b: [[u64; 2]; 2]) -> [[u64; 2]; 2] {
        [
            [
                a[0][0] * b[0][0] + a[0][1] * b[1][0],
                a[0][0] * b[0][1] + a[0][1] * b[1][1],
            ],
            [
                a[1][0] * b[0][0] + a[1][1] * b[1][0],
                a[1][0] * b[0][1] + a[1][1] * b[1][1],
            ],
        ]
    }

    fn mat_pow(mut base: [[u64; 2]; 2], mut exp: u64) -> [[u64; 2]; 2] {
        let mut result = [[1, 0], [0, 1]];
        while exp > 0 {
            if exp & 1 == 1 {
                result = mat_mult(result, base);
            }
            base = mat_mult(base, base);
            exp >>= 1;
        }
        result
    }

    if n == 0 {
        return Ok(0);
    }

    let m = [[1, 1], [1, 0]];
    let result = mat_pow(m, n - 1);
    Ok(result[0][0])
}

/// 快速排序实现
#[pyfunction]
fn quicksort(py: Python, list: &PyList) -> PyResult<PyObject> {
    let mut vec: Vec<i64> = list.extract()?;
    vec.sort_unstable();
    vec.to_object(py)
}

/// 字符串处理类
#[pyclass]
struct TextProcessor {
    text: String,
    word_count: usize,
}

#[pymethods]
impl TextProcessor {
    #[new]
    fn new(text: String) -> Self {
        let word_count = text.split_whitespace().count();
        TextProcessor { text, word_count }
    }

    /// 获取词频统计
    fn word_frequency(&self) -> PyResult<std::collections::HashMap<String, u32>> {
        let mut freq = std::collections::HashMap::new();
        for word in self.text.to_lowercase().split_whitespace() {
            let cleaned: String = word
                .chars()
                .filter(|c| c.is_alphanumeric())
                .collect();
            if !cleaned.is_empty() {
                *freq.entry(cleaned).or_insert(0) += 1;
            }
        }
        Ok(freq)
    }

    /// 计算相似度（余弦相似度）
    fn similarity(&self, other: &TextProcessor) -> f64 {
        use std::collections::HashSet;

        let words1: HashSet<_> = self.text.to_lowercase()
            .split_whitespace()
            .map(|w| w.to_string())
            .collect();
        let words2: HashSet<_> = other.text.to_lowercase()
            .split_whitespace()
            .map(|w| w.to_string())
            .collect();

        let intersection: HashSet<_> = words1.intersection(&words2).collect();
        let union: HashSet<_> = words1.union(&words2).collect();

        if union.is_empty() {
            0.0
        } else {
            intersection.len() as f64 / union.len() as f64
        }
    }

    #[getter]
    fn word_count(&self) -> usize {
        self.word_count
    }

    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("TextProcessor(text={:?}, words={})",
                   &self.text[..self.text.len().min(20)],
                   self.word_count))
    }
}

/// 并行数据处理
#[pyfunction]
fn parallel_map(py: Python, items: &PyList, py_func: PyObject) -> PyResult<PyObject> {
    use rayon::prelude::*;

    let items: Vec<PyObject> = items.extract()?;
    let results: Result<Vec<_>, _> = items
        .par_iter()
        .map(|item| {
            Python::with_gil(|py| {
                py_func.call1(py, (item,))
            })
        })
        .collect();

    results?.to_object(py)
}

/// 模块定义
#[pymodule]
fn my_rust_lib(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(fibonacci, m)?)?;
    m.add_function(wrap_pyfunction!(quicksort, m)?)?;
    m.add_function(wrap_pyfunction!(parallel_map, m)?)?;
    m.add_class::<TextProcessor>()?;
    Ok(())
}
```

**使用 Maturin 构建和发布：**

```bash
# 安装 maturin
cargo install maturin

# 开发构建
maturin develop

# 发布构建
maturin build --release

# 发布到 PyPI
maturin publish
```

**Python 使用示例：**

```python
import my_rust_lib

# 高性能斐波那契计算
print(my_rust_lib.fibonacci(50))  # 12586269025

# 快速排序
numbers = [3, 1, 4, 1, 5, 9, 2, 6]
sorted_nums = my_rust_lib.quicksort(numbers)

# 文本处理
text = my_rust_lib.TextProcessor("Hello world hello rust")
print(text.word_count)  # 4
freq = text.word_frequency()
print(freq)  # {'hello': 2, 'world': 1, 'rust': 1}
```

## 回调函数处理

处理 C 风格的回调函数是 FFI 编程中的常见需求：

```rust
use std::ffi::c_void;
use std::os::raw::{c_char, c_int};
use std::sync::{Arc, Mutex};

// C 库接口
#[link(name = "callback_lib")]
extern "C" {
    fn register_callback(
        callback: extern "C" fn(*mut c_void, c_int, *const c_char),
        user_data: *mut c_void,
    );
    fn trigger_event(event_id: c_int, message: *const c_char);
    fn unregister_callback();
}

// 安全的回调管理器
pub struct CallbackManager<T> {
    callback: Arc<Mutex<T>>,
    _phantom: std::marker::PhantomData<extern "C" fn()>,
}

impl<T> CallbackManager<T>
where
    T: FnMut(i32, &str) + Send + 'static,
{
    pub fn new<F>(callback: F) -> Self
    where
        F: FnMut(i32, &str) + Send + 'static,
    {
        CallbackManager {
            callback: Arc::new(Mutex::new(callback)),
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn register(&self) {
        let ptr = Arc::into_raw(self.callback.clone()) as *mut c_void;

        unsafe {
            register_callback(Self::trampoline, ptr);
        }
    }

    extern "C" fn trampoline(
        user_data: *mut c_void,
        event_id: c_int,
        message: *const c_char,
    ) {
        unsafe {
            let callback_ptr = user_data as *mut Arc<Mutex<T>>;
            let callback = &mut *(*callback_ptr).lock().unwrap();

            let msg = std::ffi::CStr::from_ptr(message)
                .to_str()
                .unwrap_or("<invalid utf8>");

            callback(event_id, msg);
        }
    }
}

impl<T> Drop for CallbackManager<T> {
    fn drop(&mut self) {
        unsafe {
            unregister_callback();
        }
    }
}

// 使用示例
pub fn demo_callback() {
    let events = Arc::new(Mutex::new(Vec::new()));
    let events_clone = events.clone();

    let manager = CallbackManager::new(move |id, msg| {
        println!("Event {}: {}", id, msg);
        events_clone.lock().unwrap().push((id, msg.to_string()));
    });

    manager.register();

    // 触发事件
    unsafe {
        let msg = std::ffi::CString::new("Hello from C").unwrap();
        trigger_event(1, msg.as_ptr());
    }
}
```

## 复杂数据结构

处理 C 结构体和联合体：

```rust
use std::ffi::{c_char, c_int, c_void};

// C 结构体
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

#[repr(C)]
pub struct Rectangle {
    pub top_left: Point,
    pub bottom_right: Point,
}

// 联合体
#[repr(C)]
pub union Value {
    pub int_val: c_int,
    pub float_val: f32,
    pub ptr_val: *mut c_void,
}

// 变体类型
#[repr(C)]
pub struct Variant {
    pub type_id: c_int,
    pub value: Value,
}

// 链表节点
#[repr(C)]
pub struct ListNode {
    pub data: c_int,
    pub next: *mut ListNode,
}

// 安全的链表包装器
pub struct SafeList {
    head: *mut ListNode,
}

impl SafeList {
    pub fn new() -> Self {
        SafeList { head: std::ptr::null_mut() }
    }

    pub fn push(&mut self, data: c_int) {
        unsafe {
            let new_node = Box::into_raw(Box::new(ListNode {
                data,
                next: self.head,
            }));
            self.head = new_node;
        }
    }

    pub fn iter(&self) -> ListIter {
        ListIter { current: self.head }
    }
}

impl Drop for SafeList {
    fn drop(&mut self) {
        unsafe {
            let mut current = self.head;
            while !current.is_null() {
                let node = Box::from_raw(current);
                current = node.next;
                // Box::from_raw 会自动 drop
            }
        }
    }
}

pub struct ListIter {
    current: *mut ListNode,
}

impl Iterator for ListIter {
    type Item = c_int;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.current.is_null() {
                None
            } else {
                let node = &*self.current;
                let data = node.data;
                self.current = node.next;
                Some(data)
            }
        }
    }
}
```

## 线程安全与 FFI

处理多线程 FFI 调用：

```rust
use std::ffi::{c_char, c_int};
use std::sync::{Arc, Mutex};
use std::thread;

// 假设的线程不安全 C 库
#[link(name = "thread_unsafe_lib")]
extern "C" {
    fn init_library();
    fn process_data(data: *const c_char) -> c_int;
    fn cleanup_library();
}

// 线程安全的包装器
pub struct ThreadSafeLibrary {
    inner: Arc<Mutex<LibraryHandle>>,
}

struct LibraryHandle;

impl ThreadSafeLibrary {
    pub fn new() -> Result<Self, LibraryError> {
        unsafe {
            init_library();
        }
        Ok(ThreadSafeLibrary {
            inner: Arc::new(Mutex::new(LibraryHandle)),
        })
    }

    pub fn process(&self, data: &str) -> Result<i32, LibraryError> {
        let c_data = std::ffi::CString::new(data)
            .map_err(|_| LibraryError::InvalidData)?;

        let _guard = self.inner.lock().unwrap();

        unsafe {
            let result = process_data(c_data.as_ptr());
            if result < 0 {
                Err(LibraryError::ProcessingFailed(result))
            } else {
                Ok(result)
            }
        }
    }

    pub fn clone(&self) -> Self {
        ThreadSafeLibrary {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl Drop for ThreadSafeLibrary {
    fn drop(&mut self) {
        // 只有当最后一个引用被 drop 时才清理
        if Arc::strong_count(&self.inner) == 1 {
            unsafe {
                cleanup_library();
            }
        }
    }
}

unsafe impl Send for ThreadSafeLibrary {}
unsafe impl Sync for ThreadSafeLibrary {}

// 多线程使用示例
pub fn parallel_process(items: Vec<String>) -> Vec<Result<i32, LibraryError>> {
    let lib = ThreadSafeLibrary::new().unwrap();

    let handles: Vec<_> = items
        .into_iter()
        .map(|item| {
            let lib_clone = lib.clone();
            thread::spawn(move || lib_clone.process(&item))
        })
        .collect();

    handles.into_iter().map(|h| h.join().unwrap()).collect()
}

#[derive(Debug)]
pub enum LibraryError {
    InvalidData,
    ProcessingFailed(c_int),
}
```

## 内存管理

正确处理跨语言内存边界：

```rust
use std::ffi::{c_char, c_void};
use std::os::raw::c_int;

// 内存管理策略

/// Rust 分配，C 使用
#[no_mangle]
pub extern "C" fn rust_alloc_buffer(size: usize) -> *mut u8 {
    let mut vec = vec![0u8; size];
    let ptr = vec.as_mut_ptr();
    std::mem::forget(vec); // 防止 Rust 释放
    ptr
}

#[no_mangle]
pub extern "C" fn rust_free_buffer(ptr: *mut u8, size: usize) {
    if !ptr.is_null() {
        unsafe {
            let _ = Vec::from_raw_parts(ptr, 0, size);
        }
    }
}

/// C 分配，Rust 使用
pub struct CBuffer {
    ptr: *mut c_char,
    len: usize,
    free_fn: unsafe extern "C" fn(*mut c_char),
}

impl CBuffer {
    pub unsafe fn new(
        ptr: *mut c_char,
        len: usize,
        free_fn: unsafe extern "C" fn(*mut c_char),
    ) -> Self {
        CBuffer { ptr, len, free_fn }
    }

    pub fn as_str(&self) -> Option<&str> {
        unsafe {
            if self.ptr.is_null() {
                None
            } else {
                std::str::from_utf8(
                    std::slice::from_raw_parts(self.ptr as *const u8, self.len)
                ).ok()
            }
        }
    }
}

impl Drop for CBuffer {
    fn drop(&mut self) {
        unsafe {
            if !self.ptr.is_null() {
                (self.free_fn)(self.ptr);
            }
        }
    }
}

/// 引用计数共享内存
pub struct SharedBuffer {
    data: *mut c_void,
    ref_count: *mut std::sync::atomic::AtomicUsize,
    deleter: unsafe extern "C" fn(*mut c_void),
}

impl SharedBuffer {
    pub unsafe fn new(
        data: *mut c_void,
        deleter: unsafe extern "C" fn(*mut c_void),
    ) -> Self {
        let ref_count = Box::into_raw(Box::new(
            std::sync::atomic::AtomicUsize::new(1)
        ));
        SharedBuffer { data, ref_count, deleter }
    }

    fn clone_ref(&self) -> Self {
        unsafe {
            (*self.ref_count).fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        }
        SharedBuffer {
            data: self.data,
            ref_count: self.ref_count,
            deleter: self.deleter,
        }
    }
}

impl Clone for SharedBuffer {
    fn clone(&self) -> Self {
        self.clone_ref()
    }
}

impl Drop for SharedBuffer {
    fn drop(&mut self) {
        unsafe {
            let count = (*self.ref_count).fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
            if count == 1 {
                (self.deleter)(self.data);
                let _ = Box::from_raw(self.ref_count);
            }
        }
    }
}
```

## 最佳实践

### 1. 类型安全封装

始终为 FFI 调用提供安全的 Rust 包装器：

```rust
// 不安全的原始 FFI
extern "C" {
    fn raw_process(data: *const u8, len: usize) -> c_int;
}

// 安全的包装器
pub fn process_data(data: &[u8]) -> Result<(), Error> {
    if data.is_empty() {
        return Err(Error::EmptyData);
    }

    let result = unsafe { raw_process(data.as_ptr(), data.len()) };

    match result {
        0 => Ok(()),
        err => Err(Error::from_code(err)),
    }
}
```

### 2. 文档和不变式

清晰地记录 FFI 调用的前置条件和后置条件：

```rust
/// # Safety
///
/// - `ptr` 必须是有效的、非空的指针
/// - `ptr` 必须指向由 `create_context` 创建的上下文
/// - 上下文不能在另一个线程中并发使用
/// - 调用者必须确保在最后一次使用后调用 `destroy_context`
pub unsafe fn use_context(ptr: *mut Context) -> Result<(), Error> {
    // ...
}
```

### 3. 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_wrapper() {
        let data = b"test data";
        assert!(process_data(data).is_ok());
    }

    #[test]
    fn test_empty_data_rejected() {
        assert!(matches!(
            process_data(b""),
            Err(Error::EmptyData)
        ));
    }

    // 使用 mock 进行测试
    #[test]
    fn test_with_mock() {
        // 实现测试替身
    }
}
```

### 4. 错误处理模式

```rust
#[derive(Debug)]
pub enum FfiError {
    NullPointer,
    InvalidUtf8,
    LibraryError { code: i32, message: String },
    BufferTooSmall { required: usize, provided: usize },
}

impl std::fmt::Display for FfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FfiError::NullPointer => write!(f, "Null pointer passed to FFI function"),
            FfiError::InvalidUtf8 => write!(f, "Invalid UTF-8 sequence in C string"),
            FfiError::LibraryError { code, message } => {
                write!(f, "Library error {}: {}", code, message)
            }
            FfiError::BufferTooSmall { required, provided } => {
                write!(f, "Buffer too small: need {} bytes, got {}", required, provided)
            }
        }
    }
}

impl std::error::Error for FfiError {}
```

### 5. 持续集成配置

```yaml
# .github/workflows/ffi.yml
name: FFI Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install dependencies
        run: |
          sudo apt-get update
          sudo apt-get install -y libsqlite3-dev

      - name: Install Rust
        uses: dtolnay/rust-action@stable

      - name: Build
        run: cargo build --all-features

      - name: Test
        run: cargo test --all-features

      - name: Clippy
        run: cargo clippy --all-features -- -D warnings
```

---

通过遵循这些模式和最佳实践，你可以安全高效地在 Rust 中使用 FFI，同时保持 Rust 的安全保证。
