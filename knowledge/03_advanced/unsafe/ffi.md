# Rust FFI (Foreign Function Interface)

> **版本**: Rust 1.94.0
> **难度**: 高级
> **预计学习时间**: 3-4 小时
> **权威来源**: [The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/), [nomicon](https://doc.rust-lang.org/nomicon/ffi.html)

Rust 的 FFI (Foreign Function Interface) 允许你与其他语言（主要是 C/C++）进行互操作。这是系统编程、嵌入式开发和性能关键型应用的核心技能。

---

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 理解 FFI 的基本概念和安全边界
- [ ] 使用 `extern` 块声明 C 函数
- [ ] 在 Rust 中调用 C 库函数
- [ ] 将 Rust 代码编译为可供 C 调用的库
- [ ] 正确处理 C 与 Rust 之间的类型转换
- [ ] 安全地处理 C 字符串和内存
- [ ] 使用 `bindgen` 自动生成 FFI 绑定
- [ ] 识别并避免常见的 FFI 陷阱

## 📋 先决条件

- 熟练掌握 Rust 所有权和借用规则
- 理解 `unsafe` 块的使用场景
- 基本的 C 语言知识（指针、结构体、内存管理）
- 了解平台的 ABI (Application Binary Interface) 概念

## 🧠 核心概念

### 1. 什么是 FFI

FFI (Foreign Function Interface) 是一种机制，允许一种编程语言调用另一种语言编写的函数。Rust 通过 FFI 可以：

- **调用 C 库**: 利用现有的 C 生态系统（OpenSSL、SQLite、操作系统 API 等）
- **被 C 调用**: 将 Rust 作为库提供给其他语言使用
- **性能关键路径**: 在需要时直接操作内存，绕过 Rust 的安全检查

> ⚠️ **安全边界**: FFI 调用必须包装在 `unsafe` 块中，因为 Rust 编译器无法验证外部代码的安全性。

### 2. extern 块和 ABI

`extern` 关键字用于声明外部函数接口。ABI (Application Binary Interface) 定义了函数调用的底层约定。

```rust
// 声明使用 C ABI 的外部函数
extern "C" {
    fn strlen(s: *const c_char) -> usize;
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
}

// 也可以使用其他 ABI
extern "system" {
    // Windows API 使用 system ABI
    fn GetLastError() -> u32;
}
```

常见 ABI 类型：

| ABI | 说明 | 适用平台 |
|-----|------|---------|
| `"C"` | 标准 C 调用约定 | 跨平台 |
| `"system"` | 系统默认调用约定 | Windows API |
| `"C-unwind"` | 支持堆栈展开的 C ABI | 跨平台，支持 panic |

### 3. 调用 C 函数

#### 3.1 基础示例：调用 C 标准库

```rust
use std::ffi::{CStr, c_char};

fn main() {
    let c_string = b"Hello, FFI!\0";

    unsafe {
        let ptr = c_string.as_ptr() as *const c_char;
        let len = strlen(ptr);
        println!("String length: {}", len);
    }
}
```

#### 3.2 完整示例：包装 C 数学库

```rust
use std::os::raw::{c_double, c_int};

extern "C" {
    fn pow(base: c_double, exp: c_double) -> c_double;
    fn sqrt(x: c_double) -> c_double;
    fn abs(n: c_int) -> c_int;
}

pub fn safe_pow(base: f64, exp: f64) -> f64 {
    unsafe { pow(base, exp) }
}

pub fn safe_sqrt(x: f64) -> Option<f64> {
    if x < 0.0 { None } else { Some(unsafe { sqrt(x) }) }
}

fn main() {
    println!("2^10 = {}", safe_pow(2.0, 10.0));
    println!("sqrt(16) = {:?}", safe_sqrt(16.0));
}
```

### 4. 从 C 调用 Rust

要让 C 代码调用 Rust，需要：

1. 使用 `#[no_mangle]` 防止名称修饰
2. 使用 `extern "C"` 指定 C 调用约定
3. 使用 `pub` 导出函数

```rust
use std::ffi::{CStr, c_char, c_int};

#[no_mangle]
pub extern "C" fn fibonacci(n: c_int) -> c_int {
    if n <= 1 { n } else { fibonacci(n - 1) + fibonacci(n - 2) }
}

#[no_mangle]
pub unsafe extern "C" fn process_string(input: *const c_char) -> c_int {
    if input.is_null() { return -1; }

    let c_str = unsafe { CStr::from_ptr(input) };
    match c_str.to_str() {
        Ok(s) => s.len() as c_int,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn calculate(a: c_int, b: c_int, op: c_char) -> c_int {
    match op as u8 as char {
        '+' => a + b,
        '-' => a - b,
        '*' => a * b,
        '/' => if b == 0 { 0 } else { a / b },
        _ => 0,
    }
}
```

编译配置 (Cargo.toml)：

```toml
[lib]
crate-type = ["cdylib", "staticlib"]
```

### 5. 类型转换

Rust 标准库提供了 C 类型的映射，位于 `std::os::raw` 和 `std::ffi` 模块。

#### 5.1 基本类型映射表

| C 类型 | Rust 类型 | 说明 |
|--------|-----------|------|
| `char` | `c_char` | 可能是 `i8` 或 `u8`，取决于平台 |
| `int` | `c_int` | 有符号整型 |
| `long` | `c_long` | 有符号长整型 |
| `double` | `c_double` | 双精度浮点数 |
| `void*` | `c_void` | 无类型指针 |
| `size_t` | `usize` | 无符号大小类型 |

#### 5.2 类型转换示例

```rust
use std::os::raw::{c_int, c_double, c_char};
use std::ffi::CString;

fn demonstrate_conversions() {
    // Rust 到 C
    let rust_int: i32 = 42;
    let c_int_val: c_int = rust_int as c_int;

    let rust_string = "Hello";
    let c_string = CString::new(rust_string).unwrap();
    let c_ptr: *const c_char = c_string.as_ptr();

    // C 到 Rust
    let c_value: c_int = 100;
    let rust_value: i32 = c_value as i32;
}
```

### 6. 指针和内存安全

FFI 中的指针操作是最危险的，因为 Rust 的所有权系统无法跨越语言边界。

```rust
use std::ptr;
use std::ffi::c_void;

pub struct CBuffer {
    ptr: *mut c_void,
    size: usize,
}

impl CBuffer {
    pub unsafe fn alloc(size: usize) -> Option<Self> {
        if size == 0 { return None; }
        let ptr = libc::malloc(size);
        if ptr.is_null() { None } else { Some(CBuffer { ptr, size }) }
    }

    pub fn as_ptr(&self) -> *const c_void { self.ptr }
}

impl Drop for CBuffer {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe { libc::free(self.ptr); }
            self.ptr = ptr::null_mut();
        }
    }
}
```

#### 不透明指针模式

```rust
pub struct DataProcessor {
    data: Vec<u8>,
    processed_count: usize,
}

#[no_mangle]
pub extern "C" fn processor_new() -> *mut DataProcessor {
    let processor = Box::new(DataProcessor { data: Vec::new(), processed_count: 0 });
    Box::into_raw(processor)
}

#[no_mangle]
pub unsafe extern "C" fn processor_free(ptr: *mut DataProcessor) {
    if !ptr.is_null() { unsafe { drop(Box::from_raw(ptr)); } }
}

#[no_mangle]
pub unsafe extern "C" fn processor_process(
    ptr: *mut DataProcessor,
    data: *const u8,
    len: usize,
) -> c_int {
    if ptr.is_null() || data.is_null() { return -1; }

    let processor = unsafe { &mut *ptr };
    let slice = unsafe { std::slice::from_raw_parts(data, len) };
    processor.data.extend_from_slice(slice);
    processor.processed_count += 1;
    0
}
```

### 7. 字符串处理 (CStr, CString)

| 类型 | 说明 | 使用场景 |
|------|------|----------|
| `CStr` | borrowed C 字符串引用 | 从 C 接收字符串 |
| `CString` | 拥有的 C 字符串 | 传递给 C 字符串 |

```rust
use std::ffi::{CStr, CString, c_char};

/// 安全地处理来自 C 的字符串
#[no_mangle]
pub unsafe extern "C" fn handle_c_string(input: *const c_char) -> *mut c_char {
    if input.is_null() { return std::ptr::null_mut(); }

    let c_str = unsafe { CStr::from_ptr(input) };

    match c_str.to_str() {
        Ok(rust_str) => {
            let response = format!("Processed: {}", rust_str);
            match CString::new(response) {
                Ok(c_string) => c_string.into_raw(),
                Err(_) => std::ptr::null_mut(),
            }
        }
        Err(_) => std::ptr::null_mut(),
    }
}

/// 释放由 Rust 分配的字符串
#[no_mangle]
pub unsafe extern "C" fn free_rust_string(s: *mut c_char) {
    if !s.is_null() { unsafe { drop(CString::from_raw(s)); } }
}
```

### 8. bindgen 工具简介

`bindgen` 自动生成 Rust FFI 绑定。

```toml
# Cargo.toml
[build-dependencies]
bindgen = "0.69"
```

```rust
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=wrapper.h");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings.write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

```rust
// src/lib.rs
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
```

## 💡 最佳实践

1. **最小化 unsafe 代码**: 将 FFI 调用封装在安全函数中
2. **文档化安全前提**: 每个 `unsafe` 函数都应该有 `# Safety` 文档
3. **使用 RAII 模式**: 利用 `Drop` trait 自动管理外部资源
4. **验证所有输入**: 跨越 FFI 边界时验证指针、字符串长度
5. **类型安全包装**: 创建 Rust 友好的 API

```rust
pub struct SafeDatabase {
    handle: *mut DbHandle,
}

impl SafeDatabase {
    pub fn new(path: &str) -> Result<Self, DbError> {
        let c_path = CString::new(path)?;
        let handle = unsafe { db_open(c_path.as_ptr()) };
        if handle.is_null() {
            Err(DbError::ConnectionFailed)
        } else {
            Ok(Self { handle })
        }
    }
}

impl Drop for SafeDatabase {
    fn drop(&mut self) {
        unsafe { db_close(self.handle); }
    }
}
```

## ⚠️ 常见陷阱

| 陷阱 | 说明 | 解决方案 |
|------|------|----------|
| **UB (未定义行为)** | C 代码中的 UB 会破坏 Rust 的安全保证 | 仔细审查 C 代码，使用 sanitizers |
| **panic 跨越边界** | Rust panic 进入 C 代码是 UB | 使用 `std::panic::catch_unwind` |
| **指针生命周期** | C 代码可能保存已释放的指针 | 使用不透明指针 |
| **字符串编码** | C 字符串可能不是有效 UTF-8 | 使用 `CStr::to_str()` 并处理错误 |
| **空指针** | C 代码可能返回 null | 总是检查指针是否为 null |
| **内存分配器不匹配** | 用 malloc 分配，用 Rust 释放会崩溃 | 在哪里分配，就在哪里释放 |
| **线程安全** | C 库可能不是线程安全的 | 使用 `Mutex` 包装 |

## 🎮 动手练习

### 练习 1：包装 C 数学库

创建一个 Rust 包装器，安全地暴露 C 数学库的函数。

<details>
<summary>参考答案</summary>

```rust
use std::os::raw::c_double;

extern "C" {
    fn pow(base: c_double, exp: c_double) -> c_double;
    fn sqrt(x: c_double) -> c_double;
}

pub fn safe_sqrt(x: f64) -> Option<f64> {
    if x < 0.0 { None } else { Some(unsafe { sqrt(x) }) }
}

pub fn safe_pow(base: f64, exp: f64) -> f64 {
    unsafe { pow(base, exp) }
}
```

</details>

### 练习 2：创建可导出给 C 使用的 Rust 库

创建一个计算统计信息（均值、方差）的 Rust 库。

<details>
<summary>参考答案</summary>

```rust
use std::os::raw::{c_double, c_int};
use std::slice;

#[no_mangle]
pub unsafe extern "C" fn compute_stats(
    data: *const c_double,
    len: c_int,
    mean: *mut c_double,
    variance: *mut c_double,
) -> c_int {
    if data.is_null() || mean.is_null() || variance.is_null() || len <= 0 {
        return -1;
    }

    let slice = unsafe { slice::from_raw_parts(data, len as usize) };
    let m = slice.iter().sum::<f64>() / len as f64;
    let v = slice.iter().map(|x| (x - m).powi(2)).sum::<f64>() / len as f64;

    unsafe {
        *mean = m;
        *variance = v;
    }
    0
}
```

</details>

### 练习 3：不透明指针模式

实现可通过 C 代码创建、使用和释放的 Rust 计算器。

<details>
<summary>参考答案</summary>

```rust
use std::os::raw::c_int;

pub struct Calculator {
    value: c_int,
    operation_count: usize,
}

#[no_mangle]
pub extern "C" fn calculator_new() -> *mut Calculator {
    Box::into_raw(Box::new(Calculator { value: 0, operation_count: 0 }))
}

#[no_mangle]
pub unsafe extern "C" fn calculator_free(calc: *mut Calculator) {
    if !calc.is_null() { drop(Box::from_raw(calc)); }
}

#[no_mangle]
pub unsafe extern "C" fn calculator_add(calc: *mut Calculator, n: c_int) -> c_int {
    if calc.is_null() { return -1; }
    let calc = &mut *calc;
    calc.value += n;
    calc.operation_count += 1;
    calc.value
}
```

</details>

## 📖 延伸阅读

- [The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/) - Rust FFI 实例大全
- [Rust Nomicon - FFI](https://doc.rust-lang.org/nomicon/ffi.html) - 深入 FFI 安全细节
- [The bindgen User Guide](https://rust-lang.github.io/rust-bindgen/) - bindgen 完整文档
- [Rust Reference - External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

## ✅ 自我检测

1. 为什么 FFI 调用需要 `unsafe` 块？
2. `CStr` 和 `CString` 的主要区别是什么？
3. 如何避免 Rust panic 传播到 C 代码？
4. 什么是不透明指针模式？它有什么优势？
5. `bindgen` 工具的主要用途是什么？

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
