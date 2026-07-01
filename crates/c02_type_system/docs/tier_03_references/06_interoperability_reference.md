# 3.6 Rust 类型系统 - 互操作参考

> **文档类型**: Tier 3 - 参考层
> **文档定位**: Rust 与其他语言的类型系统互操作参考
> **适用对象**: 高级开发者、系统集成开发者
> **前置知识**: [类型系统规范](01_type_system_specification.md)
> **最后更新**: 2025-12-11
> **Rust版本**: 1.92.0+

---

## 📋 目录

- [3.6 Rust 类型系统 - 互操作参考](#36-rust-类型系统---互操作参考)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [互操作范围](#互操作范围)
  - [1. C 语言互操作](#1-c-语言互操作)
    - [1.1 基本类型映射](#11-基本类型映射)
    - [1.2 调用 C 函数](#12-调用-c-函数)
    - [1.3 暴露 Rust 函数给 C](#13-暴露-rust-函数给-c)
  - [2. C++ 互操作](#2-c-互操作)
    - [2.1 使用 cxx 库](#21-使用-cxx-库)
    - [2.2 类型映射](#22-类型映射)
  - [3. Python 互操作](#3-python-互操作)
    - [3.1 使用 PyO3](#31-使用-pyo3)
    - [3.2 类型转换](#32-类型转换)
  - [4. JavaScript/WebAssembly 互操作](#4-javascriptwebassembly-互操作)
    - [4.1 使用 wasm-bindgen](#41-使用-wasm-bindgen)
    - [4.2 类型映射](#42-类型映射)
  - [5. Java 互操作](#5-java-互操作)
    - [5.1 使用 jni](#51-使用-jni)
  - [6. Go 互操作](#6-go-互操作)
    - [6.1 CGO 接口](#61-cgo-接口)
  - [7. 类型映射参考](#7-类型映射参考)
    - [7.1 完整类型映射表](#71-完整类型映射表)
  - [8. FFI 最佳实践](#8-ffi-最佳实践)
    - [8.1 安全性](#81-安全性)
    - [8.2 错误处理](#82-错误处理)
    - [8.3 内存管理](#83-内存管理)
  - [9. 常见问题](#9-常见问题)
    - [问题1: 类型大小不匹配](#问题1-类型大小不匹配)
    - [问题2: 调用约定不匹配](#问题2-调用约定不匹配)
    - [问题3: 字符串编码问题](#问题3-字符串编码问题)
  - [10. 参考资源](#10-参考资源)
    - [10.1 官方文档](#101-官方文档)
    - [10.2 相关库](#102-相关库)

---

## 🎯 概述

本文档提供 Rust 类型系统与其他编程语言互操作的完整参考，包括类型映射、FFI 使用、数据转换等。

### 互操作范围

- C/C++ FFI
- Python 绑定
- JavaScript/WebAssembly
- Java JNI
- Go cgo
- 类型系统映射

---

## 1. C 语言互操作

### 1.1 基本类型映射

Rust 与 C 的基本类型对应：

| Rust 类型  | C 类型     | 说明           |
| :--- | :--- | :--- |
| `i8`       | `int8_t`   | 8位有符号整数  |
| `u8`       | `uint8_t`  | 8位无符号整数  |
| `i16`      | `int16_t`  | 16位有符号整数 |
| `u16`      | `uint16_t` | 16位无符号整数 |
| `i32`      | `int32_t`  | 32位有符号整数 |
| `u32`      | `uint32_t` | 32位无符号整数 |
| `i64`      | `int64_t`  | 64位有符号整数 |
| `u64`      | `uint64_t` | 64位无符号整数 |
| `f32`      | `float`    | 32位浮点数     |
| `f64`      | `double`   | 64位浮点数     |
| `bool`     | `bool`     | 布尔类型       |
| `*const T` | `const T*` | 常量指针       |
| `*mut T`   | `T*`       | 可变指针       |

### 1.2 调用 C 函数

```rust
use std::os::raw::c_int;

#[link(name = "mylib")]
extern "C" {
    fn my_c_function(x: c_int, y: c_int) -> c_int;
}

fn main() {
    unsafe {
        let result = my_c_function(10, 20);
        println!("Result: {}", result);
    }
}
```

### 1.3 暴露 Rust 函数给 C

```rust
#[no_mangle]
pub extern "C" fn rust_function(x: i32, y: i32) -> i32 {
    x + y
}
```

---

## 2. C++ 互操作

### 2.1 使用 cxx 库

```rust
use cxx::bridge;

#[bridge]
mod ffi {
    extern "C++" {
        include!("myheader.hpp");

        type MyClass;

        fn new_my_class() -> UniquePtr<MyClass>;
        fn process(&self, value: i32) -> i32;
    }
}
```

### 2.2 类型映射

C++ 类型到 Rust 的映射：

| C++ 类型             | Rust 类型      | 说明     |
| :--- | :--- | :--- || `std::string`        | `String`       | 字符串   |
| `std::vector<T>`     | `Vec<T>`       | 向量     |
| `std::unique_ptr<T>` | `UniquePtr<T>` | 唯一指针 |
| `std::shared_ptr<T>` | `SharedPtr<T>` | 共享指针 |

---

## 3. Python 互操作

### 3.1 使用 PyO3

```rust
use pyo3::prelude::*;

#[pyfunction]
fn add(x: i32, y: i32) -> i32 {
    x + y
}

#[pymodule]
fn my_module(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(add, m)?)?;
    Ok(())
}
```

### 3.2 类型转换

```rust
use pyo3::types::PyDict;

fn process_dict(py: Python, dict: &PyDict) -> PyResult<()> {
    let value: i32 = dict.get_item("key")?.unwrap().extract()?;
    Ok(())
}
```

---

## 4. JavaScript/WebAssembly 互操作

### 4.1 使用 wasm-bindgen

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen]
pub struct Person {
    name: String,
    age: u32,
}

#[wasm_bindgen]
impl Person {
    #[wasm_bindgen(constructor)]
    pub fn new(name: String, age: u32) -> Person {
        Person { name, age }
    }

    #[wasm_bindgen(getter)]
    pub fn name(&self) -> String {
        self.name.clone()
    }
}
```

### 4.2 类型映射

| Rust 类型      | JavaScript 类型 |
| :--- | :--- || `i32`          | `number`        |
| `f64`          | `number`        |
| `String`       | `string`        |
| `Vec<T>`       | `Array`         |
| `Option<T>`    | `T \| null`     |
| `Result<T, E>` | `T \| Error`    |

---

## 5. Java 互操作

### 5.1 使用 jni

```rust
use jni::JNIEnv;
use jni::objects::JClass;
use jni::sys::jstring;

#[no_mangle]
pub extern "system" fn Java_HelloWorld_greet(
    env: JNIEnv,
    _class: JClass,
    input: jstring,
) -> jstring {
    let input: String = env
        .get_string(input)
        .expect("Couldn't get java string!")
        .into();

    let output = env
        .new_string(format!("Hello from Rust, {}!", input))
        .expect("Couldn't create java string!");

    output.into_inner()
}
```

---

## 6. Go 互操作

### 6.1 CGO 接口

通过 C 接口与 Go 互操作：

```rust
// Rust 侧
#[no_mangle]
pub extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}
```

```go
// Go 侧
/*
#cgo LDFLAGS: -L. -lrustlib
#include <stdint.h>
int32_t rust_function(int32_t x);
*/
import "C"

func main() {
    result := C.rust_function(42)
    fmt.Println(result)
}
```

---

## 7. 类型映射参考

### 7.1 完整类型映射表

| Rust        | C               | C++                | Python      | JavaScript  | Java          |
| :--- | :--- | :--- | :--- | :--- | :--- || `i32`       | `int32_t`       | `int32_t`          | `int`       | `number`    | `int`         |
| `i64`       | `int64_t`       | `int64_t`          | `int`       | `number`    | `long`        |
| `f64`       | `double`        | `double`           | `float`     | `number`    | `double`      |
| `bool`      | `bool`          | `bool`             | `bool`      | `boolean`   | `boolean`     |
| `String`    | `char*`         | `std::string`      | `str`       | `string`    | `String`      |
| `Vec<T>`    | `T*`            | `std::vector<T>`   | `list`      | `Array`     | `List<T>`     |
| `Option<T>` | `T*` (nullable) | `std::optional<T>` | `T \| None` | `T \| null` | `Optional<T>` |

---

## 8. FFI 最佳实践

### 8.1 安全性

```rust
// ✅ 好的做法：使用安全的包装
pub fn safe_wrapper(x: i32) -> Result<i32, String> {
    unsafe {
        let result = unsafe_c_function(x);
        if result < 0 {
            Err("Function failed".to_string())
        } else {
            Ok(result)
        }
    }
}

// ❌ 不好的做法：直接暴露 unsafe
pub unsafe fn unsafe_function(x: i32) -> i32 {
    unsafe_c_function(x)
}
```

### 8.2 错误处理

```rust
use std::ffi::CStr;
use std::os::raw::c_char;

pub fn get_error_message(ptr: *const c_char) -> Result<String, String> {
    if ptr.is_null() {
        return Err("Null pointer".to_string());
    }

    unsafe {
        let c_str = CStr::from_ptr(ptr);
        c_str.to_str()
            .map(|s| s.to_string())
            .map_err(|e| format!("Invalid UTF-8: {}", e))
    }
}
```

### 8.3 内存管理

```rust
// 使用 Box 管理 C 分配的内存
extern "C" {
    fn c_allocate() -> *mut c_void;
    fn c_free(ptr: *mut c_void);
}

struct CResource {
    ptr: *mut c_void,
}

impl Drop for CResource {
    fn drop(&mut self) {
        unsafe {
            c_free(self.ptr);
        }
    }
}
```

---

## 9. 常见问题

### 问题1: 类型大小不匹配

**错误**: C 和 Rust 类型大小不一致

**解决方案**: 使用 `std::mem::size_of` 验证

```rust
assert_eq!(std::mem::size_of::<i32>(), 4);
```

### 问题2: 调用约定不匹配

**错误**: 函数调用约定不一致

**解决方案**: 明确指定调用约定

```rust
#[no_mangle]
pub extern "C" fn function() {}  // C 调用约定
```

### 问题3: 字符串编码问题

**错误**: UTF-8 和 C 字符串转换错误

**解决方案**: 使用 `CString` 和 `CStr`

```rust
use std::ffi::{CString, CStr};

let c_str = CString::new("hello").unwrap();
let rust_str = CStr::from_ptr(c_str.as_ptr()).to_str().unwrap();
```

---

## 10. 参考资源

### 10.1 官方文档

- [Rust FFI Guide](https://doc.rust-lang.org/nomicon/ffi.html)
- [The Rust FFI Omnibus](http://jakegoulding.com/rust-ffi-omnibus/)

### 10.2 相关库

- [PyO3](https://pyo3.rs/) - Python 绑定
- [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) - WebAssembly 绑定
- [cxx](https://cxx.rs/) - C++ 互操作
- [jni](https://docs.rs/jni/) - Java 互操作

---

**最后更新**: 2025-12-11
**Rust版本**: 1.92.0+
**文档版本**: v1.0

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
