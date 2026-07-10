> **权威来源**:
>
> [ISO C++20](https://isocpp.org/std/the-standard),
> [cppreference](https://en.cppreference.com/),
> [cxx crate 文档](https://cxx.rs/),
> [Rust FFI 文档](https://doc.rust-lang.org/nomicon/ffi.html)
>
> **分级**: [A]
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 ISO C++20、cxx crate 官方文档来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

# C++ 互操作指南（cxx + bindgen） {#c-互操作指南cxx-bindgen}

> **EN**: cxx + bindgen
> **Summary**: C++ 互操作指南 cxx + bindgen.
> **Bloom 层级**: L2-L3

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [C++ 互操作指南（cxx + bindgen） {#c-互操作指南cxx-bindgen}](#c-互操作指南cxx--bindgen-c-互操作指南cxx-bindgen)
  - [📑 目录 {#目录}](#-目录-目录)
  - [概述 {#概述}](#概述-概述)
  - [cxx crate {#cxx-crate}](#cxx-crate-cxx-crate)
    - [核心理念 {#核心理念}](#核心理念-核心理念)
    - [工作流程 {#工作流程-1}](#工作流程-工作流程-1)
    - [build.rs {#buildrs}](#buildrs-buildrs)
  - [bindgen {#bindgen}](#bindgen-bindgen)
    - [工作流程 {#工作流程-1}](#工作流程-工作流程-1-1)
  - [cxx vs bindgen 对比 {#cxx-vs-bindgen-对比}](#cxx-vs-bindgen-对比-cxx-vs-bindgen-对比)
  - [项目中的使用 {#项目中的使用}](#项目中的使用-项目中的使用)
  - [参考 {#参考}](#参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 概述 {#概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 与 C++ 的互操作主要有两条技术路线：

1. **bindgen**: 从 C/C++ 头文件生成 Rust FFI 绑定（单向调用 C++）
2. **cxx**: 安全、双向的 C++/Rust 桥接，编译时检查 ABI 兼容性

## cxx crate {#cxx-crate}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 核心理念 {#核心理念}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **共享类型**: `#[cxx::bridge]` 中定义的 struct，双方都能看到完整定义
- **不透明类型**: C++ 类型对 Rust 不透明，Rust 通过 `UniquePtr<T>` 或 `Pin<&mut T>` 持有
- **安全保证**: cxx 编译器自动生成桥接代码，禁止不安全的指针传递

### 工作流程 {#工作流程-1}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
// src/lib.rs
#[cxx::bridge]
mod ffi {
    // 共享结构体
    struct Point {
        x: f64,
        y: f64,
    }

    // Rust 暴露给 C++
    extern "Rust" {
        fn compute_distance(a: &Point, b: &Point) -> f64;
    }

    // C++ 暴露给 Rust
    unsafe extern "C++" {
        type Canvas;
        fn create_canvas() -> UniquePtr<Canvas>;
        fn draw_point(self: Pin<&mut Canvas>, p: &Point);
    }
}

fn compute_distance(a: &ffi::Point, b: &ffi::Point) -> f64 {
    ((a.x - b.x).powi(2) + (a.y - b.y).powi(2)).sqrt()
}
```

```cpp
// include/cxx_bridge.h (由 cxx 自动生成)
// src/wrapper.cpp (手写 C++ 实现)
#include "rust/cxx.h"
#include "project/src/lib.rs.h"

struct Canvas {
    void draw_point(const Point& p) {
        // C++ 实现
    }
};

std::unique_ptr<Canvas> create_canvas() {
    return std::make_unique<Canvas>();
}
```

### build.rs {#buildrs}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
fn main() {
    cxx_build::bridge("src/lib.rs")
        .file("src/wrapper.cpp")
        .compile("cxx-demo");
}
```

## bindgen {#bindgen}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 工作流程 {#工作流程-1}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

1. 编写 `wrapper.h`，包含需要绑定的 C/C++ 头文件
2. `build.rs` 中调用 `bindgen::Builder` 生成 Rust 代码
3. 手动编写安全封装层（Raw FFI -> Safe Rust API）
4. 链接原生库

```rust,ignore
// build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo:rustc-link-lib=my_c_lib");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

```rust,ignore
// src/lib.rs
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub mod safe_wrapper {
    use super::*;

    pub fn safe_api_call(input: i32) -> Result<i32, String> {
        let result = unsafe { raw_c_function(input) };
        if result < 0 {
            Err("C API error".to_string())
        } else {
            Ok(result)
        }
    }
}
```

## cxx vs bindgen 对比 {#cxx-vs-bindgen-对比}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 特性 | cxx | bindgen |
|------|-----|---------|
| 方向 | 双向（Rust <-> C++） | 单向（Rust -> C/C++） |
| 安全性 | 编译时 ABI 检查 | 无，需手动保证 |
| 复杂度 | 中等（需学习 bridge 语法） | 低（自动生成） |
| C++ 特性 | 支持类、方法、异常（有限） | 仅支持 C 兼容子集 |
| 构建集成 | build.rs 调用 cxx_build | build.rs 调用 bindgen |
| 适用场景 | 新的 C++/Rust 混合项目 | 绑定现有的大型 C 库 |

## 项目中的使用 {#项目中的使用}
>
> **[来源: [crates.io](https://crates.io/)]**

本项目在 `c13_embedded` crate 中提供了 cxx 互操作的概念演示：

```rust,ignore
use c13_embedded::cxx_interop;

cxx_interop::explain_cxx_bridge();
cxx_interop::explain_bindgen_workflow();
```

启用 `cxx-interop` feature 后可尝试真实 cxx 桥接（需要 C++ 编译器）。

## 参考 {#参考}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [cxx 文档](https://cxx.rs/)
- [bindgen 文档](https://rust-lang.github.io/rust-bindgen/)
- [The Rust FFI Omnibus](https://jakegoulding.com/rust-ffi-omnibus/)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
