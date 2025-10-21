# FFI 与互操作

> **核心库**: libc, bindgen, cc, cbindgen  
> **适用场景**: C/C++互操作、系统调用、绑定生成

---

## 📋 核心库概览

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **libc** | C标准库绑定 | 跨平台系统调用 | ⭐⭐⭐⭐⭐ |
| **bindgen** | C头文件→Rust | 自动生成绑定 | ⭐⭐⭐⭐⭐ |
| **cc** | 编译C/C++代码 | build.rs集成 | ⭐⭐⭐⭐⭐ |
| **cbindgen** | Rust→C头文件 | 导出C API | ⭐⭐⭐⭐ |

---

## 🔗 libc - 系统调用

```rust
use libc::{c_int, getpid};

fn main() {
    unsafe {
        let pid: c_int = getpid();
        println!("Process ID: {}", pid);
    }
}
```

---

## 🛠️ bindgen - 自动绑定生成

```rust
// build.rs
extern crate bindgen;

fn main() {
    bindgen::Builder::default()
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("src/bindings.rs")
        .expect("Couldn't write bindings!");
}
```

---

## ⚙️ cc - 编译C代码

```rust
// build.rs
fn main() {
    cc::Build::new()
        .file("src/helper.c")
        .compile("helper");
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

