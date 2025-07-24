# 跨语言互操作与FFI（Foreign Function Interface）

## 1. 定义与软件工程对标

**FFI**是指不同编程语言之间的互操作机制，允许Rust与C/C++等语言共享数据和调用函数。软件工程wiki认为，FFI是系统集成和底层开发的基础。
**FFI** (Foreign Function Interface) enables interoperability between different programming languages, allowing Rust to share data and call functions with C/C++ and others. In software engineering, FFI is foundational for system integration and low-level development.

## 2. Rust 1.88 最新特性

- **&raw指针操作符**：安全创建原始指针，提升FFI安全性。
- **C字符串字面量**：简化C接口调用。
- **trait对象向上转型**：便于抽象多语言接口。

## 3. 典型惯用法（Idioms）

- 使用#[repr(C)]保证内存布局兼容
- 结合bindgen自动生成绑定代码
- 利用unsafe块安全调用外部函数

## 4. 代码示例

```rust
#[repr(C)]
pub struct MyStruct {
    pub a: i32,
    pub b: f64,
}
extern "C" {
    fn c_func(x: i32) -> i32;
}
```

## 5. 软件工程概念对照

- **兼容性（Compatibility）**：内存布局与ABI兼容。
- **安全性（Safety）**：Rust类型系统和unsafe块协同保障。
- **可维护性（Maintainability）**：自动生成绑定提升可维护性。

## 6. FAQ

- Q: Rust做FFI的优势？
  A: 类型安全、内存安全、自动绑定，适合系统集成和底层开发。

---
