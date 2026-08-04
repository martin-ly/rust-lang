# 外部函数接口（FFI, Foreign Function Interface）


## 📊 目录

- [外部函数接口（FFI, Foreign Function Interface）](#外部函数接口ffi-foreign-function-interface)
  - [📊 目录](#-目录)
  - [1. 工程原理与定义（Principle \& Definition）](#1-工程原理与定义principle--definition)
  - [2. Rust 1.88 新特性工程化应用](#2-rust-188-新特性工程化应用)
  - [3. 典型场景与最佳实践（Typical Scenarios \& Best Practices）](#3-典型场景与最佳实践typical-scenarios--best-practices)
  - [4. 常见问题 FAQ](#4-常见问题-faq)
  - [5. 参考与扩展阅读](#5-参考与扩展阅读)


## 1. 工程原理与定义（Principle & Definition）

FFI（外部函数接口）允许不同编程语言间互操作，常用于Rust与C/C++等系统库集成。Rust 以类型安全、内存安全和高性能适合FFI场景。
FFI (Foreign Function Interface) enables interoperability between different programming languages, commonly used for integrating Rust with C/C++ and other system libraries. Rust's type safety, memory safety, and high performance are ideal for FFI scenarios.

## 2. Rust 1.88 新特性工程化应用

- C字符串字面量：便于与C接口集成。
- &raw指针操作符：更安全的底层指针操作。
- bindgen/cbindgen：自动生成C/Rust接口绑定。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用bindgen集成C库。
- 用cbindgen为Rust库生成C头文件。
- 用unsafe块封装底层操作，保证安全边界。
- 用serde处理跨语言数据序列化。

**最佳实践：**

- 用bindgen/cbindgen自动生成接口。
- 用unsafe块隔离不安全代码。
- 用类型系统减少跨语言错误。
- 用cargo test做接口单元测试。

## 4. 常见问题 FAQ

- Q: Rust如何与C库集成？
  A: 用bindgen自动生成Rust绑定，或用cbindgen生成C头文件。
- Q: 如何保证FFI安全？
  A: 用unsafe块隔离不安全操作，类型系统约束接口。
- Q: 如何做跨语言数据序列化？
  A: 用serde等库处理数据格式转换。

## 5. 参考与扩展阅读

- [bindgen C接口生成](https://rust-lang.github.io/rust-bindgen/)
- [cbindgen 头文件生成](https://github.com/mozilla/cbindgen)
- [serde 配置解析库](https://serde.rs/)
