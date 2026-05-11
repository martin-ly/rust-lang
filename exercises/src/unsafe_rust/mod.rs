//! # Unsafe Rust 练习
//!
//! 本模块包含 5 道练习题，涵盖 Rust 不安全代码的核心概念：
//!
//! | 编号 | 主题 | 难度 | 考点 |
//! |------|------|------|------|
//! | ex01 | 原始指针与安全的数组分割 | Medium | `*mut T`、指针偏移、借用检查器交互 |
//! | ex02 | FFI 边界安全封装 | Medium | `extern "C"`、C 字符串转换、safe 封装 |
//! | ex03 | MaybeUninit 与避免不必要的初始化 | Medium | `MaybeUninit<T>`、假设初始化、Drop 安全 |
//! | ex04 | UnsafeCell 与内部可变性 | Medium | `UnsafeCell<T>`、内部可变性、`*const`/`*mut` |
//! | ex05 | Miri 验证与未定义行为识别 | Hard | Miri 工具、Tree Borrows、UB 识别与修复 |
//!
//! ## 运行测试
//!
//! ```bash
//! cd exercises
//! cargo test unsafe_rust::
//! ```
//!
//! ## Miri 验证（需要 nightly）
//!
//! ```bash
//! rustup run nightly cargo miri test unsafe_rust::ex05_miri_validation
//! ```

pub mod ex01_raw_pointers;
pub mod ex02_ffi_basics;
pub mod ex03_maybe_uninit;
pub mod ex04_unsafe_cell;
pub mod ex05_miri_validation;
