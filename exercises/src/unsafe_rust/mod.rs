//! # Unsafe Rust 练习 / Unsafe Rust Exercises
//!
//! 本模块包含 11 道练习题，涵盖 Rust 不安全代码的核心概念：
//! This module contains 11 exercises covering core concepts of unsafe Rust:
//!
//! | 编号 / ID | 主题 / Topic | 难度 / Difficulty | 考点 / Focus |
//! |------|------|------|------|
//! | ex01 | 原始指针与安全的数组分割 / Raw pointers and safe array splitting | Medium | `*mut T`、指针偏移、借用检查器交互 / Pointer offset, borrow checker interaction |
//! | ex02 | FFI 边界安全封装 / FFI boundary safe wrapping | Medium | `extern "C"`、C 字符串转换、safe 封装 / C string conversion, safe wrappers |
//! | ex03 | MaybeUninit 与避免不必要的初始化 / MaybeUninit and avoiding unnecessary init | Medium | `MaybeUninit<T>`、假设初始化、Drop 安全 / Assumed init, Drop safety |
//! | ex04 | UnsafeCell 与内部可变性 / UnsafeCell and interior mutability | Medium | `UnsafeCell<T>`、内部可变性、`*const`/`*mut` |
//! | ex05 | Miri 验证与未定义行为识别 / Miri validation and UB identification | Hard | Miri 工具、Tree Borrows、UB 识别与修复 / Miri, Tree Borrows, UB detection |
//! | ex06 | `mem::transmute` 与类型双关 / Transmute and type punning | Medium | `transmute`、`transmute_copy`、union、对齐约束 / Alignment constraints |
//! | ex07 | 内存对齐与未对齐访问 / Memory alignment and unaligned access | Hard | `read_unaligned`、`write_unaligned`、`#[repr(packed)]`、`align_offset` |
//! | ex08 | 原始引用操作符 `&raw const`/`&raw mut` / Raw reference operators | Medium | `&raw const`、避免中间引用 UB、packed/union 安全访问 / Avoiding intermediate reference UB (Rust 1.95) |
//! | ex09 | `unsafe_op_in_unsafe_fn` 规范 / unsafe_op_in_unsafe_fn lint | Medium | Rust 2024 unsafe fn 语义、`unsafe {}` 粒度控制 / Granular unsafe control (Rust 1.95) |
//! | ex10 | `c"..."` C 字符串字面量 / C string literals | Easy | `CStr`、FFI 边界安全、编译期 NUL 保证 / Compile-time NUL guarantee (Rust 1.95) |
//! | ex11 | `const {}` 块与 const 原始指针 / const blocks and raw pointers | Hard | `const {}` 块、`&raw const` in const fn、编译期计算 / Compile-time evaluation (Rust 1.95) |
//!
//! ## 运行测试 / Running Tests
//!
//! ```bash
//! cd exercises
//! cargo test unsafe_rust::
//! ```
//!
//! ## Miri 验证（需要 nightly）/ Miri Validation (requires nightly)
//!
//! ```bash
//! rustup run nightly cargo miri test unsafe_rust::ex05_miri_validation
//! rustup run nightly cargo miri test unsafe_rust::ex07_align_offset
//! ```

pub mod ex01_raw_pointers;
pub mod ex02_ffi_basics;
pub mod ex03_maybe_uninit;
pub mod ex04_unsafe_cell;
pub mod ex05_miri_validation;
pub mod ex06_transmute;
pub mod ex07_align_offset;
pub mod ex08_raw_references;
pub mod ex09_unsafe_op_in_unsafe_fn;
pub mod ex10_c_str_literals;
pub mod ex11_const_unsafe;
