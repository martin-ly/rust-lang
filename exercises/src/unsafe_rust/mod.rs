//! # Unsafe Rust 练习
//!
//! 本模块包含 11 道练习题，涵盖 Rust 不安全代码的核心概念：
//!
//! | 编号 | 主题 | 难度 | 考点 |
//! |------|------|------|------|
//! | ex01 | 原始指针与安全的数组分割 | Medium | `*mut T`、指针偏移、借用检查器交互 |
//! | ex02 | FFI 边界安全封装 | Medium | `extern "C"`、C 字符串转换、safe 封装 |
//! | ex03 | MaybeUninit 与避免不必要的初始化 | Medium | `MaybeUninit<T>`、假设初始化、Drop 安全 |
//! | ex04 | UnsafeCell 与内部可变性 | Medium | `UnsafeCell<T>`、内部可变性、`*const`/`*mut` |
//! | ex05 | Miri 验证与未定义行为识别 | Hard | Miri 工具、Tree Borrows、UB 识别与修复 |
//! | ex06 | `mem::transmute` 与类型双关 | Medium | `transmute`、`transmute_copy`、union、对齐约束 |
//! | ex07 | 内存对齐与未对齐访问 | Hard | `read_unaligned`、`write_unaligned`、`#[repr(packed)]`、`align_offset` |
//! | ex08 | 原始引用操作符 `&raw const`/`&raw mut` | Medium | `&raw const`、避免中间引用 UB、packed/union 安全访问 (Rust 1.95) |
//! | ex09 | `unsafe_op_in_unsafe_fn` 规范 | Medium | Rust 2024 unsafe fn 语义、`unsafe {}` 粒度控制 (Rust 1.95) |
//! | ex10 | `c"..."` C 字符串字面量 | Easy | `CStr`、FFI 边界安全、编译期 NUL 保证 (Rust 1.95) |
//! | ex11 | `const {}` 块与 const 原始指针 | Hard | `const {}` 块、`&raw const` in const fn、编译期计算 (Rust 1.95) |
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
