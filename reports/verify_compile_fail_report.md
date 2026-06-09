# Compile Fail 代码块验证报告

> 生成时间: 2026-05-24 16:58

## 摘要

| 状态 | 数量 |
| :--- | :--- |
| expected_fail | 333 |
| unexpected_pass | 284 |
| skipped | 100 |
| syntax_error | 76 |

## 问题代码块

| 文件 | 行号 | 状态 | 预览 | 错误信息 |
| :--- | :--- | :--- | :--- | :--- |
| concept\01_foundation\02_borrowing.md | 1552 | unexpected_pass | `fn main() {     let mut s = String::from` | warning: unused variable: `r1`  --> target\tmp\verify_compile_fail\02_borrowing_ |
| concept\01_foundation\02_borrowing.md | 1625 | unexpected_pass | `fn main() {     let mut data = vec![1, 2` | warning: unused variable: `r1`  --> target\tmp\verify_compile_fail\02_borrowing_ |
| concept\01_foundation\03_lifetimes.md | 801 | unexpected_pass | `// ❌ 编译错误: missing lifetime specifier fn` | warning: function `first_word` is never used  --> target\tmp\verify_compile_fail |
| concept\01_foundation\03_lifetimes.md | 857 | unexpected_pass | `struct Parser {     text: String, }  imp` | warning: struct `Parser` is never constructed  --> target\tmp\verify_compile_fai |
| concept\01_foundation\03_lifetimes_advanced.md | 1725 | unexpected_pass | `trait Callback {     fn call(&self, x: &` | warning: trait `Callback` is never used  --> target\tmp\verify_compile_fail\03_l |
| concept\01_foundation\06_zero_cost_abstractions.md | 568 | syntax_error | `trait Drawable {     fn draw(&self); }` | error: expected expression, found `;`  --> target\tmp\verify_compile_fail\06_zer |
| concept\01_foundation\03_lifetimes_advanced.md | 1827 | unexpected_pass | `fn main() {     let mut x = 5;     let y` | warning: unused variable: `z`  --> target\tmp\verify_compile_fail\03_lifetimes_a |
| concept\01_foundation\05_reference_semantics.md | 1633 | unexpected_pass | `fn main() {     let mut x = 5;     let r` |  |
| concept\01_foundation\05_reference_semantics.md | 1648 | unexpected_pass | `use std::cell::RefCell;  fn main() {` |  |
| concept\01_foundation\06_zero_cost_abstractions.md | 588 | unexpected_pass | `fn process<T: std::fmt::Display>(x: T) {` |  |
| concept\01_foundation\07_control_flow.md | 790 | unexpected_pass | `fn maybe_return() -> i32 {     let x = l` | warning: function `maybe_return` is never used  --> target\tmp\verify_compile_fa |
| concept\01_foundation\08_collections.md | 654 | unexpected_pass | `fn main() {     let mut v = vec![1, 2, 3` | warning: unused variable: `drained`  --> target\tmp\verify_compile_fail\08_colle |
| concept\01_foundation\08_collections.md | 667 | unexpected_pass | `use std::collections::HashMap; use std::` | warning: unused import: `std::hash::BuildHasherDefault`  --> target\tmp\verify_c |
| concept\01_foundation\10_error_handling_basics.md | 890 | unexpected_pass | `fn main() {     let res: Result<i32, &st` |  |
| concept\01_foundation\11_modules_and_paths.md | 769 | syntax_error | `// a.rs pub use crate::b::B;  // b.rs pu` | error[E0432]: unresolved import `crate::b`  --> target\tmp\verify_compile_fail\1 |
| concept\01_foundation\10_numerics.md | 784 | unexpected_pass | `fn main() {     let x: f64 = f64::NAN;` | warning: incorrect NaN comparison, NaN cannot be directly compared to itself  -- |
| concept\01_foundation\10_numerics.md | 743 | unexpected_pass | `fn main() {     let x: f64 = 0.1 + 0.2;` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\10_numerics_L7 |
| concept\01_foundation\10_numerics.md | 766 | unexpected_pass | `fn main() {     let x: i32 = -1;     let` |  |
| concept\01_foundation\11_modules_and_paths.md | 719 | unexpected_pass | `// a.rs // use crate::b::B; // a 依赖 b  /` |  |
| concept\01_foundation\12_attributes_and_macros.md | 787 | syntax_error | `macro_rules! infinite {     () => { infi` | error: recursion limit reached while expanding `infinite!`  --> target\tmp\verif |
| concept\01_foundation\11_numeric_types.md | 603 | unexpected_pass | `use std::num::Wrapping;  fn main() {` |  |
| concept\01_foundation\11_numeric_types.md | 623 | unexpected_pass | `use std::num::NonZeroU32;  fn main() {` |  |
| concept\01_foundation\13_panic_and_abort.md | 799 | syntax_error | `extern "C" {     fn c_function(); }  fn` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\13_panic |
| concept\01_foundation\12_attributes_and_macros.md | 812 | unexpected_pass | `// 假设自定义 derive 宏 #[derive(MyDebug)] //` |  |
| concept\01_foundation\12_attributes_and_macros.md | 835 | unexpected_pass | `#[cfg(target_os = "linux")] fn platform_` |  |
| concept\01_foundation\13_panic_and_abort.md | 738 | unexpected_pass | `use std::panic::catch_unwind;  // Cargo.` |  |
| concept\01_foundation\14_coercion_and_casting.md | 755 | unexpected_pass | `trait A {} trait B: A {}  fn upcast(b: &` | warning: unused variable: `b`  --> target\tmp\verify_compile_fail\14_coercion_an |
| concept\01_foundation\15_closure_basics.md | 747 | unexpected_pass | `fn main() {     let x = 5; // i32 实现 Cop` | warning: unused variable: `closure`  --> target\tmp\verify_compile_fail\15_closu |
| concept\01_foundation\16_testing_basics.md | 744 | unexpected_pass | `#[test] #[should_panic(expected = "divid` |  |
| concept\01_foundation\18_strings_and_encoding.md | 736 | unexpected_pass | `use std::ffi::OsStr;  fn main() {     le` | warning: unused variable: `os_string`   --> target\tmp\verify_compile_fail\18_st |
| concept\01_foundation\17_collections_advanced.md | 974 | unexpected_pass | `use std::collections::HashSet;  #[derive` |  |
| concept\01_foundation\19_numerics.md | 706 | syntax_error | `fn main() {     let x: u32 = 1;     // ❌` | error: this arithmetic operation will overflow  --> target\tmp\verify_compile_fa |
| concept\01_foundation\18_strings_and_encoding.md | 778 | unexpected_pass | `fn main() {     let s = "你好";     // ❌ 运` |  |
| concept\01_foundation\18_strings_and_encoding.md | 791 | unexpected_pass | `fn main() {     let bytes = vec![0x80, 0` |  |
| concept\01_foundation\19_numerics.md | 639 | unexpected_pass | `use std::num::NonZeroU32;  fn main() {` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\19_numerics_L6 |
| concept\01_foundation\19_numerics.md | 688 | unexpected_pass | `fn main() {     let a: f32 = 0.1;     le` |  |
| concept\01_foundation\20_variable_model.md | 423 | unexpected_pass | `fn main() {     let x = 5;     let r = &` |  |
| concept\01_foundation\21_effects_and_purity.md | 372 | unexpected_pass | `const fn impure_const() -> i32 {     let` | warning: function `impure_const` is never used  --> target\tmp\verify_compile_fa |
| concept\01_foundation\20_variable_model.md | 393 | unexpected_pass | `struct Resource {     data: String, }  i` | warning: struct `Resource` is never constructed  --> target\tmp\verify_compile_f |
| concept\01_foundation\21_effects_and_purity.md | 333 | unexpected_pass | `// Rust 编译器阻止隐式副作用 fn implicit_side_effe` | warning: function `implicit_side_effect` is never used  --> target\tmp\verify_co |
| concept\01_foundation\22_data_abstraction_spectrum.md | 515 | unexpected_pass | `struct ZeroSized;  fn main() {     // ❌` | warning: unused return value of `Box::<T>::from_raw` that must be used  --> targ |
| concept\01_foundation\22_data_abstraction_spectrum.md | 531 | unexpected_pass | `use std::mem::ManuallyDrop;  fn main() {` | warning: variable does not need to be mutable  --> target\tmp\verify_compile_fai |
| concept\02_intermediate\02_generics.md | 3157 | unexpected_pass | `struct Array<T, const N: usize> {     da` | warning: unused variable: `arr`  --> target\tmp\verify_compile_fail\02_generics_ |
| concept\02_intermediate\02_generics.md | 3138 | unexpected_pass | `trait Process<T = String> {     fn proce` | warning: trait `Process` is never used  --> target\tmp\verify_compile_fail\02_ge |
| concept\02_intermediate\02_generics.md | 3191 | unexpected_pass | `trait Displayable {     fn display(&self` |  |
| concept\02_intermediate\03_memory_management.md | 2338 | unexpected_pass | `fn main() {     let v = vec![1, 2, 3];` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\03_memory_mana |
| concept\02_intermediate\03_memory_management.md | 2445 | unexpected_pass | `use std::rc::{Rc, Weak}; use std::cell::` | warning: unused import: `Weak`  --> target\tmp\verify_compile_fail\03_memory_man |
| concept\02_intermediate\03_memory_management.md | 2432 | unexpected_pass | `fn main() {     let s = Box::leak(Box::n` |  |
| concept\02_intermediate\04_error_handling.md | 2961 | unexpected_pass | `const fn divide(a: i32, b: i32) -> i32 {` | warning: function `divide` is never used  --> target\tmp\verify_compile_fail\04_ |
| concept\02_intermediate\05_assert_matches.md | 570 | syntax_error | `fn main() {     let x = 42;     // ❌ 编译错` | error[E0432]: unresolved import `std::assert_matches`  --> target\tmp\verify_com |
| concept\02_intermediate\04_error_handling.md | 2979 | unexpected_pass | `fn fallible_op() -> Result<i32, String>` | warning: unused `Result` that must be used  --> target\tmp\verify_compile_fail\0 |
| concept\02_intermediate\05_assert_matches.md | 630 | syntax_error | `fn main() {     let x = 5;     // ❌ 编译错误` | error: format argument must be a string literal  --> target\tmp\verify_compile_f |
| concept\02_intermediate\06_range_types.md | 463 | syntax_error | `fn main() {     let x = 5;     // ❌ 编译错误` | error: expected `{`, found `=`  --> target\tmp\verify_compile_fail\06_range_type |
| concept\02_intermediate\04_error_handling.md | 3060 | unexpected_pass | `const fn checked_div(a: i32, b: i32) ->` | warning: function `checked_div` is never used  --> target\tmp\verify_compile_fai |
| concept\02_intermediate\05_assert_matches.md | 616 | unexpected_pass | `#[test] fn test_nested_match() {     let` |  |
| concept\02_intermediate\06_range_types.md | 530 | unexpected_pass | `fn main() {     let range = 0..;     //` |  |
| concept\02_intermediate\07_closure_types.md | 607 | unexpected_pass | `fn main() {     let f = match true {` |  |
| concept\02_intermediate\10_module_system.md | 601 | syntax_error | `// src/foo.rs 和 src/foo/ 同时存在时 // ❌ 编译错误` | error: cannot declare a file module inside a block unless it has a path attribut |
| concept\02_intermediate\10_module_system.md | 651 | syntax_error | `// lib.rs pub mod a {     pub use crate:` | error[E0432]: unresolved import `crate::b`  --> target\tmp\verify_compile_fail\1 |
| concept\02_intermediate\08_interior_mutability.md | 498 | unexpected_pass | `use std::sync::OnceLock;  fn main() {` | warning: function `correct_usage` is never used   --> target\tmp\verify_compile_ |
| concept\02_intermediate\10_module_system.md | 625 | unexpected_pass | `mod inner {     pub fn func() {} }  mod` |  |
| concept\02_intermediate\11_cow_and_borrowed.md | 639 | unexpected_pass | `use std::borrow::Borrow;  fn main() {` | warning: unused variable: `r`  --> target\tmp\verify_compile_fail\11_cow_and_bor |
| concept\02_intermediate\11_cow_and_borrowed.md | 664 | unexpected_pass | `use std::borrow::Cow;  struct MyStr<'a>` | warning: unused variable: `s`  --> target\tmp\verify_compile_fail\11_cow_and_bor |
| concept\02_intermediate\11_cow_and_borrowed.md | 686 | unexpected_pass | `use std::borrow::Cow;  fn main() {     l` |  |
| concept\02_intermediate\12_smart_pointers.md | 507 | unexpected_pass | `use std::pin::Pin;  fn pin_mut_after_pin` | warning: unused variable: `pinned`  --> target\tmp\verify_compile_fail\12_smart_ |
| concept\02_intermediate\12_smart_pointers.md | 486 | unexpected_pass | `use std::pin::Pin;  struct SelfReferenti` | warning: unused variable: `pinned`   --> target\tmp\verify_compile_fail\12_smart |
| concept\02_intermediate\13_dsl_and_embedding.md | 766 | unexpected_pass | `// 假设一个 SQL DSL: sql!(SELECT * FROM user` |  |
| concept\02_intermediate\13_dsl_and_embedding.md | 746 | unexpected_pass | `macro_rules! recursive {     () => { 0 }` |  |
| concept\02_intermediate\14_newtype_and_wrapper.md | 524 | unexpected_pass | `struct Meters(u32);  fn add_distance(a:` |  |
| concept\02_intermediate\14_newtype_and_wrapper.md | 582 | unexpected_pass | `struct Meters(u32); struct Seconds(u32);` | warning: unused variable: `total`  --> target\tmp\verify_compile_fail\14_newtype |
| concept\02_intermediate\14_newtype_and_wrapper.md | 599 | unexpected_pass | `use std::ops::Deref;  struct Wrapper(Str` | warning: unused variable: `s`   --> target\tmp\verify_compile_fail\14_newtype_an |
| concept\02_intermediate\14_newtype_and_wrapper.md | 627 | unexpected_pass | `use std::ops::Deref;  struct Username(St` |  |
| concept\02_intermediate\15_error_handling_deep_dive.md | 598 | unexpected_pass | `fn outer() -> Result<Result<i32, String>` | warning: function `outer` is never used  --> target\tmp\verify_compile_fail\15_e |
| concept\02_intermediate\15_iterator_patterns.md | 595 | unexpected_pass | `fn main() {     let mut iter = vec![1, 2` |  |
| concept\02_intermediate\16_iterator_patterns.md | 637 | unexpected_pass | `fn main() {     let data = vec![String::` | warning: unused variable: `evens`  --> target\tmp\verify_compile_fail\16_iterato |
| concept\02_intermediate\15_iterator_patterns.md | 577 | unexpected_pass | `fn main() {     let data = vec![1, 2, 3]` | warning: unused variable: `doubled`  --> target\tmp\verify_compile_fail\15_itera |
| concept\02_intermediate\16_iterator_patterns.md | 588 | unexpected_pass | `fn main() {     let data = vec![vec![1,` | warning: unused variable: `flat`  --> target\tmp\verify_compile_fail\16_iterator |
| concept\02_intermediate\15_iterator_patterns.md | 558 | unexpected_pass | `fn main() {     let keys = vec!["a", "b"` |  |
| concept\02_intermediate\16_iterator_patterns.md | 672 | unexpected_pass | `fn main() {     let v = vec![1, 2, 3, 4,` |  |
| concept\02_intermediate\17_macro_patterns.md | 603 | unexpected_pass | `macro_rules! ambiguous {     ($e:expr) =` | warning: unused macro definition: `ordered`   --> target\tmp\verify_compile_fail |
| concept\02_intermediate\17_macro_patterns.md | 657 | syntax_error | `macro_rules! count_tts {     () => { 0 }` | error: unexpected end of macro invocation  --> target\tmp\verify_compile_fail\17 |
| concept\02_intermediate\17_macro_patterns.md | 675 | unexpected_pass | `macro_rules! unsafe_op {     ($op:expr)` |  |
| concept\02_intermediate\18_lifetimes_advanced.md | 610 | unexpected_pass | `fn call_with_ref<F>(f: F) where     F: F` | warning: function `call_with_ref_fixed` is never used   --> target\tmp\verify_co |
| concept\02_intermediate\19_advanced_traits.md | 572 | unexpected_pass | `#![feature(specialization)] // 不稳定特性  tr` | warning: the feature `specialization` is incomplete and may not be safe to use a |
| concept\02_intermediate\21_metaprogramming.md | 642 | syntax_error | `use proc_macro::TokenStream;  #[proc_mac` | error: the `#[proc_macro_derive]` attribute is only usable with crates of the `p |
| concept\02_intermediate\19_advanced_traits.md | 614 | unexpected_pass | `trait MyTrait: Clone + Send + Sync + 'st` | warning: trait `MyTrait` is never used  --> target\tmp\verify_compile_fail\19_ad |
| concept\02_intermediate\20_type_system_advanced.md | 607 | unexpected_pass | `// 错误: impl Trait 在 trait 定义中使用 trait My` | warning: trait `MyTrait` is never used  --> target\tmp\verify_compile_fail\20_ty |
| concept\02_intermediate\21_metaprogramming.md | 691 | syntax_error | `#![allow(incomplete_features)] #![featur` | error: unconstrained generic constant  --> target\tmp\verify_compile_fail\21_met |
| concept\02_intermediate\20_type_system_advanced.md | 651 | unexpected_pass | `fn apply<F>(f: F) where     F: Fn(&i32)` | warning: function `apply` is never used  --> target\tmp\verify_compile_fail\20_t |
| concept\02_intermediate\21_metaprogramming.md | 707 | unexpected_pass | `use std::any::{Any, TypeId};  fn main()` | warning: unused import: `Any`  --> target\tmp\verify_compile_fail\21_metaprogram |
| concept\02_intermediate\22_iterator_patterns.md | 484 | unexpected_pass | `fn main() {     let v = vec![1, 2, 3];` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\22_ |
| concept\02_intermediate\22_iterator_patterns.md | 527 | unexpected_pass | `fn main() {     let data = vec![1, 2, 3]` | warning: unused variable: `scanned`  --> target\tmp\verify_compile_fail\22_itera |
| concept\02_intermediate\22_iterator_patterns.md | 548 | unexpected_pass | `fn main() {     let mut iter = vec![1, 2` |  |
| concept\03_advanced\02_async.md | 3785 | unexpected_pass | `use std::rc::Rc;  async fn bad_async() {` | warning: function `bad_async` is never used  --> target\tmp\verify_compile_fail\ |
| concept\03_advanced\02_async.md | 3851 | unexpected_pass | `async fn borrow_lifetime_issue() {     l` | warning: function `borrow_lifetime_issue` is never used  --> target\tmp\verify_c |
| concept\03_advanced\03_unsafe.md | 3352 | syntax_error | `fn main() {     let x = 5;     let r = &` | error: assigning to `&T` is undefined behavior, consider using an `UnsafeCell`   |
| concept\03_advanced\02_async_advanced.md | 1265 | unexpected_pass | `use std::pin::Pin;  struct SelfRef {` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile_fail\02_a |
| concept\03_advanced\02_async_patterns.md | 389 | unexpected_pass | `trait AsyncService {     async fn proces` | warning: trait `AsyncService` is never used  --> target\tmp\verify_compile_fail\ |
| concept\03_advanced\03_unsafe.md | 3384 | syntax_error | `fn main() {     let x = 5;     let r = &` | error: assigning to `&T` is undefined behavior, consider using an `UnsafeCell`   |
| concept\03_advanced\02_async_patterns.md | 431 | unexpected_pass | `use std::future::Future; use std::pin::P` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile_fail\02_a |
| concept\03_advanced\03_unsafe.md | 3337 | unexpected_pass | `fn main() {     let ptr: *const i32 = st` |  |
| concept\03_advanced\04_macros.md | 1536 | syntax_error | `// ❌ 反例: env! 读取不存在的环境变量 const MISSING:` | error: environment variable `NON_EXISTENT_VAR_12345` not defined at compile time |
| concept\03_advanced\05_rust_ffi.md | 494 | syntax_error | `extern "C" {     fn c_returns_pointer()` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\05_rust_ |
| concept\03_advanced\05_rust_ffi.md | 428 | unexpected_pass | `#[repr(C)] struct RustStruct {     data:` | warning: unused variable: `s`   --> target\tmp\verify_compile_fail\05_rust_ffi_L |
| concept\03_advanced\05_rust_ffi.md | 443 | unexpected_pass | `use std::panic::catch_unwind;  // 错误: pa` | warning: unused variable: `result`   --> target\tmp\verify_compile_fail\05_rust_ |
| concept\03_advanced\07_proc_macro.md | 498 | syntax_error | `use proc_macro::TokenStream;  // 错误: 过程宏` | error: the `#[proc_macro_derive]` attribute is only usable with crates of the `p |
| concept\03_advanced\06_pin_unpin.md | 449 | unexpected_pass | `use std::pin::Pin;  fn pin_project_misus` | warning: unused variable: `r`  --> target\tmp\verify_compile_fail\06_pin_unpin_L |
| concept\03_advanced\07_proc_macro.md | 511 | syntax_error | `// 错误: 在 proc-macro crate 中使用非 proc_macr` | error: the `#[proc_macro]` attribute is only usable with crates of the `proc-mac |
| concept\03_advanced\07_proc_macro.md | 691 | syntax_error | `use proc_macro::TokenStream; use quote::` | error: the `#[proc_macro_derive]` attribute is only usable with crates of the `p |
| concept\03_advanced\09_ffi_advanced.md | 816 | syntax_error | `use std::os::raw::c_void;  extern "C" {` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\09_ffi_a |
| concept\03_advanced\08_nll_and_polonius.md | 465 | unexpected_pass | `fn nll_scope_limitation() {     let mut` | warning: function `nll_scope_limitation` is never used  --> target\tmp\verify_co |
| concept\03_advanced\08_nll_and_polonius.md | 478 | unexpected_pass | `fn polonius_dataflow() {     let mut x =` | warning: function `polonius_dataflow` is never used  --> target\tmp\verify_compi |
| concept\03_advanced\09_ffi_advanced.md | 844 | syntax_error | `use std::os::raw::{c_double, c_longdoubl` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\09_ffi_a |
| concept\03_advanced\08_nll_and_polonius.md | 702 | unexpected_pass | `fn main() {     let mut x = 0;     let r` |  |
| concept\03_advanced\08_nll_and_polonius.md | 492 | unexpected_pass | `fn drop_order_nll() {     let mut data =` | warning: function `drop_order_nll` is never used  --> target\tmp\verify_compile_ |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 578 | syntax_error | `use std::sync::atomic::{AtomicUsize, Ord` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\11_atomics_and |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 879 | unexpected_pass | `use std::sync::atomic::{AtomicPtr, Order` |  |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 594 | unexpected_pass | `use std::sync::atomic::{AtomicPtr, Order` | warning: unused variable: `val`  --> target\tmp\verify_compile_fail\11_atomics_a |
| concept\03_advanced\12_unsafe_rust_patterns.md | 835 | unexpected_pass | `fn main() {     let x = String::from("he` | warning: unused variable: `s1`  --> target\tmp\verify_compile_fail\12_unsafe_rus |
| concept\03_advanced\12_unsafe_rust_patterns.md | 784 | unexpected_pass | `use std::pin::Pin;  struct SelfRef {` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile_fail\12_u |
| concept\03_advanced\14_custom_allocators.md | 704 | unexpected_pass | `use std::alloc::System;  #[global_alloca` |  |
| concept\03_advanced\15_zero_copy_parsing.md | 705 | syntax_error | `// 假设使用 nom 7  use nom::IResult;  fn par` | error[E0432]: unresolved import `nom`  --> target\tmp\verify_compile_fail\15_zer |
| concept\03_advanced\14_custom_allocators.md | 742 | unexpected_pass | `use std::alloc::{alloc, dealloc, Layout}` |  |
| concept\03_advanced\15_zero_copy_parsing.md | 724 | unexpected_pass | `fn main() {     let bytes = [0x12u8, 0x3` |  |
| concept\03_advanced\15_zero_copy_parsing.md | 571 | unexpected_pass | `fn get_header(data: &[u8]) -> &[u8] {` | warning: function `get_header` is never used  --> target\tmp\verify_compile_fail |
| concept\03_advanced\15_zero_copy_parsing.md | 738 | unexpected_pass | `fn parse<'a>(input: &'a [u8]) -> &'a str` | warning: unused variable: `s`  --> target\tmp\verify_compile_fail\15_zero_copy_p |
| concept\03_advanced\16_lock_free.md | 522 | unexpected_pass | `use std::sync::atomic::{AtomicPtr, Order` | warning: function `atomic_ptr_send` is never used  --> target\tmp\verify_compile |
| concept\03_advanced\16_lock_free.md | 537 | unexpected_pass | `use std::sync::atomic::{AtomicUsize, Ord` | warning: function `compare_exchange_weak_loop` is never used  --> target\tmp\ver |
| concept\03_advanced\16_lock_free.md | 795 | unexpected_pass | `use std::sync::atomic::{AtomicPtr, Order` | warning: struct `Node` is never constructed  --> target\tmp\verify_compile_fail\ |
| concept\03_advanced\17_type_erasure.md | 779 | unexpected_pass | `use std::any::Any;  fn main() {     let` | warning: unused variable: `any`  --> target\tmp\verify_compile_fail\17_type_eras |
| concept\03_advanced\17_type_erasure.md | 794 | unexpected_pass | `trait Processor {     fn process<T: Defa` | warning: trait `Processor` is never used  --> target\tmp\verify_compile_fail\17_ |
| concept\03_advanced\20_stream_processing_semantics.md | 462 | unexpected_pass | `use std::collections::HashMap; use std::` | warning: struct `StatefulOperator` is never constructed  --> target\tmp\verify_c |
| concept\04_formal\02_type_theory.md | 1305 | syntax_error | `trait Iterable {     type Item<'a>;` | error: missing required bound on `Item`  --> target\tmp\verify_compile_fail\02_t |
| concept\04_formal\01_linear_logic.md | 1262 | unexpected_pass | `fn branch(use_a: bool) {     let x = Str` | warning: function `branch` is never used  --> target\tmp\verify_compile_fail\01_ |
| concept\04_formal\01_linear_logic.md | 1282 | unexpected_pass | `fn diverges() -> ! {     panic!("never r` | warning: unreachable statement   --> target\tmp\verify_compile_fail\01_linear_lo |
| concept\04_formal\03_ownership_formal.md | 1818 | syntax_error | `fn assign_long_to_short<'a, 'b>(x: &'a s` | warning: unused variable: `y`  --> target\tmp\verify_compile_fail\03_ownership_f |
| concept\04_formal\02_type_theory.md | 1335 | unexpected_pass | `fn array_len<T, const N: usize>(arr: &[T` | warning: unused variable: `arr`  --> target\tmp\verify_compile_fail\02_type_theo |
| concept\04_formal\03_ownership_formal.md | 1761 | unexpected_pass | `struct LinearResource;  impl Drop for Li` | warning: unused variable: `r`  --> target\tmp\verify_compile_fail\03_ownership_f |
| concept\04_formal\03_ownership_formal.md | 1787 | unexpected_pass | `use std::cell::RefCell;  fn main() {` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\03_ |
| concept\04_formal\04_rustbelt.md | 1195 | unexpected_pass | `fn main() {     let mut v = vec![1, 2, 3` | warning: unused variable: `r1`  --> target\tmp\verify_compile_fail\04_rustbelt_L |
| concept\04_formal\04_rustbelt.md | 1227 | unexpected_pass | `struct Resource; impl Drop for Resource` |  |
| concept\04_formal\04_rustbelt.md | 1286 | unexpected_pass | `use std::mem;  struct Guard; impl Drop f` |  |
| concept\04_formal\06_subtype_variance.md | 579 | unexpected_pass | `fn takes_str(_: &str) {}  fn main() {` | warning: unused variable: `f`  --> target\tmp\verify_compile_fail\06_subtype_var |
| concept\04_formal\06_subtype_variance.md | 598 | unexpected_pass | `use std::cell::UnsafeCell;  fn main() {` |  |
| concept\04_formal\07_separation_logic.md | 706 | unexpected_pass | `use std::sync::atomic::{AtomicUsize, Ord` |  |
| concept\04_formal\08_type_inference.md | 198 | unexpected_pass | `fn main() {     let closure = \|x\| x + 1;` | warning: function `fixed` is never used  --> target\tmp\verify_compile_fail\08_t |
| concept\04_formal\08_type_inference.md | 644 | unexpected_pass | `trait Container {     type Item;     fn` | warning: trait `Container` is never used  --> target\tmp\verify_compile_fail\08_ |
| concept\04_formal\09_linear_logic_applications.md | 754 | unexpected_pass | `struct Resource {     name: String, }  i` |  |
| concept\04_formal\05_verification_toolchain.md | 982 | unexpected_pass | `use std::rc::Rc;  struct MyData(Rc<i32>)` | warning: struct `MyData` is never constructed  --> target\tmp\verify_compile_fai |
| concept\04_formal\10_category_theory.md | 274 | unexpected_pass | `fn main() {     let v = vec![String::fro` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\10_ |
| concept\04_formal\10_category_theory.md | 712 | unexpected_pass | `fn map_both<A, B, F>(a: Option<A>, b: Op` | warning: function `map_both` is never used  --> target\tmp\verify_compile_fail\1 |
| concept\04_formal\10_category_theory.md | 733 | unexpected_pass | `fn monadic_bind() -> Result<i32, String>` | warning: function `monadic_bind` is never used  --> target\tmp\verify_compile_fa |
| concept\04_formal\11_separation_logic.md | 731 | syntax_error | `// RustBelt 形式化中的概念，非实际 Rust 代码  // own(` | error: expected one of `:` or `\|`, found `,`  --> target\tmp\verify_compile_fail |
| concept\04_formal\11_separation_logic.md | 711 | syntax_error | `use ghost_cell::GhostCell;  fn main() {` | error[E0432]: unresolved import `ghost_cell`  --> target\tmp\verify_compile_fail |
| concept\04_formal\11_separation_logic.md | 690 | unexpected_pass | `fn swap(a: &mut i32, b: &mut i32) {` | warning: unused variable: `r`  --> target\tmp\verify_compile_fail\11_separation_ |
| concept\04_formal\12_denotational_semantics.md | 159 | unexpected_pass | `fn main() {     // ❌ 编译错误:`loop {}`的类型` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\12_denotationa |
| concept\04_formal\12_denotational_semantics.md | 181 | unexpected_pass | `fn may_fail() -> Result<i32, String> {` | warning: function `may_fail` is never used  --> target\tmp\verify_compile_fail\1 |
| concept\04_formal\12_denotational_semantics.md | 554 | unexpected_pass | `fn diverges() -> ! {     loop {} }  fn m` | warning: unreachable statement   --> target\tmp\verify_compile_fail\12_denotatio |
| concept\04_formal\13_formal_methods.md | 699 | syntax_error | `use contracts::*;  #[requires(x > 0)] #[` | error[E0432]: unresolved import `contracts`  --> target\tmp\verify_compile_fail\ |
| concept\04_formal\12_denotational_semantics.md | 572 | unexpected_pass | `fn main() {     let mut x = 42;     let` |  |
| concept\04_formal\14_lambda_calculus.md | 660 | unexpected_pass | `fn make_adder(x: i32) -> impl Fn(i32) ->` |  |
| concept\04_formal\15_hoare_logic.md | 693 | unexpected_pass | `fn divide(a: i32, b: i32) -> i32 {     /` | warning: function `divide` is never used  --> target\tmp\verify_compile_fail\15_ |
| concept\04_formal\16_aerospace_certification_formal_methods.md | 1191 | syntax_error | `#![no_panic]  fn safe_divide(a: i32, b:` | error: cannot find attribute `no_panic` in this scope  --> target\tmp\verify_com |
| concept\04_formal\15_hoare_logic.md | 749 | unexpected_pass | `// 假设 weakest precondition 计算 fn abs(x:` | warning: function `abs` is never used  --> target\tmp\verify_compile_fail\15_hoa |
| concept\04_formal\15_hoare_logic.md | 764 | unexpected_pass | `fn gcd(a: u32, b: u32) -> u32 {     let` | warning: function `gcd` is never used  --> target\tmp\verify_compile_fail\15_hoa |
| concept\04_formal\16_aerospace_certification_formal_methods.md | 1208 | unexpected_pass | `fn decision(a: bool, b: bool, c: bool) -` | warning: function `decision` is never used  --> target\tmp\verify_compile_fail\1 |
| concept\04_formal\17_operational_semantics.md | 1079 | unexpected_pass | `fn main() {     let mut x = 0;     let r` |  |
| concept\04_formal\17_operational_semantics.md | 1098 | unexpected_pass | `fn main() {     let mut x = 0;     // ❌` | warning: variable `x` is assigned to, but never used  --> target\tmp\verify_comp |
| concept\04_formal\18_evaluation_strategies.md | 413 | unexpected_pass | `fn main() {     let v = vec![1, 2, 3];` |  |
| concept\04_formal\18_evaluation_strategies.md | 392 | unexpected_pass | `fn main() {     let v = vec![1, 2, 3];` |  |
| concept\04_formal\09_operational_semantics.md | 1125 | unexpected_pass | `const fn slow(n: usize) -> usize {     l` |  |
| concept\05_comparative\02_cpp_abi_object_model.md | 624 | syntax_error | `// C++ 侧 // struct Base { virtual int fo` | error: extern blocks must be unsafe   --> target\tmp\verify_compile_fail\02_cpp_ |
| concept\05_comparative\01_rust_vs_cpp.md | 2688 | unexpected_pass | `trait A { fn method(&self); } trait B: A` | warning: unused variable: `d`   --> target\tmp\verify_compile_fail\01_rust_vs_cp |
| concept\05_comparative\02_rust_vs_go.md | 1042 | unexpected_pass | `fn main() {     // ❌ 编译错误:`Option<&str>` | warning: unused variable: `s`  --> target\tmp\verify_compile_fail\02_rust_vs_go_ |
| concept\05_comparative\02_rust_vs_go.md | 1011 | unexpected_pass | `trait Reader {     fn read(&mut self, bu` |  |
| concept\05_comparative\02_cpp_abi_object_model.md | 653 | unexpected_pass | `struct Outer {     inner1: Inner,     in` | warning: unused variable: `o`   --> target\tmp\verify_compile_fail\02_cpp_abi_ob |
| concept\05_comparative\02_rust_vs_go.md | 1064 | unexpected_pass | `// Go: 隐式实现接口（struct 有方法即实现接口） // type R` | warning: variable does not need to be mutable   --> target\tmp\verify_compile_fa |
| concept\05_comparative\03_paradigm_matrix.md | 1009 | unexpected_pass | `mod inner {     pub struct Config {` | warning: struct `Config` is never constructed   --> target\tmp\verify_compile_fa |
| concept\05_comparative\02_rust_vs_go.md | 1096 | unexpected_pass | `// Go: interface 值可为 nil，但 nil interface` | warning: unused variable: `p`  --> target\tmp\verify_compile_fail\02_rust_vs_go_ |
| concept\05_comparative\03_paradigm_matrix.md | 985 | unexpected_pass | `fn main() {     let mut sum = 0;     let` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\03_ |
| concept\05_comparative\04_safety_boundaries.md | 1158 | syntax_error | `extern "C" {     fn c_api(ptr: *mut u8,` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\04_safet |
| concept\05_comparative\03_paradigm_matrix.md | 1064 | unexpected_pass | `fn functional_style(data: Vec<i32>) -> V` | warning: variable does not need to be mutable   --> target\tmp\verify_compile_fa |
| concept\05_comparative\04_safety_boundaries.md | 1177 | unexpected_pass | `fn bad_unsafe() {     let mut x = 5;` | warning: function `bad_unsafe` is never used  --> target\tmp\verify_compile_fail |
| concept\05_comparative\05_execution_model_isomorphism.md | 900 | unexpected_pass | `// 假设使用 green-thread 库（如 early Rust 的 li` |  |
| concept\05_comparative\05_execution_model_isomorphism.md | 916 | unexpected_pass | `fn cps_style<F>(x: i32, cont: F) -> Resu` | warning: function `cps_style` is never used  --> target\tmp\verify_compile_fail\ |
| concept\05_comparative\05_execution_model_isomorphism.md | 939 | unexpected_pass | `fn cps_factorial(n: u64, k: Box<dyn Fn(u` | warning: function `cps_factorial` is never used  --> target\tmp\verify_compile_f |
| concept\05_comparative\06_rust_vs_java.md | 513 | unexpected_pass | `// Java: List<String> 和 List<Integer> 运行` | warning: unused variable: `nums`   --> target\tmp\verify_compile_fail\06_rust_vs |
| concept\05_comparative\07_rust_vs_python.md | 581 | unexpected_pass | `fn main() {     let x = 42;     // ❌ 编译错` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\07_rust_vs_pyt |
| concept\05_comparative\07_rust_vs_python.md | 607 | unexpected_pass | `fn main() {     let x = 42;     // ❌ 编译错` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\07_rust_vs_pyt |
| concept\05_comparative\06_rust_vs_java.md | 536 | unexpected_pass | `struct FileHandle {     path: String, }` | warning: unused variable: `file2`   --> target\tmp\verify_compile_fail\06_rust_v |
| concept\05_comparative\08_rust_vs_javascript.md | 693 | unexpected_pass | `fn main() {     let x = "5";     // ❌ 编译` |  |
| concept\05_comparative\07_rust_vs_python.md | 660 | unexpected_pass | `use std::sync::{Arc, Mutex}; use std::th` |  |
| concept\05_comparative\08_rust_vs_ruby.md | 718 | unexpected_pass | `trait Greet {     fn greet(&self); }  //` | warning: trait `Greet` is never used  --> target\tmp\verify_compile_fail\08_rust |
| concept\05_comparative\08_rust_vs_ruby.md | 736 | unexpected_pass | `trait Quacks {     fn quack(&self); }  s` | warning: struct `Dog` is never constructed   --> target\tmp\verify_compile_fail\ |
| concept\05_comparative\08_rust_vs_ruby.md | 764 | unexpected_pass | `// Ruby: 可随时为任何类添加方法 // class String //` |  |
| concept\05_comparative\09_rust_vs_swift.md | 732 | syntax_error | `use std::rc::{Rc, RefCell};  struct Node` | error[E0432]: unresolved import `std::rc::RefCell`  --> target\tmp\verify_compil |
| concept\05_comparative\09_rust_vs_swift.md | 752 | unexpected_pass | `fn main() {     let opt: Option<Option<i` |  |
| concept\05_comparative\10_rust_vs_zig.md | 787 | unexpected_pass | `const fn factorial(n: u32) -> u32 {` |  |
| concept\05_comparative\10_rust_vs_zig.md | 766 | unexpected_pass | `fn main() {     let s = String::from("he` | warning: unused variable: `ptr`  --> target\tmp\verify_compile_fail\10_rust_vs_z |
| concept\05_comparative\10_rust_vs_zig.md | 810 | unexpected_pass | `fn main() {     // Rust: Vec 使用全局分配器，隐式` |  |
| concept\05_comparative\11_rust_vs_kotlin.md | 845 | unexpected_pass | `fn main() {     let s: Option<String> =` | warning: unused variable: `len`  --> target\tmp\verify_compile_fail\11_rust_vs_k |
| concept\05_comparative\11_rust_vs_kotlin.md | 784 | unexpected_pass | `struct User {     name: String,     age:` | warning: unused variable: `u1`  --> target\tmp\verify_compile_fail\11_rust_vs_ko |
| concept\05_comparative\12_rust_vs_scala.md | 728 | unexpected_pass | `trait ToJson {     fn to_json(&self) ->` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\12_rust_vs_sca |
| concept\05_comparative\12_rust_vs_scala.md | 778 | unexpected_pass | `struct Meters(u32); struct Kilometers(u3` |  |
| concept\05_comparative\12_rust_vs_scala.md | 757 | unexpected_pass | `fn main() {     // ❌ 编译错误: Rust 没有 null` | warning: unused variable: `s`  --> target\tmp\verify_compile_fail\12_rust_vs_sca |
| concept\05_comparative\13_rust_vs_csharp.md | 852 | unexpected_pass | `// C#: [Serializable] 是运行时反射标记 // [Seria` | warning: field `x` is never read  --> target\tmp\verify_compile_fail\13_rust_vs_ |
| concept\05_comparative\13_rust_vs_csharp.md | 813 | unexpected_pass | `fn main() {     let data = vec![1, 2, 3]` | warning: unused variable: `result`  --> target\tmp\verify_compile_fail\13_rust_v |
| concept\05_comparative\14_rust_vs_elixir.md | 839 | unexpected_pass | `fn main() {     let x = 42;     // ❌ 编译错` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\14_rust_vs_eli |
| concept\05_comparative\14_rust_vs_elixir.md | 813 | unexpected_pass | `fn main() {     let x = 42;     // ❌ 编译错` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\14_rust_vs_eli |
| concept\05_comparative\14_rust_vs_elixir.md | 891 | unexpected_pass | `use std::sync::Arc; use std::thread;  fn` | warning: unused import: `std::thread`  --> target\tmp\verify_compile_fail\14_rus |
| concept\05_comparative\15_rust_vs_typescript.md | 760 | unexpected_pass | `fn main() {     // ❌ 编译错误: Rust 没有 any 类` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail\15_rust_vs_typ |
| concept\05_comparative\14_rust_vs_elixir.md | 862 | unexpected_pass | `use std::sync::mpsc;  fn main() {     le` | warning: unused variable: `tx`  --> target\tmp\verify_compile_fail\14_rust_vs_el |
| concept\05_comparative\15_rust_vs_typescript.md | 809 | unexpected_pass | `struct Point {     x: i32,     y: i32, }` | warning: unused variable: `p`   --> target\tmp\verify_compile_fail\15_rust_vs_ty |
| concept\05_comparative\15_rust_vs_typescript.md | 841 | unexpected_pass | `fn main() {     // TypeScript: any 绕过所有类` |  |
| concept\05_comparative\16_rust_vs_ruby.md | 746 | unexpected_pass | `// Ruby: 运行时元编程 // class Foo //   define` |  |
| concept\05_comparative\16_rust_vs_ruby.md | 698 | unexpected_pass | `trait Greet {     fn greet(&self); }  //` | warning: trait `Greet` is never used  --> target\tmp\verify_compile_fail\16_rust |
| concept\05_comparative\16_rust_vs_ruby.md | 716 | unexpected_pass | `fn main() {     // ❌ 编译错误: Rust 没有 metho` | warning: struct `Point` is never constructed   --> target\tmp\verify_compile_fai |
| concept\06_ecosystem\01_toolchain.md | 1786 | unexpected_pass | `// Rust 2015 Edition extern crate std;` |  |
| concept\06_ecosystem\01_toolchain.md | 1820 | unexpected_pass | `// Cargo.toml // [profile.release] // lt` |  |
| concept\06_ecosystem\01_toolchain.md | 1800 | unexpected_pass | `// Cargo.toml (workspace root) // [works` |  |
| concept\06_ecosystem\03_idioms_spectrum.md | 1560 | unexpected_pass | `fn main() {     let s = String::from("he` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\03_ |
| concept\06_ecosystem\04_application_domains.md | 1700 | syntax_error | `#![no_std]  fn main() {     // ❌ 编译错误: n` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\03_idioms_spectrum.md | 1625 | unexpected_pass | `use std::mem;  fn main() {     let mut s` |  |
| concept\06_ecosystem\04_application_domains.md | 1656 | unexpected_pass | `use std::rc::Rc;  struct AppState {` | warning: struct `AppState` is never constructed  --> target\tmp\verify_compile_f |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 561 | unexpected_pass | `fn sum(n: u32) -> u32 {     let mut tota` | warning: function `sum` is never used  --> target\tmp\verify_compile_fail\05_for |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 539 | unexpected_pass | `// #[requires(x > 0)] // Prusti 前置条件 fn` | warning: function `sqrt` is never used  --> target\tmp\verify_compile_fail\05_fo |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 599 | unexpected_pass | `// crate-a: 经过形式化验证，无 unsafe // crate-b:` |  |
| concept\06_ecosystem\06_blockchain.md | 816 | syntax_error | `use secp256k1::{SecretKey, PublicKey, Me` | error[E0432]: unresolved import `secp256k1`  --> target\tmp\verify_compile_fail\ |
| concept\06_ecosystem\05_system_design_principles.md | 676 | unexpected_pass | `trait Handler {     fn handle(&self, req` | warning: trait `Handler` is never used  --> target\tmp\verify_compile_fail\05_sy |
| concept\06_ecosystem\05_system_design_principles.md | 697 | unexpected_pass | `trait Repository {     fn find(&self, id` | warning: trait `Repository` is never used  --> target\tmp\verify_compile_fail\05 |
| concept\06_ecosystem\06_blockchain.md | 831 | syntax_error | `#![no_std]  fn hash_data(data: &[u8]) ->` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\06_blockchain.md | 849 | syntax_error | `#![no_std]  fn main() {     // ❌ 编译错误: V` | error: cannot find macro `println` in this scope  --> target\tmp\verify_compile_ |
| concept\06_ecosystem\06_blockchain.md | 794 | unexpected_pass | `struct Contract {     balance: u64, }  i` | warning: struct `Contract` is never constructed  --> target\tmp\verify_compile_f |
| concept\06_ecosystem\05_system_design_principles.md | 718 | unexpected_pass | `struct HttpRequest<State> {     url: Str` | warning: struct `HttpRequest` is never constructed  --> target\tmp\verify_compil |
| concept\06_ecosystem\08_wasi.md | 466 | unexpected_pass | `// 错误：组件 A 导出 i32，组件 B 期望 s64 // 组件组合时的类` |  |
| concept\06_ecosystem\08_wasi.md | 448 | unexpected_pass | `// 错误：尝试访问未被授予能力的资源 // WASI 能力安全模型在运行时拒绝` | warning: function `escape_sandbox` is never used  --> target\tmp\verify_compile_ |
| concept\06_ecosystem\08_wasi.md | 573 | unexpected_pass | `use std::fs::File; use std::io::Read;  f` |  |
| concept\06_ecosystem\11_webassembly.md | 529 | syntax_error | `#![no_std]  #[no_mangle] pub extern "C"` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\10_public_private_deps.md | 442 | unexpected_pass | `// crate A v1.0.0 pub fn old_api() {}  /` | warning: function `old_api` is never used  --> target\tmp\verify_compile_fail\10 |
| concept\06_ecosystem\10_public_private_deps.md | 482 | unexpected_pass | `// Crate A 依赖 tokio = { version = "1", f` |  |
| concept\06_ecosystem\11_webassembly.md | 545 | syntax_error | `#![no_std]  fn main() {     // ❌ 运行时陷阱:` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\10_public_private_deps.md | 496 | unexpected_pass | `// Crate A 的 Cargo.toml // [dependencies` |  |
| concept\06_ecosystem\11_webassembly.md | 492 | syntax_error | `#![no_main]  use std::thread;  fn main()` | warning: function `main` is never used  --> target\tmp\verify_compile_fail\11_we |
| concept\06_ecosystem\12_testing_strategies.md | 658 | syntax_error | `use mockall::automock;  #[automock] trai` | error[E0432]: unresolved import `mockall`  --> target\tmp\verify_compile_fail\12 |
| concept\06_ecosystem\12_testing_strategies.md | 638 | unexpected_pass | `static mut COUNTER: i32 = 0;  #[test] fn` | warning: static `COUNTER` is never used  --> target\tmp\verify_compile_fail\12_t |
| concept\06_ecosystem\15_performance_optimization.md | 702 | unexpected_pass | `use std::arch::asm;  fn main() {     let` | warning: formatting may not be suitable for sub-register argument   --> target\t |
| concept\06_ecosystem\15_performance_optimization.md | 723 | unexpected_pass | `#[inline(always)] fn huge_function() ->` |  |
| concept\06_ecosystem\15_performance_optimization.md | 740 | unexpected_pass | `#[inline(always)] fn tiny_helper(x: i32)` | warning: function `tiny_helper` is never used  --> target\tmp\verify_compile_fai |
| concept\06_ecosystem\16_testing.md | 606 | unexpected_pass | `#[test] fn broken_test() {     // ❌ 编译错误` |  |
| concept\06_ecosystem\16_testing.md | 618 | unexpected_pass | `#[cfg(test)] mod tests {     use super::` | warning: trait `Database` is never used   --> target\tmp\verify_compile_fail\16_ |
| concept\06_ecosystem\16_testing.md | 648 | unexpected_pass | `#[cfg(test)] mod tests {     #[test]` |  |
| concept\06_ecosystem\16_testing.md | 668 | unexpected_pass | `/// ```no_run /// let x = 1 / 0; // 运行时` | warning: function `documented` is never used  --> target\tmp\verify_compile_fail |
| concept\06_ecosystem\17_cross_compilation.md | 640 | syntax_error | `#![no_std]  fn main() {     // ❌ 编译错误: `` | error: an inner attribute is not permitted in this context   --> target\tmp\veri |
| concept\06_ecosystem\17_cross_compilation.md | 663 | unexpected_pass | `// 目标: aarch64-unknown-linux-gnu // 但系统未` |  |
| concept\06_ecosystem\18_distributed_systems.md | 659 | unexpected_pass | `// 概念代码: Raft 节点在分区时的投票冲突 struct RaftNod` | warning: struct `RaftNode` is never constructed  --> target\tmp\verify_compile_f |
| concept\06_ecosystem\18_distributed_systems.md | 638 | unexpected_pass | `use std::time::{SystemTime, Duration};` |  |
| concept\06_ecosystem\19_security_practices.md | 625 | unexpected_pass | `// Cargo.toml // [dependencies] // serde` |  |
| concept\06_ecosystem\19_security_practices.md | 641 | unexpected_pass | `fn main() {     let password = String::f` |  |
| concept\06_ecosystem\20_licensing_and_compliance.md | 647 | unexpected_pass | `// Cargo.toml 依赖链引入 GPL 代码  // [dependen` |  |
| concept\06_ecosystem\22_embedded_systems.md | 711 | syntax_error | `#![no_std]  fn main() {     // ❌ 编译错误: `` | error: an inner attribute is not permitted in this context   --> target\tmp\veri |
| concept\06_ecosystem\22_embedded_systems.md | 748 | syntax_error | `static mut COUNTER: u32 = 0;  fn increme` | error: unsafe attribute used without unsafe   --> target\tmp\verify_compile_fail |
| concept\06_ecosystem\20_licensing_and_compliance.md | 682 | unexpected_pass | `// 假设 proprietary 项目依赖 GPL-3.0 库  // [de` |  |
| concept\06_ecosystem\22_embedded_systems.md | 769 | syntax_error | `#![no_std]  fn main() {     // ❌ 链接错误: p` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\20_licensing_and_compliance.md | 699 | unexpected_pass | `// ❌ 法律风险: 静态链接 GPL 库可能使整个项目变为 GPL // [d` |  |
| concept\06_ecosystem\21_game_development.md | 677 | unexpected_pass | `use std::time::{Duration, Instant};  fn` |  |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 777 | syntax_error | `# Dockerfile # FROM rust:1.75 AS builder` | error: unknown start of token: \u{ff0c}  --> target\tmp\verify_compile_fail\28_d |
| concept\06_ecosystem\25_cli_development.md | 638 | unexpected_pass | `fn main() {     // ❌ 运行时问题: 若未检查终端能力，在管道` |  |
| concept\06_ecosystem\25_cli_development.md | 654 | unexpected_pass | `fn main() {     // ❌ 运行时显示异常: 纯 ANSI 转义序` |  |
| concept\06_ecosystem\26_game_development.md | 669 | unexpected_pass | `// 假设使用 bevy_ecs 风格 API  struct Position` | warning: struct `Position` is never constructed  --> target\tmp\verify_compile_f |
| concept\06_ecosystem\26_game_development.md | 690 | unexpected_pass | `use std::thread;  struct Renderer {` | warning: unused variable: `renderer`  --> target\tmp\verify_compile_fail\26_game |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 738 | unexpected_pass | `// Cargo.toml 中无特别配置  fn main() {     //` |  |
| concept\06_ecosystem\26_game_development.md | 732 | unexpected_pass | `// 概念代码: Bevy ECS 的 archetype 变更 // ❌ 运行` |  |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 800 | syntax_error | `# .github/workflows/ci.yml # ❌ 配置错误: 缓存键` | error: unknown start of token: \u{ff0c}  --> target\tmp\verify_compile_fail\28_d |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 753 | unexpected_pass | `static mut COUNTER: i32 = 0;  #[test] fn` | warning: static `COUNTER` is never used  --> target\tmp\verify_compile_fail\28_d |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1126 | unexpected_pass | `fn main() {     // ❌ 编译错误/链接错误: 栈数组太大（可能` |  |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1109 | unexpected_pass | `fn main() {     let mut data = vec![3, 1` |  |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1159 | unexpected_pass | `use std::collections::BinaryHeap;  fn ma` |  |
| concept\06_ecosystem\30_system_composability.md | 876 | unexpected_pass | `trait A { fn method(&self); } trait B: A` | warning: unused variable: `t`   --> target\tmp\verify_compile_fail\30_system_com |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1138 | unexpected_pass | `fn main() {     let mut v = vec![3, 1, 4` |  |
| concept\06_ecosystem\30_system_composability.md | 903 | unexpected_pass | `struct Engine {     horsepower: u32, }` | warning: struct `Engine` is never constructed  --> target\tmp\verify_compile_fai |
| concept\06_ecosystem\31_microservice_patterns.md | 98 | syntax_error | `use consul::{Client, Config};  async fn` | error[E0432]: unresolved import `consul`  --> target\tmp\verify_compile_fail\31_ |
| concept\06_ecosystem\31_microservice_patterns.md | 974 | unexpected_pass | `trait Service {     fn handle(&self, req` | warning: trait `Service` is never used  --> target\tmp\verify_compile_fail\31_mi |
| concept\06_ecosystem\31_microservice_patterns.md | 998 | unexpected_pass | `// 概念代码: 断路器半开状态的问题 enum CircuitState {` | warning: enum `CircuitState` is never used  --> target\tmp\verify_compile_fail\3 |
| concept\06_ecosystem\32_event_driven_architecture.md | 1047 | unexpected_pass | `use std::any::Any;  struct EventBus {` | warning: unused variable: `bus`   --> target\tmp\verify_compile_fail\32_event_dr |
| concept\06_ecosystem\32_event_driven_architecture.md | 1073 | unexpected_pass | `struct EventSystem<'a> {     listeners:` | warning: unused variable: `msg`  --> target\tmp\verify_compile_fail\32_event_dri |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 569 | syntax_error | `extern "C" {     // 假设 C 库函数: int proces` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\34_forma |
| concept\06_ecosystem\33_idioms_spectrum.md | 1554 | unexpected_pass | `fn critical_function() -> i32 {     // ❌` |  |
| concept\06_ecosystem\33_idioms_spectrum.md | 1569 | unexpected_pass | `use std::ops::Deref;  struct Wrapper(Str` |  |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 539 | unexpected_pass | `pub struct SafeVec<T> {     inner: Vec<T` |  |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 587 | unexpected_pass | `// 规格（Prusti 注解）: // #[requires(n >= 0)]` | warning: function `factorial` is never used  --> target\tmp\verify_compile_fail\ |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 397 | unexpected_pass | `// 错误: Singleton 隐藏依赖，与 DI 哲学冲突 struct L` | warning: unused variable: `logger`   --> target\tmp\verify_compile_fail\35_patte |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 427 | unexpected_pass | `use std::rc::Rc; use std::cell::RefCell;` | warning: method `update` is never used  --> target\tmp\verify_compile_fail\35_pa |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 576 | unexpected_pass | `struct Wrapper<T>(T);  fn main() {     l` | warning: unused variable: `inner`  --> target\tmp\verify_compile_fail\35_pattern |
| concept\06_ecosystem\38_network_protocols.md | 246 | syntax_error | `use aya::{include_bytes_aligned, Ebpf};` | error[E0432]: unresolved import `aya`  --> target\tmp\verify_compile_fail\38_net |
| concept\06_ecosystem\38_network_protocols.md | 276 | syntax_error | `use quinn::{Connection, Endpoint};  asyn` | error[E0432]: unresolved import `quinn`  --> target\tmp\verify_compile_fail\38_n |
| concept\06_ecosystem\39_os_kernel.md | 260 | syntax_error | `#![no_std]  fn kernel_compute(x: f32) ->` | error: `#[panic_handler]` function required, but not found  error: unwinding pan |
| concept\06_ecosystem\39_os_kernel.md | 304 | syntax_error | `// Redox 使用 URL 作为资源标识符 // file:/path/to` | error[E0432]: unresolved import `redox_scheme`   --> target\tmp\verify_compile_f |
| concept\06_ecosystem\39_os_kernel.md | 247 | unexpected_pass | `const fn kernel_init(value: usize) -> us` | warning: function `kernel_init` is never used  --> target\tmp\verify_compile_fai |
| concept\07_future\01_ai_integration.md | 677 | unexpected_pass | `// AI 可能生成"编译通过但逻辑错误"的代码 // 反例：错误地实现了二分查` |  |
| concept\07_future\03_evolution.md | 1478 | syntax_error | `fn main() {     // ❌ 编译错误:`async`在 Rus` | error: expected identifier, found keyword `async`  --> target\tmp\verify_compile |
| concept\07_future\03_evolution.md | 617 | syntax_error | `trait LendingIterator {     type Item<'a` | error: missing required bound on `Item`  --> target\tmp\verify_compile_fail\03_e |
| concept\07_future\02_formal_methods.md | 1965 | unexpected_pass | `// 规格: fn add(a: u32, b: u32) -> u32 { a` | warning: function `add` is never used  --> target\tmp\verify_compile_fail\02_for |
| concept\07_future\01_ai_integration.md | 843 | unexpected_pass | `// AI 生成的代码可能包含微妙的 unsafe 错误 fn ai_gener` | warning: function `ai_generated_parse` is never used  --> target\tmp\verify_comp |
| concept\07_future\02_formal_methods.md | 1982 | unexpected_pass | `// 假设项目使用 nightly-2024-01-01 的 Miri // 但` | warning: the feature `custom_mir` is internal to the compiler or standard librar |
| concept\07_future\03_evolution.md | 1496 | unexpected_pass | `fn array_size<const N: usize>(arr: [i32;` | warning: unused variable: `arr`  --> target\tmp\verify_compile_fail\03_evolution |
| concept\07_future\03_evolution.md | 1544 | unexpected_pass | `fn main() {     let opt = Some(5);     /` | warning: function `fixed` is never used   --> target\tmp\verify_compile_fail\03_ |
| concept\07_future\04_effects_system.md | 527 | unexpected_pass | `use std::sync::Mutex;  async fn bad_mute` | warning: function `bad_mutex_usage` is never used  --> target\tmp\verify_compile |
| concept\07_future\04_effects_system.md | 574 | unexpected_pass | `async fn bad_capture(data: &mut Vec<i32>` | warning: function `bad_capture` is never used  --> target\tmp\verify_compile_fai |
| concept\07_future\05_rust_version_tracking.md | 798 | unexpected_pass | `#![feature(generic_const_exprs)]  fn mak` | warning: the feature `generic_const_exprs` is incomplete and may not be safe to  |
| concept\07_future\05_rust_version_tracking.md | 837 | unexpected_pass | `// Cargo.toml // [package] // rust-versi` |  |
| concept\07_future\05_rust_version_tracking.md | 818 | unexpected_pass | `// Edition 2021 代码 fn main() {     let a` |  |
| concept\07_future\07_mcdc_coverage_preview.md | 403 | unexpected_pass | `// Cargo.toml // [profile.dev] // debug` |  |
| concept\07_future\07_mcdc_coverage_preview.md | 378 | unexpected_pass | `fn decide(a: bool, b: bool, c: bool) ->` | warning: function `decide` is never used  --> target\tmp\verify_compile_fail\07_ |
| concept\07_future\07_mcdc_coverage_preview.md | 446 | unexpected_pass | `#[inline(always)] fn hot_path(x: i32) ->` |  |
| concept\07_future\07_mcdc_coverage_preview.md | 424 | unexpected_pass | `fn complex_decision(a: bool, b: bool, c:` | warning: function `complex_decision` is never used  --> target\tmp\verify_compil |
| concept\07_future\09_parallel_frontend_preview.md | 449 | unexpected_pass | `// build.rs 生成代码到 OUT_DIR/generated.rs /` |  |
| concept\07_future\09_parallel_frontend_preview.md | 425 | unexpected_pass | `macro_rules! counter {     () => {` | warning: unused macro definition: `use_counter`   --> target\tmp\verify_compile_ |
| concept\07_future\09_parallel_frontend_preview.md | 482 | unexpected_pass | `macro_rules! count {     () => { 0 };` |  |
| concept\07_future\09_parallel_frontend_preview.md | 466 | unexpected_pass | `// build.rs use std::process::Command;` |  |
| concept\07_future\12_return_type_notation_preview.md | 456 | syntax_error | `trait Factory {     fn create<T: Default` | error: expected one of `!`, `+`, `::`, `:`, `==`, or `=`, found `(`  --> target\ |
| concept\07_future\11_const_trait_impl_preview.md | 488 | syntax_error | `#![feature(const_trait_impl)]  pub trait` | error: const `impl` for trait `ConstDefault` which is not `const`  --> target\tm |
| concept\07_future\12_return_type_notation_preview.md | 492 | unexpected_pass | `trait Processor {     fn process(&self)` | warning: impl trait in impl method signature does not match trait method signatu |
| concept\07_future\16_cranelift_backend_preview.md | 462 | syntax_error | `#[cfg(target_arch = "x86_64")] fn cpuid(` | error: cannot use register `bx`: rbx is used internally by LLVM and cannot be us |
| concept\07_future\16_cranelift_backend_preview.md | 534 | syntax_error | `// ❌ 运行时差异: Cranelift 的 debug 优化级别与 LLVM` | error: this arithmetic operation will overflow  --> target\tmp\verify_compile_fa |
| concept\07_future\16_cranelift_backend_preview.md | 502 | unexpected_pass | `#[cfg(target_arch = "x86_64")] use std::` | warning: unused variable: `c`   --> target\tmp\verify_compile_fail\16_cranelift_ |
| concept\07_future\16_cranelift_backend_preview.md | 521 | unexpected_pass | `fn main() {     let x = 42;     // ⚠️ 调试` |  |
| concept\07_future\19_rust_for_linux.md | 713 | syntax_error | `#![no_std]  extern crate alloc; use allo` | error: no global memory allocator found but one is required; link to std or add  |
| concept\07_future\17_rust_specification_preview.md | 501 | unexpected_pass | `fn main() {     let mut x = 0;     let r` |  |
| concept\07_future\17_rust_specification_preview.md | 557 | unexpected_pass | `// ❌ 潜在不一致: Rust 规范草案定义的行为与 rustc 实际实现可能` |  |
| concept\07_future\17_rust_specification_preview.md | 538 | unexpected_pass | `fn main() {     let mut x = 0;     let r` |  |
| concept\07_future\20_borrowsanitizer_preview.md | 478 | syntax_error | `extern "C" {     fn c_modify(ptr: *mut i` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\20_borro |
| concept\07_future\20_borrowsanitizer_preview.md | 442 | unexpected_pass | `fn main() {     let mut x = [0i32; 4];` |  |
| concept\07_future\22_edition_guide.md | 637 | syntax_error | `macro_rules! gen {     ($e:expr) => { $e` | error: expected identifier, found reserved keyword `gen`  --> target\tmp\verify_ |
| concept\07_future\20_borrowsanitizer_preview.md | 519 | unexpected_pass | `// ❌ 检测盲区: BorrowSanitizer（运行时）与 Miri（解释` | warning: function `alias_violation` is never used  --> target\tmp\verify_compile |
| concept\07_future\20_borrowsanitizer_preview.md | 499 | unexpected_pass | `fn main() {     let mut x = [0i32; 4];` |  |
| concept\07_future\21_rust_in_ai.md | 628 | unexpected_pass | `// 假设使用 candle-core  fn matmul_incompati` | warning: function `matmul_incompatible` is never used  --> target\tmp\verify_com |
| concept\07_future\21_rust_in_ai.md | 643 | unexpected_pass | `#[cfg(target_arch = "x86_64")] use std::` | warning: function `simd_add` is never used  --> target\tmp\verify_compile_fail\2 |
| concept\07_future\23_rust_edition_guide.md | 544 | syntax_error | `struct Gen {     value: i32, }  fn main(` | error: expected identifier, found reserved keyword `gen`  --> target\tmp\verify_ |
| concept\07_future\22_edition_guide.md | 652 | unexpected_pass | `// 迁移前 (Edition 2021) fn main() {     le` |  |
| concept\07_future\22_edition_guide.md | 670 | unexpected_pass | `// Rust 2018 → 2021 迁移中，cargo fix 无法处理所有` | warning: unused import: `inner::helper`   --> target\tmp\verify_compile_fail\22_ |
| concept\07_future\23_rust_edition_guide.md | 522 | unexpected_pass | `// Edition 2021 宏 macro_rules! old_macro` | warning: unused variable: `x`   --> target\tmp\verify_compile_fail\23_rust_editi |
| concept\07_future\24_roadmap.md | 1010 | syntax_error | `trait Iterable {     type Item<'a>;` | error: missing required bound on `Item`  --> target\tmp\verify_compile_fail\24_r |
| concept\07_future\23_rust_edition_guide.md | 561 | unexpected_pass | `// Workspace Cargo.toml // [workspace] /` |  |
| concept\07_future\25_open_enums_preview.md | 674 | syntax_error | `#[open_enum] enum HttpStatus {     Ok =` | error: cannot find attribute `open_enum` in this scope  --> target\tmp\verify_co |
| concept\07_future\24_roadmap.md | 988 | unexpected_pass | `fn always_panic() -> ! {     panic!("nev` |  |
| concept\07_future\25_open_enums_preview.md | 716 | syntax_error | `#[open_enum] enum Status {     Ok = 200,` | error: cannot find attribute `open_enum` in this scope  --> target\tmp\verify_co |
| concept\07_future\24_roadmap.md | 1033 | unexpected_pass | `fn make_iter() -> impl Iterator<Item = i` | warning: unused variable: `x`   --> target\tmp\verify_compile_fail\24_roadmap_L1 |
| concept\07_future\24_roadmap.md | 1052 | unexpected_pass | `// ❌ 规划风险: 依赖 nightly 特性的项目面临稳定化时间表不确定 #` | warning: the feature `generic_const_exprs` is incomplete and may not be safe to  |
| concept\07_future\27_compile_time_execution.md | 677 | syntax_error | `use proc_macro::TokenStream; use quote::` | error: the `#[proc_macro_derive]` attribute is only usable with crates of the `p |
| concept\07_future\28_rust_for_webassembly.md | 865 | syntax_error | `#![no_std]  use wee_alloc::WeeAlloc;  #[` | error[E0432]: unresolved import `wee_alloc`  --> target\tmp\verify_compile_fail\ |
| concept\07_future\27_compile_time_execution.md | 705 | unexpected_pass | `const fn compute_area(r: f64) -> f64 {` |  |
| knowledge\01_fundamentals\lifetimes.md | 359 | syntax_error | `struct Arena<'a> {     buffer: &'a mut [` | error: lifetime may not live long enough   --> target\tmp\verify_compile_fail\li |
| concept\07_future\29_ebpf_rust.md | 974 | unexpected_pass | `// eBPF 程序 (kernel space) #[repr(C)] str` | warning: struct `Event` is never constructed  --> target\tmp\verify_compile_fail |
| knowledge\03_advanced\macros\declarative.md | 448 | syntax_error | `macro_rules! bad_parse {     ($a:expr, $` | error: no rules expected `,`  --> target\tmp\verify_compile_fail\declarative_L44 |
| knowledge\03_advanced\unsafe\ffi.md | 289 | syntax_error | `use std::os::raw::c_int;  // 声明 C 函数 ext` | error: extern blocks must be unsafe  --> target\tmp\verify_compile_fail\ffi_L289 |
| knowledge\03_advanced\unsafe\inline_asm.md | 161 | syntax_error | `use std::arch::asm;  /// 获取 CPU 厂商信息 fn` | error: cannot use register `bx`: rbx is used internally by LLVM and cannot be us |
| knowledge\04_expert\safety_critical\08_training\INTERACTIVE_LEARNING_RESOURCES.md | 112 | syntax_error | `//! 在线实验: 安全LED闪烁器 //! 平台: https://wokwi` | error[E0432]: unresolved import `cortex_m_rt`  --> target\tmp\verify_compile_fai |
| knowledge\04_expert\safety_critical\08_training\HANDS_ON_LAB_EXERCISES.md | 40 | syntax_error | `#![no_std] #![no_main]  use cortex_m_rt:` | error[E0433]: cannot find module or crate `stm32f4` in this scope  --> target\tm |
| knowledge\04_expert\safety_critical\09_reference\API_DESIGN_GUIDELINES.md | 485 | syntax_error | `/// examples/temperature_monitor.rs  use` | error[E0432]: unresolved import `safety_drivers`  --> target\tmp\verify_compile_ |
| knowledge\99_archive\exercises.md | 494 | syntax_error | `use std::collections::BTreeMap;  struct` | error: cannot explicitly dereference within an implicitly-borrowing pattern   -- |
