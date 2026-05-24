# Compile Fail 验证报告 v2 (bin + lib)

> 生成时间: 2026-05-24 17:03

## 摘要

| 状态 | 数量 |
|:---|:---|
| expected_fail | 573 |
| skipped | 100 |
| unexpected_pass | 69 |
| syntax_error | 51 |

## 问题代码块

| 文件 | 行号 | 状态 | 编译模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|:---|
| concept\01_foundation\02_borrowing.md | 1566 | syntax_error | bin_wrapped | `fn longest(x: &str, y: &str) -> &st` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\01_foundation\02_borrowing.md | 1583 | syntax_error | bin_wrapped | `fn dangle() -> &String {     let s ` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\01_foundation\03_lifetimes.md | 801 | unexpected_pass | all_pass | `// ❌ 编译错误: missing lifetime specifi` | warning: struct `Parser` is never constructed  --> target\tmp\verify_c |
| concept\01_foundation\05_reference_semantics.md | 1648 | syntax_error | bin_direct | `use std::cell::RefCell;  fn main() ` | error: expected expression, found `;`  --> target\tmp\verify_compile_f |
| concept\01_foundation\05_reference_semantics.md | 1605 | unexpected_pass | bin_direct | `fn takes_str(s: &str) {     println` |  |
| concept\01_foundation\07_control_flow.md | 790 | unexpected_pass | all_pass | `fn maybe_return() -> i32 {     let ` | warning: function `maybe_return` is never used  --> target\tmp\verify_ |
| concept\01_foundation\11_numeric_types.md | 603 | syntax_error | bin_direct | `use std::num::Wrapping;  fn main() ` | error: expected one of `!` or `::`, found `:`   --> target\tmp\verify_ |
| concept\01_foundation\12_attributes_and_macros.md | 812 | unexpected_pass | all_pass | `// 假设自定义 derive 宏 #[derive(MyDebug)` |   |
| concept\01_foundation\19_numerics.md | 639 | unexpected_pass | bin_direct | `use std::num::NonZeroU32;  fn main(` |  |
| concept\02_intermediate\03_memory_management.md | 2356 | syntax_error | bin_direct | `use std::pin::Pin;  fn main() {    ` | error: unexpected closing delimiter: `}`  --> target\tmp\verify_compil |
| concept\02_intermediate\03_memory_management.md | 2338 | syntax_error | bin_direct | `fn main() {     let v = vec![1, 2, ` | error: unexpected closing delimiter: `}`  --> target\tmp\verify_compil |
| concept\02_intermediate\03_memory_management.md | 2432 | syntax_error | bin_direct | `fn main() {     let s = Box::leak(B` | error: unexpected closing delimiter: `}`  --> target\tmp\verify_compil |
| concept\02_intermediate\02_generics.md | 3191 | syntax_error | bin_direct | `trait Displayable {     fn display(` | error: unexpected closing delimiter: `}`  --> target\tmp\verify_compil |
| concept\02_intermediate\02_generics.md | 3157 | syntax_error | bin_direct | `struct Array<T, const N: usize> {  ` | error: unexpected closing delimiter: `}`  --> target\tmp\verify_compil |
| concept\02_intermediate\04_error_handling.md | 2961 | unexpected_pass | all_pass | `const fn divide(a: i32, b: i32) -> ` | warning: function `checked_div` is never used  --> target\tmp\verify_c |
| concept\02_intermediate\05_assert_matches.md | 616 | unexpected_pass | all_pass | `#[test] fn test_nested_match() {   ` |   |
| concept\02_intermediate\07_closure_types.md | 593 | unexpected_pass | bin_direct | `fn main() {     // ❌ 编译错误: 递归闭包的类型无` | warning: function `correct_usage` is never used   --> target\tmp\verif |
| concept\02_intermediate\11_cow_and_borrowed.md | 611 | unexpected_pass | bin_direct | `use std::borrow::Cow;  fn main() { ` |  |
| concept\02_intermediate\13_dsl_and_embedding.md | 746 | unexpected_pass | bin_direct | `macro_rules! recursive {     () => ` |  |
| concept\02_intermediate\14_newtype_and_wrapper.md | 524 | syntax_error | bin_direct | `struct Meters(u32);  fn add_distanc` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\02_intermediate\14_newtype_and_wrapper.md | 582 | syntax_error | bin_direct | `struct Meters(u32); struct Seconds(` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\02_intermediate\12_smart_pointers.md | 507 | unexpected_pass | all_pass | `use std::pin::Pin;  fn pin_mut_afte` | warning: unused variable: `pinned`  --> target\tmp\verify_compile_fail |
| concept\02_intermediate\15_iterator_patterns.md | 577 | syntax_error | bin_direct | `fn main() {     let data = vec![1, ` | error: unexpected closing delimiter: `)`  --> target\tmp\verify_compil |
| concept\02_intermediate\14_newtype_and_wrapper.md | 627 | unexpected_pass | bin_direct | `use std::ops::Deref;  struct Userna` |  |
| concept\02_intermediate\15_error_handling_deep_dive.md | 598 | unexpected_pass | all_pass | `fn outer() -> Result<Result<i32, St` | warning: function `outer` is never used  --> target\tmp\verify_compile |
| concept\02_intermediate\16_iterator_patterns.md | 637 | unexpected_pass | bin_direct | `fn main() {     let data = vec![Str` | warning: unused variable: `evens`  --> target\tmp\verify_compile_fail_ |
| concept\02_intermediate\17_macro_patterns.md | 628 | unexpected_pass | bin_direct | `macro_rules! declare_x {     () => ` |  |
| concept\02_intermediate\21_metaprogramming.md | 668 | unexpected_pass | bin_direct | `fn array_size<const N: usize>() -> ` | warning: unused variable: `scanned`  --> target\tmp\verify_compile_fai |
| concept\03_advanced\02_async_advanced.md | 1265 | unexpected_pass | bin_direct | `use std::pin::Pin;  struct SelfRef ` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile |
| concept\03_advanced\03_unsafe.md | 3384 | unexpected_pass | bin_direct | `fn main() {     let x = 5;     let ` | warning: unused variable: `result`   --> target\tmp\verify_compile_fai |
| concept\03_advanced\08_nll_and_polonius.md | 465 | unexpected_pass | all_pass | `fn nll_scope_limitation() {     let` | warning: function `drop_order_nll` is never used  --> target\tmp\verif |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 879 | unexpected_pass | bin_direct | `use std::sync::atomic::{AtomicPtr, ` | warning: unused variable: `s1`  --> target\tmp\verify_compile_fail_v2\ |
| concept\03_advanced\14_custom_allocators.md | 704 | unexpected_pass | bin_direct | `use std::alloc::System;  #[global_a` |  |
| concept\03_advanced\15_zero_copy_parsing.md | 724 | unexpected_pass | bin_direct | `fn main() {     let bytes = [0x12u8` |  |
| concept\04_formal\04_rustbelt.md | 1227 | syntax_error | bin_direct | `struct Resource; impl Drop for Reso` | error: expected one of `!` or `::`, found `提供内部可变性`   --> target\tmp\v |
| concept\04_formal\04_rustbelt.md | 1248 | syntax_error | bin_direct | `fn main() {     let mut v = vec![1,` | error: expected one of `!` or `::`, found `提供内部可变性`   --> target\tmp\v |
| concept\04_formal\04_rustbelt.md | 1286 | syntax_error | bin_direct | `use std::mem;  struct Guard; impl D` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\04_rustbelt.md | 1263 | syntax_error | bin_direct | `use std::cell::Cell;  fn main() {  ` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\11_separation_logic.md | 711 | syntax_error | bin_direct | `use ghost_cell::GhostCell;  fn main` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\11_separation_logic.md | 731 | syntax_error | bin_direct | `// RustBelt 形式化中的概念，非实际 Rust 代码  //` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\11_separation_logic.md | 690 | syntax_error | bin_direct | `fn swap(a: &mut i32, b: &mut i32) {` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\10_category_theory.md | 712 | unexpected_pass | all_pass | `fn map_both<A, B, F>(a: Option<A>, ` | warning: function `monadic_bind` is never used  --> target\tmp\verify_ |
| concept\04_formal\14_lambda_calculus.md | 644 | syntax_error | bin_wrapped | `fn y_combinator<F, T>(f: F) -> T wh` | error: unexpected closing delimiter: `)`   --> target\tmp\verify_compi |
| concept\04_formal\14_lambda_calculus.md | 590 | syntax_error | bin_wrapped | `// Y = λf.(λx.f (x x)) (λx.f (x x))` | error: unexpected closing delimiter: `)`   --> target\tmp\verify_compi |
| concept\04_formal\14_lambda_calculus.md | 660 | syntax_error | bin_direct | `fn make_adder(x: i32) -> impl Fn(i3` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\04_formal\14_lambda_calculus.md | 613 | unexpected_pass | bin_direct | `fn main() {     // ❌ 编译错误: type ann` |  |
| concept\04_formal\15_hoare_logic.md | 749 | unexpected_pass | all_pass | `// 假设 weakest precondition 计算 fn ab` | warning: function `gcd` is never used  --> target\tmp\verify_compile_f |
| concept\04_formal\17_operational_semantics.md | 1033 | unexpected_pass | bin_direct | `fn main() {     let x = 5;     let ` | warning: variable `x` is assigned to, but never used  --> target\tmp\v |
| concept\04_formal\16_aerospace_certification_formal_methods.md | 1208 | unexpected_pass | all_pass | `fn decision(a: bool, b: bool, c: bo` | warning: function `decision` is never used  --> target\tmp\verify_comp |
| concept\04_formal\18_evaluation_strategies.md | 371 | unexpected_pass | bin_direct | `struct Config {     data: Vec<u8>, ` |  |
| concept\05_comparative\01_rust_vs_cpp.md | 2688 | unexpected_pass | bin_direct | `trait A { fn method(&self); } trait` |  |
| concept\05_comparative\02_rust_vs_go.md | 1042 | unexpected_pass | bin_direct | `fn main() {     // ❌ 编译错误: `Option<` | warning: unused variable: `p`  --> target\tmp\verify_compile_fail_v2\t |
| concept\05_comparative\03_paradigm_matrix.md | 985 | unexpected_pass | bin_direct | `fn main() {     let mut sum = 0;   ` | warning: struct `Config` is never constructed   --> target\tmp\verify_ |
| concept\05_comparative\04_safety_boundaries.md | 1110 | unexpected_pass | bin_direct | `fn main() {     let ptr = 0x1234 as` | warning: variable does not need to be mutable   --> target\tmp\verify_ |
| concept\05_comparative\04_safety_boundaries.md | 1177 | unexpected_pass | all_pass | `fn bad_unsafe() {     let mut x = 5` | warning: function `cps_factorial` is never used  --> target\tmp\verify |
| concept\05_comparative\06_rust_vs_java.md | 493 | unexpected_pass | bin_direct | `fn main() {     // ❌ 编译错误: `Option<` | warning: unused variable: `file2`   --> target\tmp\verify_compile_fail |
| concept\05_comparative\07_rust_vs_python.md | 581 | unexpected_pass | bin_direct | `fn main() {     let x = 42;     // ` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail_v2\t |
| concept\05_comparative\08_rust_vs_javascript.md | 667 | unexpected_pass | bin_direct | `struct Counter {     count: i32, } ` |  |
| concept\05_comparative\08_rust_vs_ruby.md | 718 | unexpected_pass | all_pass | `trait Greet {     fn greet(&self); ` | warning: trait `Greet` is never used  --> target\tmp\verify_compile_fa |
| concept\05_comparative\13_rust_vs_csharp.md | 852 | unexpected_pass | bin_direct | `// C#: [Serializable] 是运行时反射标记 // [` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail_v2\t |
| concept\05_comparative\14_rust_vs_elixir.md | 839 | unexpected_pass | bin_direct | `fn main() {     let x = 42;     // ` | warning: unused variable: `x`  --> target\tmp\verify_compile_fail_v2\t |
| concept\05_comparative\15_rust_vs_typescript.md | 784 | unexpected_pass | bin_direct | `struct Config {     port: u16,     ` | warning: struct `Point` is never constructed   --> target\tmp\verify_c |
| concept\05_comparative\16_rust_vs_ruby.md | 698 | unexpected_pass | all_pass | `trait Greet {     fn greet(&self); ` | warning: trait `Greet` is never used  --> target\tmp\verify_compile_fa |
| concept\05_comparative\16_rust_vs_ruby.md | 746 | unexpected_pass | bin_direct | `// Ruby: 运行时元编程 // class Foo //   d` |  |
| concept\06_ecosystem\03_idioms_spectrum.md | 1560 | unexpected_pass | bin_direct | `fn main() {     let s = String::fro` |  |
| concept\06_ecosystem\01_toolchain.md | 1800 | unexpected_pass | all_pass | `// Cargo.toml (workspace root) // [` | warning: struct `AppState` is never constructed  --> target\tmp\verify |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 539 | unexpected_pass | all_pass | `// #[requires(x > 0)] // Prusti 前置条` | warning: struct `Contract` is never constructed  --> target\tmp\verify |
| concept\06_ecosystem\06_blockchain.md | 849 | unexpected_pass | bin_direct | `#![no_std]  fn main() {     // ❌ 编译` |  |
| concept\06_ecosystem\10_public_private_deps.md | 482 | unexpected_pass | all_pass | `// Crate A 依赖 tokio = { version = "` | warning: static `COUNTER` is never used  --> target\tmp\verify_compile |
| concept\06_ecosystem\15_performance_optimization.md | 689 | unexpected_pass | bin_direct | `fn main() {     let x: u32 = 0x1234` |  |
| concept\06_ecosystem\16_testing.md | 606 | syntax_error | bin_wrapped | `#[test] fn broken_test() {     // ❌` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\15_performance_optimization.md | 740 | syntax_error | bin_wrapped | `#[inline(always)] fn tiny_helper(x:` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\16_testing.md | 618 | syntax_error | bin_wrapped | `#[cfg(test)] mod tests {     use su` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\16_testing.md | 648 | syntax_error | bin_wrapped | `#[cfg(test)] mod tests {     #[test` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\16_testing.md | 668 | syntax_error | bin_wrapped | `/// ```no_run /// let x = 1 / 0; //` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\17_cross_compilation.md | 663 | unexpected_pass | bin_direct | `// 目标: aarch64-unknown-linux-gnu //` |  |
| concept\06_ecosystem\19_security_practices.md | 625 | unexpected_pass | bin_direct | `// Cargo.toml // [dependencies] // ` |  |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1109 | unexpected_pass | bin_direct | `fn main() {     let mut data = vec!` |  |
| concept\06_ecosystem\30_system_composability.md | 876 | unexpected_pass | bin_direct | `trait A { fn method(&self); } trait` | warning: unused variable: `t`   --> target\tmp\verify_compile_fail_v2\ |
| concept\06_ecosystem\31_microservice_patterns.md | 936 | unexpected_pass | bin_direct | `struct Config {     db_url: String,` | warning: unused variable: `msg`  --> target\tmp\verify_compile_fail_v2 |
| concept\06_ecosystem\33_idioms_spectrum.md | 1554 | syntax_error | bin_direct | `fn critical_function() -> i32 {    ` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\33_idioms_spectrum.md | 1569 | syntax_error | bin_direct | `use std::ops::Deref;  struct Wrappe` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 539 | syntax_error | bin_direct | `pub struct SafeVec<T> {     inner: ` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 427 | unexpected_pass | bin_direct | `use std::rc::Rc; use std::cell::Ref` | warning: unused variable: `inner`  --> target\tmp\verify_compile_fail_ |
| concept\07_future\02_formal_methods.md | 1982 | syntax_error | bin_direct | `// 假设项目使用 nightly-2024-01-01 的 Miri` | error: expected identifier, found keyword `async`  --> target\tmp\veri |
| concept\07_future\03_evolution.md | 1478 | syntax_error | bin_direct | `fn main() {     // ❌ 编译错误: `async` ` | error: expected identifier, found keyword `async`  --> target\tmp\veri |
| concept\07_future\03_evolution.md | 1496 | unexpected_pass | bin_direct | `fn array_size<const N: usize>(arr: ` | warning: function `fixed` is never used   --> target\tmp\verify_compil |
| concept\07_future\05_rust_version_tracking.md | 798 | unexpected_pass | bin_direct | `#![feature(generic_const_exprs)]  f` | warning: the feature `generic_const_exprs` is incomplete and may not b |
| concept\07_future\05_rust_version_tracking.md | 837 | unexpected_pass | bin_direct | `// Cargo.toml // [package] // rust-` |  |
| concept\07_future\07_mcdc_coverage_preview.md | 378 | unexpected_pass | all_pass | `fn decide(a: bool, b: bool, c: bool` | warning: function `decide` is never used  --> target\tmp\verify_compil |
| concept\07_future\08_safety_tags_preview.md | 446 | unexpected_pass | bin_direct | `#[safety::tag("memory-safe")] #[saf` |  |
| concept\07_future\09_parallel_frontend_preview.md | 449 | unexpected_pass | bin_direct | `// build.rs 生成代码到 OUT_DIR/generated` |  |
| concept\07_future\11_const_trait_impl_preview.md | 455 | syntax_error | bin_wrapped | `trait Compute {     fn compute(&sel` | error: expected one of `!`, `+`, `::`, `:`, `==`, or `=`, found `(`  - |
| concept\07_future\11_const_trait_impl_preview.md | 488 | syntax_error | bin_wrapped | `#![feature(const_trait_impl)]  pub ` | error: expected one of `!`, `+`, `::`, `:`, `==`, or `=`, found `(`  - |
| concept\07_future\11_const_trait_impl_preview.md | 470 | syntax_error | bin_wrapped | `trait Add {     fn add(&self, other` | error: expected one of `!`, `+`, `::`, `:`, `==`, or `=`, found `(`  - |
| concept\07_future\12_return_type_notation_preview.md | 437 | syntax_error | bin_wrapped | `trait Parser<'a> {     type Output;` | error: expected one of `!`, `+`, `::`, `:`, `==`, or `=`, found `(`  - |
| concept\07_future\16_cranelift_backend_preview.md | 521 | unexpected_pass | bin_direct | `fn main() {     let x = 42;     // ` |  |
| concept\07_future\16_cranelift_backend_preview.md | 534 | unexpected_pass | bin_direct | `// ❌ 运行时差异: Cranelift 的 debug 优化级别与` |  |
| concept\07_future\20_borrowsanitizer_preview.md | 442 | unexpected_pass | bin_direct | `fn main() {     let mut x = [0i32; ` |  |
| concept\07_future\22_edition_guide.md | 620 | unexpected_pass | bin_direct | `fn main() {     let x = {         l` |  |
| concept\07_future\23_rust_edition_guide.md | 503 | syntax_error | bin_direct | `fn make_iter() -> impl Iterator<Ite` | error: expected identifier, found reserved keyword `gen`  --> target\t |
| concept\07_future\20_borrowsanitizer_preview.md | 519 | unexpected_pass | all_pass | `// ❌ 检测盲区: BorrowSanitizer（运行时）与 Mi` | warning: function `simd_add` is never used  --> target\tmp\verify_comp |
| concept\07_future\22_edition_guide.md | 670 | unexpected_pass | all_pass | `// Rust 2018 → 2021 迁移中，cargo fix 无` | warning: unused import: `inner::helper`   --> target\tmp\verify_compil |
| concept\07_future\23_rust_edition_guide.md | 544 | unexpected_pass | bin_direct | `struct Gen {     value: i32, }  fn ` |  |
| concept\07_future\23_rust_edition_guide.md | 522 | unexpected_pass | all_pass | `// Edition 2021 宏 macro_rules! old_` |  warning: unused variable: `x`   --> target\tmp\verify_compile_fail_v2 |
| concept\07_future\27_compile_time_execution.md | 661 | unexpected_pass | bin_direct | `const fn allocate() -> Vec<i32> {  ` |  |
| knowledge\02_intermediate\smart_pointers.md | 798 | syntax_error | bin_direct | `use std::rc::Rc; use std::thread;  ` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\03_advanced\concurrency\threads.md | 997 | syntax_error | bin_direct | `use std::sync::atomic::{AtomicUsize` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\03_advanced\concurrency\threads.md | 970 | syntax_error | bin_direct | `use std::thread;  fn main() {     l` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\02_intermediate\type_conversions.md | 360 | syntax_error | bin_direct | `use std::ffi::{CString, CStr, OsStr` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\02_intermediate\type_conversions.md | 195 | syntax_error | bin_direct | `use std::convert::TryFrom; use std:` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\02_intermediate\strings.md | 827 | syntax_error | bin_direct | `use std::ffi::{CString, CStr, OsStr` | error: no rules expected `,`  --> target\tmp\verify_compile_fail_v2\te |
| knowledge\99_archive\exercises.md | 350 | syntax_error | bin_direct | `struct Fibonacci {     // 实现这里 }  i` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 262 | syntax_error | bin_direct | `fn sum_of_even_squares(numbers: &[i` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 494 | syntax_error | bin_direct | `use std::collections::BTreeMap;  st` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 418 | syntax_error | bin_direct | `fn sort_and_deduplicate(nums: Vec<i` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 457 | syntax_error | bin_direct | `use std::collections::BTreeMap;  st` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 603 | syntax_error | bin_direct | `use std::error::Error; use std::fmt` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 547 | syntax_error | bin_direct | `fn binary_search<T: Ord>(arr: &[T],` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
| knowledge\99_archive\exercises.md | 302 | syntax_error | bin_direct | `use std::collections::HashMap;  fn ` | error: unexpected closing delimiter: `}`   --> target\tmp\verify_compi |
