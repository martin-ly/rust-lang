# Compile Fail 验证报告 v3 (唯一文件名)

> 生成时间: 2026-06-01 21:00

## 摘要

| 状态 | 数量 |
|:---|:---|
| expected_fail | 511 |
| skipped | 125 |
| unexpected_pass | 9 |
| syntax_error | 1 |

## 问题代码块

| 文件 | 行号 | 状态 | 编译模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|:---|
| concept\01_foundation\04_type_system.md | 2399 | unexpected_pass | all_pass | `// ❌ 编译错误:`impl Trait`在参数位置不允许 fn` | warning: function `bad_param` is never used  --> target\tmp\verify_com |
| concept\02_intermediate\05_assert_matches.md | 450 | unexpected_pass | bin_direct | `fn main() {     let x = 42;     //` | warning: function `fixed` is never used   --> target\tmp\verify_compil |
| concept\03_advanced\01_concurrency.md | 1093 | unexpected_pass | all_pass | `// 错误: 在 safe Rust 中直接创建裸指针并解引用 fn` | warning: function `unsafe_in_safe` is never used  --> target\tmp\verif |
| concept\03_advanced\01_concurrency.md | 1263 | unexpected_pass | bin_direct | `use std::sync::{Arc, Mutex}; use st` |  |
| concept\03_advanced\01_concurrency.md | 1289 | unexpected_pass | bin_direct | `use std::sync::mpsc; use std::threa` |  |
| concept\04_formal\21_type_semantics.md | 515 | unexpected_pass | bin_direct | `fn main() {     let mut cats: Vec<&` | warning: variable does not need to be mutable  --> target\tmp\verify_c |
| concept\04_formal\21_type_semantics.md | 537 | unexpected_pass | bin_direct | `trait Drawable { fn draw(&self); }` | warning: unused variable: `d1`   --> target\tmp\verify_compile_fail_v3 |
| concept\04_formal\21_type_semantics.md | 707 | unexpected_pass | all_pass | `use std::pin::Pin;  struct SelfRefe` | warning: unused import: `std::pin::Pin`  --> target\tmp\verify_compile |
| concept\06_ecosystem\41_workflow_theory.md | 1103 | unexpected_pass | all_pass | `// ❌ 错误：状态机遗漏转换导致 match 不穷尽 #[deriv` | warning: enum `WorkflowState` is never used  --> target\tmp\verify_com |
| concept\06_ecosystem\53_embedded_graphics.md | 895 | syntax_error | bin_direct | `#![no_std]  static mut FRAMEBUFFER:` | error: `#[panic_handler]` function required, but not found  error: unw |
