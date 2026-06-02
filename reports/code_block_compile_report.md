# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-06-02
> 扫描范围: concept/ + knowledge/

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 1750 |
| 编译通过 | 1587 |
| 编译失败 | 163 |
| 跳过 (ignore/no_run) | 1978 |
| 通过率 | 90.7% |

## 编译失败的代码块（concept/）

| 文件 | 行号 | 模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|
| concept\01_foundation\15_closure_basics.md | 98 | normal | `// 三种闭包 trait  // Fn: 不可变借用捕获，可多次调用 fn c` | warning: variable does not need to be mutable   --> target\tmp\code_block_tests\ |
| concept\01_foundation\17_collections_advanced.md | 602 | normal | `use std::collections::{BTreeMap, HashMap` | warning: unused import: `HashMap`  --> target\tmp\code_block_tests\17_collection |
| concept\01_foundation\21_effects_and_purity.md | 276 | normal | `// 命令式: 可变状态 + 循环 fn imperative_sum(data` | warning: function `imperative_sum` is never used  --> target\tmp\code_block_test |
| concept\01_foundation\22_data_abstraction_spectrum.md | 268 | normal | `trait Drawable { fn draw(&self); } trait` | warning: trait `Drawable` is never used  --> target\tmp\code_block_tests\22_data |
| concept\01_foundation\22_data_abstraction_spectrum.md | 365 | normal | `// Rust: enum 的 match 强制穷尽 enum Value {` | warning: variants `Float` and `Text` are never constructed  --> target\tmp\code_ |
| concept\01_foundation\22_data_abstraction_spectrum.md | 448 | normal | `struct ZeroSized; // 零大小类型  fn main() {` | warning: function `fixed` is never used   --> target\tmp\code_block_tests\22_dat |
| concept\01_foundation\22_data_abstraction_spectrum.md | 473 | normal | `enum Message {     Quit,     Move { x: i` | warning: unused variable: `msg`  --> target\tmp\code_block_tests\22_data_abstrac |
| concept\02_intermediate\01_traits.md | 441 | normal | `// ✅ 自动推导示例 struct Point { x: i32, y: i3` | warning: struct `Point` is never constructed  --> target\tmp\code_block_tests\01 |
| concept\02_intermediate\01_traits.md | 867 | normal | `// Rust: Trait bound 是显式的约束 fn add<T: st` | warning: function `add` is never used  --> target\tmp\code_block_tests\01_traits |
| concept\02_intermediate\01_traits.md | 1058 | normal | `// 边界: Orphan Rule 对嵌套泛型、元组、引用的精确判定  //` | warning: struct `Local` is never constructed  --> target\tmp\code_block_tests\01 |
| concept\02_intermediate\01_traits.md | 1088 | normal | `// 边界: 对象安全条件的精确测试与分发方式差异  // ✅ 对象安全: 方法` | warning: trait `SafeTrait` is never used  --> target\tmp\code_block_tests\01_tra |
| concept\02_intermediate\01_traits.md | 1135 | normal | `// 边界: Blanket impl 与关联类型的递归约束求解 + Auto` | warning: unused import: `std::rc::Rc`   --> target\tmp\code_block_tests\01_trait |
| concept\02_intermediate\02_generics.md | 1283 | normal | `// 边界: const generics 支持有限类型级运算，特化尚未稳定` | warning: struct `Matrix` is never constructed  --> target\tmp\code_block_tests\0 |
| concept\02_intermediate\02_generics.md | 1661 | normal | `#![feature(min_specialization)]  use std` | warning: trait `Append` is never used  --> target\tmp\code_block_tests\02_generi |
| concept\02_intermediate\02_generics.md | 1869 | normal | `// Peano 数：Z 和 S<N> struct Z; struct S<N` | warning: struct `Z` is never constructed  --> target\tmp\code_block_tests\02_gen |
| concept\02_intermediate\03_memory_management.md | 373 | normal | `// ✅ 正确: Box 提供堆分配 + 自动释放 fn main() {` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\02_intermediate\03_memory_management.md | 850 | normal | `use std::cell::RefCell;  // 边界: RefCell` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\02_intermediate\03_memory_management.md | 884 | normal | `use std::mem::ManuallyDrop;  // 边界: 故意放弃` | warning: function `box_leak_boundary` is never used  --> target\tmp\code_block_t |
| concept\02_intermediate\03_memory_management.md | 920 | normal | `use std::sync::Arc; use std::thread;  //` | warning: function `arc_thread_safety` is never used  --> target\tmp\code_block_t |
| concept\02_intermediate\03_memory_management.md | 1303 | normal | `// ✅ Vec 的扩容行为（标准库实现细节） let mut v = Vec:` | error: could not write output to 03_memory_management_L1303.03_memory_management |
| concept\02_intermediate\03_memory_management.md | 1324 | normal | `let mut v = vec![1, 2, 3]; let r = &v[0]` | warning: unused variable: `r`  --> target\tmp\code_block_tests\03_memory_managem |
| concept\02_intermediate\03_memory_management.md | 1662 | normal | `fn main() {     let b = Box::new(42);` | error: could not write output to 03_memory_management_L1662.03_memory_management |
| concept\02_intermediate\03_memory_management.md | 1749 | normal | `use std::alloc::{alloc, dealloc, Layout}` | warning: function `fixed` is never used   --> target\tmp\code_block_tests\03_mem |
| concept\02_intermediate\08_interior_mutability.md | 495 | normal | `use std::sync::RwLock;  fn main() {` | warning: function `correct_upgrade` is never used   --> target\tmp\code_block_te |
| concept\02_intermediate\15_iterator_patterns.md | 523 | normal | `fn main() {     let data = vec![1, 2, 3]` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\02_intermediate\16_iterator_patterns.md | 106 | normal | `// 迭代器的惰性计算  let result: Vec<i32> = vec!` | warning: unused variable: `result`  --> target\tmp\code_block_tests\16_iterator_ |
| concept\02_intermediate\21_metaprogramming.md | 135 | normal | `// 声明宏示例：递归实现 vec! 变体 // [来源: The Little` | warning: unused macro definition: `my_vec`  --> target\tmp\code_block_tests\21_m |
| concept\03_advanced\01_concurrency.md | 815 | normal | `// ✅ 正确: 所有权转移到新线程 use std::thread;  fn` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\03_advanced\01_concurrency.md | 858 | normal | `// ✅ 正确: mpsc channel 所有权转移 use std::syn` | error: could not write output to 01_concurrency_L858.01_concurrency_L858.7b5d250 |
| concept\03_advanced\01_concurrency.md | 1231 | normal | `use std::sync::Mutex;  fn main() {     l` | warning: function `correct_order` is never used   --> target\tmp\code_block_test |
| concept\03_advanced\01_concurrency.md | 1261 | normal | `use std::sync::{Arc, Mutex}; use std::th` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\02_async.md | 1834 | normal | `// ✅ 修正: 使用 Box::pin 打破递归类型 use std::fut` | warning: function `recursive` is never used  --> target\tmp\code_block_tests\02_ |
| concept\03_advanced\02_async.md | 2181 | normal | `// ❌ UB: 使用已释放的指针 fn main() {     let x` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\02_async_advanced.md | 659 | normal | `// ✅ 正确: 栈 pinning（Rust 1.68+） use std::` | warning: function `stack_pinning` is never used  --> target\tmp\code_block_tests |
| concept\03_advanced\02_async_advanced.md | 709 | normal | `// ✅ 修正: 使用 Box::pin 打破递归类型 use std::fut` | warning: function `recursive` is never used  --> target\tmp\code_block_tests\02_ |
| concept\03_advanced\03_unsafe.md | 608 | normal | `fn stacked_borrows_ub() {     let mut x` | warning: unused variable: `r2`  --> target\tmp\code_block_tests\03_unsafe_L608.r |
| concept\03_advanced\03_unsafe.md | 1115 | normal | `// ❌ 反例: 创建无效枚举值 enum Color { Red, Green` | warning[E0133]: call to unsafe function `std::intrinsics::transmute` is unsafe a |
| concept\03_advanced\03_unsafe.md | 1164 | normal | `// 边界: 未定义行为（UB）的微妙性  fn undefined_behav` | warning: function `undefined_behavior_example` is never used  --> target\tmp\cod |
| concept\03_advanced\03_unsafe.md | 1234 | normal | `// extern "C" = 使用 C 调用约定 unsafe extern` | warning: function `c_function` is never used  --> target\tmp\code_block_tests\03 |
| concept\03_advanced\03_unsafe.md | 2057 | normal | `use std::mem::MaybeUninit;  // ✅ 正确: [Ma` | warning: variable does not need to be mutable   --> target\tmp\code_block_tests\ |
| concept\03_advanced\03_unsafe.md | 2092 | normal | `use std::mem::MaybeUninit;  // ✅ 更安全的封装：` | warning: function `init_array_safe` is never used  --> target\tmp\code_block_tes |
| concept\03_advanced\03_unsafe.md | 2119 | normal | `use std::mem::MaybeUninit;  // ❌ 反例: 对未写` | warning: variable does not need to be mutable  --> target\tmp\code_block_tests\0 |
| concept\03_advanced\03_unsafe.md | 2331 | normal | `// Rust 2021：隐式 unsafe unsafe fn old_sty` | warning[E0133]: dereference of raw pointer is unsafe and requires unsafe block   |
| concept\03_advanced\03_unsafe.md | 2797 | normal | `use std::ptr::NonNull;  // Rust 1.96+: N` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\03_advanced\04_macros.md | 1148 | normal | `// ✅ 正确: 多个重复器（长度一致时） macro_rules! zip {` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\04_macros.md | 1164 | normal | `// ✅ 正确: 可选尾随逗号（Trailing comma） macro_ru` | error[E0601]: `main` function not found in crate `04_macros_L1164`   \|   = note: |
| concept\03_advanced\08_nll_and_polonius.md | 498 | normal | `fn main() {     let mut data = vec![1, 2` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\15_zero_copy_parsing.md | 670 | normal | `fn parse_header(data: &[u8]) -> &[u8] {` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\17_type_erasure.md | 105 | normal | `trait Greet {     fn greet(&self); }  st` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\03_advanced\17_type_erasure.md | 237 | normal | `trait Process {     fn run(&self); }  st` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 247 | normal | `use std::sync::mpsc; use std::thread;  /` | error: could not write output to 19_parallel_distributed_pattern_spectrum_L247.1 |
| concept\03_advanced\20_stream_processing_semantics.md | 497 | normal | `// 错误：无 Watermark 时，系统不知道何时关闭窗口 // 导致窗口状` | error[E0601]: `main` function not found in crate `20_stream_processing_semantics |
| concept\04_formal\02_type_theory.md | 647 | normal | `// ✅ Rust: 值（常量）出现在类型参数中 struct Array<T,` | warning: unused variable: `a`  --> target\tmp\code_block_tests\02_type_theory_L6 |
| concept\04_formal\02_type_theory.md | 746 | normal | `// 用 GATs 模拟 "类型构造器作为关联类型" trait TypeCon` | warning: trait `TypeConstructor` is never used  --> target\tmp\code_block_tests\ |
| concept\04_formal\04_rustbelt.md | 1096 | normal | `// ✅ 借用检查器阻止观察 realloc let mut v = vec![` | warning: unnecessary `unsafe` block   --> target\tmp\code_block_tests\04_rustbel |
| concept\04_formal\05_verification_toolchain.md | 1294 | normal | `fn main() {     let x = 5;     assert_eq` | error: could not write output to 05_verification_toolchain_L1294.05_verification |
| concept\04_formal\18_evaluation_strategies.md | 136 | normal | `fn side_effect() -> bool {     println!(` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\04_formal\20_axiomatic_semantics.md | 220 | normal | `// 正确示例：所有权转移的公理化 let s1 = String::from(` | warning: unused variable: `s2`  --> target\tmp\code_block_tests\20_axiomatic_sem |
| concept\04_formal\20_axiomatic_semantics.md | 243 | normal | `// 后置条件 Q: s2 拥有字符串 "hello" 且 s1 已失效 let` | warning: unused variable: `s2`  --> target\tmp\code_block_tests\20_axiomatic_sem |
| concept\04_formal\21_type_semantics.md | 164 | normal | `// 语义示例：共享借用的只读性 let x = 5; let r1 = &x;` | error: could not write output to 21_type_semantics_L164.21_type_semantics_L164.a |
| concept\04_formal\23_programming_language_foundations.md | 117 | normal | `// Rust: 副作用是类型系统的一部分，但不是 Monad fn main(` | warning: unused variable: `x`  --> target\tmp\code_block_tests\23_programming_la |
| concept\04_formal\23_programming_language_foundations.md | 147 | normal | `// CPS (Continuation Passing Style) — 显式` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\04_formal\23_programming_language_foundations.md | 210 | normal | `// 自引用结构体（async 状态机的核心问题） struct SelfRef` | warning: struct `SelfReferential` is never constructed  --> target\tmp\code_bloc |
| concept\04_formal\23_programming_language_foundations.md | 269 | normal | `fn example() {     let x = 42;` | warning: unused variable: `y`  --> target\tmp\code_block_tests\23_programming_la |
| concept\05_comparative\02_rust_vs_go.md | 428 | normal | `// Rust: 错误处理通过类型系统强制传播 use std::fs::Fil` | error: could not write output to 02_rust_vs_go_L428.02_rust_vs_go_L428.35a1cfded |
| concept\05_comparative\14_rust_vs_elixir.md | 102 | normal | `fn safe_divide(a: i32, b: i32) -> Result` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\05_comparative\14_rust_vs_elixir.md | 357 | normal | `enum Message {     Text(String),     Num` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\03_core_crates.md | 580 | normal | `// 模拟 serde 的核心抽象：编译期派生与类型同构 // 实际使用需添加` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\06_ecosystem\03_core_crates.md | 623 | normal | `// 模拟 tokio 的核心抽象：Future trait 的类型安全保证 u` | error: could not write output to 03_core_crates_L623.03_core_crates_L623.26f5cf7 |
| concept\06_ecosystem\03_idioms_spectrum.md | 473 | normal | `// 惯用：实现 From 获得 Into struct Port(u16);` | warning: unused variable: `p`   --> target\tmp\code_block_tests\03_idioms_spectr |
| concept\06_ecosystem\03_idioms_spectrum.md | 542 | normal | `// 惯用：接受最通用的借用类型 fn greeting(name: &str)` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\03_idioms_spectrum.md | 1195 | normal | `fn main() {     let data = vec![1, 2, 3]` | warning: function `fixed` is never used   --> target\tmp\code_block_tests\03_idi |
| concept\06_ecosystem\04_application_domains.md | 831 | normal | `// 模拟 Web 路由框架的核心类型约束（类似 axum 的设计） use s` | warning: unused import: `std::collections::HashMap`  --> target\tmp\code_block_t |
| concept\06_ecosystem\04_application_domains.md | 881 | normal | `// ✅ Python 开发者常见的第一个 Rust 程序 use std::c` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\06_ecosystem\04_application_domains.md | 1430 | normal | `// ✅ 基础组件定义完全合法 struct Position { x: f32` | warning: field `y` is never read  --> target\tmp\code_block_tests\04_application |
| concept\06_ecosystem\05_system_design_principles.md | 157 | normal | `// Tower Service = 范畴论语义 trait Service<R` | error[E0601]: `main` function not found in crate `05_system_design_principles_L1 |
| concept\06_ecosystem\11_webassembly.md | 87 | normal | `/// 编译目标: wasm32-unknown-unknown /// 此函数` | error: unsafe attribute used without unsafe  --> target\tmp\code_block_tests\11_ |
| concept\06_ecosystem\15_performance_optimization.md | 156 | normal | `// 验证零成本抽象: 迭代器 vs 手写循环  // 迭代器版本（清晰） fn` | warning: function `sum_iter` is never used  --> target\tmp\code_block_tests\15_p |
| concept\06_ecosystem\15_performance_optimization.md | 520 | normal | `fn main() {     let mut data = vec![1, 2` | warning: function `fixed` is never used   --> target\tmp\code_block_tests\15_per |
| concept\06_ecosystem\15_performance_optimization.md | 548 | normal | `use std::mem::MaybeUninit;  fn main() {` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\06_ecosystem\16_testing.md | 99 | normal | `// 单元测试写在同一个文件中 pub fn add(a: i32, b: i3` | warning: function `add` is never used  --> target\tmp\code_block_tests\16_testin |
| concept\06_ecosystem\17_cross_compilation.md | 94 | normal | `// cfg 属性: 条件编译  // 平台特定代码 #[cfg(target_` | warning: function `platform_specific` is never used   --> target\tmp\code_block_ |
| concept\06_ecosystem\20_licensing_and_compliance.md | 474 | normal | `fn main() {     let data = vec![1, 2, 3]` | error: could not write output to 20_licensing_and_compliance_L474.20_licensing_a |
| concept\06_ecosystem\21_game_development.md | 418 | normal | `fn main() {     let data = vec![1, 2, 3]` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\22_embedded_systems.md | 504 | normal | `fn main() {     let data = vec![1, 2, 3]` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\06_ecosystem\22_embedded_systems.md | 513 | normal | `use core::sync::atomic::{AtomicU32, Orde` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\23_database_access.md | 570 | normal | `fn main() {     let mut conn = std::coll` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\24_cloud_native.md | 457 | normal | `fn main() {     let mut config = std::co` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\33_cqrs_event_sourcing.md | 434 | normal | `// 共享数据库策略：使用 PostgreSQL 的只读副本 // 命令端写入主` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\40_reactive_programming.md | 548 | normal | `// FRP 的核心问题：信号网络中的共享可变状态 // 在 Haskell 中` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\06_ecosystem\43_security_cryptography.md | 77 | normal | `use std::collections::hash_map::DefaultH` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\06_ecosystem\47_formal_verification_tools.md | 119 | normal | `// Rust 形式化验证的核心难点示例  // 挑战 1: 生命周期子类型 f` | warning[E0133]: dereference of raw pointer is unsafe and requires unsafe block   |
| concept\07_future\03_evolution.md | 764 | normal | `#![feature(never_type)]           // 启用` | warning: the feature `generic_const_exprs` is incomplete and may not be safe to  |
| concept\07_future\07_mcdc_coverage_preview.md | 172 | normal | `// 源代码 fn decision(a: bool, b: bool, c:` | warning: function `decision` is never used  --> target\tmp\code_block_tests\07_m |
| concept\07_future\08_safety_tags_preview.md | 230 | normal | `// Rust 1.82+ 的 FFI 安全标注 use std::os::ra` | warning: function `strlen` is never used  --> target\tmp\code_block_tests\08_saf |
| concept\07_future\12_return_type_notation_preview.md | 60 | normal | `// 隐式捕获: async fn 自动捕获 'a async fn borro` | warning: function `borrow` is never used  --> target\tmp\code_block_tests\12_ret |
| concept\07_future\16_cranelift_backend_preview.md | 409 | normal | `fn recursive(n: usize) -> usize {     if` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\07_future\20_borrowsanitizer_preview.md | 312 | normal | `fn main() {     let feature = "preview";` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\07_future\20_borrowsanitizer_preview.md | 378 | normal | `fn main() {     let mut x = 0;     let r` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\07_future\24_roadmap.md | 715 | normal | `fn make_iter() -> impl Iterator<Item = i` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\07_future\25_open_enums_preview.md | 69 | normal | `enum HttpStatus {     Ok,     NotFound,` | warning: enum `HttpStatus` is never used  --> target\tmp\code_block_tests\25_ope |
| concept\07_future\28_rust_for_webassembly.md | 531 | normal | `// Wasm 多线程需要 SharedArrayBuffer + Atomic` | error: linking with `link.exe` failed: exit code: 1104   \|   = note: "C:\\Progra |
| concept\07_future\archive\01_ai_integration_original.md | 929 | normal | `// 用类型系统标记 AI 生成代码的 unsafe 边界 struct AiG` | error: linking with `link.exe` failed: exit code: 1181   \|   = note: "C:\\Progra |
| concept\archive\01_foundation_03_lifetimes_original.md | 1475 | normal | `// ✅ 修正：使用显式 where 子句或泛型参数 fn borrow_fro` | warning: function `borrow_from_fixed` is never used  --> target\tmp\code_block_t |
| concept\archive\01_foundation_03_lifetimes_original.md | 1547 | normal | `// 定义: 每次迭代返回的元素可以借用迭代器自身 trait LendingI` | warning: trait `LendingIterator` is never used  --> target\tmp\code_block_tests\ |
| concept\archive\01_foundation_03_lifetimes_original.md | 1590 | normal | `trait Iterator {     type Item;     fn n` | warning: trait `Iterator` is never used  --> target\tmp\code_block_tests\01_foun |

## 编译失败的代码块（knowledge/）

> knowledge/ 中的 57 个失败块多为教学片段（不完整代码、故意展示编译错误），
> 属于预期行为。以下显示前 5 个示例：

| 文件 | 行号 | 预览 | 错误信息 |
|:---|:---|:---|:---|
| knowledge\01_fundamentals\01_borrowing.md | 105 | `fn main() {     let s1 = String::from("h` | error: linking with `link.exe` failed: exit code: 1181   \|   |
| knowledge\01_fundamentals\01_borrowing.md | 125 | `fn main() {     let x = 5;     let r = &` | error: could not write output to 01_borrowing_L125.01_borrow |
| knowledge\01_fundamentals\01_borrowing.md | 464 | `fn main() {     let data = vec![1, 2, 3,` | error: linking with `link.exe` failed: exit code: 1104   \|   |
| knowledge\02_intermediate\02_error_handling.md | 208 | `// Result<i32, String> 的内存布局（简化）: // 判别式` | error: linking with `link.exe` failed: exit code: 1104   \|   |
| knowledge\02_intermediate\05_strings.md | 256 | `use std::borrow::Cow;  fn process_input(` | warning: unused variable: `s1`   --> target\tmp\code_block_t |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 185 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 444 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 494 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 95 | normal | `async fn foo() -> i32 { 42 } // 等价于: fn` |
| concept\00_meta\quick_reference.md | 169 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 224 | normal | `enum Option<T> { None, Some(T) } enum Re` |
| concept\00_meta\quick_reference.md | 289 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 303 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 337 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 371 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 396 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 415 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 431 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 455 | normal | `let x: Option<i32> = Some(5); let y = x.` |
| concept\00_meta\quick_reference.md | 615 | normal | `let mut v = vec![1, 2, 3]; v.push(4);` |
| concept\00_meta\self_assessment.md | 176 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 230 | normal | `trait Drawable {     fn draw(&self);` |
| concept\00_meta\self_assessment.md | 267 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 283 | normal | `struct A(&'static str); impl Drop for A` |
| concept\00_meta\self_assessment.md | 311 | normal | `fn identity<T>(x: T) -> T { x } let a =` |
