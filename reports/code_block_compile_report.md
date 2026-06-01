# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-05-24
> 扫描范围: concept/ + knowledge/

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 1853 |
| 编译通过 | 1503 |
| 编译失败 | 350 |
| 跳过 (ignore/no_run) | 1259 |
| 通过率 | 81.1% |

## 编译失败的代码块（concept/）

| 文件 | 行号 | 模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|:---|
| concept\00_meta\semantic_bridge_algorithms_patterns.md | 69 | normal | `fn merge_sort<T: Ord + Clone>(data: &[T]` | error[E0425]: cannot find function `merge` in this scope   --> target\tmp\code_b |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | 85 | normal | `// Composite: 递归数据结构 trait DataStructure` | error[E0425]: cannot find function `merge` in this scope   --> target\tmp\code_b |
| concept\01_foundation\01_ownership.md | 860 | normal | `// Rust: 初始化 = 所有权获取 let w1 = Widget::ne` | error[E0433]: cannot find type `Widget` in this scope  --> target\tmp\code_block |
| concept\01_foundation\21_effects_and_purity.md | 96 | normal | `// Rust: 副作用通过参数类型和返回类型显式表达 fn process_p` | error[E0433]: cannot find module or crate `io` in this scope  --> target\tmp\cod |
| concept\01_foundation\21_effects_and_purity.md | 176 | normal | `// 显式异常效果: 调用者必须处理 Err 分支 fn may_fail()` | error[E0425]: cannot find type `Error` in this scope  --> target\tmp\code_block_|
| concept\01_foundation\21_effects_and_purity.md | 205 | normal | `// async 效果: 函数返回 Future，实际计算延迟到 await a` | error[E0728]: `await` is only allowed inside `async` functions and blocks   -->  |
| concept\01_foundation\21_effects_and_purity.md | 232 | normal | `// 纯函数 fn add(a: i32, b: i32) -> i32 { a` | error[E0433]: cannot find module or crate `rand` in this scope  --> target\tmp\c |
| concept\01_foundation\21_effects_and_purity.md | 247 | normal | `// 纯函数的 Rust 签名特征: // 1. 不接受 &mut T 参数 /` | error[E0277]: the trait bound `T: Clone` is not satisfied    --> target\tmp\code |
| concept\01_foundation\21_effects_and_purity.md | 309 | normal | `// Rust 的 enum = 代数数据类型（来自 ML/Haskell） e` | error[E0308]: mismatched types    --> target\tmp\code_block_tests\21_effects_and |
| concept\01_foundation\21_effects_and_purity.md | 353 | normal | `// 边界测试: unsafe 块内的副作用不受编译器验证 fn unsafe_` | warning: variable does not need to be mutable  --> target\tmp\code_block_tests\2 |
| concept\01_foundation\22_data_abstraction_spectrum.md | 138 | normal | `// 代数数据类型: Shape = Circle + Rectangle tr` | error[E0425]: cannot find type `Point` in this scope   --> target\tmp\code_block |
| concept\01_foundation\22_data_abstraction_spectrum.md | 191 | normal | `// 文件句柄: 抽象了操作系统资源 struct File {     fd:` | error[E0425]: cannot find type `RawFd` in this scope  --> target\tmp\code_block_ |
| concept\01_foundation\22_data_abstraction_spectrum.md | 251 | normal | `// Rust: 为已有 Point 添加新行为，无需修改 Point trai` | error[E0425]: cannot find type `Color` in this scope  --> target\tmp\code_block_ |
| concept\01_foundation\22_data_abstraction_spectrum.md | 321 | normal | `// Rust: Option 强迫调用者处理 None 分支 fn find_` | error[E0425]: cannot find type `User` in this scope  --> target\tmp\code_block_t |
| concept\01_foundation\22_data_abstraction_spectrum.md | 337 | normal | `enum Result<T, E> {     Ok(T),     Err(E` | error[E0433]: cannot find module or crate `io` in this scope  --> target\tmp\cod |
| concept\02_intermediate\04_error_handling.md | 2198 | normal | `// Rust: Result（强制处理） fn parse_int(s: &s` | error[E0425]: cannot find type `ParseIntError` in this scope  --> target\tmp\cod |
| concept\02_intermediate\04_error_handling.md | 2228 | normal | `// Rust: Drop 不能失败 impl Drop for Safe {` | error[E0425]: cannot find type `Safe` in this scope  --> target\tmp\code_block_t |
| concept\02_intermediate\14_newtype_and_wrapper.md | 554 | normal | `struct Container<T> {     ptr: *const u` | error[E0425]: cannot find type `PhantomData` in this scope  --> target\tmp\code_|
| concept\02_intermediate\20_type_system_advanced.md | 553 | normal | `// Rust: Deref 和 Mul 是两个不同的 trait let a` | error[E0369]: cannot multiply `Box<{integer}>` by `{integer}`    --> target\tmp\ |
| concept\03_advanced\02_async.md | 3737 | normal | `pub trait Stream {     type Item;     fn` | error[E0425]: cannot find type `Pin` in this scope  --> target\tmp\code_block_te |
| concept\03_advanced\06_pin_unpin.md | 499 | normal | `use std::pin::Pin; use std::marker::Phan` | warning: unused import: `std::pin::Pin`  --> target\tmp\code_block_tests\06_pin_ |
| concept\03_advanced\10_concurrency_patterns.md | 583 | normal | `use std::sync::{Arc, Mutex, Condvar}; us` | warning: variable does not need to be mutable   --> target\tmp\code_block_tests\ |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 609 | normal | `use std::sync::atomic::{AtomicUsize, Ord` | error[E0373]: closure may outlive the current function, but it borrows `data`, w |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 632 | normal | `use std::sync::atomic::{AtomicBool, Orde` | error[E0425]: cannot find type `AtomicUsize` in this scope  --> target\tmp\code_ |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 166 | normal | `use actix::prelude::*;  // Actor: 封装状态 +` | error[E0433]: cannot find module or crate `actix` in this scope  --> target\tmp\ |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 279 | normal | `// Raft 的核心状态机（简化概念模型） enum NodeState {` | error[E0425]: cannot find type `NodeId` in this scope  --> target\tmp\code_block |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 334 | normal | `// G-Counter（Grow-only Counter）: 单调递增的分布` | error[E0432]: unresolved import `crdt`  --> target\tmp\code_block_tests\19_paral |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 508 | normal | `use crdt::GCounter;  fn crdt_commutativi` | error[E0432]: unresolved import `crdt`  --> target\tmp\code_block_tests\19_paral |
| concept\04_formal\18_evaluation_strategies.md | 34 | normal | `// Rust: 严格求值 — 参数先求值，再调用函数 fn strict_ex` | error: unknown start of token: \u{ff01}   --> target\tmp\code_block_tests\18_eva |
| concept\04_formal\18_evaluation_strategies.md | 169 | normal | `// Iterator: 惰性构造，消费时才求值 let iter = vec!` | error[E0716]: temporary value dropped while borrowed  --> target\tmp\code_block_ |
| concept\04_formal\18_evaluation_strategies.md | 253 | normal | `// Rust: 可变性通过 &mut T 显式追踪 fn mutate(x:` | error: expected one of `!`, `.`, `::`, `;`, `?`, `{`, `}`, or an operator, found |
| concept\04_formal\18_evaluation_strategies.md | 274 | normal | `fn strict_trap() {     let expensive = c` | error[E0425]: cannot find value `condition` in this scope  --> target\tmp\code_b |
| concept\04_formal\18_evaluation_strategies.md | 295 | normal | `fn evaluation_order() {     let mut v =` | error[E0499]: cannot borrow `v` as mutable more than once at a time  --> target\ |
| concept\05_comparative\02_cpp_abi_object_model.md | 173 | normal | `trait Drawable {     fn draw(&self);` | error[E0425]: cannot find type `Rect` in this scope  --> target\tmp\code_block_t |
| concept\05_comparative\02_cpp_abi_object_model.md | 208 | normal | `fn draw_shape(shape: &dyn Drawable) {` | error[E0405]: cannot find trait `Drawable` in this scope  --> target\tmp\code_bl |
| concept\05_comparative\02_cpp_abi_object_model.md | 451 | normal | `// Cargo.toml 中配置 panic 策略 [profile.rele` | error: expected `;`, found `panic`  --> target\tmp\code_block_tests\02_cpp_abi_o |
| concept\05_comparative\02_cpp_abi_object_model.md | 473 | normal | `// Rust 端（错误：忘记 #[repr(C)]） struct Point` | error: unsafe attribute used without unsafe  --> target\tmp\code_block_tests\02_|
| concept\05_comparative\02_cpp_abi_object_model.md | 524 | normal | `// 错误：试图将 dyn Trait 传递给 C #[no_mangle] p` | error[E0405]: cannot find trait `Drawable` in this scope  --> target\tmp\code_bl |
| concept\06_ecosystem\06_blockchain.md | 768 | normal | `fn main() {     let secret = [1u8, 2, 3,` | error[E0432]: unresolved import `subtle`   --> target\tmp\code_block_tests\06_bl |
| concept\06_ecosystem\08_wasi.md | 484 | normal | `// 边界测试：Resource 句柄在跨组件传递时的生命周期  // 宿主创建` | error[E0425]: cannot find function `preopen_file` in this scope  --> target\tmp\ |
| concept\06_ecosystem\10_public_private_deps.md | 426 | normal | `// crate A pub struct PublicType;  // cr` | error[E0432]: unresolved import `a`  --> target\tmp\code_block_tests\10_public_p |
| concept\06_ecosystem\13_logging_observability.md | 556 | normal | `use opentelemetry::global;  fn main() {` | error[E0432]: unresolved import `opentelemetry`  --> target\tmp\code_block_tests |
| concept\06_ecosystem\19_security_practices.md | 570 | normal | `fn verify_password(input: &[u8], secret:` | error[E0432]: unresolved import `subtle`   --> target\tmp\code_block_tests\19_se |
| concept\06_ecosystem\30_system_composability.md | 855 | normal | `// 主机程序 pub trait Plugin {     fn proces` | error[E0425]: cannot find type `c_void` in this scope   --> target\tmp\code_bloc |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 42 | normal | `// Observer ⊗ Factory: 事件通知与对象创建独立运行 use` | error[E0405]: cannot find trait `Observer` in this scope  --> target\tmp\code_bl |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 69 | normal | `// Validation ∘ Transformation ∘ Persist` | error[E0425]: cannot find type `Request` in this scope  --> target\tmp\code_bloc |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 85 | normal | `// CircuitBreaker ⊕ Retry ⊕ Fallback //` | error[E0425]: cannot find type `CircuitBreaker` in this scope  --> target\tmp\co |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 110 | normal | `// Strategy → Command: 策略的执行被封装为命令  trai` | error[E0425]: cannot find type `Data` in this scope  --> target\tmp\code_block_t |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 227 | normal | `// Typestate 模式: 编译期保证状态转换合法 struct Unin` | error[E0425]: cannot find type `Config` in this scope  --> target\tmp\code_block |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 301 | normal | `// 编译期多态（零成本）+ 运行期多态（动态分发）的组合  trait Pay` | error[E0425]: cannot find type `Transaction` in this scope  --> target\tmp\code_|
| concept\06_ecosystem\35_pattern_composition_algebra.md | 358 | normal | `// Saga = T1 ∘ T2 ∘ ... ∘ Tn ∘ (Compensa` | error[E0425]: cannot find type `Error` in this scope  --> target\tmp\code_block_|
| concept\06_ecosystem\35_pattern_composition_algebra.md | 467 | normal | `// 边界测试: 当组合的模式数量增加时，状态空间呈指数增长  // 2 个模式` | error[E0425]: cannot find type `Duration` in this scope   --> target\tmp\code_bl |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | 66 | normal | `use timely::dataflow::operators::{ToStre` | error[E0433]: cannot find module or crate `timely` in this scope  --> target\tmp |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | 90 | normal | `use differential_dataflow::input::Input;` | error[E0433]: cannot find module or crate `differential_dataflow` in this scope  |
| concept\06_ecosystem\37_database_systems.md | 88 | normal | `// TiKV 中的事务状态机（简化） pub enum TxnStatus {` | error[E0425]: cannot find type `Txn` in this scope   --> target\tmp\code_block_t |
| concept\06_ecosystem\37_database_systems.md | 163 | normal | `// Meilisearch 的索引段（segment）所有权模型 struct` | error[E0425]: cannot find type `Segment` in this scope  --> target\tmp\code_bloc |
| concept\06_ecosystem\38_network_protocols.md | 61 | normal | `// quinn 中的连接状态机（简化） pub enum State {` | error[E0425]: cannot find type `StreamManager` in this scope   --> target\tmp\co |
| concept\06_ecosystem\39_os_kernel.md | 51 | normal | `// 内核中的 Rust 驱动示例（简化） use kernel::prelud` | error[E0433]: cannot find module or crate `kernel` in this scope  --> target\tmp |
| concept\06_ecosystem\39_os_kernel.md | 111 | normal | `// Theseus 中的 Cell 隔离（简化概念） struct Cell<` | error[E0425]: cannot find type `Message` in this scope   --> target\tmp\code_blo |
| concept\07_future\01_ai_integration.md | 158 | normal | `// 状态: 错误代码 + rustc JSON 诊断 // 动作: 修改代码（` | error[E0502]: cannot borrow `x` as immutable because it is also borrowed as muta |
| concept\07_future\01_ai_integration.md | 788 | normal | `use ndarray::Array2;  fn predict(model:` | error[E0432]: unresolved import `ndarray`  --> target\tmp\code_block_tests\01_ai |
| concept\01_foundation\02_borrowing.md | 1552 | compile_fail | `fn main() {     let mut s = String::from` | 应编译失败但通过了 |
| concept\01_foundation\02_borrowing.md | 1625 | compile_fail | `fn main() {     let mut data = vec![1, 2` | 应编译失败但通过了 |
| concept\01_foundation\03_lifetimes.md | 801 | compile_fail | `// ❌ 编译错误: missing lifetime specifier fn` | 应编译失败但通过了 |
| concept\01_foundation\03_lifetimes.md | 857 | compile_fail | `struct Parser {     text: String, }  imp` | 应编译失败但通过了 |
| concept\01_foundation\03_lifetimes_advanced.md | 1725 | compile_fail | `trait Callback {     fn call(&self, x: &` | 应编译失败但通过了 |
| concept\01_foundation\03_lifetimes_advanced.md | 1827 | compile_fail | `fn main() {     let mut x = 5;     let y` | 应编译失败但通过了 |
| concept\01_foundation\05_reference_semantics.md | 1633 | compile_fail | `fn main() {     let mut x = 5;     let r` | 应编译失败但通过了 |
| concept\01_foundation\05_reference_semantics.md | 1648 | compile_fail | `use std::cell::RefCell;  fn main() {` | 应编译失败但通过了 |
| concept\01_foundation\06_zero_cost_abstractions.md | 588 | compile_fail | `fn process<T: std::fmt::Display>(x: T) {` | 应编译失败但通过了 |
| concept\01_foundation\06_zero_cost_abstractions.md | 609 | compile_fail | `use std::pin::Pin;  async fn self_ref()` | 应编译失败但通过了 |
| concept\01_foundation\07_control_flow.md | 790 | compile_fail | `fn maybe_return() -> i32 {     let x = l` | 应编译失败但通过了 |
| concept\01_foundation\08_collections.md | 654 | compile_fail | `fn main() {     let mut v = vec![1, 2, 3` | 应编译失败但通过了 |
| concept\01_foundation\08_collections.md | 667 | compile_fail | `use std::collections::HashMap; use std::` | 应编译失败但通过了 |
| concept\01_foundation\10_error_handling_basics.md | 890 | compile_fail | `fn main() {     let res: Result<i32, &st` | 应编译失败但通过了 |
| concept\01_foundation\10_numerics.md | 743 | compile_fail | `fn main() {     let x: f64 = 0.1 + 0.2;` | 应编译失败但通过了 |
| concept\01_foundation\10_numerics.md | 766 | compile_fail | `fn main() {     let x: i32 = -1;     let` | 应编译失败但通过了 |
| concept\01_foundation\10_numerics.md | 784 | compile_fail | `fn main() {     let x: f64 = f64::NAN;` | 应编译失败但通过了 |
| concept\01_foundation\11_modules_and_paths.md | 719 | compile_fail | `// a.rs // use crate::b::B; // a 依赖 b  /` | 应编译失败但通过了 |
| concept\01_foundation\11_numeric_types.md | 603 | compile_fail | `use std::num::Wrapping;  fn main() {` | 应编译失败但通过了 |
| concept\01_foundation\11_numeric_types.md | 623 | compile_fail | `use std::num::NonZeroU32;  fn main() {` | 应编译失败但通过了 |
| concept\01_foundation\12_attributes_and_macros.md | 812 | compile_fail | `// 假设自定义 derive 宏 #[derive(MyDebug)] //` | 应编译失败但通过了 |
| concept\01_foundation\12_attributes_and_macros.md | 835 | compile_fail | `#[cfg(target_os = "linux")] fn platform_` | 应编译失败但通过了 |
| concept\01_foundation\13_panic_and_abort.md | 738 | compile_fail | `use std::panic::catch_unwind;  // Cargo.` | 应编译失败但通过了 |
| concept\01_foundation\14_coercion_and_casting.md | 755 | compile_fail | `trait A {} trait B: A {}  fn upcast(b: &` | 应编译失败但通过了 |
| concept\01_foundation\15_closure_basics.md | 747 | compile_fail | `fn main() {     let x = 5; // i32 实现 Cop` | 应编译失败但通过了 |
| concept\01_foundation\16_testing_basics.md | 744 | compile_fail | `#[test] #[should_panic(expected = "divid` | 应编译失败但通过了 |
| concept\01_foundation\17_collections_advanced.md | 974 | compile_fail | `use std::collections::HashSet;  #[derive` | 应编译失败但通过了 |
| concept\01_foundation\18_strings_and_encoding.md | 736 | compile_fail | `use std::ffi::OsStr;  fn main() {     le` | 应编译失败但通过了 |
| concept\01_foundation\18_strings_and_encoding.md | 778 | compile_fail | `fn main() {     let s = "你好";     // ❌ 运` | 应编译失败但通过了 |
| concept\01_foundation\18_strings_and_encoding.md | 791 | compile_fail | `fn main() {     let bytes = vec![0x80, 0` | 应编译失败但通过了 |
| concept\01_foundation\19_numerics.md | 639 | compile_fail | `use std::num::NonZeroU32;  fn main() {` | 应编译失败但通过了 |
| concept\01_foundation\19_numerics.md | 688 | compile_fail | `fn main() {     let a: f32 = 0.1;     le` | 应编译失败但通过了 |
| concept\01_foundation\20_variable_model.md | 393 | compile_fail | `struct Resource {     data: String, }  i` | 应编译失败但通过了 |
| concept\01_foundation\20_variable_model.md | 423 | compile_fail | `fn main() {     let x = 5;     let r = &` | 应编译失败但通过了 |
| concept\01_foundation\21_effects_and_purity.md | 333 | compile_fail | `// Rust 编译器阻止隐式副作用 fn implicit_side_effe` | 应编译失败但通过了 |
| concept\01_foundation\21_effects_and_purity.md | 372 | compile_fail | `const fn impure_const() -> i32 {     let` | 应编译失败但通过了 |
| concept\01_foundation\22_data_abstraction_spectrum.md | 515 | compile_fail | `struct ZeroSized;  fn main() {     // ❌` | 应编译失败但通过了 |
| concept\01_foundation\22_data_abstraction_spectrum.md | 531 | compile_fail | `use std::mem::ManuallyDrop;  fn main() {` | 应编译失败但通过了 |
| concept\02_intermediate\02_generics.md | 3138 | compile_fail | `trait Process<T = String> {     fn proce` | 应编译失败但通过了 |
| concept\02_intermediate\02_generics.md | 3157 | compile_fail | `struct Array<T, const N: usize> {     da` | 应编译失败但通过了 |
| concept\02_intermediate\02_generics.md | 3191 | compile_fail | `trait Displayable {     fn display(&self` | 应编译失败但通过了 |
| concept\02_intermediate\03_memory_management.md | 2338 | compile_fail | `fn main() {     let v = vec![1, 2, 3];` | 应编译失败但通过了 |
| concept\02_intermediate\03_memory_management.md | 2432 | compile_fail | `fn main() {     let s = Box::leak(Box::n` | 应编译失败但通过了 |
| concept\02_intermediate\03_memory_management.md | 2445 | compile_fail | `use std::rc::{Rc, Weak}; use std::cell::` | 应编译失败但通过了 |
| concept\02_intermediate\04_error_handling.md | 2961 | compile_fail | `const fn divide(a: i32, b: i32) -> i32 {` | 应编译失败但通过了 |
| concept\02_intermediate\04_error_handling.md | 2979 | compile_fail | `fn fallible_op() -> Result<i32, String>` | 应编译失败但通过了 |
| concept\02_intermediate\04_error_handling.md | 3060 | compile_fail | `const fn checked_div(a: i32, b: i32) ->` | 应编译失败但通过了 |
| concept\02_intermediate\05_assert_matches.md | 616 | compile_fail | `#[test] fn test_nested_match() {     let` | 应编译失败但通过了 |
| concept\02_intermediate\06_range_types.md | 530 | compile_fail | `fn main() {     let range = 0..;     //` | 应编译失败但通过了 |
| concept\02_intermediate\07_closure_types.md | 607 | compile_fail | `fn main() {     let f = match true {` | 应编译失败但通过了 |
| concept\02_intermediate\08_interior_mutability.md | 498 | compile_fail | `use std::sync::OnceLock;  fn main() {` | 应编译失败但通过了 |
| concept\02_intermediate\10_module_system.md | 625 | compile_fail | `mod inner {     pub fn func() {} }  mod` | 应编译失败但通过了 |
| concept\02_intermediate\11_cow_and_borrowed.md | 639 | compile_fail | `use std::borrow::Borrow;  fn main() {` | 应编译失败但通过了 |
| concept\02_intermediate\11_cow_and_borrowed.md | 664 | compile_fail | `use std::borrow::Cow;  struct MyStr<'a>` | 应编译失败但通过了 |
| concept\02_intermediate\11_cow_and_borrowed.md | 686 | compile_fail | `use std::borrow::Cow;  fn main() {     l` | 应编译失败但通过了 |
| concept\02_intermediate\12_smart_pointers.md | 486 | compile_fail | `use std::pin::Pin;  struct SelfReferenti` | 应编译失败但通过了 |
| concept\02_intermediate\12_smart_pointers.md | 507 | compile_fail | `use std::pin::Pin;  fn pin_mut_after_pin` | 应编译失败但通过了 |
| concept\02_intermediate\13_dsl_and_embedding.md | 746 | compile_fail | `macro_rules! recursive {     () => { 0 }` | 应编译失败但通过了 |
| concept\02_intermediate\13_dsl_and_embedding.md | 766 | compile_fail | `// 假设一个 SQL DSL: sql!(SELECT * FROM user` | 应编译失败但通过了 |
| concept\02_intermediate\14_newtype_and_wrapper.md | 524 | compile_fail | `struct Meters(u32);  fn add_distance(a:` | 应编译失败但通过了 |
| concept\02_intermediate\14_newtype_and_wrapper.md | 582 | compile_fail | `struct Meters(u32); struct Seconds(u32);` | 应编译失败但通过了 |
| concept\02_intermediate\14_newtype_and_wrapper.md | 599 | compile_fail | `use std::ops::Deref;  struct Wrapper(Str` | 应编译失败但通过了 |
| concept\02_intermediate\14_newtype_and_wrapper.md | 627 | compile_fail | `use std::ops::Deref;  struct Username(St` | 应编译失败但通过了 |
| concept\02_intermediate\15_error_handling_deep_dive.md | 598 | compile_fail | `fn outer() -> Result<Result<i32, String>` | 应编译失败但通过了 |
| concept\02_intermediate\15_iterator_patterns.md | 558 | compile_fail | `fn main() {     let keys = vec!["a", "b"` | 应编译失败但通过了 |
| concept\02_intermediate\15_iterator_patterns.md | 577 | compile_fail | `fn main() {     let data = vec![1, 2, 3]` | 应编译失败但通过了 |
| concept\02_intermediate\15_iterator_patterns.md | 595 | compile_fail | `fn main() {     let mut iter = vec![1, 2` | 应编译失败但通过了 |
| concept\02_intermediate\16_iterator_patterns.md | 588 | compile_fail | `fn main() {     let data = vec![vec![1,` | 应编译失败但通过了 |
| concept\02_intermediate\16_iterator_patterns.md | 637 | compile_fail | `fn main() {     let data = vec![String::` | 应编译失败但通过了 |
| concept\02_intermediate\16_iterator_patterns.md | 672 | compile_fail | `fn main() {     let v = vec![1, 2, 3, 4,` | 应编译失败但通过了 |
| concept\02_intermediate\17_macro_patterns.md | 603 | compile_fail | `macro_rules! ambiguous {     ($e:expr) =` | 应编译失败但通过了 |
| concept\02_intermediate\17_macro_patterns.md | 675 | compile_fail | `macro_rules! unsafe_op {     ($op:expr)` | 应编译失败但通过了 |
| concept\02_intermediate\18_lifetimes_advanced.md | 610 | compile_fail | `fn call_with_ref<F>(f: F) where     F: F` | 应编译失败但通过了 |
| concept\02_intermediate\19_advanced_traits.md | 572 | compile_fail | `#![feature(specialization)] // 不稳定特性  tr` | 应编译失败但通过了 |
| concept\02_intermediate\19_advanced_traits.md | 614 | compile_fail | `trait MyTrait: Clone + Send + Sync + 'st` | 应编译失败但通过了 |
| concept\02_intermediate\20_type_system_advanced.md | 607 | compile_fail | `// 错误: impl Trait 在 trait 定义中使用 trait My` | 应编译失败但通过了 |
| concept\02_intermediate\20_type_system_advanced.md | 651 | compile_fail | `fn apply<F>(f: F) where     F: Fn(&i32)` | 应编译失败但通过了 |
| concept\02_intermediate\21_metaprogramming.md | 707 | compile_fail | `use std::any::{Any, TypeId};  fn main()` | 应编译失败但通过了 |
| concept\02_intermediate\22_iterator_patterns.md | 484 | compile_fail | `fn main() {     let v = vec![1, 2, 3];` | 应编译失败但通过了 |
| concept\02_intermediate\22_iterator_patterns.md | 527 | compile_fail | `fn main() {     let data = vec![1, 2, 3]` | 应编译失败但通过了 |
| concept\02_intermediate\22_iterator_patterns.md | 548 | compile_fail | `fn main() {     let mut iter = vec![1, 2` | 应编译失败但通过了 |
| concept\03_advanced\02_async.md | 3785 | compile_fail | `use std::rc::Rc;  async fn bad_async() {` | 应编译失败但通过了 |
| concept\03_advanced\02_async.md | 3851 | compile_fail | `async fn borrow_lifetime_issue() {     l` | 应编译失败但通过了 |
| concept\03_advanced\02_async_advanced.md | 1265 | compile_fail | `use std::pin::Pin;  struct SelfRef {` | 应编译失败但通过了 |
| concept\03_advanced\02_async_patterns.md | 389 | compile_fail | `trait AsyncService {     async fn proces` | 应编译失败但通过了 |
| concept\03_advanced\02_async_patterns.md | 431 | compile_fail | `use std::future::Future; use std::pin::P` | 应编译失败但通过了 |
| concept\03_advanced\03_unsafe.md | 3337 | compile_fail | `fn main() {     let ptr: *const i32 = st` | 应编译失败但通过了 |
| concept\03_advanced\05_rust_ffi.md | 428 | compile_fail | `#[repr(C)] struct RustStruct {     data:` | 应编译失败但通过了 |
| concept\03_advanced\05_rust_ffi.md | 443 | compile_fail | `use std::panic::catch_unwind;  // 错误: pa` | 应编译失败但通过了 |
| concept\03_advanced\06_pin_unpin.md | 449 | compile_fail | `use std::pin::Pin;  fn pin_project_misus` | 应编译失败但通过了 |
| concept\03_advanced\08_nll_and_polonius.md | 465 | compile_fail | `fn nll_scope_limitation() {     let mut` | 应编译失败但通过了 |
| concept\03_advanced\08_nll_and_polonius.md | 478 | compile_fail | `fn polonius_dataflow() {     let mut x =` | 应编译失败但通过了 |
| concept\03_advanced\08_nll_and_polonius.md | 492 | compile_fail | `fn drop_order_nll() {     let mut data =` | 应编译失败但通过了 |
| concept\03_advanced\08_nll_and_polonius.md | 702 | compile_fail | `fn main() {     let mut x = 0;     let r` | 应编译失败但通过了 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 594 | compile_fail | `use std::sync::atomic::{AtomicPtr, Order` | 应编译失败但通过了 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 879 | compile_fail | `use std::sync::atomic::{AtomicPtr, Order` | 应编译失败但通过了 |
| concept\03_advanced\12_unsafe_rust_patterns.md | 784 | compile_fail | `use std::pin::Pin;  struct SelfRef {` | 应编译失败但通过了 |
| concept\03_advanced\12_unsafe_rust_patterns.md | 835 | compile_fail | `fn main() {     let x = String::from("he` | 应编译失败但通过了 |
| concept\03_advanced\14_custom_allocators.md | 704 | compile_fail | `use std::alloc::System;  #[global_alloca` | 应编译失败但通过了 |
| concept\03_advanced\14_custom_allocators.md | 742 | compile_fail | `use std::alloc::{alloc, dealloc, Layout}` | 应编译失败但通过了 |
| concept\03_advanced\15_zero_copy_parsing.md | 571 | compile_fail | `fn get_header(data: &[u8]) -> &[u8] {` | 应编译失败但通过了 |
| concept\03_advanced\15_zero_copy_parsing.md | 724 | compile_fail | `fn main() {     let bytes = [0x12u8, 0x3` | 应编译失败但通过了 |
| concept\03_advanced\15_zero_copy_parsing.md | 738 | compile_fail | `fn parse<'a>(input: &'a [u8]) -> &'a str` | 应编译失败但通过了 |
| concept\03_advanced\16_lock_free.md | 522 | compile_fail | `use std::sync::atomic::{AtomicPtr, Order` | 应编译失败但通过了 |
| concept\03_advanced\16_lock_free.md | 537 | compile_fail | `use std::sync::atomic::{AtomicUsize, Ord` | 应编译失败但通过了 |
| concept\03_advanced\16_lock_free.md | 795 | compile_fail | `use std::sync::atomic::{AtomicPtr, Order` | 应编译失败但通过了 |
| concept\03_advanced\17_type_erasure.md | 779 | compile_fail | `use std::any::Any;  fn main() {     let` | 应编译失败但通过了 |
| concept\03_advanced\17_type_erasure.md | 794 | compile_fail | `trait Processor {     fn process<T: Defa` | 应编译失败但通过了 |
| concept\03_advanced\20_stream_processing_semantics.md | 462 | compile_fail | `use std::collections::HashMap; use std::` | 应编译失败但通过了 |
| concept\04_formal\01_linear_logic.md | 1262 | compile_fail | `fn branch(use_a: bool) {     let x = Str` | 应编译失败但通过了 |
| concept\04_formal\01_linear_logic.md | 1282 | compile_fail | `fn diverges() -> ! {     panic!("never r` | 应编译失败但通过了 |
| concept\04_formal\02_type_theory.md | 1335 | compile_fail | `fn array_len<T, const N: usize>(arr: &[T` | 应编译失败但通过了 |
| concept\04_formal\03_ownership_formal.md | 1761 | compile_fail | `struct LinearResource;  impl Drop for Li` | 应编译失败但通过了 |
| concept\04_formal\03_ownership_formal.md | 1787 | compile_fail | `use std::cell::RefCell;  fn main() {` | 应编译失败但通过了 |
| concept\04_formal\04_rustbelt.md | 1195 | compile_fail | `fn main() {     let mut v = vec![1, 2, 3` | 应编译失败但通过了 |
| concept\04_formal\04_rustbelt.md | 1227 | compile_fail | `struct Resource; impl Drop for Resource` | 应编译失败但通过了 |
| concept\04_formal\04_rustbelt.md | 1286 | compile_fail | `use std::mem;  struct Guard; impl Drop f` | 应编译失败但通过了 |
| concept\04_formal\05_verification_toolchain.md | 982 | compile_fail | `use std::rc::Rc;  struct MyData(Rc<i32>)` | 应编译失败但通过了 |
| concept\04_formal\06_subtype_variance.md | 579 | compile_fail | `fn takes_str(_: &str) {}  fn main() {` | 应编译失败但通过了 |
| concept\04_formal\06_subtype_variance.md | 598 | compile_fail | `use std::cell::UnsafeCell;  fn main() {` | 应编译失败但通过了 |
| concept\04_formal\07_separation_logic.md | 706 | compile_fail | `use std::sync::atomic::{AtomicUsize, Ord` | 应编译失败但通过了 |
| concept\04_formal\08_type_inference.md | 198 | compile_fail | `fn main() {     let closure = \|x\| x + 1;` | 应编译失败但通过了 |
| concept\04_formal\08_type_inference.md | 644 | compile_fail | `trait Container {     type Item;     fn` | 应编译失败但通过了 |
| concept\04_formal\09_linear_logic_applications.md | 754 | compile_fail | `struct Resource {     name: String, }  i` | 应编译失败但通过了 |
| concept\04_formal\09_operational_semantics.md | 1125 | compile_fail | `const fn slow(n: usize) -> usize {     l` | 应编译失败但通过了 |
| concept\04_formal\10_category_theory.md | 274 | compile_fail | `fn main() {     let v = vec![String::fro` | 应编译失败但通过了 |
| concept\04_formal\10_category_theory.md | 712 | compile_fail | `fn map_both<A, B, F>(a: Option<A>, b: Op` | 应编译失败但通过了 |
| concept\04_formal\10_category_theory.md | 733 | compile_fail | `fn monadic_bind() -> Result<i32, String>` | 应编译失败但通过了 |
| concept\04_formal\11_separation_logic.md | 690 | compile_fail | `fn swap(a: &mut i32, b: &mut i32) {` | 应编译失败但通过了 |
| concept\04_formal\12_denotational_semantics.md | 159 | compile_fail | `fn main() {     // ❌ 编译错误:`loop {}`的类型` | 应编译失败但通过了 |
| concept\04_formal\12_denotational_semantics.md | 181 | compile_fail | `fn may_fail() -> Result<i32, String> {` | 应编译失败但通过了 |
| concept\04_formal\12_denotational_semantics.md | 554 | compile_fail | `fn diverges() -> ! {     loop {} }  fn m` | 应编译失败但通过了 |
| concept\04_formal\12_denotational_semantics.md | 572 | compile_fail | `fn main() {     let mut x = 42;     let` | 应编译失败但通过了 |
| concept\04_formal\14_lambda_calculus.md | 660 | compile_fail | `fn make_adder(x: i32) -> impl Fn(i32) ->` | 应编译失败但通过了 |
| concept\04_formal\15_hoare_logic.md | 693 | compile_fail | `fn divide(a: i32, b: i32) -> i32 {     /` | 应编译失败但通过了 |
| concept\04_formal\15_hoare_logic.md | 749 | compile_fail | `// 假设 weakest precondition 计算 fn abs(x:` | 应编译失败但通过了 |
| concept\04_formal\15_hoare_logic.md | 764 | compile_fail | `fn gcd(a: u32, b: u32) -> u32 {     let` | 应编译失败但通过了 |
| concept\04_formal\16_aerospace_certification_formal_methods.md | 1208 | compile_fail | `fn decision(a: bool, b: bool, c: bool) -` | 应编译失败但通过了 |
| concept\04_formal\17_operational_semantics.md | 1079 | compile_fail | `fn main() {     let mut x = 0;     let r` | 应编译失败但通过了 |
| concept\04_formal\17_operational_semantics.md | 1098 | compile_fail | `fn main() {     let mut x = 0;     // ❌` | 应编译失败但通过了 |
| concept\04_formal\18_evaluation_strategies.md | 392 | compile_fail | `fn main() {     let v = vec![1, 2, 3];` | 应编译失败但通过了 |
| concept\04_formal\18_evaluation_strategies.md | 413 | compile_fail | `fn main() {     let v = vec![1, 2, 3];` | 应编译失败但通过了 |
| concept\05_comparative\01_rust_vs_cpp.md | 2688 | compile_fail | `trait A { fn method(&self); } trait B: A` | 应编译失败但通过了 |
| concept\05_comparative\02_cpp_abi_object_model.md | 653 | compile_fail | `struct Outer {     inner1: Inner,     in` | 应编译失败但通过了 |
| concept\05_comparative\02_rust_vs_go.md | 1011 | compile_fail | `trait Reader {     fn read(&mut self, bu` | 应编译失败但通过了 |
| concept\05_comparative\02_rust_vs_go.md | 1042 | compile_fail | `fn main() {     // ❌ 编译错误:`Option<&str>` | 应编译失败但通过了 |
| concept\05_comparative\02_rust_vs_go.md | 1064 | compile_fail | `// Go: 隐式实现接口（struct 有方法即实现接口） // type R` | 应编译失败但通过了 |
| concept\05_comparative\02_rust_vs_go.md | 1096 | compile_fail | `// Go: interface 值可为 nil，但 nil interface` | 应编译失败但通过了 |
| concept\05_comparative\03_paradigm_matrix.md | 985 | compile_fail | `fn main() {     let mut sum = 0;     let` | 应编译失败但通过了 |
| concept\05_comparative\03_paradigm_matrix.md | 1009 | compile_fail | `mod inner {     pub struct Config {` | 应编译失败但通过了 |
| concept\05_comparative\03_paradigm_matrix.md | 1064 | compile_fail | `fn functional_style(data: Vec<i32>) -> V` | 应编译失败但通过了 |
| concept\05_comparative\04_safety_boundaries.md | 1177 | compile_fail | `fn bad_unsafe() {     let mut x = 5;` | 应编译失败但通过了 |
| concept\05_comparative\05_execution_model_isomorphism.md | 875 | compile_fail | `async fn async_task() {     // ❌ 编译错误: a` | 应编译失败但通过了 |
| concept\05_comparative\05_execution_model_isomorphism.md | 900 | compile_fail | `// 假设使用 green-thread 库（如 early Rust 的 li` | 应编译失败但通过了 |
| concept\05_comparative\05_execution_model_isomorphism.md | 916 | compile_fail | `fn cps_style<F>(x: i32, cont: F) -> Resu` | 应编译失败但通过了 |
| concept\05_comparative\05_execution_model_isomorphism.md | 939 | compile_fail | `fn cps_factorial(n: u64, k: Box<dyn Fn(u` | 应编译失败但通过了 |
| concept\05_comparative\06_rust_vs_java.md | 513 | compile_fail | `// Java: List<String> 和 List<Integer> 运行` | 应编译失败但通过了 |
| concept\05_comparative\06_rust_vs_java.md | 536 | compile_fail | `struct FileHandle {     path: String, }` | 应编译失败但通过了 |
| concept\05_comparative\07_rust_vs_python.md | 581 | compile_fail | `fn main() {     let x = 42;     // ❌ 编译错` | 应编译失败但通过了 |
| concept\05_comparative\07_rust_vs_python.md | 607 | compile_fail | `fn main() {     let x = 42;     // ❌ 编译错` | 应编译失败但通过了 |
| concept\05_comparative\07_rust_vs_python.md | 660 | compile_fail | `use std::sync::{Arc, Mutex}; use std::th` | 应编译失败但通过了 |
| concept\05_comparative\08_rust_vs_javascript.md | 693 | compile_fail | `fn main() {     let x = "5";     // ❌ 编译` | 应编译失败但通过了 |
| concept\05_comparative\08_rust_vs_ruby.md | 718 | compile_fail | `trait Greet {     fn greet(&self); }  //` | 应编译失败但通过了 |
| concept\05_comparative\08_rust_vs_ruby.md | 736 | compile_fail | `trait Quacks {     fn quack(&self); }  s` | 应编译失败但通过了 |
| concept\05_comparative\08_rust_vs_ruby.md | 764 | compile_fail | `// Ruby: 可随时为任何类添加方法 // class String //` | 应编译失败但通过了 |
| concept\05_comparative\09_rust_vs_swift.md | 752 | compile_fail | `fn main() {     let opt: Option<Option<i` | 应编译失败但通过了 |
| concept\05_comparative\10_rust_vs_zig.md | 766 | compile_fail | `fn main() {     let s = String::from("he` | 应编译失败但通过了 |
| concept\05_comparative\10_rust_vs_zig.md | 787 | compile_fail | `const fn factorial(n: u32) -> u32 {` | 应编译失败但通过了 |
| concept\05_comparative\10_rust_vs_zig.md | 810 | compile_fail | `fn main() {     // Rust: Vec 使用全局分配器，隐式` | 应编译失败但通过了 |
| concept\05_comparative\11_rust_vs_kotlin.md | 784 | compile_fail | `struct User {     name: String,     age:` | 应编译失败但通过了 |
| concept\05_comparative\11_rust_vs_kotlin.md | 845 | compile_fail | `fn main() {     let s: Option<String> =` | 应编译失败但通过了 |
| concept\05_comparative\12_rust_vs_scala.md | 728 | compile_fail | `trait ToJson {     fn to_json(&self) ->` | 应编译失败但通过了 |
| concept\05_comparative\12_rust_vs_scala.md | 757 | compile_fail | `fn main() {     // ❌ 编译错误: Rust 没有 null` | 应编译失败但通过了 |
| concept\05_comparative\12_rust_vs_scala.md | 778 | compile_fail | `struct Meters(u32); struct Kilometers(u3` | 应编译失败但通过了 |
| concept\05_comparative\13_rust_vs_csharp.md | 813 | compile_fail | `fn main() {     let data = vec![1, 2, 3]` | 应编译失败但通过了 |
| concept\05_comparative\13_rust_vs_csharp.md | 852 | compile_fail | `// C#: [Serializable] 是运行时反射标记 // [Seria` | 应编译失败但通过了 |
| concept\05_comparative\14_rust_vs_elixir.md | 813 | compile_fail | `fn main() {     let x = 42;     // ❌ 编译错` | 应编译失败但通过了 |
| concept\05_comparative\14_rust_vs_elixir.md | 839 | compile_fail | `fn main() {     let x = 42;     // ❌ 编译错` | 应编译失败但通过了 |
| concept\05_comparative\14_rust_vs_elixir.md | 862 | compile_fail | `use std::sync::mpsc;  fn main() {     le` | 应编译失败但通过了 |
| concept\05_comparative\14_rust_vs_elixir.md | 891 | compile_fail | `use std::sync::Arc; use std::thread;  fn` | 应编译失败但通过了 |
| concept\05_comparative\15_rust_vs_typescript.md | 760 | compile_fail | `fn main() {     // ❌ 编译错误: Rust 没有 any 类` | 应编译失败但通过了 |
| concept\05_comparative\15_rust_vs_typescript.md | 809 | compile_fail | `struct Point {     x: i32,     y: i32, }` | 应编译失败但通过了 |
| concept\05_comparative\15_rust_vs_typescript.md | 841 | compile_fail | `fn main() {     // TypeScript: any 绕过所有类` | 应编译失败但通过了 |
| concept\05_comparative\16_rust_vs_ruby.md | 698 | compile_fail | `trait Greet {     fn greet(&self); }  //` | 应编译失败但通过了 |
| concept\05_comparative\16_rust_vs_ruby.md | 716 | compile_fail | `fn main() {     // ❌ 编译错误: Rust 没有 metho` | 应编译失败但通过了 |
| concept\05_comparative\16_rust_vs_ruby.md | 746 | compile_fail | `// Ruby: 运行时元编程 // class Foo //   define` | 应编译失败但通过了 |
| concept\06_ecosystem\01_toolchain.md | 1786 | compile_fail | `// Rust 2015 Edition extern crate std;` | 应编译失败但通过了 |
| concept\06_ecosystem\01_toolchain.md | 1800 | compile_fail | `// Cargo.toml (workspace root) // [works` | 应编译失败但通过了 |
| concept\06_ecosystem\01_toolchain.md | 1820 | compile_fail | `// Cargo.toml // [profile.release] // lt` | 应编译失败但通过了 |
| concept\06_ecosystem\03_idioms_spectrum.md | 1560 | compile_fail | `fn main() {     let s = String::from("he` | 应编译失败但通过了 |
| concept\06_ecosystem\03_idioms_spectrum.md | 1625 | compile_fail | `use std::mem;  fn main() {     let mut s` | 应编译失败但通过了 |
| concept\06_ecosystem\04_application_domains.md | 1656 | compile_fail | `use std::rc::Rc;  struct AppState {` | 应编译失败但通过了 |
| concept\06_ecosystem\04_application_domains.md | 1681 | compile_fail | `struct Position { x: f32, y: f32 } struc` | 应编译失败但通过了 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 539 | compile_fail | `// #[requires(x > 0)] // Prusti 前置条件 fn` | 应编译失败但通过了 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 561 | compile_fail | `fn sum(n: u32) -> u32 {     let mut tota` | 应编译失败但通过了 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 599 | compile_fail | `// crate-a: 经过形式化验证，无 unsafe // crate-b:` | 应编译失败但通过了 |
| concept\06_ecosystem\05_system_design_principles.md | 676 | compile_fail | `trait Handler {     fn handle(&self, req` | 应编译失败但通过了 |
| concept\06_ecosystem\05_system_design_principles.md | 697 | compile_fail | `trait Repository {     fn find(&self, id` | 应编译失败但通过了 |
| concept\06_ecosystem\05_system_design_principles.md | 718 | compile_fail | `struct HttpRequest<State> {     url: Str` | 应编译失败但通过了 |
| concept\06_ecosystem\06_blockchain.md | 794 | compile_fail | `struct Contract {     balance: u64, }  i` | 应编译失败但通过了 |
| concept\06_ecosystem\08_wasi.md | 448 | compile_fail | `// 错误：尝试访问未被授予能力的资源 // WASI 能力安全模型在运行时拒绝` | 应编译失败但通过了 |
| concept\06_ecosystem\08_wasi.md | 466 | compile_fail | `// 错误：组件 A 导出 i32，组件 B 期望 s64 // 组件组合时的类` | 应编译失败但通过了 |
| concept\06_ecosystem\08_wasi.md | 573 | compile_fail | `use std::fs::File; use std::io::Read;  f` | 应编译失败但通过了 |
| concept\06_ecosystem\10_public_private_deps.md | 442 | compile_fail | `// crate A v1.0.0 pub fn old_api() {}  /` | 应编译失败但通过了 |
| concept\06_ecosystem\10_public_private_deps.md | 482 | compile_fail | `// Crate A 依赖 tokio = { version = "1", f` | 应编译失败但通过了 |
| concept\06_ecosystem\10_public_private_deps.md | 496 | compile_fail | `// Crate A 的 Cargo.toml // [dependencies` | 应编译失败但通过了 |
| concept\06_ecosystem\12_testing_strategies.md | 615 | compile_fail | `#[test] async fn async_test() {     // ❌` | 应编译失败但通过了 |
| concept\06_ecosystem\12_testing_strategies.md | 638 | compile_fail | `static mut COUNTER: i32 = 0;  #[test] fn` | 应编译失败但通过了 |
| concept\06_ecosystem\15_performance_optimization.md | 702 | compile_fail | `use std::arch::asm;  fn main() {     let` | 应编译失败但通过了 |
| concept\06_ecosystem\15_performance_optimization.md | 723 | compile_fail | `#[inline(always)] fn huge_function() ->` | 应编译失败但通过了 |
| concept\06_ecosystem\15_performance_optimization.md | 740 | compile_fail | `#[inline(always)] fn tiny_helper(x: i32)` | 应编译失败但通过了 |
| concept\06_ecosystem\16_testing.md | 606 | compile_fail | `#[test] fn broken_test() {     // ❌ 编译错误` | 应编译失败但通过了 |
| concept\06_ecosystem\16_testing.md | 618 | compile_fail | `#[cfg(test)] mod tests {     use super::` | 应编译失败但通过了 |
| concept\06_ecosystem\16_testing.md | 648 | compile_fail | `#[cfg(test)] mod tests {     #[test]` | 应编译失败但通过了 |
| concept\06_ecosystem\16_testing.md | 668 | compile_fail | `/// ```no_run /// let x = 1 / 0; // 运行时` | 应编译失败但通过了 |
| concept\06_ecosystem\17_cross_compilation.md | 663 | compile_fail | `// 目标: aarch64-unknown-linux-gnu // 但系统未` | 应编译失败但通过了 |
| concept\06_ecosystem\18_distributed_systems.md | 638 | compile_fail | `use std::time::{SystemTime, Duration};` | 应编译失败但通过了 |
| concept\06_ecosystem\18_distributed_systems.md | 659 | compile_fail | `// 概念代码: Raft 节点在分区时的投票冲突 struct RaftNod` | 应编译失败但通过了 |
| concept\06_ecosystem\19_security_practices.md | 625 | compile_fail | `// Cargo.toml // [dependencies] // serde` | 应编译失败但通过了 |
| concept\06_ecosystem\19_security_practices.md | 641 | compile_fail | `fn main() {     let password = String::f` | 应编译失败但通过了 |
| concept\06_ecosystem\20_licensing_and_compliance.md | 647 | compile_fail | `// Cargo.toml 依赖链引入 GPL 代码  // [dependen` | 应编译失败但通过了 |
| concept\06_ecosystem\20_licensing_and_compliance.md | 682 | compile_fail | `// 假设 proprietary 项目依赖 GPL-3.0 库  // [de` | 应编译失败但通过了 |
| concept\06_ecosystem\20_licensing_and_compliance.md | 699 | compile_fail | `// ❌ 法律风险: 静态链接 GPL 库可能使整个项目变为 GPL // [d` | 应编译失败但通过了 |
| concept\06_ecosystem\21_game_development.md | 677 | compile_fail | `use std::time::{Duration, Instant};  fn` | 应编译失败但通过了 |
| concept\06_ecosystem\24_cloud_native.md | 655 | compile_fail | `// 假设同时依赖 tokio 和 async-std  async fn ta` | 应编译失败但通过了 |
| concept\06_ecosystem\25_cli_development.md | 638 | compile_fail | `fn main() {     // ❌ 运行时问题: 若未检查终端能力，在管道` | 应编译失败但通过了 |
| concept\06_ecosystem\25_cli_development.md | 654 | compile_fail | `fn main() {     // ❌ 运行时显示异常: 纯 ANSI 转义序` | 应编译失败但通过了 |
| concept\06_ecosystem\26_game_development.md | 669 | compile_fail | `// 假设使用 bevy_ecs 风格 API  struct Position` | 应编译失败但通过了 |
| concept\06_ecosystem\26_game_development.md | 690 | compile_fail | `use std::thread;  struct Renderer {` | 应编译失败但通过了 |
| concept\06_ecosystem\26_game_development.md | 732 | compile_fail | `// 概念代码: Bevy ECS 的 archetype 变更 // ❌ 运行` | 应编译失败但通过了 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 738 | compile_fail | `// Cargo.toml 中无特别配置  fn main() {     //` | 应编译失败但通过了 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 753 | compile_fail | `static mut COUNTER: i32 = 0;  #[test] fn` | 应编译失败但通过了 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1109 | compile_fail | `fn main() {     let mut data = vec![3, 1` | 应编译失败但通过了 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1126 | compile_fail | `fn main() {     // ❌ 编译错误/链接错误: 栈数组太大（可能` | 应编译失败但通过了 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1138 | compile_fail | `fn main() {     let mut v = vec![3, 1, 4` | 应编译失败但通过了 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1159 | compile_fail | `use std::collections::BinaryHeap;  fn ma` | 应编译失败但通过了 |
| concept\06_ecosystem\30_system_composability.md | 876 | compile_fail | `trait A { fn method(&self); } trait B: A` | 应编译失败但通过了 |
| concept\06_ecosystem\30_system_composability.md | 903 | compile_fail | `struct Engine {     horsepower: u32, }` | 应编译失败但通过了 |
| concept\06_ecosystem\31_microservice_patterns.md | 974 | compile_fail | `trait Service {     fn handle(&self, req` | 应编译失败但通过了 |
| concept\06_ecosystem\31_microservice_patterns.md | 998 | compile_fail | `// 概念代码: 断路器半开状态的问题 enum CircuitState {` | 应编译失败但通过了 |
| concept\06_ecosystem\32_event_driven_architecture.md | 1047 | compile_fail | `use std::any::Any;  struct EventBus {` | 应编译失败但通过了 |
| concept\06_ecosystem\32_event_driven_architecture.md | 1073 | compile_fail | `struct EventSystem<'a> {     listeners:` | 应编译失败但通过了 |
| concept\06_ecosystem\33_idioms_spectrum.md | 1554 | compile_fail | `fn critical_function() -> i32 {     // ❌` | 应编译失败但通过了 |
| concept\06_ecosystem\33_idioms_spectrum.md | 1569 | compile_fail | `use std::ops::Deref;  struct Wrapper(Str` | 应编译失败但通过了 |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 539 | compile_fail | `pub struct SafeVec<T> {     inner: Vec<T` | 应编译失败但通过了 |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 587 | compile_fail | `// 规格（Prusti 注解）: // #[requires(n >= 0)]` | 应编译失败但通过了 |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 397 | compile_fail | `// 错误: Singleton 隐藏依赖，与 DI 哲学冲突 struct L` | 应编译失败但通过了 |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 427 | compile_fail | `use std::rc::Rc; use std::cell::RefCell;` | 应编译失败但通过了 |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 576 | compile_fail | `struct Wrapper<T>(T);  fn main() {     l` | 应编译失败但通过了 |
| concept\06_ecosystem\39_os_kernel.md | 247 | compile_fail | `const fn kernel_init(value: usize) -> us` | 应编译失败但通过了 |
| concept\07_future\01_ai_integration.md | 677 | compile_fail | `// AI 可能生成"编译通过但逻辑错误"的代码 // 反例：错误地实现了二分查` | 应编译失败但通过了 |
| concept\07_future\01_ai_integration.md | 843 | compile_fail | `// AI 生成的代码可能包含微妙的 unsafe 错误 fn ai_gener` | 应编译失败但通过了 |
| concept\07_future\02_formal_methods.md | 1965 | compile_fail | `// 规格: fn add(a: u32, b: u32) -> u32 { a` | 应编译失败但通过了 |
| concept\07_future\02_formal_methods.md | 1982 | compile_fail | `// 假设项目使用 nightly-2024-01-01 的 Miri // 但` | 应编译失败但通过了 |
| concept\07_future\03_evolution.md | 1496 | compile_fail | `fn array_size<const N: usize>(arr: [i32;` | 应编译失败但通过了 |
| concept\07_future\03_evolution.md | 1544 | compile_fail | `fn main() {     let opt = Some(5);     /` | 应编译失败但通过了 |
| concept\07_future\04_effects_system.md | 527 | compile_fail | `use std::sync::Mutex;  async fn bad_mute` | 应编译失败但通过了 |
| concept\07_future\04_effects_system.md | 574 | compile_fail | `async fn bad_capture(data: &mut Vec<i32>` | 应编译失败但通过了 |
| concept\07_future\05_rust_version_tracking.md | 798 | compile_fail | `#![feature(generic_const_exprs)]  fn mak` | 应编译失败但通过了 |
| concept\07_future\05_rust_version_tracking.md | 818 | compile_fail | `// Edition 2021 代码 fn main() {     let a` | 应编译失败但通过了 |
| concept\07_future\05_rust_version_tracking.md | 837 | compile_fail | `// Cargo.toml // [package] // rust-versi` | 应编译失败但通过了 |
| concept\07_future\07_mcdc_coverage_preview.md | 378 | compile_fail | `fn decide(a: bool, b: bool, c: bool) ->` | 应编译失败但通过了 |
| concept\07_future\07_mcdc_coverage_preview.md | 403 | compile_fail | `// Cargo.toml // [profile.dev] // debug` | 应编译失败但通过了 |
| concept\07_future\07_mcdc_coverage_preview.md | 424 | compile_fail | `fn complex_decision(a: bool, b: bool, c:` | 应编译失败但通过了 |
| concept\07_future\07_mcdc_coverage_preview.md | 446 | compile_fail | `#[inline(always)] fn hot_path(x: i32) ->` | 应编译失败但通过了 |
| concept\07_future\09_parallel_frontend_preview.md | 425 | compile_fail | `macro_rules! counter {     () => {` | 应编译失败但通过了 |
| concept\07_future\09_parallel_frontend_preview.md | 449 | compile_fail | `// build.rs 生成代码到 OUT_DIR/generated.rs /` | 应编译失败但通过了 |
| concept\07_future\09_parallel_frontend_preview.md | 466 | compile_fail | `// build.rs use std::process::Command;` | 应编译失败但通过了 |
| concept\07_future\09_parallel_frontend_preview.md | 482 | compile_fail | `macro_rules! count {     () => { 0 };` | 应编译失败但通过了 |
| concept\07_future\12_return_type_notation_preview.md | 492 | compile_fail | `trait Processor {     fn process(&self)` | 应编译失败但通过了 |
| concept\07_future\16_cranelift_backend_preview.md | 502 | compile_fail | `#[cfg(target_arch = "x86_64")] use std::` | 应编译失败但通过了 |
| concept\07_future\16_cranelift_backend_preview.md | 521 | compile_fail | `fn main() {     let x = 42;     // ⚠️ 调试` | 应编译失败但通过了 |
| concept\07_future\17_rust_specification_preview.md | 501 | compile_fail | `fn main() {     let mut x = 0;     let r` | 应编译失败但通过了 |
| concept\07_future\17_rust_specification_preview.md | 538 | compile_fail | `fn main() {     let mut x = 0;     let r` | 应编译失败但通过了 |
| concept\07_future\17_rust_specification_preview.md | 557 | compile_fail | `// ❌ 潜在不一致: Rust 规范草案定义的行为与 rustc 实际实现可能` | 应编译失败但通过了 |
| concept\07_future\20_borrowsanitizer_preview.md | 442 | compile_fail | `fn main() {     let mut x = [0i32; 4];` | 应编译失败但通过了 |
| concept\07_future\20_borrowsanitizer_preview.md | 499 | compile_fail | `fn main() {     let mut x = [0i32; 4];` | 应编译失败但通过了 |
| concept\07_future\20_borrowsanitizer_preview.md | 519 | compile_fail | `// ❌ 检测盲区: BorrowSanitizer（运行时）与 Miri（解释` | 应编译失败但通过了 |
| concept\07_future\21_rust_in_ai.md | 628 | compile_fail | `// 假设使用 candle-core  fn matmul_incompati` | 应编译失败但通过了 |
| concept\07_future\21_rust_in_ai.md | 643 | compile_fail | `#[cfg(target_arch = "x86_64")] use std::` | 应编译失败但通过了 |
| concept\07_future\22_edition_guide.md | 652 | compile_fail | `// 迁移前 (Edition 2021) fn main() {     le` | 应编译失败但通过了 |
| concept\07_future\22_edition_guide.md | 670 | compile_fail | `// Rust 2018 → 2021 迁移中，cargo fix 无法处理所有` | 应编译失败但通过了 |
| concept\07_future\23_rust_edition_guide.md | 522 | compile_fail | `// Edition 2021 宏 macro_rules! old_macro` | 应编译失败但通过了 |
| concept\07_future\23_rust_edition_guide.md | 561 | compile_fail | `// Workspace Cargo.toml // [workspace] /` | 应编译失败但通过了 |
| concept\07_future\24_roadmap.md | 988 | compile_fail | `fn always_panic() -> ! {     panic!("nev` | 应编译失败但通过了 |
| concept\07_future\24_roadmap.md | 1033 | compile_fail | `fn make_iter() -> impl Iterator<Item = i` | 应编译失败但通过了 |
| concept\07_future\24_roadmap.md | 1052 | compile_fail | `// ❌ 规划风险: 依赖 nightly 特性的项目面临稳定化时间表不确定 #` | 应编译失败但通过了 |
| concept\07_future\27_compile_time_execution.md | 705 | compile_fail | `const fn compute_area(r: f64) -> f64 {` | 应编译失败但通过了 |
| concept\07_future\29_ebpf_rust.md | 974 | compile_fail | `// eBPF 程序 (kernel space) #[repr(C)] str` | 应编译失败但通过了 |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 192 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 462 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 514 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 97 | normal | `async fn foo() -> i32 { 42 } // 等价于: fn` |
| concept\00_meta\quick_reference.md | 171 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 226 | normal | `enum Option<T> { None, Some(T) } enum Re` |
| concept\00_meta\quick_reference.md | 291 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 305 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 339 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 373 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 398 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 417 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 433 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 457 | normal | `let x: Option<i32> = Some(5); let y = x.` |
| concept\00_meta\quick_reference.md | 617 | normal | `let mut v = vec![1, 2, 3]; v.push(4);` |
| concept\00_meta\self_assessment.md | 178 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 234 | normal | `trait Drawable {     fn draw(&self);` |
| concept\00_meta\self_assessment.md | 272 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 289 | normal | `struct A(&'static str); impl Drop for A` |
| concept\00_meta\self_assessment.md | 318 | normal | `fn identity<T>(x: T) -> T { x } let a =` |
