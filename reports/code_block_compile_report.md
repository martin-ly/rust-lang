# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-05-13
> 扫描文件数: 37

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 161 |
| 编译通过 | 125 |
| 编译失败 | 36 |
| 跳过 (ignore/no_run) | 13 |
| 通过率 | 77.6% |

## 编译失败的代码块

| 文件 | 行号 | 模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|
| concept\00_meta\quick_reference.md | 152 | normal | `fn read_file(path: &str) -> Result<Strin` | error[E0433]: cannot find module or crate `io` in this scope  --> target\tmp\cod |
| concept\00_meta\quick_reference.md | 171 | normal | `trait Future {     type Output;     fn p` | error[E0425]: cannot find type `Pin` in this scope  --> target\tmp\code_block_te |
| concept\00_meta\quick_reference.md | 488 | normal | `struct Door<State> { _marker: PhantomDat` | error: unexpected token: `...`  --> target\tmp\code_block_tests\quick_reference_ |
| concept\00_meta\quick_reference.md | 505 | normal | `unsafe {     let raw_ptr = &mut x as *mu` | error[E0425]: cannot find value `x` in this scope  --> target\tmp\code_block_tes |
| concept\00_meta\self_assessment.md | 396 | normal | `async fn fetch_and_update(data: &Mutex<i` | error[E0425]: cannot find type `Mutex` in this scope  --> target\tmp\code_block_ |
| concept\00_meta\self_assessment.md | 429 | normal | `let a = Mutex::new(0); let b = Mutex::ne` | error[E0433]: cannot find type `Mutex` in this scope  --> target\tmp\code_block_ |
| concept\00_meta\self_assessment.md | 564 | normal | `fn identity<T>(x: T) -> T { ... }` | error: unexpected token: `...`  --> target\tmp\code_block_tests\self_assessment_ |
| concept\00_meta\self_assessment.md | 1392 | normal | `// proc macro quote! {     let x = 42;  ` | error: cannot find macro `quote` in this scope  --> target\tmp\code_block_tests\ |
| concept\00_meta\self_assessment.md | 1421 | normal | `struct MyFuture {     data: String,     ` | error[E0425]: cannot find type `Pin` in this scope  --> target\tmp\code_block_te |
| concept\01_foundation\01_ownership.md | 669 | normal | `// ✅ 模式 1: Rust 所有权转移给 C pub extern "C" ` | error: unsafe attribute used without unsafe  --> target\tmp\code_block_tests\01_ |
| concept\01_foundation\03_lifetimes.md | 637 | normal | `fn get_default<'r, K, V>(     map: &'r m` | error[E0404]: expected trait, found derive macro `Hash`  --> target\tmp\code_blo |
| concept\01_foundation\03_lifetimes.md | 689 | normal | `let mut x = 0; let p = &mut x; if condit` | error[E0425]: cannot find value `condition` in this scope  --> target\tmp\code_b |
| concept\01_foundation\04_type_system.md | 749 | normal | `// ✅ impl Trait: 隐藏实现，零成本 fn make_iter()` | error[E0405]: cannot find trait `Drawable` in this scope  --> target\tmp\code_bl |
| concept\02_intermediate\01_traits.md | 937 | normal | `// 显式关联类型版本（等价但冗长） trait DrawableExplici` | error[E0425]: cannot find type `Point` in this scope  --> target\tmp\code_block_ |
| concept\02_intermediate\02_generics.md | 196 | normal | `// 单态化：每个调用点生成专用代码，直接内联 fn push_mono(v: ` | error[E0405]: cannot find trait `Drawable` in this scope  --> target\tmp\code_bl |
| concept\02_intermediate\02_generics.md | 352 | normal | `// ✅ 修正: 使用 ?Sized 解除 Sized 约束 fn draw_a` | error[E0405]: cannot find trait `Drawable` in this scope  --> target\tmp\code_bl |
| concept\02_intermediate\02_generics.md | 447 | normal | `// ❌ 边界 1: Trait Bound 提供构造能力，打破纯参数性 fn ` | warning: unused variable: `ptr`  --> target\tmp\code_block_tests\02_generics_L44 |
| concept\02_intermediate\03_memory_management.md | 679 | normal | `// 核心语法模式: let b = Box::new(5);         ` | error[E0433]: cannot find type `Rc` in this scope  --> target\tmp\code_block_tes |
| concept\02_intermediate\03_memory_management.md | 816 | normal | `use std::mem;  // ❌ 危险：uninitialized 立即产` | error[E0425]: cannot find type `MaybeUninit` in this scope  --> target\tmp\code_ |
| concept\03_advanced\01_concurrency.md | 798 | normal | `use std::sync::atomic::{AtomicBool, Atom` | error[E0382]: the type `Arc` does not implement `Copy`   --> target\tmp\code_blo |
| concept\03_advanced\01_concurrency.md | 1004 | normal | `// ✅ 编译通过，无数据竞争；❌ 但逻辑错误（非原子 RMW） let d =` | error[E0433]: cannot find type `Arc` in this scope  --> target\tmp\code_block_te |
| concept\03_advanced\02_async.md | 181 | normal | `// 原始 async fn async fn foo() -> T {    ` | error[E0425]: cannot find type `T` in this scope  --> target\tmp\code_block_test |
| concept\03_advanced\02_async.md | 211 | normal | `async fn self_ref() {     let s = String` | error[E0425]: cannot find function `some_async` in this scope  --> target\tmp\co |
| concept\03_advanced\03_unsafe.md | 852 | normal | `// extern "C" = 使用 C 调用约定 extern "C" {  ` | error: extern blocks must be unsafe  --> target\tmp\code_block_tests\03_unsafe_L |
| concept\03_advanced\03_unsafe.md | 902 | normal | `// ✅ repr(C) + 指针传递：C 结构体互操作 #[repr(C)] ` | error: extern blocks must be unsafe   --> target\tmp\code_block_tests\03_unsafe_ |
| concept\03_advanced\04_macros.md | 166 | normal | `// C 预处理器（不卫生）: // #define SWAP(a, b) { ` | error[E0384]: cannot assign twice to immutable variable `temp`   --> target\tmp\ |
| concept\04_formal\03_ownership_formal.md | 647 | normal | `// 合法 Safe Rust，但 Stacked Borrows 下 Miri` | error[E0133]: dereference of raw pointer is unsafe and requires unsafe block  -- |
| concept\04_formal\04_rustbelt.md | 193 | normal | `// CSL 规范: Mutex 守卫整数不变量 "x ≥ 0" // Inva` | error[E0425]: cannot find type `Mutex` in this scope  --> target\tmp\code_block_ |
| concept\04_formal\04_rustbelt.md | 207 | normal | `// CSL 规范: Arc 共享不可变字符串 // Invariant: ∃n` | error[E0425]: cannot find type `Arc` in this scope  --> target\tmp\code_block_te |
| concept\05_comparative\02_rust_vs_go.md | 288 | normal | `// Rust: trait 静态派发 — 编译期内联，零运行时开销 fn pr` | error[E0405]: cannot find trait `Serializer` in this scope  --> target\tmp\code_ |
| concept\06_ecosystem\01_toolchain.md | 278 | normal | `// ❌ 反模式：feature 层互斥 #[cfg(all(feature =` | error[E0425]: cannot find type `ABackend` in this scope  --> target\tmp\code_blo |
| concept\06_ecosystem\02_patterns.md | 241 | normal | `struct ShoppingCart<S: PaymentStrategy> ` | error[E0405]: cannot find trait `PaymentStrategy` in this scope  --> target\tmp\ |
| concept\06_ecosystem\02_patterns.md | 273 | normal | `enum ConnectionState {     Closed,     S` | error[E0425]: cannot find type `Event` in this scope   --> target\tmp\code_block |
| concept\06_ecosystem\02_patterns.md | 498 | normal | `// 深度案例：封装 C 库 libfoo 的上下文句柄 pub struct ` | error[E0425]: cannot find type `NonNull` in this scope  --> target\tmp\code_bloc |
| concept\06_ecosystem\04_application_domains.md | 435 | normal | `// Bevy 系统：函数签名即数据依赖声明 fn move_player(  ` | error[E0425]: cannot find type `Res` in this scope  --> target\tmp\code_block_te |
| concept\07_future\02_formal_methods.md | 241 | normal | `// 类型: Box<i32> // 逻辑: ∃l. l ↦ 5  （存在某个地` | error[E0596]: cannot borrow `*x` as mutable, as `x` is not declared as mutable   |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\quick_reference.md | 203 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 217 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 251 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 283 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 308 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 327 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 343 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 523 | normal | `let mut v = vec![1, 2, 3]; v.push(4);   ` |
| concept\00_meta\self_assessment.md | 57 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 107 | normal | `trait Drawable {     fn draw(&self);    ` |
| concept\00_meta\self_assessment.md | 143 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 158 | normal | `struct A(&'static str); impl Drop for A ` |
| concept\00_meta\self_assessment.md | 185 | normal | `fn identity<T>(x: T) -> T { x } let a = ` |
| concept\00_meta\self_assessment.md | 246 | normal | `struct MyPtr<T> {     ptr: *mut (),     ` |
| concept\00_meta\self_assessment.md | 272 | normal | `use std::cell::RefCell; let cell = RefCe` |
| concept\00_meta\self_assessment.md | 319 | normal | `fn process<T>(data: T) {     let size = ` |
| concept\00_meta\self_assessment.md | 340 | normal | `let x = String::from("hello"); let f = \|` |
| concept\00_meta\self_assessment.md | 500 | normal | `macro_rules! make_var {     ($name:ident` |
| concept\00_meta\self_assessment.md | 1243 | normal | `struct Unit; struct Pair(Unit, Unit); en` |
| concept\00_meta\self_assessment.md | 1340 | normal | `use std::cell::UnsafeCell; let cell = Un` |
