# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-05-13
> 扫描文件数: 37

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 282 |
| 编译通过 | 226 |
| 编译失败 | 56 |
| 跳过 (ignore/no_run) | 368 |
| 通过率 | 80.1% |

## 编译失败的代码块

| 文件 | 行号 | 模式 | 预览 | 错误信息 |
|:---|:---|:---|:---|:---|
| concept\00_meta\boundary_extension_tree.md | 91 | normal | `// FFI 边界示例：Rust 调用 C extern "C" {     f` | error: extern blocks must be unsafe  --> target\tmp\code_block_tests\boundary_ex |
| concept\00_meta\expressiveness_multiview.md | 235 | normal | `// 直接风格（伪代码） async fn fetch_and_process(` | error[E0425]: cannot find type `Data` in this scope  --> target\tmp\code_block_t |
| concept\00_meta\expressiveness_multiview.md | 296 | normal | `// gen block: 懒性迭代器生成 let gen = gen {` | error: expected identifier, found reserved keyword `gen`  --> target\tmp\code_bl |
| concept\00_meta\expressiveness_multiview.md | 381 | normal | `// 会话类型编码：Client 发送请求，接收响应，关闭 struct Cli` | error[E0425]: cannot find type `Sender` in this scope   --> target\tmp\code_bloc |
| concept\00_meta\expressiveness_multiview.md | 451 | normal | `// ML functor: functor MakeSet(Element:` | error[E0425]: cannot find type `Ordering` in this scope  --> target\tmp\code_blo |
| concept\00_meta\quick_reference.md | 505 | normal | `fn may_fail() -> Result<i32, String> {` | error[E0425]: cannot find function `random` in this scope  --> target\tmp\code_b |
| concept\00_meta\semantic_expressiveness.md | 599 | normal | `// 编译器自动推导（auto trait） unsafe impl Send` | error[E0425]: cannot find type `MyType` in this scope  --> target\tmp\code_block |
| concept\01_foundation\03_lifetimes.md | 1036 | normal | `// ✅ 正确：Rule 1 自动为每个输入引用分配独立生命周期 fn prin` | error: free function without a body  --> target\tmp\code_block_tests\03_lifetime |
| concept\01_foundation\03_lifetimes.md | 1077 | normal | `// ✅ 正确：单输入引用，返回引用自动关联 fn first(s: &str)` | error: free function without a body  --> target\tmp\code_block_tests\03_lifetime |
| concept\01_foundation\03_lifetimes.md | 1137 | normal | `// ✅ 修正：当返回引用的生命周期应独立于 self 时，显式标注 impl<` | error[E0425]: cannot find type `Parser` in this scope  --> target\tmp\code_block |
| concept\01_foundation\03_lifetimes.md | 1627 | normal | `// ✅ union 可自动实现 Copy（所有 variant 都是 Copy` | error[E0425]: cannot find type `ManuallyDrop` in this scope   --> target\tmp\cod |
| concept\01_foundation\03_lifetimes.md | 1657 | normal | `#[repr(C)] union RustUnion {     i: i32,` | error: extern blocks must be unsafe  --> target\tmp\code_block_tests\03_lifetime |
| concept\02_intermediate\01_traits.md | 1417 | normal | `// 稳定 Rust：为每个需要支持的类型写宏展开 macro_rules! c` | error[E0015]: cannot call non-const method `<i32 as ConstDouble>::const_double`  |
| concept\02_intermediate\01_traits.md | 1443 | normal | `// 稳定 Rust：通过结构体封装避免 trait bound struct` | error[E0034]: multiple applicable items in scope   --> target\tmp\code_block_tes |
| concept\02_intermediate\02_generics.md | 607 | normal | `// ✅ 合法: 简单算术表达式（1.51+） fn double_array<` | error: generic parameters may not be used in const operations  --> target\tmp\co |
| concept\02_intermediate\02_generics.md | 662 | normal | `// ✅ 合法: 显式约束数组类型满足 Sized fn process_arr` | error: generic parameters may not be used in const operations   --> target\tmp\c |
| concept\02_intermediate\02_generics.md | 1940 | normal | `// Const Generics: 值直接参数化类型（直观、高效） struc` | error[E0428]: the name `Vector` is defined multiple times   --> target\tmp\code_ |
| concept\02_intermediate\03_memory_management.md | 1385 | normal | `let rc = Rc::new(Point { x: 1, y: 2 });` | error[E0433]: cannot find type `Rc` in this scope  --> target\tmp\code_block_tes |
| concept\02_intermediate\04_error_handling.md | 1662 | normal | `use std::panic::Location; use std::fmt;` | error[E0277]: the trait bound `Result<u16, LocatedError>: FromStr` is not satisf |
| concept\03_advanced\03_unsafe.md | 1410 | normal | `// ✅ 正确: Vec::pop 的简化实现 impl<T> MyVec<T>` | error[E0425]: cannot find type `MyVec` in this scope  --> target\tmp\code_block_ |
| concept\03_advanced\03_unsafe.md | 1427 | normal | `use std::mem::ManuallyDrop; use std::ptr` | error[E0308]: mismatched types    --> target\tmp\code_block_tests\03_unsafe_L142 |
| concept\03_advanced\03_unsafe.md | 2009 | normal | `// ✅ 安全替代 1: array::from_fn（Rust 1.63+）` | error[E0308]: mismatched types   --> target\tmp\code_block_tests\03_unsafe_L2009 |
| concept\05_comparative\05_execution_model_isomorphism.md | 179 | normal | `// 源代码 async fn example() -> i32 {     l` | error[E0425]: cannot find type `Pin` in this scope   --> target\tmp\code_block_t |
| concept\05_comparative\05_execution_model_isomorphism.md | 362 | normal | `// 概念性：Rust Actor 的类型安全 struct MyActor {` | error[E0405]: cannot find trait `Handler` in this scope  --> target\tmp\code_blo |
| concept\06_ecosystem\01_toolchain.md | 729 | normal | `// 嵌入式裸机目标示例（thumbv7em-none-eabihf） #![n` | error: unwinding panics are not supported without std   \|   = help: using nightl |
| concept\06_ecosystem\03_idioms_spectrum.md | 194 | normal | `fn read_file(path: &str) -> Result<Strin` | error[E0433]: cannot find module or crate `io` in this scope  --> target\tmp\cod |
| concept\06_ecosystem\03_idioms_spectrum.md | 210 | normal | `fn read_file(path: &str) -> Result<Strin` | error[E0433]: cannot find module or crate `io` in this scope  --> target\tmp\cod |
| concept\06_ecosystem\03_idioms_spectrum.md | 229 | normal | `// Rust 1.95+ 惯用：match 中使用 if let guards` | error[E0425]: cannot find type `Error` in this scope  --> target\tmp\code_block_ |
| concept\06_ecosystem\03_idioms_spectrum.md | 250 | normal | `// 惯用：if let 局部绑定 if let Some(value) = m` | error[E0425]: cannot find value `map` in this scope  --> target\tmp\code_block_t |
| concept\06_ecosystem\03_idioms_spectrum.md | 269 | normal | `// 惯用：Iterator 消费链 let sum_of_squares: i` | error[E0425]: cannot find value `numbers` in this scope  --> target\tmp\code_blo |
| concept\06_ecosystem\03_idioms_spectrum.md | 320 | normal | `// 惯用：Typestate 编码连接状态 struct Disconnect` | error[E0425]: cannot find type `TcpStream` in this scope  --> target\tmp\code_bl |
| concept\06_ecosystem\03_idioms_spectrum.md | 356 | normal | `// 惯用：PhantomData 标记生命周期关系 struct Iter<'` | error[E0425]: cannot find type `PhantomData` in this scope  --> target\tmp\code_ |
| concept\06_ecosystem\03_idioms_spectrum.md | 377 | normal | `// 惯用：ZST 作为能力标记（Capability） struct Read` | error[E0425]: cannot find type `RawFd` in this scope  --> target\tmp\code_block_ |
| concept\06_ecosystem\03_idioms_spectrum.md | 458 | normal | `// 惯用：trait bound 组合 fn process<T>(item:` | error[E0405]: cannot find trait `Display` in this scope  --> target\tmp\code_blo |
| concept\06_ecosystem\03_idioms_spectrum.md | 501 | normal | `// 惯用：RAII 锁守卫 {     let guard = mutex.l` | error[E0425]: cannot find value `mutex` in this scope  --> target\tmp\code_block |
| concept\06_ecosystem\03_idioms_spectrum.md | 521 | normal | `// 惯用：scopeguard 保证退出处理 use scopeguard::` | error[E0432]: unresolved import `scopeguard`  --> target\tmp\code_block_tests\03 |
| concept\06_ecosystem\03_idioms_spectrum.md | 592 | normal | `// 惯用：Iterator 消费链（零成本抽象） let max_even:` | error[E0425]: cannot find value `numbers` in this scope  --> target\tmp\code_blo |
| concept\06_ecosystem\03_idioms_spectrum.md | 638 | normal | `// 惯用：早期返回 + 守卫子句 fn process(data: Optio` | error[E0425]: cannot find type `Output` in this scope  --> target\tmp\code_block |
| concept\06_ecosystem\03_idioms_spectrum.md | 687 | normal | `// 惯用：结构化推导线程安全 #[derive(Clone)] struct` | error[E0425]: cannot find type `RefCell` in this scope   --> target\tmp\code_blo |
| concept\06_ecosystem\03_idioms_spectrum.md | 710 | normal | `// 惯用：Actor 单线程处理（概念性，基于 actix 风格） struc` | error[E0405]: cannot find trait `Actor` in this scope   --> target\tmp\code_bloc |
| concept\06_ecosystem\03_idioms_spectrum.md | 739 | normal | `// 惯用：channel + 所有权转移 let (tx, rx) = mps` | error[E0433]: cannot find module or crate `mpsc` in this scope  --> target\tmp\c |
| concept\06_ecosystem\03_idioms_spectrum.md | 809 | normal | `// 惯用：洋葱中间件（Tower 风格） async fn handler(r` | error[E0425]: cannot find type `Request` in this scope  --> target\tmp\code_bloc |
| concept\06_ecosystem\03_idioms_spectrum.md | 829 | normal | `// 惯用：Bevy ECS 风格（概念性） #[derive(Componen` | error: cannot find derive macro `Component` in this scope  --> target\tmp\code_b |
| concept\06_ecosystem\03_idioms_spectrum.md | 853 | normal | `// 惯用：错误内核模式（Erlang 思想在 Rust 中的编码） struc` | error[E0433]: cannot find module or crate `log` in this scope   --> target\tmp\c |
| concept\06_ecosystem\05_system_design_principles.md | 208 | normal | `// Rust 中的 Error Kernel 模式 struct ErrorK` | error[E0433]: cannot find module or crate `log` in this scope   --> target\tmp\c |
| concept\06_ecosystem\09_cargo_script.md | 59 | normal | `#!/usr/bin/env cargo` | error: expected `[`, found `/`  --> target\tmp\code_block_tests\09_cargo_script_ |
| concept\06_ecosystem\09_cargo_script.md | 81 | normal | `#!/usr/bin/env rust-script --- [package]` | error[E0658]: frontmatters are experimental  --> target\tmp\code_block_tests\09_ |
| concept\06_ecosystem\09_cargo_script.md | 208 | normal | `#!/usr/bin/env cargo` | error: expected `[`, found `/`  --> target\tmp\code_block_tests\09_cargo_script_ |
| concept\06_ecosystem\09_cargo_script.md | 250 | normal | `#!/usr/bin/env cargo` | error: expected `[`, found `/`  --> target\tmp\code_block_tests\09_cargo_script_ |
| concept\06_ecosystem\10_public_private_deps.md | 47 | normal | `// Crate A 的 src/lib.rs pub use B::SomeT` | error[E0432]: unresolved import `B`  --> target\tmp\code_block_tests\10_public_p |
| concept\06_ecosystem\10_public_private_deps.md | 56 | normal | `// Crate C use A::foo; let x = B::SomeTy` | error[E0432]: unresolved import `A`  --> target\tmp\code_block_tests\10_public_p |
| concept\06_ecosystem\10_public_private_deps.md | 91 | normal | `// Crate A (public = true for B, public` | error: expected one of `->`, `where`, or `{`, found `}`  --> target\tmp\code_blo |
| concept\06_ecosystem\10_public_private_deps.md | 168 | normal | `// 重构前：泄漏 B::Config pub fn parse_config(` | error[E0428]: the name `parse_config` is defined multiple times  --> target\tmp\ |
| concept\07_future\03_evolution.md | 278 | normal | `// Rust 2015 — dyn 可省略 fn process(x: &My` | error[E0428]: the name `process` is defined multiple times  --> target\tmp\code_ |
| concept\07_future\03_evolution.md | 340 | normal | `// Rust 2021 — impl Trait 默认不捕获生命周期，导致常见` | error[E0428]: the name `numbers` is defined multiple times  --> target\tmp\code_ |
| concept\07_future\03_evolution.md | 382 | normal | `// Rust 2021 extern "C" {     fn strlen(` | error[E0428]: the name `strlen` is defined multiple times   --> target\tmp\code_ |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 179 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 420 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 470 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 161 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 277 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 291 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 325 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 357 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 382 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 401 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 417 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 599 | normal | `let mut v = vec![1, 2, 3]; v.push(4);` |
| concept\00_meta\self_assessment.md | 165 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 217 | normal | `trait Drawable {     fn draw(&self);` |
| concept\00_meta\self_assessment.md | 253 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 268 | normal | `struct A(&'static str); impl Drop for A` |
| concept\00_meta\self_assessment.md | 295 | normal | `fn identity<T>(x: T) -> T { x } let a =` |
| concept\00_meta\self_assessment.md | 360 | normal | `struct MyPtr<T> {     ptr: *mut (),` |
| concept\00_meta\self_assessment.md | 386 | normal | `use std::cell::RefCell; let cell = RefCe` |
| concept\00_meta\self_assessment.md | 1054 | normal | `fn first_char(s: &String) -> &str {` |
