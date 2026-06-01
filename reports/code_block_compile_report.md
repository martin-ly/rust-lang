# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-06-01
> 扫描范围: concept/ + knowledge/

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 1751 |
| 编译通过 | 1742 |
| 编译失败 | 9 |
| 跳过 (ignore/no_run) | 1954 |
| 通过率 | 99.5% |

## 编译失败的代码块（knowledge/）

> knowledge/ 中的 9 个失败块多为教学片段（不完整代码、故意展示编译错误），
> 属于预期行为。以下显示前 5 个示例：

| 文件 | 行号 | 预览 | 错误信息 |
|:---|:---|:---|:---|
| knowledge\06_ecosystem\emerging\05_rust_1_96.md | 119 | `use std::assert_matches;  let result: Re` | error: cannot find macro `debug_assert_matches` in this scop |
| knowledge\06_ecosystem\emerging\05_rust_1_96.md | 225 | `/// Trait 文档中的代码示例仍被检查 pub trait MyTrait` | error[E0425]: cannot find type `MyStruct` in this scope  --> |
| knowledge\06_ecosystem\emerging\05_rust_1_96.md | 351 | `// 现在产生 deny 级错误 static NEVER: std::conv` | error: static of uninhabited type  --> target\tmp\code_block |
| knowledge\06_ecosystem\emerging\05_rust_1_96.md | 390 | `#[export_name = "first"]  // 生效 #[export` | error: unsafe attribute used without unsafe  --> target\tmp\ |
| knowledge\06_ecosystem\emerging\05_rust_1_96.md | 404 | `// AVR 目标上 let d: libc::c_double = 1.0f3` | error[E0433]: cannot find module or crate `libc` in this sco |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 182 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 441 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 491 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 90 | normal | `async fn foo() -> i32 { 42 } // 等价于: fn` |
| concept\00_meta\quick_reference.md | 164 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 219 | normal | `enum Option<T> { None, Some(T) } enum Re` |
| concept\00_meta\quick_reference.md | 284 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 298 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 332 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 366 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 391 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 410 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 426 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 450 | normal | `let x: Option<i32> = Some(5); let y = x.` |
| concept\00_meta\quick_reference.md | 610 | normal | `let mut v = vec![1, 2, 3]; v.push(4);` |
| concept\00_meta\self_assessment.md | 171 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 225 | normal | `trait Drawable {     fn draw(&self);` |
| concept\00_meta\self_assessment.md | 262 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 278 | normal | `struct A(&'static str); impl Drop for A` |
| concept\00_meta\self_assessment.md | 306 | normal | `fn identity<T>(x: T) -> T { x } let a =` |
