# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-05-13
> 扫描文件数: 37

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 269 |
| 编译通过 | 269 |
| 编译失败 | 0 |
| 跳过 (ignore/no_run) | 579 |
| 通过率 | 100.0% |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 187 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 453 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 504 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 169 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 289 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 303 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 337 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 371 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 396 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 415 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 431 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 615 | normal | `let mut v = vec![1, 2, 3]; v.push(4);   ` |
| concept\00_meta\self_assessment.md | 178 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 234 | normal | `trait Drawable {     fn draw(&self);    ` |
| concept\00_meta\self_assessment.md | 272 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 289 | normal | `struct A(&'static str); impl Drop for A ` |
| concept\00_meta\self_assessment.md | 318 | normal | `fn identity<T>(x: T) -> T { x } let a = ` |
| concept\00_meta\self_assessment.md | 391 | normal | `struct MyPtr<T> {     ptr: *mut (),     ` |
| concept\00_meta\self_assessment.md | 419 | normal | `use std::cell::RefCell; let cell = RefCe` |
| concept\00_meta\self_assessment.md | 1171 | normal | `fn first_char(s: &String) -> &str {     ` |
