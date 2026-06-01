# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-06-02
> 扫描范围: concept/ + knowledge/

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 1744 |
| 编译通过 | 1744 |
| 编译失败 | 0 |
| 跳过 (ignore/no_run) | 1978 |
| 通过率 | 100.0% |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\expressiveness_multiview.md | 185 | normal | `// 构造性排中律：不是「T 或 ¬T」，而是「T 或 E」 enum Resu` |
| concept\00_meta\expressiveness_multiview.md | 444 | normal | `// 参数性保证：id 函数对任何 T 的行为都相同 fn id<T>(x: T` |
| concept\00_meta\expressiveness_multiview.md | 494 | normal | `// 使用 Newtype + 私有字段编码安全级别 struct High<T` |
| concept\00_meta\quick_reference.md | 93 | normal | `async fn foo() -> i32 { 42 } // 等价于: fn ` |
| concept\00_meta\quick_reference.md | 167 | normal | `#[derive(Copy, Clone)] struct Point { x:` |
| concept\00_meta\quick_reference.md | 222 | normal | `enum Option<T> { None, Some(T) } enum Re` |
| concept\00_meta\quick_reference.md | 287 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 301 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 335 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 369 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 394 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 413 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 429 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 453 | normal | `let x: Option<i32> = Some(5); let y = x.` |
| concept\00_meta\quick_reference.md | 613 | normal | `let mut v = vec![1, 2, 3]; v.push(4);   ` |
| concept\00_meta\self_assessment.md | 174 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 228 | normal | `trait Drawable {     fn draw(&self);    ` |
| concept\00_meta\self_assessment.md | 265 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 281 | normal | `struct A(&'static str); impl Drop for A ` |
| concept\00_meta\self_assessment.md | 309 | normal | `fn identity<T>(x: T) -> T { x } let a = ` |
