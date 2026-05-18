# 代码块编译验证报告 (Code Block Compile Report)

> 生成时间: 2026-05-13
> 扫描文件数: 37

## 摘要

| 指标 | 数值 |
|:---|:---|
| 测试代码块 | 232 |
| 编译通过 | 232 |
| 编译失败 | 0 |
| 跳过 (ignore/no_run) | 183 |
| 通过率 | 100.0% |

## 编译通过的代码块（抽样）

| 文件 | 行号 | 模式 | 预览 |
|:---|:---|:---|:---|
| concept\00_meta\quick_reference.md | 205 | normal | `fn identity<T>(x: T) -> T { x } // 单态化后生` |
| concept\00_meta\quick_reference.md | 219 | normal | `trait LendingIterator {     type Item<'a` |
| concept\00_meta\quick_reference.md | 253 | normal | `fn make_iter() -> impl Iterator<Item = i` |
| concept\00_meta\quick_reference.md | 285 | normal | `fn longest<'a>(x: &'a str, y: &'a str) -` |
| concept\00_meta\quick_reference.md | 310 | normal | `macro_rules! vec {     ($($x:expr),*) =>` |
| concept\00_meta\quick_reference.md | 329 | normal | `let s1 = String::from("hello"); let s2 =` |
| concept\00_meta\quick_reference.md | 345 | normal | `struct Meters(u32); struct Kilometers(u3` |
| concept\00_meta\quick_reference.md | 527 | normal | `let mut v = vec![1, 2, 3]; v.push(4);` |
| concept\00_meta\self_assessment.md | 57 | normal | `fn first_word(s: &str) -> &str {     &s[` |
| concept\00_meta\self_assessment.md | 109 | normal | `trait Drawable {     fn draw(&self);` |
| concept\00_meta\self_assessment.md | 145 | normal | `fn read_config(path: &str) -> Result<Str` |
| concept\00_meta\self_assessment.md | 160 | normal | `struct A(&'static str); impl Drop for A` |
| concept\00_meta\self_assessment.md | 187 | normal | `fn identity<T>(x: T) -> T { x } let a =` |
| concept\00_meta\self_assessment.md | 248 | normal | `struct MyPtr<T> {     ptr: *mut (),` |
| concept\00_meta\self_assessment.md | 274 | normal | `use std::cell::RefCell; let cell = RefCe` |
| concept\00_meta\self_assessment.md | 928 | normal | `fn first_char(s: &String) -> &str {` |
| concept\00_meta\self_assessment.md | 988 | normal | `let v: Vec<i32> = Vec::new(); // 或 let v` |
| concept\00_meta\self_assessment.md | 1007 | normal | `let x = Some(String::from("hello")); mat` |
| concept\00_meta\self_assessment.md | 1062 | normal | `fn process<T>(item: T) where     T: Clon` |
| concept\00_meta\self_assessment.md | 1088 | normal | `trait Container {     type Item;     fn` |
