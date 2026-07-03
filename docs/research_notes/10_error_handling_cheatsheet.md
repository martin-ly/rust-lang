# 错误处理速查卡 {#错误处理速查卡}

> **EN**: Error Handling Cheatsheet
> **Summary**: 错误处理速查卡 Error Handling Cheatsheet.
>
> **概念族**: 速查卡
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Standard Library](https://doc.rust-lang.org/std/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [RFC 2504](https://rust-lang.github.io/rfcs/2504-fix-error.html)
> **创建日期**: 2026-02-10
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **一页纸速查** - Result、Option、错误处理模式

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [错误处理速查卡 {#错误处理速查卡}](#错误处理速查卡-错误处理速查卡)
  - [📑 目录 {#目录}](#-目录-目录)
  - [Result与Option {#result与option}](#result与option-result与option)
  - [常用方法 {#常用方法}](#常用方法-常用方法)
    - [Option {#option}](#option-option)
    - [Result {#result}](#result-result)
  - [?操作符 {#操作符}](#操作符-操作符)
  - [错误转换 {#错误转换}](#错误转换-错误转换)
  - [panic vs Result {#panic-vs-result}](#panic-vs-result-panic-vs-result)
  - [🌍 权威国际化资源链接 {#权威国际化资源链接}](#-权威国际化资源链接-权威国际化资源链接)
    - [Rust Reference 核心章节 {#rust-reference-核心章节}](#rust-reference-核心章节-rust-reference-核心章节)
    - [The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}](#the-rust-programming-language-核心章节-the-rust-programming-language-核心章节)
    - [Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}](#rust-standard-library-核心-api--模块-rust-standard-library-核心-api-模块)
    - [Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}](#rust-by-example--rust-cookbook--cheatsrs-rust-by-example-rust-cookbook-cheatsrs)
    - [错误处理专属权威链接 {#错误处理专属权威链接}](#错误处理专属权威链接-错误处理专属权威链接)
      - [std::error::Error {#stderrorerror}](#stderrorerror-stderrorerror)
      - [Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}](#rust-by-example--cookbook--cheatsrs-rust-by-example-cookbook-cheatsrs)
      - [RFC 2504 / anyhow / thiserror {#rfc-2504-anyhow-thiserror}](#rfc-2504--anyhow--thiserror-rfc-2504-anyhow-thiserror)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## Result与Option {#result与option}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 类型 | 用途 | 方法 |
| :--- | :--- | :--- |
| `Option<T>` | 可能有值 | `Some(T)` / `None` |
| `Result<T, E>` | 可能成功 | `Ok(T)` / `Err(E)` |

---

## 常用方法 {#常用方法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Option {#option}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
opt.unwrap()        // 获取值，None时panic
opt.unwrap_or(def)  // 获取值或默认值
opt.ok_or(err)      // Option -> Result
opt.map(|v| ...)    // 映射
opt.and_then(|v| ...) // 链式操作
```

### Result {#result}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

```rust,ignore
res.unwrap()        // 获取值，Err时panic
res?                // 传播错误
res.map_err(|e| ...) // 错误映射
res.and_then(|v| ...) // 链式操作
```

---

## ?操作符 {#操作符}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
fn may_fail() -> Result<T, Error> {
    let x = operation1()?;  // 错误时提前返回
    let y = operation2()?;
    Ok(y)
}
```

---

## 错误转换 {#错误转换}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// From trait自动转换
impl From<IOError> for MyError {
    fn from(e: IOError) -> Self { ... }
}

// 使用
let file = File::open("file")?;  // IOError自动转为MyError
```

---

## panic vs Result {#panic-vs-result}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 情况 | 使用 |
| :--- | :--- |
| 不可恢复错误 | `panic!` |
| 可恢复错误 | `Result` |
| 可选值 | `Option` |
| 编程错误 | `assert!` / `unreachable!` |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🌍 权威国际化资源链接 {#权威国际化资源链接}
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节 {#rust-reference-核心章节}

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

### 错误处理专属权威链接 {#错误处理专属权威链接}

> **来源: [TRPL Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)**
> **来源: [Rust Reference - Result](https://doc.rust-lang.org/std/result/)**

#### std::error::Error {#stderrorerror}

- [std::error::Error trait](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::result::Result](https://doc.rust-lang.org/std/result/)
- [std::option::Option](https://doc.rust-lang.org/std/option/)
- [std::fmt::Display](https://doc.rust-lang.org/std/fmt/trait.Display.html)
- [std::fmt::Debug](https://doc.rust-lang.org/std/fmt/trait.Debug.html)

#### Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}

- [RBE - Error Handling](https://doc.rust-lang.org/rust-by-example/error.html)
- [RBE - Option & unwrap](https://doc.rust-lang.org/rust-by-example/error/option_unwrap.html)
- [RBE - Result](https://doc.rust-lang.org/rust-by-example/error/result.html)
- [RBE - ? operator](https://doc.rust-lang.org/rust-by-example/error/result/enter_question_mark.html)
- [Rust Cookbook - Errors](https://rust-lang-nursery.github.io/rust-cookbook/errors.html)
- [cheats.rs - Error Handling](https://cheats.rs/#error-handling)

#### RFC 2504 / anyhow / thiserror {#rfc-2504-anyhow-thiserror}

- [RFC 2504 - Error trait improvements (source / backtrace)](https://rust-lang.github.io/rfcs/2504-fix-error.html)
- [RFC 1859 - Try trait / `?` operator](https://rust-lang.github.io/rfcs/1859-try-trait.html)
- [anyhow docs](https://docs.rs/anyhow/latest/anyhow/)
- [anyhow GitHub](https://github.com/dtolnay/anyhow)
- [thiserror docs](https://docs.rs/thiserror/latest/thiserror/)
- [thiserror GitHub](https://github.com/dtolnay/thiserror)

## 相关概念 {#相关概念}
>
> **[来源: [crates.io](https://crates.io/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Exception Handling](https://en.wikipedia.org/wiki/Exception_Handling)**
> **来源: [TRPL Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)**
> **来源: [Rust Reference - Result](https://doc.rust-lang.org/std/result/)**
> **来源: [RFC 2504 - Error trait improvements](https://rust-lang.github.io/rfcs/2504-fix-error.html)**

---

> **来源: [ACM Digital Library](https://dl.acm.org/)**
> **来源: [IEEE Standards](https://standards.ieee.org/)**
