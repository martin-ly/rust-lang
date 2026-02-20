# 📖 Rust 1.90 术语表 (Glossary)

> **创建日期**: 2026-01-26
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已归档
---

## 目录

- [A](#a)
- [C](#c)
- [E](#e)
- [G](#g)
- [I](#i)
- [L](#l)
- [M](#m)
- [R](#r)
- [S](#s)
- [T](#t)

---

## A

### API (Application Programming Interface)

**应用程序编程接口**:

定义：提供给开发者使用的函数、类型、trait 等接口。

在 Rust 1.90 中：

- 新增多个稳定 API
- const 函数 API 扩展
- 更好的 trait 实现

参考：[Rust API Documentation](https://doc.rust-lang.org/std/)

---

## C

### Cargo Workspace

**Cargo 工作空间**:

定义：将多个相关的 Rust 包组织在一起的项目结构。

在 Rust 1.90 中：

- 支持工作空间发布
- 改进的依赖解析
- 更好的构建缓存

参考：[Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)

---

### checked_sub_signed()

**带符号减法检查方法**:

定义：无符号整数类型的新方法，用于与有符号数进行安全减法。

```rust
let x: u32 = 10;
let y: i32 = -5;
let result = x.checked_sub_signed(y); // Some(15)
```

特性：

- Rust 1.90 新增
- 防止溢出
- 返回 `Option<T>`

相关方法：

- `overflowing_sub_signed()`
- `saturating_sub_signed()`
- `wrapping_sub_signed()`

---

### const Context

**const 上下文**:

定义：在编译时求值的代码环境。

在 Rust 1.90 中可用的 const 函数：

- `<[T]>::reverse()` - 数组反转
- `f32/f64::floor()` - 向下取整
- `f32/f64::ceil()` - 向上取整
- `f32/f64::trunc()` - 截断
- `f32/f64::round()` - 四舍五入

示例：

```rust
const fn example() -> f64 {
    let x = 3.7;
    x.floor()  // Rust 1.90 中可用
}

const RESULT: f64 = example();  // 3.0
```

---

### Const Generic

**常量泛型**:

定义：使用常量值作为泛型参数的特性。

示例：

```rust
fn create_array<const N: usize>() -> [i32; N] {
    [0; N]
}

let arr: [i32; 5] = create_array();
```

参考：[Const Generics](https://doc.rust-lang.org/reference/items/generics.html#const-generics)

---

## E

### Edition

**版次**:

定义：Rust 语言的版本划分方式，每个版次可能包含向后不兼容的变更。

版次历史：

- Edition 2015 (Rust 1.0)
- Edition 2018 (Rust 1.31)
- Edition 2021 (Rust 1.56)
- **Edition 2024** (Rust 1.90)

配置方式：

```toml
[package]
edition = "2024"
```

参考：[Edition Guide](https://doc.rust-lang.org/edition-guide/)

---

## G

### GAT (Generic Associated Types)

**泛型关联类型**:

定义：在关联类型中使用泛型参数的特性。

示例：

```rust
trait Container {
    type Item<'a> where Self: 'a;

    fn get<'a>(&'a self) -> Option<Self::Item<'a>>;
}
```

在 Rust 1.90 中：

- 完全稳定
- 性能优化
- 更好的错误信息

---

## I

### Incremental Compilation

**增量编译**:

定义：只重新编译修改过的代码部分，加快编译速度。

在 Rust 1.90 中：

- 增量编译优化
- 更智能的缓存
- 更快的重新编译

启用方式：

```bash
# 默认启用，可以手动设置
CARGO_INCREMENTAL=1 cargo build
```

---

### IntErrorKind

**整数错误类型**:

定义：表示整数解析错误的枚举类型。

在 Rust 1.90 中：

- 实现了 `Copy` trait
- 实现了 `Hash` trait
- 更方便的错误处理

示例：

```rust
use std::num::IntErrorKind;

let err_kind: IntErrorKind = // ...
// 现在可以 copy 和 hash
```

---

## L

### LLD Linker

**LLD 链接器**:

定义：LLVM 项目的高性能链接器。

特性：

- **速度**: 比传统链接器快约 2倍
- **内存**: 内存使用更优化
- **跨平台**: 支持多种目标平台

在 Rust 1.90 中：

- Linux x86_64 上默认启用
- 显著提升链接速度
- 改善构建体验

手动启用（其他平台）：

```toml
# .cargo/config.toml
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=lld"]
```

参考：[LLVM LLD](https://lld.llvm.org/)

---

### Lint

**代码检查规则**:

定义：编译器或 Clippy 提供的代码质量检查规则。

在 Rust 1.90 中的新 lint：

- `mismatched_lifetime_syntaxes` - 默认启用

配置方式：

```rust
#![warn(mismatched_lifetime_syntaxes)]
#![allow(specific_lint)]
```

---

### Lifetime

**生命周期**:

定义：Rust 用于追踪引用有效性的机制。

在 Rust 1.90 中：

- 改进的生命周期推断
- 新的 `mismatched_lifetime_syntaxes` lint
- 更好的错误信息

示例：

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

---

## M

### mismatched_lifetime_syntaxes

**不匹配的生命周期语法 Lint**:

定义：检查生命周期语法一致性的新 lint 规则。

在 Rust 1.90 中：

- **默认启用**
- 提高代码可读性
- 确保生命周期标注一致

触发场景：

```rust
// ❌ 触发警告
fn items(scores: &[u8]) -> std::slice::Iter<'_, u8> {
    scores.iter()
}

// ✅ 推荐写法
fn items<'a>(scores: &'a [u8]) -> std::slice::Iter<'a, u8> {
    scores.iter()
}
```

---

## R

### RPITIT (Return Position Impl Trait In Traits)

**Trait 中返回位置的 impl Trait**:

定义：允许在 trait 方法的返回位置使用 `impl Trait` 语法。

示例：

```rust
trait Container {
    fn items(&self) -> impl Iterator<Item = i32>;
}
```

在 Rust 1.90 中：

- 完全稳定
- 与 async trait 配合良好
- 提供零成本抽象

---

### rust-version

**Rust 版本声明**:

定义：在 `Cargo.toml` 中声明项目所需的最低 Rust 版本。

配置方式：

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"  # 声明最低版本
```

作用：

- 防止使用低版本 Rust 编译
- 提供清晰的版本要求
- 改善团队协作

---

## S

### Stabilization

**稳定化**:

定义：将 nightly 特性转为稳定特性的过程。

Rust 1.90 稳定化的特性：

- 多个新的标准库 API
- const 函数增强
- trait 实现扩展

流程：

1. RFC 提案
2. Nightly 实现
3. 社区反馈
4. 稳定化发布

---

## T

### TAIT (Type Alias Impl Trait)

**类型别名实现 Trait**:

定义：使用类型别名定义 `impl Trait` 类型。

示例：

```rust
type MyIterator = impl Iterator<Item = i32>;

fn create_iter() -> MyIterator {
    vec![1, 2, 3].into_iter()
}
```

在 Rust 1.90 中：

- 继续完善
- 更好的类型推断
- 与其他特性配合

---

### Trait

**特征**:

定义：定义类型共享行为的机制。

在 Rust 1.90 中的改进：

- RPITIT 完全稳定
- GAT 优化
- 更多标准 trait 实现

基本示例：

```rust
trait Summary {
    fn summarize(&self) -> String;
}
```

参考：[The Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)

---

## 附录

### 缩写对照表

| 缩写   | 全称                                 | 中文                      |
| :--- | :--- | :--- || API    | Application Programming Interface    | 应用程序编程接口          |
| GAT    | Generic Associated Types             | 泛型关联类型              |
| LLD    | LLVM Linker                          | LLVM 链接器               |
| RPITIT | Return Position Impl Trait In Traits | Trait 返回位置 impl Trait |
| TAIT   | Type Alias Impl Trait                | 类型别名实现 Trait        |

---

### 版本对照

| 特性                         | Rust 1.89 | Rust 1.90         |
| :--- | :--- | :--- || LLD 链接器                   | 可选      | Linux x86_64 默认 |
| checked_sub_signed()         | ❌ 不支持 | ✅ 新增           |
| const reverse()              | ❌ 不支持 | ✅ 支持           |
| mismatched_lifetime_syntaxes | ❌ 未启用 | ✅ 默认启用       |

---

### 相关文档

- 📄 [FAQ 文档](RUST_190_FAQ.md)
- 📄 [主报告](RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md)
- 📄 [完整会话总结](RUST_190_完整会话总结_2025_10_26.md)

---

### 外部参考

- 📖 [Rust Reference](https://doc.rust-lang.org/reference/)
- 📖 [Rust Glossary](https://doc.rust-lang.org/reference/glossary.html)
- 📖 [Rust API Docs](https://doc.rust-lang.org/std/)
- 📖 [Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)

---

**文档维护**: 本术语表会持续更新
**最后更新**: 2025-10-26
**版本**: 1.0

---

## 贡献

如果您发现术语定义不准确或有遗漏，欢迎：

1. 提交 Issue
2. 提出修改建议
3. 补充新术语

感谢您的贡献！🙏