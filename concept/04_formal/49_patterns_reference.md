# 模式参考（Patterns Reference）

> **EN**: Patterns Reference
> **Summary**: Rust 模式系统的规范：模式位置、可反驳/不可反驳模式、各种模式形式（字面量、标识符、通配符、范围、引用、结构体、元组、数组、or、guard 等）及其绑定规则。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Patterns](../01_foundation/40_patterns.md) · [Statements and Expressions Reference](48_statements_and_expressions_reference.md) · [Variables](../03_advanced/33_variables.md)
> **后置概念**: [Destructors](43_destructors.md) · [Match Expressions](48_statements_and_expressions_reference.md)
> **定理链**: Value → Pattern Match → Binding → Destructuring
>
> **来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

## 一、模式位置

Rust 模式出现在以下上下文：

| 位置 | 示例 |
|:---|:---|
| `let` 语句 | `let Some(x) = opt;` |
| 函数参数 | `fn foo((a, b): (i32, i32)) {}` |
| `match` 分支 | `match x { 1 => ..., _ => ... }` |
| `if let` / `while let` | `if let Ok(v) = res { ... }` |
| `for` 循环 | `for (k, v) in map { ... }` |

## 二、可反驳性

| 模式类型 | 说明 | 示例 |
|:---|:---|:---|
| 不可反驳（irrefutable） | 任何值都匹配 | `x`, `(a, b)`, `Some(x)`（当类型仅含此变体） |
| 可反驳（refutable） | 某些值不匹配 | `Some(x)`, `1..=10`, `Ok(v)` |

`let` 与函数参数要求不可反驳模式（除非使用 `@` 等允许可反驳的扩展上下文）。

## 三、模式形式

| 模式 | 说明 | 示例 |
|:---|:---|:---|
| 通配符 | 匹配任意值，不绑定 | `_` |
| 标识符 | 绑定整个值 | `x` |
| 字面量 | 匹配具体常量 | `42`, `"x"` |
| 范围 | 匹配区间内的值 | `1..=10` |
| 引用 | 匹配引用 | `&x`, `&mut y` |
| 结构体 | 按字段解构 | `Point { x, y }` |
| 元组 | 按位置解构 | `(a, b, c)` |
| 数组/切片 | 匹配数组或可变长度切片 | `[a, b, ..]` |
| 枚举变体 | 匹配枚举 | `Some(x)`, `None` |
| `@` 绑定 | 同时匹配并绑定 | `e @ 1..=10` |
| `|` 或模式 | 多个模式之一 | `1 | 2 | 3` |
| `..` / `..=` | 忽略剩余字段或范围边界 | `Point { x, .. }` |
| Guard | 匹配后附加条件 | `x if x > 0 => ...` |

## 四、绑定模式

默认绑定为 `move`；使用 `ref` 和 `ref mut` 可改为按引用绑定：

```rust
let x = &mut 5;
match x {
    ref mut n => **n += 1,
}
```

> 在 2024 Edition 之前，`ref`/`ref mut` 在 `match` 中常见；现代 Rust 更推荐通过类型系统显式使用 `&` / `&mut` 模式。

## 五、穷尽性检查

`match` 要求模式覆盖被匹配类型的所有可能值。编译器使用模式穷尽性算法确保无遗漏。

---

> **权威来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [Rust Reference — Match Expressions](https://doc.rust-lang.org/reference/expressions/match-expr.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
