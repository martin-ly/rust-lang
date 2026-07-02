# 词法结构（Lexical Structure）

> **EN**: Lexical Structure
> **Summary**: Rust 源程序的 lexical 层面：输入格式、shebang、关键字、标识符、注释、空白、token 分类，以及它们如何被解析为语法单元。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Notation](44_notation.md) · [Programming Language Foundations](23_programming_language_foundations.md)
> **后置概念**: [Names and Resolution](40_names_and_resolution.md) · [Items Reference](46_items_reference.md) · [Keywords](../01_foundation/36_keywords.md)
> **定理链**: Source Bytes → Unicode → Tokens → AST
>
> **来源**: [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/lexical-structure.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、输入格式

Rust 源文件必须是有效的 **UTF-8** 编码字节序列。编译器不接受其他编码。

- 允许的字符包括所有 Unicode 标量值（Unicode scalar value）。
- 不允许的字符包括：surrogate code point（U+D800–U+DFFF）以及大于 U+10FFFF 的值。

## 二、Shebang

文件首行若以 `#!` 开头，则视为 shebang 行，编译器忽略其内容。这允许在类 Unix 系统上直接执行 Rust 源文件。

```rust
#!/usr/bin/env rust-script
fn main() {}
```

## 三、关键字

Rust 将标识符分为三类：

| 类别 | 说明 | 示例 |
|:---|:---|:---|
| 严格关键字 | 永远不能用作标识符 | `fn`, `let`, `mut`, `if`, `match` |
| 保留关键字 | 当前未使用，但保留给未来 | `become`, `priv`, `typeof`, `unsized`, `do`, `abstract`, `final`, `override` |
| 上下文关键字 | 在特定上下文中具有特殊含义 | `async`, `await`, `dyn`, `union` |

详细列表见 [Keywords](../01_foundation/36_keywords.md)。

## 四、标识符

标识符由 `XID_Start` 或下划线 `_` 开头，后续字符为 `XID_Continue`。下划线单独出现时不是标识符，而是模式中的通配符。

```rust
let valid_name = 1;
let _ = 2; // 通配符，非标识符
```

## 五、注释

| 注释形式 | 说明 |
|:---|:---|
| `//` | 行注释 |
| `/* ... */` | 块注释，可嵌套 |
| `///` | 外部文档注释（doc comment），作用于后续 item |
| `//!` | 内部文档注释，作用于 enclosing item |
| `//=` / `/*=` | 不稳定：保留用于 future expansion |

文档注释在词法阶段被解析为 `#[doc = "..."]` 属性。

## 六、空白

空白字符包括空格、制表符、换行、回车以及 Unicode 中的其他空白字符。空白用于分隔 token，但在大多数场景下不影响语义。

## 七、Token 分类

Rust token 主要包括：

| 类别 | 示例 |
|:---|:---|
| 字面量 | `42`, `"hello"`, `'a'`, `b"bytes"`, `0xFF`, `1.5e10` |
| 标识符 | `foo`, `Foo`, `_bar` |
| 关键字 | `fn`, `let`, `struct` |
| 标点符号 | `(`, `)`, `{`, `}`, `;`, `,`, `::`, `->` |
| 生命周期 | `'a`, `'static` |
| 文档注释 | `///`, `//!` |

## 八、与语法分析的关系

词法分析将源文件转换为 token 流；语法分析在 token 流上应用产生式规则。词法规则与语法规则共同构成 Rust 完整文法。

---

> **权威来源**: [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/lexical-structure.html) · [Rust Reference — Keywords](https://doc.rust-lang.org/reference/keywords.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
