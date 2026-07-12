# 词法结构（Lexical Structure）

> **EN**: Lexical Structure
> **Summary**: Rust 源程序的 lexical 层面：输入格式、shebang、关键字、标识符、注释、空白、token 分类，以及它们如何被解析为语法单元。 Lexical layer of Rust source programs: input format, shebang, keywords, identifiers, comments, whitespace, token classification, and how they form syntactic units.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位声明**: 本页为 Rust Reference 对应章节的**规范摘译与注解**（规范条文摘译 + 示例 + 交叉引用），非形式化推导或机器验证证明；形式化理论内容见 [Notation](../06_notation/44_notation.md)。依据 [A/S/P 标记规范](../../00_meta/03_audit/asp_marking_guide.md) §3.4，L4 形式化层同时容纳 S（Specification）规范分析类内容，故本页保留于 L4，Bloom 层级维持与内容相符的标注（理解/分析层的规范内容）。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Notation](../06_notation/44_notation.md) · [Programming Language Foundations](../04_model_checking/23_programming_language_foundations.md)
> **后置概念**: [Names and Resolution](40_names_and_resolution.md) · [Items Reference](46_items_reference.md) · [Keywords](../../01_foundation/00_start/36_keywords.md)
> **定理链**: Source Bytes → Unicode → Tokens → AST
>
> **来源**: [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/lexical-structure.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

> **跨层回溯**: [宏系统](../../03_advanced/03_proc_macros/04_macros.md) · [过程宏（Procedural Macro）](../../03_advanced/03_proc_macros/07_proc_macro.md)

---

## 认知路径

1. **问题识别**: 为什么词法结构在 Rust 中值得关注？宏（Macro）展开、属性解析和编译错误定位都依赖精确的 token 划分。
2. **概念建立**: 掌握输入格式、token、关键字、标识符、字面量、注释和白空格的核心定义。
3. **机制推理**: 通过 ⟹ 定理链将字节流、Unicode 解码、token 流和 AST 构建串联起来。
4. **迁移应用**: 将词法结构与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 2**: "忽略词法结构的细节也能写出正确代码" ⟹ 不成立。`macro_rules!` follow-set 歧义、关键字误用和无效标识符都是词法层面的错误。

> **反命题 3**: "其他语言对词法结构的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的生命周期（Lifetimes） token、原始标识符和嵌套块注释具有语言特有形态。

## 一、输入格式

Rust 源文件必须是有效的 **UTF-8** 编码字节序列。编译器不接受其他编码。 (Source: [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/lexical-structure.html))

- 允许的字符包括所有 Unicode 标量值（Unicode scalar value）。
- 不允许的字符包括：surrogate code point（U+D800–U+DFFF）以及大于 U+10FFFF 的值。

```bnf
SourceFile ::= UTF8_Byte*
UTF8_Byte  ::= 0x00 .. 0xFF
ValidChar  ::= UnicodeScalar \ (U+D800 .. U+DFFF | > U+10FFFF)
```

## 二、Shebang

文件首行若以 `#!` 开头，则视为 shebang 行，编译器忽略其内容。这允许在类 Unix 系统上直接执行 Rust 源文件。

```rust
#!/usr/bin/env rust-script
fn main() {}
```

## 三、关键字

Rust 将标识符分为三类 (Source: [Rust Reference — Keywords](https://doc.rust-lang.org/reference/keywords.html))：

| 类别 | 说明 | 示例 |
|:---|:---|:---|
| 严格关键字 | 永远不能用作标识符 | `fn`, `let`, `mut`, `if`, `match`, `struct` |
| 保留关键字 | 当前未使用，但保留给未来 | `become`, `priv`, `typeof`, `unsized`, `do`, `abstract`, `final`, `override` |
| 上下文关键字 | 在特定上下文中具有特殊含义 | `async`, `await`, `dyn`, `union`, `gen`, `yield` |

详细列表见 [Keywords](../../01_foundation/00_start/36_keywords.md)。

## 四、标识符

标识符由 `XID_Start` 或下划线 `_` 开头，后续字符为 `XID_Continue`。下划线单独出现时不是标识符，而是模式中的通配符。

### 原始标识符

使用 `r#` 前缀可以将关键字用作标识符：

```rust
let r#match = 1;
let r#type = "keyword as identifier";
```

### 下划线与未使用绑定

下划线 `_` 作为模式时，表示"忽略该值"，不会触发未使用变量警告：

```rust
let _ = some_side_effect();
```

## 五、注释

| 注释类型 | 语法 | 说明 |
|:---|:---|:---|
| 行注释 | `// ...` | 单行注释 |
| 块注释 | `/* ... */` | 可跨多行，支持嵌套 |
| 文档行注释 | `/// ...` | 生成 rustdoc 文档 |
| 文档块注释 | `/** ... */` | 生成 rustdoc 文档 |
| 模块（Module）文档注释 | `//! ...` | 为包含它的模块生成文档 |

```rust
/// 计算两数之和
///
/// # Examples
/// ```
/// let s = add(1, 2);
/// ```
fn add(a: i32, b: i32) -> i32 {
    a + b // 行注释
}

/* 外层块注释
   /* 嵌套块注释 */
*/
```

## 六、字面量

| 字面量类型 | 示例 | 说明 |
|:---|:---|:---|
| 整数 | `42`, `0x2A`, `0b101010`, `0o52` | 支持十进制/十六进制/二进制/八进制 |
| 浮点数 | `3.14`, `1e10` | `f64` 默认 |
| 字符 | `'a'`, `'\n'`, `'\u{1F600}'` | Unicode 标量值 |
| 字符串 | `"hello"` | UTF-8 字符串 |
| 原始字符串 | `r#"..."#` | 不处理转义 |
| 字节字符串 | `b"hello"` | `&[u8]` 类型 |
| C 字符串 | `c"hello"` | 以 NUL 结尾，用于 FFI |

## 七、Token 与 Token Tree

词法分析将源代码转换为 token 流：

```bnf
Token     ::= Keyword | Identifier | Literal | Punctuation | Delimiter
token_tree::= Token | "(" token_tree* ")" | "[" token_tree* "]" | "{" token_tree* "}"
```

Token tree 是宏系统（`macro_rules!` 和过程宏（Procedural Macro））处理的基本单元。过程宏接收 `TokenStream`，可以遍历、转换并输出新的 token tree。

```bnf
Identifier      ::= XID_Start XID_Continue* | "_" XID_Continue+
RawIdentifier   ::= "r#" Identifier
```

```rust
let valid_name = 1;
let _ = 2;            // 通配符，非标识符
let r#match = 3;      // 原始标识符
let r#type = "type";  // 原始标识符
```

## 五、注释

| 注释形式 | 说明 |
|:---|:---|
| `//` | 行注释 |
| `/* ... */` | 块注释，可嵌套 |
| `///` | 外部文档注释，作用于后续 item |
| `//!` | 内部文档注释，作用于 enclosing item |
| `//=` / `/*=` | 不稳定：保留用于 future expansion |

文档注释在词法阶段被解析为 `#[doc = "..."]` 属性：

```rust
/// A point in 2D space.
struct Point;

// 等价于
#[doc = " A point in 2D space."]
struct Point2;
```

## 六、空白

空白字符包括空格、制表符、换行、回车以及 Unicode 中的其他空白字符。空白用于分隔 token，但在大多数场景下不影响语义。

```bnf
Whitespace ::= " " | "\t" | "\n" | "\r" | Unicode_White_Space
```

## 七、Token 分类

Rust token 主要包括：

| 类别 | 示例 |
|:---|:---|
| 字面量 | `42`, `"hello"`, `'a'`, `b"bytes"`, `0xFF`, `1.5e10` |
| 标识符 | `foo`, `Foo`, `_bar`, `r#match` |
| 关键字 | `fn`, `let`, `struct`, `async` |
| 标点符号 | `(`, `)`, `{`, `}`, `;`, `,`, `::`, `->` |
| 生命周期（Lifetimes） | `'a`, `'static` |
| 文档注释 | `///`, `//!` |

### 字面量子类

| 类型 | 示例 | 说明 |
|:---|:---|:---|
| 整数字面量 | `123`, `0xFF`, `0o77`, `0b1010` | 支持类型后缀如 `1u32` |
| 浮点字面量 | `1.5`, `1e10`, `1.5f64` | 必须包含小数点或指数 |
| 字符字面量 | `'a'`, `'\n'`, `'\u{1F600}'` | 单个 Unicode 标量值 |
| 字符串字面量 | `"hello"`, `r#"raw"#` | UTF-8 字符串 |
| 字节字符串 | `b"bytes"`, `br#"raw"#` | ASCII 字节串 |
| 字节字面量 | `b'a'` | 单个 `u8` 值 |

## 八、与语法分析的关系

词法分析将源文件转换为 token 流；语法分析在 token 流上应用产生式规则。词法规则与语法规则共同构成 Rust 完整文法。

```text
Source Bytes → UTF-8 Decode → Char Stream
Char Stream  → Lexer       → Token Stream
Token Stream → Parser      → AST
```

## 九、Token Tree 与宏

过程宏和声明宏（Declarative Macro）操作的单位是 **Token Tree（TokenTree）**：

```bnf
TokenTree ::= Token | DelimitedTree
DelimitedTree ::= "(" TokenTree* ")"
                | "[" TokenTree* "]"
                | "{" TokenTree* "}"
```

宏（Macro）展开阶段，编译器在 token tree 层面匹配和替换，随后再次进行名称解析和类型检查。

## 十、相关概念

| 概念 | 关系 |
|:---|:---|
| [Names and Resolution](40_names_and_resolution.md) | token 之上进行名称解析 |
| [Items Reference](46_items_reference.md) | item 语法基于 token 流构建 |
| [Macros](../../03_advanced/03_proc_macros/04_macros.md) | 宏在 token tree 层面操作 |
| [Keywords](../../01_foundation/00_start/36_keywords.md) | 关键字是特殊 token |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | `unsafe` 是词法关键字，触发特殊解析上下文 |

## 过渡段

> **过渡**: 从源文件字节序列过渡到 Unicode 规范化，可以理解 Rust 词法分析的第一步如何处理输入编码。
>
> **过渡**: 从标识符规则与关键字过渡到 token 分类，可以建立“字符流 → token 流 → 语法树”的编译前端模型。
>
> **过渡**: 从 token 分类过渡到语法产生式，可以链接 [Notation](../06_notation/44_notation.md) 与条目参考，形成完整参考链。
>
---

> **权威来源**: [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/lexical-structure.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Rust Reference — Keywords](https://doc.rust-lang.org/reference/keywords.html) · [Rust Reference — Tokens](https://doc.rust-lang.org/reference/tokens.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Oxide: The Essence of Rust (arXiv:1903.00982)](https://arxiv.org/abs/1903.00982) · [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs (PLDI 2022)](https://dl.acm.org/doi/10.1145/3519939.3523704)
- **P2 生态/社区**: [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) · [model-checking/kani — 模型检查器](https://github.com/model-checking/kani)
