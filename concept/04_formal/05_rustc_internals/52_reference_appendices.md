# Rust Reference 附录（Reference Appendices）

> **EN**: Reference Appendices
> **Summary**: Rust Reference 附录概览：语法摘要、语法索引、宏 follow-set 歧义规范、语言影响、测试摘要与术语表。 Overview of Rust Reference appendices: grammar summary, syntax index, macro follow-set ambiguity, language influences, test summary, and glossary.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ref — 规范参考
> **前置依赖**: [Notation](../06_notation/44_notation.md) · [Lexical Structure](45_lexical_structure.md) · [Items Reference](46_items_reference.md)
> **后置概念**: [Statements and Expressions Reference](48_statements_and_expressions_reference.md) · [Patterns Reference](49_patterns_reference.md)
> **定理链**: Grammar → Lexicon → Syntax Index → Test Summary
>
> **来源**: [Rust Reference — Appendices](https://doc.rust-lang.org/reference/appendices.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

> **跨层回溯**: [宏系统](../../03_advanced/03_proc_macros/04_macros.md) · [过程宏（Procedural Macro）](../../03_advanced/03_proc_macros/07_proc_macro.md)

---

## 认知路径

> **认知路径**: 本节从 "Rust Reference 附录（Reference Appendices）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust Reference 附录值得关注？附录汇总了完整文法、语法索引和宏（Macro）歧义规则，是阅读规范时的快速参考。
2. **概念建立**: 掌握附录结构、语法摘要、语法索引和术语表的内容。
3. **机制推理**: 通过 ⟹ 定理链将文法、词法、语法索引和测试摘要串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与 Rust Reference 附录的适用边界。
5. **迁移应用**: 将 Rust Reference 附录与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust Reference 附录在所有场景下都适用" ⟹ 不成立。附录是规范摘要，实际编译器实现可能包含尚未写入 Reference 的扩展或 nightly 特性。

> **反命题 2**: "忽略 Rust Reference 附录的细节也能写出正确代码" ⟹ 不成立。宏 follow-set 歧义规则和完整文法是编写复杂宏和形式化分析的基础。

> **反命题 3**: "其他语言对参考附录的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust Reference 附录的组织方式、测试映射和术语定义具有语言特异性。

## 一、附录结构

Rust Reference 包含以下附录：

| 附录 | 主题 | 用途 |
|:---|:---|:---|
| A | Grammar Summary | 完整文法产生式汇总 |
| B | Syntax Index | 按关键字/符号索引语法规则 |
| C | Macro Follow-Set Ambiguity | `macro_rules!` follow-set 歧义判定 |
| D | Influences | Rust 设计的语言和理论影响 |
| E | Glossary | 术语表 |
| F | Test Summary | Reference 规则与 rustc 测试的映射 |

## 二、Grammar Summary

Grammar Summary 汇总 Rust 完整文法，包括：

- Lexical 产生式（token 定义）
- 语句和表达式产生式
- 类型、模式、item 产生式
- 属性与 macro 产生式

阅读时应结合 [Notation](../06_notation/44_notation.md) 理解产生式符号。

### 示例产生式

```bnf
BlockExpression ::= "{" Statement* Expression? "}"
Statement       ::= LetStatement | ItemStatement | ExpressionStatement
LetStatement    ::= "let" Pattern (":" Type)? ("=" Expression)? ";"
```

## 三、Syntax Index

Syntax Index 按关键字和标点符号列出相关语法规则，便于快速查找：

| 符号/关键字 | 相关规则 |
|:---|:---|
| `fn` | 函数定义、函数指针类型 |
| `impl` | 实现、inherent impl、trait impl |
| `->` | 返回类型、函数类型 |
| `?` | try 运算符、宏重复计数器 |
| `unsafe` | `unsafe` 块、函数、trait、impl |
| `async` | async 块、async 闭包（Closures） |
| `match` | match 表达式 |

## 四、Macro Follow-Set Ambiguity

该附录形式化定义 `macro_rules!` 重复模式后接 token 是否会产生解析歧义，决定宏定义是否合法。

核心规则：若某 token 可能作为多个重复模式的 follow，则产生歧义。

```rust
macro_rules! ambiguous {
    ($($e:expr),* $(,)?) => {}; // OK：尾随逗号处理
}
```

### Follow-Set 规则概要

| 片段分类器 | Follow-Set 示例 |
|:---|:---|
| `expr` | `=>`, `,`, `;` 等 |
| `stmt` | `=>`, `,`, `;` 等 |
| `ty` | `=>`, `,`, `=`, `>`, `;` 等 |
| `pat` | `=>`, `,`, `=`, `\|`, `if`, `in` 等 |

## 五、Influences

Rust 受到多种语言影响：

| 语言/理论 | 影响领域 |
|:---|:---|
| C/C++ | 零成本抽象（Zero-Cost Abstraction）、内存布局、FFI |
| ML/OCaml | 类型推断（Type Inference）、代数数据类型、模式匹配（Pattern Matching） |
| Haskell | Type classes → traits、类型系统（Type System） |
| Cyclone | 区域类型、借用（Borrowing）概念 |
| Linear Logic | 所有权（Ownership）与资源管理 |
| Newsqueak/Alef/Limbo | 通道与并发模型 |

## 六、Glossary

术语表定义 Rust Reference 中使用的核心术语：

| 术语 | 定义 |
|:---|:---|
| item | crate 中的声明单元 |
| place expression | 表示内存位置的表达式 |
| value expression | 产生值的表达式 |
| const context | 要求常量表达式的上下文 |
| dangling pointer | 指向已释放内存的指针 |
| unsized type | 编译期大小未知的类型，如 `dyn Trait` |

## 七、测试摘要

Rust Reference 附录的 Test Summary 将规范规则映射到 rustc 测试文件，帮助实现者和研究者验证规范与编译器行为的一致性（Coherence）。

| 规范区域 | 典型测试目录 |
|:---|:---|
| 词法结构 | `src/test/ui/lexer/` |
| 名称解析 | `src/test/ui/resolve/` |
| 类型检查 | `src/test/ui/typeck/` |
| borrowck | `src/test/ui/borrowck/` |
| unsafe | `src/test/ui/unsafe/` |

## 八、关联概念

| 概念 | 关系 |
|:---|:---|
| [Lexical Structure](45_lexical_structure.md) | Grammar Summary 的词法基础 |
| [Items Reference](46_items_reference.md) | item 产生式是文法核心 |
| [Statements and Expressions Reference](48_statements_and_expressions_reference.md) | 表达式产生式构成文法主体 |
| [Patterns Reference](49_patterns_reference.md) | 模式产生式是文法重要部分 |
| [Macros](../../03_advanced/03_proc_macros/04_macros.md) | Follow-Set 规则用于宏定义 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | unsafe 相关产生式在文法中特殊处理 |

---

> **权威来源**: [Rust Reference — Appendices](https://doc.rust-lang.org/reference/appendices.html) · [Rust Reference — Grammar Summary](https://doc.rust-lang.org/reference/grammar.html) · [Rust Reference — Macro Follow-Set Ambiguity](https://doc.rust-lang.org/reference/macros-by-example.html#follow-set-ambiguity-restrictions) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
