# Rust Reference 附录（Reference Appendices）

> **EN**: Reference Appendices
> **Summary**: Rust Reference 附录概览：语法摘要、语法索引、宏（Macro） follow-set 歧义规范、语言影响、测试摘要与术语表。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ref — 规范参考
> **前置依赖**: [Notation](44_notation.md) · [Lexical Structure](45_lexical_structure.md) · [Items Reference](46_items_reference.md)
> **后置概念**: [Statements and Expressions Reference](48_statements_and_expressions_reference.md) · [Patterns Reference](49_patterns_reference.md)
> **定理链**: Grammar → Lexicon → Syntax Index → Test Summary
>
> **来源**: [Rust Reference — Appendices](https://doc.rust-lang.org/reference/appendices.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

> **跨层回溯**: [宏系统](../03_advanced/04_macros.md) · [过程宏（Procedural Macro）](../03_advanced/07_proc_macro.md)

---

## 认知路径

> **认知路径**: 本节从 "Rust Reference 附录（Reference Ap" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust Reference 附录（Reference Ap 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Rust Reference 附录（Reference Ap 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Rust Reference 附录（Reference Ap的适用边界。
5. **迁移应用**: 将 Rust Reference 附录（Reference Ap 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust Reference 附录（Reference Ap 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Rust Reference 附录（Reference Ap 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Rust Reference 附录（Reference Ap 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Rust Reference 附录（Reference Ap 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Rust Reference 附录（Reference Ap 具有语言特有的形态。

## 一、附录结构

Rust Reference 包含以下附录：

| 附录 | 主题 | 用途 |
|:---|:---|:---|
| A | Grammar Summary | 完整文法产生式汇总 |
| B | Syntax Index | 按关键字/符号索引语法规则 |
| C | Macro Follow-Set Ambiguity | `macro_rules!`  follow-set 歧义判定 |
| D | Influences | Rust 设计的语言和理论影响 |
| E | Glossary | 术语表 |
| F | Test Summary | Reference 规则与 rustc 测试的映射 |

## 二、Grammar Summary

Grammar Summary 汇总 Rust 完整文法，包括：

- Lexical 产生式（token 定义）
- 语句和表达式产生式
- 类型、模式、item 产生式
- 属性与 macro 产生式

阅读时应结合 [Notation](44_notation.md) 理解产生式符号。

## 三、Syntax Index

Syntax Index 按关键字和标点符号列出相关语法规则，便于快速查找：

- `fn` → 函数定义、函数指针类型
- `impl` → 实现、inherent impl、trait impl
- `->` → 返回类型、函数类型
- `?` → try 运算符、宏（Macro）重复计数器

## 四、Macro Follow-Set Ambiguity

该附录形式化定义 `macro_rules!` 重复模式后接 token 是否会产生解析歧义，决定宏（Macro）定义是否合法。

核心规则：若某 token 可能作为多个重复模式的 follow，则产生歧义。

## 五、Influences

Rust 受到多种语言影响：

| 语言/理论 | 影响领域 |
|:---|:---|
| C/C++ | 零成本抽象（Zero-Cost Abstraction）、内存布局、FFI |
| ML/OCaml | 类型推断（Type Inference）、代数数据类型、模式匹配（Pattern Matching） |
| Haskell | Type classes → traits、类型系统（Type System） |
| Cyclone | 区域类型、借用（Borrowing）概念 |
| Linear Logic | 所有权（Ownership）与资源管理 |

## 六、Glossary

术语表定义 Rust Reference 中使用的核心术语：

- **item**：crate 中的声明单元。
- **place expression**：表示内存位置的表达式。
- **value expression**：产生值的表达式。
- **const context**：要求常量表达式的上下文。

---

> **权威来源**: [Rust Reference — Appendices](https://doc.rust-lang.org/reference/appendices.html) · [Rust Reference — Grammar Summary](https://doc.rust-lang.org/reference/grammar.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
