# 宏系统形式化 {#宏系统形式化}

> **EN**: Macro System
> **Summary**: 宏系统形式化 Macro System.
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L3-L5 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: 🔄 持续推进中（骨架已建立，形式化定义与反例待补全）
> **层级**: L3-L5
> **概念族**: 形式化方法 / 宏（Macro）系统
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) | [Rust RFCs](https://rust-lang.github.io/rfcs/)

---

## 📑 目录 {#目录}

- [宏系统形式化 {#宏系统形式化}](#宏系统形式化-宏系统形式化)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、核心概念 {#一核心概念}](#一核心概念-一核心概念)
  - [二、形式化定义 {#二形式化定义}](#二形式化定义-二形式化定义)
    - [Def 1.1 声明宏（Declarative Macro） {#def-11-声明宏}](#def-11-声明宏-def-11-声明宏)
    - [Def 1.2 过程宏（Procedural Macro） {#def-12-过程宏}](#def-12-过程宏-def-12-过程宏)
    - [Axiom 1.1 卫生性 {#axiom-11-卫生性}](#axiom-11-卫生性-axiom-11-卫生性)
  - [三、Rust 实现 {#三rust-实现}](#三rust-实现-三rust-实现)
  - [四、反例与边界 {#四反例与边界}](#四反例与边界-四反例与边界)
    - [反例 1：宏规则歧义 {#反例-1宏规则歧义}](#反例-1宏规则歧义-反例-1宏规则歧义)
    - [反例 2：过程宏生成非法代码 {#反例-2过程宏生成非法代码}](#反例-2过程宏生成非法代码-反例-2过程宏生成非法代码)
  - [五、与其他概念的关系 {#五与其他概念的关系}](#五与其他概念的关系-五与其他概念的关系)
  - [六、权威来源索引 {#六权威来源索引}](#六权威来源索引-六权威来源索引)
  - [学术/社区来源参考 {#学术社区来源参考}](#学术社区来源参考-学术社区来源参考)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、核心概念 {#一核心概念}

Rust 宏系统分为两大类：

- **声明宏（Declarative Macros）**：`macro_rules!`，基于模式匹配（Pattern Matching）和模板替换。
- **过程宏（Procedural Macros）**：在编译期接收 TokenStream 并输出 TokenStream，包括 derive、attribute-like 和 function-like 三种。

形式化上，声明宏可视为从语法树模式到语法树模板的偏函数；过程宏则可视为编译期函数 `TokenStream -> TokenStream`。

---

## 二、形式化定义 {#二形式化定义}

### Def 1.1 声明宏 {#def-11-声明宏}

一个声明宏是二元组

```text
M := (P, T)
```

其中：

- `P`：匹配模式集合，每个模式包含 matcher（`$x:expr` 等）和重复操作符（`$()*`、`$()+`、`$()?`）。
- `T`：对应模板集合，模板中的元变量按模式捕获的值进行替换。

### Def 1.2 过程宏 {#def-12-过程宏}

过程宏是编译期函数

```text
proc_macro: TokenStream -> Result<TokenStream, CompileError>
```

其输入/输出均满足 Rust 词法/语法规则，但函数体可用任意语言编写（通常用 Rust）。

### Axiom 1.1 卫生性 {#axiom-11-卫生性}

> **来源**: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)

宏引入的标识符不会与调用处标识符意外冲突；反过来说，调用处标识符也不会直接捕获宏内部私有标识符。

---

## 三、Rust 实现 {#三rust-实现}

```rust
// 声明宏示例
macro_rules! assert_matches {
    ($left:expr, $right:pat) => {{
        match $left {
            $right => {}
            _ => panic!("pattern does not match"),
        }
    }};
}

// 过程宏示例（框架）
use proc_macro::TokenStream;

#[proc_macro]
pub fn cfg_select(input: TokenStream) -> TokenStream {
    // 解析 input 并生成 cfg 分支代码
    input
}
```

> **待补全**：`assert_matches!` / `cfg_select!` 的完整形式化语义、与 1.96 宏特性的衔接。

---

## 四、反例与边界 {#四反例与边界}

### 反例 1：宏规则歧义 {#反例-1宏规则歧义}

多个模式可能同时匹配同一输入，导致歧义或意外选择。

> **待补全**：给出具体歧义示例与修复方案。

### 反例 2：过程宏生成非法代码 {#反例-2过程宏生成非法代码}

过程宏输出不符合 Rust 语法时，编译错误定位在调用处而非宏定义处。

---

## 五、与其他概念的关系 {#五与其他概念的关系}

- **类型系统（Type System）**：过程宏生成的代码必须仍通过类型检查。
- **借用（Borrowing）检查器**：宏展开后的代码受相同借用规则约束。
- **宏速查卡**: [10_macros_cheatsheet.md](../10_macros_cheatsheet.md) 提供语法和模式速查。

---

## 六、权威来源索引 {#六权威来源索引}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
> **来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
> **来源**: [Rust Reference – Macros](https://doc.rust-lang.org/reference/macros.html)
> **来源**: [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Oxide](https://arxiv.org/abs/1903.00982)
