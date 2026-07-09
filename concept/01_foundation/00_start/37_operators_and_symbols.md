> **内容分级**: [综述级]
>
# Rust 运算符与符号（Operators and Symbols）

> **EN**: Operators and Symbols
> **Summary**: Rust 语法中运算符与各类符号的速查参考，包括可重载运算符对应的 trait、路径/泛型/trait bound/宏（Macro）/注释/括号等上下文中的符号含义。 Quick reference of Rust operators and symbols, including overloadable traits and meanings in paths, generics, trait bounds, macros, comments, and brackets.
>
> **受众**: [初学者] / [中级]
> **Bloom 层级**: 记忆 → 理解
> **A/S/P 标记**: **S** — Specification / Language syntax
> **双维定位**: S×Lang — 语言词法与语法
> **前置依赖**: [Keywords](36_keywords.md) · [Type System](../02_type_system/04_type_system.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Traits](../02_type_system/04_type_system.md) · [Generics](../../02_intermediate/01_generics/02_generics.md) · [Macros](../../03_advanced/03_proc_macros/04_macros.md)
> **定理链**: N/A — 参考级文档
> **主要来源**: [Rust Reference — Tokens](https://doc.rust-lang.org/reference/tokens.html) · [TRPL — Appendix B](https://doc.rust-lang.org/book/appendix-02-operators.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Unicode UAX #31 — Identifier and Pattern Syntax](https://www.unicode.org/reports/tr31/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)

>
> **来源**: [TRPL — Appendix B: Operators and Symbols](https://doc.rust-lang.org/book/appendix-02-operators.html)

---

---

## 认知路径

> **认知路径**: 本节从 "Rust 运算符与符号（Operators and Symb" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 运算符与符号（Operators and Symb 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Rust 运算符与符号（Operators and Symb 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Rust 运算符与符号（Operators and Symb的适用边界。
5. **迁移应用**: 将 Rust 运算符与符号（Operators and Symb 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 Rust 运算符与符号（Operators and Symb 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Rust 运算符与符号（Operators and Symb 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Rust 运算符与符号（Operators and Symb 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Rust 运算符与符号（Operators and Symb 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Rust 运算符与符号（Operators and Symb 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Rust 运算符与符号（Operators and Symb 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "Rust 运算符与符号（Operators and Symb 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Rust 运算符与符号（Operators and Symb 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Rust 运算符与符号（Operators and Symb 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Rust 运算符与符号（Operators and Symb 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Rust 运算符与符号（Operators and Symb 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 Rust 运算符与符号（Operators and Symb 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 Rust 运算符与符号（Operators and Symb 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、运算符

| 运算符 | 示例 | 说明 | 可重载？ |
|:---|:---|:---|:---:|
| `!` | `ident!(...)` / `ident!{...}` / `ident![...]` | 宏（Macro）展开 | — |
| `!` | `!expr` | 按位/逻辑取反 | `Not` |
| `!=` | `expr != expr` | 不等比较 | `PartialEq` |
| `%` | `expr % expr` | 算术取余 | `Rem` |
| `%=` | `var %= expr` | 取余并赋值 | `RemAssign` |
| `&` | `&expr` / `&mut expr` | 借用（Borrowing） | — |
| `&` | `&type` / `&mut type` / `&'a type` | 借用（Borrowing）指针类型 | — |
| `&` | `expr & expr` | 按位与 | `BitAnd` |
| `&=` | `var &= expr` | 按位与并赋值 | `BitAndAssign` |
| `&&` | `expr && expr` | 短路逻辑与 | — |
| `*` | `expr * expr` | 算术乘法 | `Mul` |
| `*=` | `var *= expr` | 乘法并赋值 | `MulAssign` |
| `*` | `*expr` | 解引用（Reference） | `Deref` |
| `*` | `*const type` / `*mut type` | 原始指针（Raw Pointer）类型 | — |
| `+` | `trait + trait` / `'a + trait` | 复合类型约束 | — |
| `+` | `expr + expr` | 算术加法 | `Add` |
| `+=` | `var += expr` | 加法并赋值 | `AddAssign` |
| `,` | `expr, expr` | 参数/元素分隔符 | — |
| `-` | `-expr` | 算术取负 | `Neg` |
| `-` | `expr - expr` | 算术减法 | `Sub` |
| `-=` | `var -= expr` | 减法并赋值 | `SubAssign` |
| `->` | `fn(...) -> type` / `|…| -> type` | 函数/闭包（Closures）返回类型 | — |
| `.` | `expr.ident` | 字段访问 | — |
| `.` | `expr.ident(...)` | 方法调用 | — |
| `.` | `expr.0` / `expr.1` | 元组索引 | — |
| `..` | `..` / `expr..` / `..expr` / `expr..expr` | 右开区间 | `PartialOrd` |
| `..=` | `..=expr` / `expr..=expr` | 右闭区间 | `PartialOrd` |
| `..` | `..expr` | struct update 语法 | — |
| `..` | `variant(x, ..)` / `struct { x, .. }` | “其余部分”模式绑定 | — |
| `...` | `expr...expr` | 已废弃，改用 `..=` | — |
| `/` | `expr / expr` | 算术除法 | `Div` |
| `/=` | `var /= expr` | 除法并赋值 | `DivAssign` |
| `:` | `pat: type` / `ident: type` | 类型约束 | — |
| `:` | `ident: expr` | struct 字段初始化 | — |
| `:` | `'a: loop { ... }` | 循环标签 | — |
| `;` | `expr;` | 语句/项结束符 | — |
| `;` | `[...; len]` | 定长数组语法的一部分 | — |
| `<<` | `expr << expr` | 左移 | `Shl` |
| `<<=` | `var <<= expr` | 左移并赋值 | `ShlAssign` |
| `<` | `expr < expr` | 小于 | `PartialOrd` |
| `<=` | `expr <= expr` | 小于等于 | `PartialOrd` |
| `=` | `var = expr` / `ident = type` | 赋值/等价 | — |
| `==` | `expr == expr` | 等于 | `PartialEq` |
| `=>` | `pat => expr` | match arm 语法 | — |
| `>` | `expr > expr` | 大于 | `PartialOrd` |
| `>=` | `expr >= expr` | 大于等于 | `PartialOrd` |
| `>>` | `expr >> expr` | 右移 | `Shr` |
| `>>=` | `var >>= expr` | 右移并赋值 | `ShrAssign` |
| `@` | `ident @ pat` | 模式绑定 | — |
| `^` | `expr ^ expr` | 按位异或 | `BitXor` |
| `^=` | `var ^= expr` | 按位异或并赋值 | `BitXorAssign` |
| `\|` | `pat \| pat` | 模式备选 | — |
| `\|` | `expr \| expr` | 按位或 | `BitOr` |
| `\|=` | `var \|= expr` | 按位或并赋值 | `BitOrAssign` |
| `\|\|` | `expr \|\| expr` | 短路逻辑或 | — |
| `?` | `expr?` | 错误传播 | `Try` |

---

## 二、独立符号

| 符号 | 说明 |
|:---|:---|
| `'ident` | 命名生命周期（Lifetimes）或循环标签 |
| `123i32` / `3.14f64` / `0xFFu8` | 带类型后缀的数字字面量 |
| `"..."` | 字符串字面量 |
| `r"..."` / `r#"..."#` | 原始字符串字面量（不处理转义） |
| `b"..."` | 字节字符串字面量（`&[u8]`） |
| `br"..."` / `br#"..."#` | 原始字节字符串字面量 |
| `'a'` | 字符字面量 |
| `b'a'` | ASCII 字节字面量 |
| `\|…\| expr` | 闭包（Closures） |
| `!` | 发散函数/ never type |
| `_` | 忽略的模式绑定；也用于数字可读性分隔 |

---

## 三、路径相关符号

| 符号 | 说明 |
|:---|:---|
| `ident::ident` | 命名空间路径 |
| `::path` | 相对于 crate root 的绝对路径 |
| `self::path` | 相对于当前模块（Module）的路径 |
| `super::path` | 相对于父模块（Module）的路径 |
| `type::ident` / `<type as trait>::ident` | 关联常量、函数、类型 |
| `<type>::...` | 不能直接命名的类型的关联项，如 `<&T>::...`、`<[T]>::...` |
| `trait::method(...)` | 通过 trait 名消除方法调用歧义 |
| `type::method(...)` | 通过类型名消除方法调用歧义 |
| `<type as trait>::method(...)` | 通过 trait 和类型同时消除歧义 |

---

## 四、泛型相关符号

| 符号 | 说明 |
|:---|:---|
| `path<...>` | 为泛型（Generics）类型指定参数，如 `Vec<u8>` |
| `path::<...>` / `method::<...>` | 表达式中为泛型（Generics）指定参数（turbofish），如 `"42".parse::<i32>()` |
| `fn ident<...> ...` | 定义泛型（Generics）函数 |
| `struct ident<...> ...` | 定义泛型（Generics）结构体（Struct） |
| `enum ident<...> ...` | 定义泛型（Generics）枚举（Enum） |
| `impl<...> ...` | 定义泛型（Generics）实现 |
| `for<...> type` | 高阶生命周期（Lifetimes）约束 |
| `type<ident=type>` | 为关联类型赋值，如 `Iterator<Item=T>` |

---

## 五、Trait Bound 约束

| 符号 | 说明 |
|:---|:---|
| `T: U` | 泛型参数 `T` 必须实现 `U` |
| `T: 'a` | `T` 必须 outlive 生命周期（Lifetimes） `'a` |
| `T: 'static` | `T` 不包含非 `'static` 的借用（Borrowing） |
| `'b: 'a` | 生命周期（Lifetimes） `'b` 必须 outlive `'a` |
| `T: ?Sized` | 允许 `T` 为动态大小类型 |
| `'a + trait` / `trait + trait` | 复合约束 |

---

## 六、宏与属性

| 符号 | 说明 |
|:---|:---|
| `#[meta]` | 外部属性 |
| `#![meta]` | 内部属性 |
| `$ident` | 宏（Macro）替换 |
| `$ident:kind` | 宏（Macro）元变量 |
| `$(...)...` | 宏（Macro）重复 |
| `ident!(...)` / `ident!{...}` / `ident![...]` | 宏（Macro）调用 |

---

## 七、注释

| 符号 | 说明 |
|:---|:---|
| `//` | 行注释 |
| `///` | 外部行文档注释 |
| `//!` | 内部行文档注释 |
| `/* ... */` | 块注释 |
| `/** ... */` | 外部块文档注释 |
| `/*! ... */` | 内部块文档注释 |

---

## 八、括号

### 圆括号 `()`

| 符号 | 说明 |
|:---|:---|
| `()` | 空元组 / unit 类型 |
| `(expr)` | 括号表达式 |
| `(expr,)` | 单元素元组表达式 |
| `(type,)` | 单元素元组类型 |
| `(expr, ...)` | 元组表达式 |
| `(type, ...)` | 元组类型 |
| `expr(expr, ...)` | 函数调用；也用于初始化元组 struct/enum 变体 |

### 花括号 `{}`

| 符号 | 说明 |
|:---|:---|
| `{ ... }` | 块表达式 |
| `Type { ... }` | struct 字面量 |

### 方括号 `[]`

| 符号 | 说明 |
|:---|:---|
| `[...]` | 数组字面量 |
| `[expr; len]` | 包含 `len` 个 `expr` 的数组 |
| `[type; len]` | 包含 `len` 个 `type` 的数组类型 |
| `expr[expr]` | 集合索引（可重载：`Index`、`IndexMut`） |
| `expr[..]` / `expr[a..]` / `expr[..b]` / `expr[a..b]` | 使用 range 类型的切片（Slice）索引 |

---

## 九、关联概念

| 概念 | 关系 |
|:---|:---|
| [Keywords](36_keywords.md) | 运算符与符号共同构成 Rust 词法 |
| [Traits](../02_type_system/04_type_system.md) | 多数运算符通过 trait 重载 |
| [Generics](../../02_intermediate/01_generics/02_generics.md) | `<>`、`:`、`where` 用于泛型约束 |
| [Macros](../../03_advanced/03_proc_macros/04_macros.md) | `!`、`$`、`$(...)` 用于宏系统 |
