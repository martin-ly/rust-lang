# 语句与表达式（Statements and Expressions）

> **EN**: Statements and Expressions
> **Summary**: Rust 作为表达式语言的核心特征：表达式嵌套、求值顺序，以及语句如何封装和显式排序表达式求值。 Core characteristics of Rust as an expression language: nested expressions, evaluation order, and how statements sequence expression evaluation.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Control Flow](01_control_flow.md) · [Variables and Bindings](../03_values_and_references/03_variable_model.md) · [Patterns](02_patterns.md)
> **后置概念**: [Closures](../00_start/03_closure_basics.md) · [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) · [Async/Await](../../03_advanced/01_async/01_async.md)
> **定理链**: Expression → Evaluation Order → Statement Sequencing
> **主要来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [Herlihy & Shavit — The Art of Multiprocessor Programming](https://dl.acm.org/doi/10.5555/2385452) · [Batty et al. — The Semantics of Multicore C](https://doi.org/10.1145/2049706.2049711) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [MIT 6.824 — Distributed Systems](https://pdos.csail.mit.edu/6.824/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL — Functions](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html)

---
> **权威来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [TRPL — Functions](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL）

---

## 一、Rust 是表达式语言

> (Source: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html))

Rust **主要**是一门表达式语言。这意味着大多数产生值或产生副作用的求值都由统一的**表达式（expression）**语法类别驱动。

- 每种表达式通常可以嵌套在另一种表达式内部。
- 表达式求值规则既规定产生的值，也规定子表达式的求值顺序。

相比之下，**语句（statement）**主要用于封装和显式排序表达式的求值。

---

## 二、表达式

Rust 表达式种类繁多，包括但不限于：

| 表达式 | 示例 |
|:---|:---|
| 字面量表达式 | `42`、`"hello"`、`true` |
| 路径表达式 | `foo`、`crate::bar` |
| 块表达式 | `{ let x = 1; x + 2 }` |
| 运算符表达式 | `a + b`、`!x` |
| 分组表达式 | `(a + b) * c` |
| 数组与索引表达式 | `[1, 2, 3]`、`arr[0]` |
| 元组与索引表达式 | `(1, "a")`、`tuple.0` |
| 结构体（Struct）表达式 | `Point { x: 1, y: 2 }` |
| 调用表达式 | `foo(1, 2)` |
| 方法调用表达式 | `obj.method()` |
| 字段访问表达式 | `s.field` |
| 闭包（Closures）表达式 | `\|x\| x + 1` |
| 循环表达式 | `loop {}`、`while cond {}`、`for x in iter {}` |
| Range 表达式 | `1..5`、`1..=5` |
| `if` 表达式 | `if cond { a } else { b }` |
| `match` 表达式 | `match x { ... }` |
| `return` 表达式 | `return 42` |
| `await` 表达式 | `future.await` |
| 下划线表达式 | `_ = expr` |

### 块表达式

块表达式 `{ ... }` 是 Rust 中最重要的表达式之一：

- 内部可以包含语句和末尾表达式。
- 块的值是最后一个表达式的值（若没有则为 `()`）。

```rust
let x = {
    let a = 1;
    let b = 2;
    a + b  // 块的值
};
```

---

## 三、语句

Rust 中的语句主要分为两类：

### 1. 声明语句（Declaration statements）

引入名称的语句，例如 `let` 绑定、item 声明：

```rust
let x = 5;
fn foo() {}
```

### 2. 表达式语句（Expression statements）

由一个表达式加分号 `;` 组成，求值结果被丢弃：

```rust
println!("hello");
```

表达式语句的作用是**显式排序**副作用的发生顺序。

---

## 四、表达式的求值顺序

> (Source: [Rust Reference — Evaluation Order](https://doc.rust-lang.org/reference/expressions.html#evaluation-order))

Rust 规定了大多数子表达式的求值顺序：

- 函数调用参数按**从左到右**顺序求值。
- 结构体（Struct）、数组、元组等复合表达式的元素按**从左到右**顺序求值。
- 短路运算符 `&&`、`\|\|` 按短路语义求值。
- 赋值表达式先求右操作数，再求左操作数。

理解求值顺序对避免未定义行为至关重要，尤其是在 `unsafe` 代码中。

---

## 五、表达式语言的优势

因为 Rust 是表达式语言，许多控制结构本身也是表达式，可以直接返回值：

```rust
let condition = true;
let option = Some(21);

let value = if condition {
    42
} else {
    0
};

let result = match option {
    Some(x) => x * 2,
    None => 0,
};
```

这使得代码更紧凑，同时保持类型安全。

---

## 六、相关概念

- **上层概念**: [Control Flow](01_control_flow.md) · [Variables and Bindings](../03_values_and_references/03_variable_model.md) · [Patterns](02_patterns.md)
- **下层概念**: [Closures](../00_start/03_closure_basics.md) · [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) · [Async/Await](../../03_advanced/01_async/01_async.md)

| 概念 | 关系 |
|:---|:---|
| [Patterns](02_patterns.md) | `let`、`match`、`if let` 等使用模式绑定变量 |
| [Control Flow](01_control_flow.md) | `if`、`match`、`loop` 是核心控制流表达式 |
| [Closures](../00_start/03_closure_basics.md) | 闭包是表达式的一种 |
| [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) | `?` 运算符是基于表达式的错误传播 |
| [Async/Await](../../03_advanced/01_async/01_async.md) | `.await` 是表达式求值的挂起点 |
| [Terminology Glossary](../../00_meta/01_terminology/01_terminology_glossary.md) | 术语表（元层参考） |

---

## 国际权威参考 / International Authority References（P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/if_chain — 生态权威 API 文档（嵌套 `if let` 表达式的宏化实践）](https://docs.rs/if_chain)（2026-07-12 验证 HTTP 200）

---

## 嵌入式测验（Embedded Quiz）

> W3-b 补充（2026-07-12）：本页原无嵌入式测验，按四级题型规范补 3 题（🟢🟡🔴 各 1 题，`<details>` 折叠答案），内容与本页正文严格一致。

### 测验 1：块表达式的值（🟢 基础）

以下代码中 `x` 的值是？

```rust
let x = {
    let a = 1;
    let b = 2;
    a + b
};
```

- A. `()`
- B. `3`
- C. `2`
- D. 编译错误：块不能作为表达式

<details>
<summary>✅ 答案</summary>

**B 正确，`x = 3`**。按本页「块表达式」：块内部可以包含语句和末尾表达式，**块的值是最后一个表达式的值**（若没有则为 `()`）。`a + b` 无分号，是块的末尾表达式，值为 `3`。

</details>

---

### 测验 2：语句的两个类别（🟡 进阶）

关于 Rust 语句的分类，下列说法正确的是？

- A. 声明语句引入名称（如 `let` 绑定、item 声明）；表达式语句由表达式加分号组成，求值结果被丢弃
- B. 所有语句都会产生可被使用的值
- C. 表达式语句的作用是定义新类型
- D. `let x = 5;` 是表达式语句

<details>
<summary>✅ 答案</summary>

**A 正确**。按本页「三、语句」：语句分两类——**声明语句**（引入名称，如 `let x = 5;`、`fn foo() {}`）与**表达式语句**（表达式加分号 `;`，求值结果被丢弃，作用是**显式排序**副作用的发生顺序）。D 错：`let x = 5;` 是声明语句而非表达式语句。

</details>

---

### 测验 3：求值顺序规则（🔴 专家）

关于 Rust 的表达式求值顺序，下列哪项**错误**？

- A. 函数调用参数按从左到右顺序求值
- B. 结构体、数组、元组等复合表达式的元素按从左到右顺序求值
- C. 赋值表达式先求左操作数，再求右操作数
- D. 短路运算符 `&&`、`||` 按短路语义求值

<details>
<summary>✅ 答案</summary>

**C 错误**。按本页「四、表达式的求值顺序」(Source: Rust Reference — Evaluation Order)：赋值表达式是**先求右操作数，再求左操作数**——恰好与 C 所述相反。A/B/D 均为正文列出的规则。理解求值顺序对避免未定义行为至关重要，尤其是在 `unsafe` 代码中。

</details>

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 语言类别 | 面向表达式语言：块、`if`、`match`、`loop` 皆有值 | 语言设计决策 |
| 语句分类 | 声明语句（`let`、项声明）与表达式语句（`;`）两类 | Reference |
| 块求值 | 块值 = 尾表达式值；尾加分号则块值为 `()` | 求值规则 |
| 求值顺序 | 操作数从左到右求值 | Reference 求值顺序 |
| 发散处理 | 发散表达式可出现在任意类型位置（`!` 强制转换） | 类型规则 |

## 🔗 概念关系

- **上位（is-a）**：[Control Flow](01_control_flow.md) 的求值语义基础。
- **下位（实例）**：`if`/`match`/`loop`/块表达式四类表达式实例见本页正文。
- **对偶**：语句（副作用、值为 `()`）与表达式（产出值）二分本身即对偶。
- **组合**：函数体是块表达式，见 [Functions](../07_modules_and_items/02_functions.md)。
- **依赖**：发散表达式的类型合法性依赖 [Never Type](../02_type_system/02_never_type.md)。

---

## ⚠️ 反例与陷阱：表达式块末尾多写分号

**反例**（rustc 1.97 实测编译失败：E0308）：

```rust,compile_fail
fn f() -> i32 {
    5;
}
fn main() { println!("{}", f()); }
```

带分号的 `5;` 是语句而非表达式，函数体尾表达式变为 `()`，与声明的 `i32` 返回类型不匹配。

**修正**：

```rust
fn f() -> i32 {
    5
}
fn main() { println!("{}", f()); }
```
