# 模式匹配（Patterns）

> **EN**: Patterns
> **Summary**: Rust 模式匹配的权威规范：解构、可反驳性、各种模式形式（literal、identifier、wildcard、rest、range、reference、struct、tuple、slice、path、or-patterns）及其绑定模式。 Authoritative specification of Rust pattern matching: destructuring, refutability, all pattern forms, and binding modes.
>
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Type System](../02_type_system/04_type_system.md) · [Control Flow](07_control_flow.md) · [Enums and Variants](../02_type_system/04_type_system.md)
> **后置概念**: [Match Expressions](41_statements_and_expressions.md) · [Destructuring](../../02_intermediate/01_generics/02_generics.md) · [Refutability Analysis](../../02_intermediate/04_types_and_conversions/20_type_system_advanced.md)
> **定理链**: Pattern → Refutability → Exhaustiveness
> **主要来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL — Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html)

---

---
> **权威来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [TRPL — Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL）

## 认知路径

> **认知路径**: 本节从 "模式匹配（Patterns）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 模式匹配（Patterns） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 模式匹配（Patterns） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与模式匹配（Patterns）的适用边界。
5. **迁移应用**: 将 模式匹配（Patterns） 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 模式匹配（Patterns） 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 模式匹配（Patterns） 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 模式匹配（Patterns） 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 模式匹配（Patterns） 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 模式匹配（Patterns） 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 模式匹配（Patterns） 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "模式匹配（Patterns） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 模式匹配（Patterns） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 模式匹配（Patterns） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 模式匹配（Patterns） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 模式匹配（Patterns） 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 模式匹配（Patterns） 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 模式匹配（Patterns） 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、什么是模式

**模式（pattern）** 用于将值与结构进行匹配，并可选地将变量绑定到这些结构内部的值。模式还用于变量声明、函数/闭包（Closures）参数等场景。

模式常见于：

- `let` 声明
- 函数和闭包（Closures）参数
- `match` 表达式
- `if let` / `while let` 表达式
- `for` 表达式

---

## 二、解构（Destructuring）

模式可以**解构**结构体（Struct）、枚举（Enum）和元组，将值拆分为各个组成部分。

```rust
enum Message {
    Quit,
    WriteString(String),
    Move { x: i32, y: i32 },
    ChangeColor(u8, u8, u8),
}

match message {
    Message::Quit => println!("Quit"),
    Message::WriteString(write) => println!("{}", &write),
    Message::Move { x, y: 0 } => println!("move {} horizontally", x),
    Message::Move { .. } => println!("other move"),
    Message::ChangeColor { 0: red, 1: green, 2: _ } => {
        println!("color change, red: {}, green: {}", red, green);
    }
}
```

- `_` 匹配单个字段。
- `..` 匹配剩余所有字段。
- 命名字段可简写：`Move { x, y }` 等价于 `Move { x: x, y: y }`。

---

## 三、可反驳性

> (Source: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html))
（Refutability）

- **可反驳模式（refutable）**: 可能无法匹配被匹配的值。
- **不可反驳模式（irrefutable）**: 总是匹配被匹配的值。

```rust
let (x, y) = (1, 2);           // 不可反驳
if let (a, 3) = (1, 2) { }     // 可反驳
```

`let` 绑定和函数参数要求不可反驳模式；`if let`、`while let`、`match` 允许可反驳模式。

---

## 四、模式形式

### Literal patterns

匹配与字面量完全相同的值。总是可反驳。

```rust
match i {
    -1 => println!("minus one"),
    1 => println!("one"),
    2 | 4 => println!("two or four"),
    _ => println!("other"),
}
```

### Identifier patterns

绑定匹配值到变量。单独使用 `x` 或带 `mut`、`ref`、`ref mut`：

```rust
let a = Some(10);
match a {
    Some(value) => (),      // move/copy
    Some(ref value) => (),  // 共享引用绑定
}
```

`x @ subpattern` 将匹配值绑定到 `x`，同时继续匹配子模式：

```rust
match x {
    e @ 1..=5 => println!("range element {}", e),
    _ => (),
}
```

### 绑定模式（Binding modes）

当引用（Reference）值被非引用模式匹配（Pattern Matching）时，编译器会自动按 `ref` 或 `ref mut` 绑定，避免手动写 `&`。

```rust
let x: &Option<i32> = &Some(3);
if let Some(y) = x {
    // y 自动转为 ref y，类型为 &i32
}
```

### Wildcard pattern (`_`)

匹配任意单个值，不绑定、不 move、不借用（Borrowing）。总是不可反驳。

### Rest pattern (`..`)

匹配零个或多个剩余元素，用于元组、元组结构体（Struct）、切片（Slice）模式。不可反驳。

```rust
match slice {
    [] => (),
    [one] => (),
    [head, tail @ ..] => (),
}
```

### Range patterns

匹配标量值范围：

- `a..b`：左闭右开
- `a..=b`：闭区间
- `a..`：从 `a` 到最大值
- `..b`：小于 `b`
- `..=b`：小于等于 `b`

范围必须非空。

### Reference patterns (`&` / `&mut`)

解引用（Reference）被匹配的指针并借用（Borrowing）它们。

```rust
let int_reference = &3;
match int_reference {
    &0 => "zero",
    _ => "some",
}
```

### Struct / tuple struct / tuple patterns

用于解构结构体（Struct）、元组结构体、元组。未使用 `..` 时，结构体模式必须指定所有字段。

### Slice patterns

匹配固定大小数组或动态大小切片（Slice）。

```rust
let arr = [1, 2, 3];
match arr {
    [1, _, _] => (),
    [a, b, c] => (),
}
```

### Path patterns

指向常量、枚举（Enum）变体、结构体（Struct）（无字段）或关联常量的路径。

### Or-patterns (`|`)

匹配多个子模式之一：

```rust
match x {
    1 | 2 | 3 => (),
    _ => (),
}
```

`let` 绑定和函数/闭包（Closures）参数中不允许使用 or-patterns。

---

## 五、穷尽性检查

Rust 编译器检查 `match` 表达式是否穷尽所有可能的值。不可穷尽的模式匹配（Pattern Matching）会导致编译错误。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Match Expressions](41_statements_and_expressions.md) | 模式在 `match` 中应用 |
| [Enums and Variants](../02_type_system/04_type_system.md) | 枚举（Enum）变体是模式匹配（Pattern Matching）的主要对象 |
| [Destructuring](../../02_intermediate/01_generics/02_generics.md) | 模式解构与泛型（Generics）结合使用 |
| [Control Flow](07_control_flow.md) | `if let`、`while let`、`for` 依赖模式 |
| [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md) | 术语表（元层参考） |
