# 02. 条件表达式 (Conditional Expressions)

> **文档类型**：基础  
> **难度等级**：⭐⭐  
> **预计阅读时间**：1.5小时  
> **前置知识**：Rust 基本语法、布尔类型、模式匹配基础

## 📊 目录

- [02. 条件表达式 (Conditional Expressions)](#02-条件表达式-conditional-expressions)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [2.1. `if` 与 `if let`](#21-if-与-if-let)
    - [2.1.1. `if` 表达式](#211-if-表达式)
    - [2.1.2. `if let` 表达式：便捷的模式匹配](#212-if-let-表达式便捷的模式匹配)
  - [2.2. `match` 表达式：强大的模式匹配](#22-match-表达式强大的模式匹配)

## 📖 内容概述

条件表达式是 Rust 控制流的基石，允许程序根据不同条件执行不同的代码路径。本文档详细介绍 if、if let 和 match 表达式，以及它们与所有权系统的交互。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 理解 if 表达式的表达式特性和类型约束
- [ ] 使用 if let 简化简单的模式匹配
- [ ] 掌握 match 表达式的强大功能和穷尽性检查
- [ ] 理解条件表达式中的所有权和借用规则
- [ ] 应用守卫条件实现复杂的匹配逻辑

## 📚 目录

- [02. 条件表达式 (Conditional Expressions)](#02-条件表达式-conditional-expressions)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [2.1. `if` 与 `if let`](#21-if-与-if-let)
    - [2.1.1. `if` 表达式](#211-if-表达式)
    - [2.1.2. `if let` 表达式：便捷的模式匹配](#212-if-let-表达式便捷的模式匹配)
  - [2.2. `match` 表达式：强大的模式匹配](#22-match-表达式强大的模式匹配)

---

## 2.1. `if` 与 `if let`

### 2.1.1. `if` 表达式

`if` 表达式基于一个布尔条件来选择执行两个代码块之一。

**形式化定义**:
一个 `if` 表达式 \(E_{if}\) 接受一个条件 \(c\) (必须为 `bool` 类型) 和两个代码块，一个用于 `true` 情况 (\(b_t\))，一个用于 `false` 情况 (\(b_f\))。
\[ E_{if}(c, b_t, b_f) = \begin{cases} eval(b_t) & \text{if } c = \text{true} \\ eval(b_f) & \text{if } c = \text{false} \end{cases} \]

**类型系统约束**:
为了保证类型安全，`if` 表达式的所有分支必须返回**相同类型**的值。如果分支不显式返回值，则它们隐式返回单元类型 `()`。

**所有权与借用**:
借用检查器会独立但协同地分析所有分支：

1. **移动 (Move)**: 如果一个值的所有权在**某个**分支中被移出，那么在 `if` 表达式之后，该值通常被视为不可用，除非**所有**分支都将所有权移出到同一个变量中。编译器需要确保在所有路径结束后，变量的初始化状态是一致的。
2. **借用 (Borrow)**: 在一个分支中创建的借用，其有效性不能与另一分支中的借用相冲突。例如，不能在一个分支中对变量 `x` 进行可变借用，而在另一分支中进行不可变借用，如果这两个借用在 `if` 块之外仍然可能被使用。

**代码示例**:

```rust
fn get_level(score: i32) -> &'static str {
    // 表达式返回值，所有分支类型必须为 &'static str
    let level = if score > 90 {
        "Expert"
    } else if score > 60 {
        "Advanced"
    } else {
        "Beginner"
    };
    level
}

fn move_semantics_example(condition: bool) {
    let s = String::from("hello");
    if condition {
        // s 的所有权被移动
        drop(s);
    }
    // 编译错误: `s` 在此可能未被初始化，因为 `if` 分支消耗了它
    // println!("{}", s);
}
```

### 2.1.2. `if let` 表达式：便捷的模式匹配

`if let` 是 `match` 表达式的语法糖，用于处理只关心一种或少数几种模式匹配成功的情况，避免了编写 `match` 时需要处理所有可能情况的冗长代码。

**形式化定义**:
`if let pattern = expression { block_true } else { block_false }`
这在语义上等价于：

```rust
match expression {
    pattern => { block_true },
    _ => { block_false },
}
```

`else` 分支是可选的。

**用例**:
`if let` 最常用于解构 `Option` 和 `Result`。

```rust
let maybe_value: Option<i32> = Some(10);

if let Some(value) = maybe_value {
    // 仅在 maybe_value 是 Some(...) 时执行
    println!("Got value: {}", value);
}
// `value` 变量的作用域仅限于 if let 块内部
```

## 2.2. `match` 表达式：强大的模式匹配

`match` 是 Rust 中最强大、最通用的控制流结构之一。它允许将一个值与一系列模式进行比较，并根据第一个成功匹配的模式执行相应的代码块。

**形式化定义**:
一个 `match` 表达式 \(E_{m}\) 接受一个值 \(v\) 和一个模式-表达式对的列表 \([(p_i, e_i), ...]\)。它会返回第一个匹配成功的模式 \(p_k\) 对应的表达式 \(e_k\) 的求值结果。
\[ E_{match}(v, [(p_i, e_i)]) = eval(e_k) \text{ where } p_k \text{ is the first pattern matching } v \]

**核心特性**:

1. **穷尽性 (Exhaustiveness)**
    - **定义**: `match` 表达式必须是**穷尽的**，即它的模式必须覆盖所有可能输入的值。
    - **保证**: 编译器在编译时静态地强制执行此规则。如果一个 `match` 非穷尽，代码将无法编译。这从根本上消除了因忘记处理某些情况而导致的 bug（例如 C/C++ `switch` 语句忘记 `default`）。
    - **实现**: 对于 `enum`，需要覆盖所有变体。对于整数、字符串等开放类型，通常需要使用通配符 `_` 来处理所有其他情况。

2. **模式 (Patterns)**
    Rust 的模式非常强大，包括：
    - 字面值: `1`, `"hello"`
    - 变量绑定: `Some(x)` 会将 `Option` 内部的值绑定到变量 `x`
    - 解构: `Point { x, y }` 可以解构结构体
    - 通配符: `_` 匹配任何值但不绑定
    - 范围: `1..=5` (仅限数字和字符)
    - 守卫 (Guards): `Some(n) if n > 0`，提供额外的条件判断

**所有权与借用**:
`match` 分支中的所有权规则与 `if` 类似。

- **绑定模式**: 当一个模式绑定一个变量时，所有权会根据被匹配值的类型和绑定的方式进行移动或借用。
  - 对于非 `Copy` 类型，如 `String`，`case Message::Write(text)` 会将值移入 `text`。
  - 若要避免移动，可以使用 `ref` 关键字 (`ref text`) 或对引用进行匹配 (`&Message::Write(ref text)`)。
- **分支兼容性**: 所有分支必须在所有权上兼容，确保 `match` 结束后所有变量的状态是确定的。

**代码示例**:

```rust
enum State {
    Idle,
    Processing(u32),
    Finished,
    Error(String),
}

fn process_state(state: State) -> &'static str {
    match state {
        State::Idle => "Waiting to start.",
        State::Processing(id) if id > 100 => { // 带守卫的模式
            "Processing a high-priority item."
        },
        State::Processing(_) => "Processing.",
        State::Finished => "Done.",
        // `Error(s)` 会移动 String，但由于我们只返回 &'static str
        // 且不再使用 `s`，这是允许的。
        State::Error(_) => "An error occurred.",
    } // 编译器确保所有 State 变体都被处理
}
```

---

**章节导航:**

- **上一章 ->** `01_foundations_of_control_flow.md`
- **下一章 ->** `03_iterative_constructs.md`: 探讨 `loop`, `for`, `while` 等循环结构。
- **返回目录 ->** `_index.md`
