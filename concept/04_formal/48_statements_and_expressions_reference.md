# 语句与表达式参考（Statements and Expressions Reference）

> **EN**: Statements and Expressions Reference
> **Summary**: Rust Reference 对语句（let、item、expression statement）与全部表达式形式（字面量、路径、块、运算符、数组、元组、结构体、调用、方法调用、字段访问、闭包、循环、范围、if、match、return、await 等）的规范定义。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Statements and Expressions](../01_foundation/41_statements_and_expressions.md) · [Variables](../03_advanced/33_variables.md) · [Type System](../01_foundation/04_type_system.md)
> **后置概念**: [Patterns Reference](49_patterns_reference.md) · [Constant Evaluation](39_constant_evaluation.md) · [Destructors](43_destructors.md)
> **定理链**: Statement → Expression → Value / Effect
>
> **来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、语句

Rust 有三种语句：

| 语句 | 形式 | 说明 |
|:---|:---|:---|
| Let 语句 | `let pat: Ty = expr;` | 引入变量绑定 |
| Item 语句 | `fn foo() {}` | 在块内声明 item |
| 表达式语句 | `expr;` | 求值并丢弃结果 |

```rust
fn example() {
    let x = 1;          // let 语句
    fn inner() {}       // item 语句
    println!("ok");     // 表达式语句
}
```

## 二、表达式分类

Rust 表达式按语义可分为：

| 类别 | 说明 | 示例 |
|:---|:---|:---|
| 值表达式 | 产生值 | `42`, `"x"` |
| 位置表达式 | 表示内存位置 | `x`, `s.field`, `a[i]` |
| 赋值表达式 | 修改位置 | `x = 1` |
| 复合表达式 | 包含子表达式 | 块、调用、match |

## 三、主要表达式形式

| 表达式 | 要点 |
|:---|:---|
| 字面量 | `true`, `42`, `"s"`, `'c'`, `b"b"` |
| 路径 | 变量、常量、函数路径 |
| 块 | `{ stmt; expr }`，最后一个表达式为块值 |
| 运算符 | 算术、位、比较、逻辑、赋值、复合赋值 |
| 数组/索引 | `[1, 2, 3]`, `[0; 5]`, `a[i]` |
| 元组/索引 | `(1, 2)`, `t.0` |
| 结构体 | `Point { x: 1, y: 2 }` |
| 调用 | `f(a, b)` |
| 方法调用 | `obj.method(a)` |
| 字段访问 | `s.field` |
| 闭包 | `|x| x + 1` |
| 循环 | `loop`, `while`, `while let`, `for` |
| 范围 | `1..5`, `1..=5` |
| `if` / `if let` | 条件分支 |
| `match` | 模式匹配 |
| `return` | 从函数返回 |
| `await` | 挂起 async 求值 |
| `_` | 下划线表达式，显式丢弃值 |

## 四、临时值作用域

表达式的临时值通常在**最小包围语句**结束时丢弃；2024 Edition 进一步收窄了部分临时值的作用域。详见 [Destructors](43_destructors.md)。

## 五、与模式的关系

`let`、`match`、`for`、`while let`、`if let`、`函数参数` 等上下文都使用模式解构值。详见 [Patterns Reference](49_patterns_reference.md)。

---

> **权威来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
