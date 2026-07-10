# 语句与表达式参考（Statements and Expressions Reference）

> **EN**: Statements and Expressions Reference
> **Summary**: Rust Reference 对语句（let、item、expression statement）与全部表达式形式（字面量、路径、块、运算符、数组、元组、结构体（Struct）、调用、方法调用、字段访问、闭包、循环、范围、if、match、return、await 等）的规范定义。 Normative definitions of Rust statements and expressions: literals, paths, blocks, operators, arrays, tuples, structs, calls, method calls, field access, closures, loops, ranges, if, match, return, await, and more.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Statements and Expressions](../../01_foundation/04_control_flow/41_statements_and_expressions.md) · [Variables](../../03_advanced/06_low_level_patterns/33_variables.md) · [Type System](../../01_foundation/02_type_system/04_type_system.md)
> **后置概念**: [Patterns Reference](49_patterns_reference.md) · [Constant Evaluation](../03_operational_semantics/39_constant_evaluation.md) · [Destructors](43_destructors.md)
> **定理链**: Statement → Expression → Value / Effect
>
> **来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

---

## 认知路径

> **认知路径**: 本节从 "语句与表达式参考（Statements and Expressions Reference）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么语句与表达式参考在 Rust 中值得关注？Rust 中几乎所有构造都是表达式，理解求值规则、临时值作用域和常量求值边界是写好 Rust 的基础。
2. **概念建立**: 掌握语句分类、表达式分类和主要表达式形式的语法与语义。
3. **机制推理**: 通过 ⟹ 定理链将语句、表达式、值和副作用串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与语句与表达式参考的适用边界。
5. **迁移应用**: 将语句与表达式参考与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "语句与表达式参考在所有场景下都适用" ⟹ 不成立。`unsafe` 块、常量上下文和异步（Async）上下文对某些表达式有特殊限制。
> **反命题 2**: "忽略语句与表达式参考的细节也能写出正确代码" ⟹ 不成立。临时值生命周期（Lifetimes）、move 语义和常量求值限制都源于表达式语义。
> **反命题 3**: "其他语言对语句与表达式的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的块表达式、match 表达式和所有权（Ownership）移动语义具有语言特有形态。

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

### 语法概要

```bnf
Statement      ::= LetStatement | ItemStatement | ExpressionStatement
LetStatement   ::= "let" Pattern (":" Type)? ("=" Expression)? ";"
ItemStatement  ::= Item
ExpressionStmt ::= Expression ";"
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
| 结构体（Struct） | `Point { x: 1, y: 2 }` |
| 调用 | `f(a, b)` |
| 方法调用 | `obj.method(a)` |
| 字段访问 | `s.field` |
| 闭包（Closures） | `\|x\| x + 1` |
| 循环 | `loop`, `while`, `while let`, `for` |
| 范围 | `1..5`, `1..=5` |
| `if` / `if let` | 条件分支 |
| `match` | 模式匹配（Pattern Matching） |
| `return` | 从函数返回 |
| `await` | 挂起 async 求值 |
| `_` | 下划线表达式，显式丢弃值 |

### 闭包表达式

```rust
let add = |a: i32, b: i32| -> i32 { a + b };
let add2 = |a, b| a + b; // 类型可推断
```

### Match 表达式

```rust
match option {
    Some(x) if x > 0 => println!("positive"),
    Some(_) => println!("non-positive"),
    None => println!("none"),
}
```

## 四、临时值作用域

表达式的临时值通常在**最小包围语句**结束时丢弃；2024 Edition 进一步收窄了部分临时值的作用域。详见 [Destructors](43_destructors.md)。

```rust
let s = String::from("hello").as_str(); // 错误：临时值在语句结束时释放
```

## 五、与模式的关系

`let`、`match`、`for`、`while let`、`if let`、函数参数等上下文都使用模式解构值。详见 [Patterns Reference](49_patterns_reference.md)。

## 六、Unsafe 表达式

`unsafe` 块本身是一个表达式，其值是最后一个表达式的值：

```rust
let x = unsafe { *raw_ptr };
```

在 `unsafe` 块内允许：

- 解引用（Reference）裸指针
- 调用 `unsafe` 函数
- 访问 `union` 字段
- 访问可变 `static`

详见 [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)。

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Patterns Reference](49_patterns_reference.md) | 多种表达式上下文依赖模式 |
| [Destructors](43_destructors.md) | 临时值作用域决定析构时机 |
| [Constant Evaluation](../03_operational_semantics/39_constant_evaluation.md) | 常量上下文限制可用表达式 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | `unsafe` 块是特殊表达式 |
| [Async/Await](../../03_advanced/01_async/02_async.md) | `await` 表达式只能在 async 上下文中使用 |

---

> **权威来源**: [Rust Reference — Statements and Expressions](https://doc.rust-lang.org/reference/statements-and-expressions.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Rust Reference — Expressions](https://doc.rust-lang.org/reference/expressions.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)
