# 常量求值（Constant Evaluation）

> **EN**: Constant Evaluation
> **Summary**: Rust 编译期常量求值机制：常量表达式、常量上下文（const context）与 `const fn` 的规则与限制。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Type System](../01_foundation/04_type_system.md) · [Expressions](../01_foundation/07_control_flow.md) · [Functions](../01_foundation/07_control_flow.md)
> **后置概念**: [Generics](../02_intermediate/02_generics.md) · [Const Generics](../02_intermediate/02_generics.md) · [Unsafe Rust](../03_advanced/03_unsafe.md)
> **定理链**: Const Context → Constant Expression → Compile-time Evaluation
> **主要来源**: [Rust Reference — Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Tarditi — Design and Implementation of Code Optimization](https://www.microsoft.com/en-us/research/publication/design-and-implementation-of-code-optimization/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

## 一、什么是常量求值

**常量求值（Constant Evaluation）** 是指在编译期计算表达式结果的过程。Rust 只允许一部分表达式在编译期求值，这些表达式称为**常量表达式（constant expressions）**。

常量求值发生在**常量上下文（const context）**中，例如：

- 数组类型长度 `[T; N]`
- 数组重复表达式 `[x; N]`
- `const`、`static`、枚举 discriminant 的初始化器
- const 泛型参数
- `const { ... }` 块

在 const context 中，表达式**必须**是常量表达式，并且**一定**在编译期求值。

---

## 二、常量表达式

以下表达式形式在操作数本身也是常量表达式、且不触发 `Drop::drop` 的前提下，属于常量表达式：

| 表达式 | 说明 |
|:---|:---|
| 字面量 | `42`、`"hello"`、`true` 等 |
| const 参数 | 泛型 const 参数 |
| 函数/常量路径 | 指向函数或常量的路径；不允许递归定义常量 |
| static 路径 | 限制：不可写入 static；不可读取 `extern` static；非 static 初始化器中不可读取 mutable static |
| 元组、数组、结构体表达式 |  |
| 块表达式 | 包括 `unsafe` 块与 `const` 块 |
| 字段访问 |  |
| 数组/切片索引 | 索引必须是 `usize` |
| Range 表达式 |  |
| 闭包 | 不捕获环境变量的闭包 |
| 内置运算符 | 整数、浮点、`bool`、`char` 上的算术、逻辑、比较、惰性布尔运算 |
| 各种借用 | 限制见下文 |
| 解引用 |  |
| 分组表达式 |  |
| 类型转换 | 除外：指针转地址、函数指针转地址 |
| const 函数/方法调用 |  |
| `loop` / `while` |  |
| `if` / `match` |  |

### 借用限制

在常量表达式中，对临时值的共享借用或可变借用受到限制：

- 不允许对生命周期被延长到程序末尾的临时值进行**可变借用**。
- 不允许对生命周期被延长到程序末尾、且具有内部可变性（interior mutability）的临时值进行**共享借用**。

允许的 place 表达式归纳为三类：**瞬态（transient）**、**间接（indirect）**、**静态（static）**。

---

## 三、常量上下文（Const Context）

常量上下文包括：

1. 数组类型长度表达式
2. 数组重复长度表达式
3. `const`、`static`、枚举 discriminant 的初始化器
4. const 泛型参数
5. `const` 块

对于数组长度、数组重复长度和 const 泛型参数，外部泛型参数的使用受到限制：表达式必须是单个 const 泛型参数，或者不引用任何泛型参数。

---

## 四、Const Functions

**`const fn`** 是可以在常量上下文中被调用的函数。定义时使用 `const` 限定符。

```rust
const fn square(x: i32) -> i32 { x * x }
const VALUE: i32 = square(12);
```

### 限制

- const 函数体只能使用常量表达式。
- const 函数不能是 `async`。
- 参数类型和返回类型必须兼容常量上下文。
- 在 const context 外调用 const 函数时，行为与普通函数相同。
- const 函数的解释发生在**编译目标**环境中，而非宿主机。例如，若目标系统是 32 位，则 `usize` 为 32 位。

---

## 五、溢出与越界

在 const context 中，数组越界索引、整数溢出等行为是**编译错误**。在非 const context 中，这些行为可能只是警告，并可能在运行时 panic。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Generics](../02_intermediate/02_generics.md) | const 泛型参数扩展了常量求值的应用 |
| [Unsafe Rust](../03_advanced/03_unsafe.md) | const 块中允许使用 `unsafe` 块，但需满足常量表达式规则 |
| [Memory Model](../03_advanced/29_memory_model.md) | 常量求值涉及初始化字节、指针 provenance 等内存模型概念 |
| [Application Binary Interface](38_application_binary_interface.md) | `static` 初始化与 ABI 属性交互 |