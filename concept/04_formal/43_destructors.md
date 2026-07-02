# 析构函数与 Drop Scope（Destructors）

> **EN**: Destructors
> **Summary**: Rust 析构函数规则：变量与临时值何时被 drop、drop scope 嵌套、临时生命周期延长、手动抑制析构。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Ownership](../01_foundation/01_ownership.md) · [Variables](../03_advanced/33_variables.md) · [Special Types and Traits](41_special_types_and_traits.md)
> **后置概念**: [Panic](../03_advanced/31_panic.md) · [Memory Model](../03_advanced/29_memory_model.md) · [Behavior Considered Undefined](37_behavior_considered_undefined.md)
> **定理链**: Scope → Drop Order → Temporary Lifetime Extension
> **主要来源**: [Rust Reference — Destructors](https://doc.rust-lang.org/reference/destructors.html) · [Tofte & Talpin — Region-Based Memory Management](https://doi.org/10.1016/0890-5401(94)00052-3) · [Wadler — Linear Types Can Change the World!](https://doi.org/10.1007/978-1-4471-3227-7_5) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Destructors](https://doc.rust-lang.org/reference/destructors.html)

---

## 一、什么是析构函数

当已初始化的变量或临时值离开作用域时，会运行其**析构函数（destructor）**，也称为被 **drop**。赋值也会运行左操作数的析构函数（如果已初始化）。部分初始化的变量只 drop 已初始化的字段。

---

## 二、析构函数构成

类型 `T` 的析构函数包括：

1. 若 `T: Drop`，调用 `<T as Drop>::drop`。
2. 递归运行其所有字段的析构函数：
   - 结构体字段按声明顺序 drop。
   - 枚举活跃变体字段按声明顺序 drop。
   - 元组按顺序 drop。
   - 数组或 owned slice 从第一个元素到最后一个元素 drop。
   - 闭包按 move 捕获的变量 drop（顺序未指定）。
   - trait object 运行底层类型的析构函数。

如需手动运行析构函数，可使用 `core::ptr::drop_in_place`。

---

## 三、Drop Scope

每个变量或临时值都关联一个 **drop scope**。当控制流离开 drop scope 时，该作用域内所有变量按声明的**反向顺序** drop，临时值按创建的反向顺序 drop。

### 主要 drop scope

- 整个函数
- 每个语句
- 每个表达式
- 每个块（包括函数体）
- `match` 表达式的每个 arm

Drop scope 是嵌套的。当同时离开多个 scope（如函数返回）时，变量按从内到外的顺序 drop。

---

## 四、函数参数作用域

所有函数参数位于整个函数体的作用域内，因此是最后 drop 的。模式绑定在参数 drop 之前 drop。

```rust
fn patterns_in_parameters(
    (x, _): (PrintOnDrop, PrintOnDrop),
    (_, y): (PrintOnDrop, PrintOnDrop),
) {}
// drop 顺序：y, 第二个参数, x, 第一个参数
```

---

## 五、局部变量作用域

`let` 声明的局部变量关联到包含该 `let` 语句的块作用域。`match` arm 中绑定的变量关联到对应 arm 的作用域。

```rust
{
    let declared_in_block = PrintOnDrop("inner");
}
let declared_last = PrintOnDrop("outer last");
```

---

## 六、临时作用域（Temporary Scopes）

表达式的**临时作用域**用于存放该表达式产生的临时变量。除生命周期延长外，临时作用域是包含该表达式的最小 scope：

- 整个函数
- 一个语句
- `if` / `while` / `loop` 体
- `if` 的 `else` 块
- `match` arm 的 guard 与 body
- 惰性布尔表达式的每个操作数
- 块的 tail expression

> **2024 Edition 差异**: 2024 Edition 新增规则：`if let` 的临时值在 `else` 块之前 drop；块 tail expression 的临时值在表达式求值后立即 drop。

---

## 七、常量提升（Constant Promotion）

当某个值表达式可以在常量上下文中写出并被借用，且该借用可以在原位置解引用而不改变运行时行为时，该表达式会被提升到 `'static` 槽位。被提升的表达式不能包含内部可变性或析构函数。

---

## 八、临时生命周期延长

`let` 语句中的表达式临时作用域有时会被**延长**到包含该 `let` 语句的块作用域。例如：

```rust
let x = &mut 0;
println!("{}", x);
```

这里 `0` 的临时作用域被延长到块结束。

延长规则基于**扩展模式（extending patterns）**和**扩展表达式（extending expressions）**。例如：

- `let ref x = temp()` 是扩展模式。
- `let x = &temp()` 是扩展表达式（借用的操作数）。
- 函数调用参数、方法调用 receiver、`match` scrutinee、`async` 块 tail、闭包 tail、`break` 操作数等**不会**延长。

---

## 九、手动抑制析构

- `core::mem::forget`：阻止变量析构函数运行。
- `core::mem::ManuallyDrop<T>`：包装值或字段，阻止自动 drop。

> 注意：阻止析构是安全的，但类型不应依赖析构函数一定运行来保证 soundness。

---

## 十、不运行析构的情况

某些终止进程的方式不会触发析构：

- `std::process::exit`
- `std::process::abort`
- panic handler 设置为 `abort` 时的 panic
- panic 到达非 unwinding ABI 边界时（可能不运行析构，或运行到边界为止）

---

## 十一、关联概念

| 概念 | 关系 |
|:---|:---|
| [Variables](../03_advanced/33_variables.md) | 变量离开作用域触发析构 |
| [Special Types and Traits](41_special_types_and_traits.md) | `Drop` trait 定义析构行为 |
| [Panic](../03_advanced/31_panic.md) | panic 与 unwind 影响析构执行 |
| [Memory Model](../03_advanced/29_memory_model.md) | drop 是内存模型的一部分 |
| [Behavior Considered Undefined](37_behavior_considered_undefined.md) | 错误依赖析构可能导致 UB |
