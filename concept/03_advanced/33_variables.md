# 变量（Variables）

> **EN**: Variables
> **Summary**: Rust 变量的规范定义：函数参数、匿名临时值、命名局部变量；栈分配、可变性、初始化规则。 Normative definition of Rust variables: function parameters, anonymous temporaries, named locals; stack allocation, mutability, and initialization rules.
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Ownership](../01_foundation/01_ownership.md) · [Move Semantics](../01_foundation/23_move_semantics.md) · [Memory Model](29_memory_model.md)
> **后置概念**: [Memory Allocation and Lifetime](32_memory_allocation_and_lifetime.md) · [Destructors](../04_formal/43_destructors.md) · [Unsafe Rust](03_unsafe.md)
> **定理链**: Variable → Initialization → Drop Scope
> **主要来源**: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Variables](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html)

---

## 一、什么是变量

**变量（variable）** 是栈帧的组成部分，包括：

- 命名的函数参数（named function parameter）
- 匿名临时值（anonymous temporary）
- 命名的局部变量（named local variable）

---

## 二、局部变量

**局部变量（local variable）** 直接在栈内存中持有值，该值是栈帧的一部分。

### 可变性

- 局部变量默认不可变。
- 使用 `let mut` 声明可变局部变量。

```rust
let x = 5;      // 不可变
let mut y = 5;  // 可变
y = 6;
```

### 函数参数

- 函数参数默认不可变。
- 使用 `mut` 声明可变参数，该关键字只影响紧随其后的参数。

```rust
fn f(mut x: Box<i32>, y: Box<i32>) {
    // x 可变，y 不可变
}

let closure = |mut a, b| { /* a 可变，b 不可变 */ };
```

---

## 三、初始化规则

局部变量在分配时**未初始化**。进入函数时，整个栈帧的局部变量都以未初始化状态分配。后续语句可能初始化这些变量。

变量只能在所有可达控制流路径都已初始化之后才能使用。

```rust
fn random_bool() -> bool { true }

fn initialization_example() {
    let init_after_if: ();
    let uninit_after_if: ();

    if random_bool() {
        init_after_if = ();
        uninit_after_if = ();
    } else {
        init_after_if = ();
    }

    init_after_if;      // OK
    // uninit_after_if; // ERROR: use of possibly uninitialized
}
```

---

## 四、变量与 Drop

当已初始化的变量或临时值离开作用域时，会运行其**析构函数（destructor）**。赋值也会运行左操作数的析构函数（如果已初始化）。部分初始化的变量只 drop 已初始化的字段。

更多细节参见 [Destructors](../04_formal/43_destructors.md)。

---

## 五、关联概念

| 概念 | 关系 |
|:---|:---|
| [Ownership](../01_foundation/01_ownership.md) | 变量是所有权系统的核心载体 |
| [Move Semantics](../01_foundation/23_move_semantics.md) | 变量赋值涉及 move 语义 |
| [Memory Allocation and Lifetime](32_memory_allocation_and_lifetime.md) | 局部变量在栈上分配 |
| [Destructors](../04_formal/43_destructors.md) | 变量离开作用域时触发析构 |
| [Unsafe Rust](03_unsafe.md) | 未初始化内存操作需要 unsafe |
| [Smart Pointers](../02_intermediate/12_smart_pointers.md) | 智能指针管理堆上变量所有权 |
