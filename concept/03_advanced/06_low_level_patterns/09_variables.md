# 变量（Variables）

> **EN**: Variables
> **Summary**: Rust 变量的规范定义：函数参数、匿名临时值、命名局部变量；栈分配、可变性、初始化规则。 Normative definition of Rust variables: function parameters, anonymous temporaries, named locals; stack allocation, mutability, and initialization rules.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Move Semantics](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) · [Memory Model](../02_unsafe/06_memory_model.md)
> **后置概念**: [Memory Allocation and Lifetime](08_memory_allocation_and_lifetime.md) · [Destructors](../../04_formal/05_rustc_internals/09_destructors.md) · [Unsafe Rust](../02_unsafe/01_unsafe.md)
> **定理链**: Variable → Initialization → Drop Scope
> **主要来源**: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Variables](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html)

---

## 一、什么是变量

**变量（variable）** 是栈帧的组成部分，包括：(Source: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html))

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

局部变量在分配时**未初始化**。进入函数时，整个栈帧的局部变量都以未初始化状态分配。(Source: [Rust Reference — Local Variables](https://doc.rust-lang.org/reference/variables.html#local-variables))后续语句可能初始化这些变量。

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

## 四、变量遮蔽（Shadowing）

Rust 允许在同一作用域内使用相同名称重新绑定变量，这称为**遮蔽**：(Source: [TRPL Ch3 — Variables and Mutability](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html#shadowing))

```rust
let x = 5;
let x = x + 1; // 新变量 x，类型可以不同
let x = "shadowed"; // x 现在是 &str
```

遮蔽与可变的区别：

| 特性 | `let mut` | 遮蔽 |
|:---|:---|:---|
| 名称 | 相同 | 相同 |
| 内存位置 | 同一变量 | 新变量 |
| 类型 | 不可变 | 可变 |
| 使用 `=` 赋值 | 允许 | 实际上是新绑定 |

## 五、临时值生命周期

表达式创建的临时值通常在语句结束时销毁：

```rust
let s = &String::from("temp"); // ❌ 悬垂引用：临时值在语句结束即 drop
```

临时值的生命周期（Lifetimes）会按规则延长，例如通过 `let` 绑定或作为常量引用（Reference）参数传递。

## 六、常量、静态与局部变量

| 特性 | `let` | `const` | `static` |
|:---|:---|:---|:---|
| 求值时机 | 运行时（Runtime） | 编译期 | 编译期 |
| 可变性 | `let mut` | 不可变（默认） | `static mut` 需 unsafe |
| 存储位置 | 栈 | 内联到使用处 | 全局静态区 |
| 类型推断（Type Inference） | 支持 | 必须标注 | 必须标注 |

## 七、变量与 Drop

当已初始化的变量或临时值离开作用域时，会运行其**析构函数（destructor）**。赋值也会运行左操作数的析构函数（如果已初始化）。部分初始化的变量只 drop 已初始化的字段。

更多细节参见 [Destructors](../../04_formal/05_rustc_internals/09_destructors.md)。

## 八、unsafe 中的变量

在 unsafe 块中，可以通过裸指针读写变量，但仍需遵守 Rust 的别名规则与初始化规则：

```rust
let mut x = 0;
unsafe {
    let r = &mut x as *mut i32;
    *r = 1;
}
```

---

## 九、相关概念

| 概念 | 关系 |
|:---|:---|
| [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 变量是所有权系统的核心载体 |
| [Move Semantics](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | 变量赋值涉及 move 语义 |
| [Memory Allocation and Lifetime](08_memory_allocation_and_lifetime.md) | 局部变量在栈上分配 |
| [Destructors](../../04_formal/05_rustc_internals/09_destructors.md) | 变量离开作用域时触发析构 |
| [Unsafe Rust](../02_unsafe/01_unsafe.md) | 未初始化内存操作需要 unsafe |
| [Smart Pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) | 智能指针（Smart Pointer）管理堆上变量所有权（Ownership） |

> **权威来源**: [Rust Reference — Variables](https://doc.rust-lang.org/reference/variables.html), [TRPL Ch3 — Variables and Mutability](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)
>
> **权威来源对齐变更日志**: 2026-07-10 Stage F L3 补全权威来源块与关键引用 [Authority Source Sprint Batch Batch 10](../../00_meta/02_sources/05_international_authority_index.md)

---

## 国际权威参考 / International Authority References（P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/lazy_static — 生态权威 API 文档（静态变量惰性初始化的生态实践）](https://docs.rs/lazy_static)（2026-07-12 验证 HTTP 200）
