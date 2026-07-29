# System F 与 Rust 泛型多态

**EN**: System F and Rust Generic Polymorphism
**Summary**: A self-contained introduction to Girard-Reynolds System F (polymorphic lambda calculus), its typing rules, erasure semantics, and how Rust's monomorphized generics approximate parametric polymorphism while staying type-safe.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [Type Theory](01_type_theory.md) · [Lambda Calculus](05_lambda_calculus.md) · [Parametricity and Theorems for Free](15_parametricity_and_theorems_for_free.md)
> **后置概念**: [Type Semantics](06_type_semantics.md) · [Category Theory](04_category_theory.md) · [Rust Generics](../../02_intermediate/01_generics/01_generics.md) · [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md)

---

> **来源**: [Girard 1972 — *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur*](https://doi.org/10.1016/B978-0-444-10494-0.50008-7) · [Reynolds 1974 — *Towards a Theory of Type Structure*](https://doi.org/10.1007/3-540-06859-7_148) · [Pierce 2002 — *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Harper 2016 — *Practical Foundations for Programming Languages*](https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf) · [Rust Reference — Generic Parameters](https://doc.rust-lang.org/reference/items/generics.html)
>
> ⚠️ **声明**: 本页使用形式化符号辅助直觉理解，呈现的“定理/规则”为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Coq](https://coq.inria.fr/)、[Agda](https://agda.readthedocs.io/) 或 [Lean](https://leanprover.github.io/)。

---

## 🧠 知识结构图

```mermaid
mindmap
  root((System F 与 Rust 泛型))
    语法
      项 λx:τ.e
      类型抽象 Λα.e
      类型应用 e[τ]
    类型
      类型变量 α
      函数类型 τ → τ
      全称类型 ∀α.τ
    核心规则
      类型抽象 ∀-intro
      类型应用 ∀-elim
      擦除语义
    Rust 映射
      fn id<T>(x: T) -> T
      Monomorphization
      Zero-cost abstraction
    边界
      无类型内省
      无值依赖类型
      unsafe / transmute 破坏参数性
```

---

## 一、权威定义

**System F**（又称 *polymorphic lambda calculus*，多态 λ 演算）由 Jean-Yves Girard（1972）与 John C. Reynolds（1974）独立提出，是在简单类型 λ 演算基础上加入**全称类型**（universal type）`∀α.τ` 的形式系统。

### 1.1 语法

```text
类型  τ ::= α                 (类型变量)
      | ρ → τ            (函数类型)
      | ∀α. τ             (全称/多态类型)

项   e ::= x                 (变量)
      | λx:τ. e           (λ 抽象)
      | e e                (应用)
      | Λα. e             (Π-抽象 / 类型抽象)
      | e [τ]             (Π-应用 / 类型实例化)
```

- `Λα. e` 表示“对任意类型 `α`，项 `e` 都成立”。
- `e [τ]` 把全称类型实例化为具体类型 `τ`。

### 1.2 类型规则（教学版）

```text
Γ, x:ρ ⊢ e : τ
----------------- (→-intro)
Γ ⊢ λx:ρ. e : ρ → τ

Γ ⊢ e₁ : ρ → τ    Γ ⊢ e₂ : ρ
--------------------------------- (→-elim)
Γ ⊢ e₁ e₂ : τ

Γ, α ⊢ e : τ
---------------- (∀-intro, α ∉ FTV(Γ))
Γ ⊢ Λα. e : ∀α. τ

Γ ⊢ e : ∀α. τ
---------------- (∀-elim)
Γ ⊢ e [ρ] : τ[α := ρ]
```

> **关键约束**：`∀-intro` 要求类型变量 `α` 在上下文 `Γ` 中自由出现；这对应 Rust 中泛型参数不能在函数体内被假设为某个具体类型。

### 1.3 标准示例：多态恒等函数

```text
id ≔ Λα. λx:α. x    :    ∀α. α → α

id [i32]  :  i32 → i32
id [bool] :  bool → bool
```

---

## 二、Rust 映射：从 `∀α.α → α` 到 `fn id<T>(x: T) -> T`

Rust 的泛型函数在源码层面与 System F 的全称类型高度对应：

```rust
fn id<T>(x: T) -> T {
    x
}
```

| System F | Rust | 说明 |
|---|---|---|
| `Λα. e` | `<T>` | 类型抽象：函数对任意类型 `T` 定义 |
| `e [τ]` | 调用 `id(42)`、`id(true)` | 类型应用由类型推断自动完成 |
| `∀α. α → α` | `fn id<T>(T) -> T` | 多态类型签名 |
| 类型擦除 | Monomorphization | Rust 在编译期为每个实例生成独立代码 |

System F 的**擦除语义**（erasure semantics）说：类型应用 `e[τ]` 在运行时不产生计算开销。Rust 的 monomorphization 是这一性质的最激进实现——它不仅在语义上“无开销”，在实现上也把每个实例编译为独立机器码。

```rust
fn main() {
    let _a = id(42i32);   // 编译期生成 id::<i32>
    let _b = id("hi");    // 编译期生成 id::<&str>
}

fn id<T>(x: T) -> T { x }
```

---

## 三、System F 的能力与限制

### 3.1 表达能力

System F 可以编码：

- products（`∀α.(τ₁ → τ₂ → α) → α` 即 Church encoding）
- sums / booleans / natural numbers
- existential types（`∃α.τ` 可编码为 `∀β.(∀α.τ → β) → β`）

### 3.2 限制：它不能表达什么

System F 仍然较弱：

- **没有依赖类型**：不能根据运行时值构造类型。
- **没有递归类型**：需要额外加入 `μ`-算子才能表达自指类型。
- **没有子类型**：`∀α.α → α` 与 `∀α.α` 之间没有子类型关系。

Rust 的类型系统远超 System F：

- `trait bounds` 对应受限量化（bounded quantification）。
- `struct`/`enum` 提供递归类型。
- `lifetime` 引入区域类型（region types）。

```rust,compile_fail
// 非法：Rust 泛型不能根据运行时值选择返回类型。
fn bad<T, U>(flag: bool, x: T, y: U) -> if flag { T } else { U } {
    if flag { x } else { y }
}
```

---

## 四、参数性再回顾

System F 是 [Parametricity](15_parametricity_and_theorems_for_free.md) 的最干净载体：

> **Reynolds 抽象定理**：System F 中每个良类型项都保持所有可容许关系；因此 `∀α.α → α` 的任意全函数必等价于恒等函数。

Rust 的 monomorphization 不破坏这一性质，因为单态化只是**编译期展开**，不改变源码层面的参数性。但以下行为会破坏：

- `unsafe` / `std::mem::transmute`
- `Any::type_id` 运行时类型内省
- 发散函数 / panic

```rust,compile_fail
// 非法：即便在运行时识别出 T == i32，也不能把具体值 0 当作 T 返回。
fn not_parametric<T: 'static>(x: T) -> T {
    if std::any::TypeId::of::<T>() == std::any::TypeId::of::<i32>() {
        return 0; // 错误：expected `T`, found integer
    }
    x
}
```

---

## 五、反例与边界

### 反例 1：把 Rust 泛型当成“模板元编程”

C++ 模板在实例化时可以执行任意编译期计算，Rust 泛型不行：

```rust,compile_fail
// 非法：不能根据类型参数 T 在运行时做类型分支并执行 T 专属操作。
fn specialize<T>(x: T) -> T {
    if std::any::TypeId::of::<T>() == std::any::TypeId::of::<i32>() {
        x + 1  // 错误：cannot add `{integer}` to `T`
    } else {
        x
    }
}
```

### 反例 2：试图返回“与输入不同类型”的全称函数

```rust,compile_fail
fn swap<A, B>(a: A, b: B) -> (B, A) {
    (b, a)  // 合法：签名允许
}

// 但下面这种签名在 System F 中无法被满足：
fn impossible<T, U>(x: T) -> U {
    // 没有信息可以构造 U
}
```

### 边界：Monomorphization 的编译代价

System F 的擦除语义保证零运行时开销，但 Rust 的 monomorphization 可能产生**二进制膨胀**。这不是语义问题，而是工程权衡。

---

## 六、国际权威参考

- **P1 学术/形式化**
  - [Girard 1972 — *Interprétation fonctionnelle et élimination des coupures*](https://doi.org/10.1016/B978-0-444-10494-0.50008-7)
  - [Reynolds 1974 — *Towards a Theory of Type Structure*](https://doi.org/10.1007/3-540-06859-7_148)
  - [Pierce 2002 — *Types and Programming Languages*, Ch. 23–24](https://www.cis.upenn.edu/~bcpierce/tapl/)
  - [Harper 2016 — *Practical Foundations for Programming Languages*, 2nd ed.](https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf)
  - [Wadler 1989 — *Theorems for Free!*](https://arxiv.org/abs/cs/9201102)

- **P0 官方**
  - [The Rust Reference — Generic Parameters](https://doc.rust-lang.org/reference/items/generics.html)
  - [The Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)
  - [Rustonomicon — Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html)

- **P2 生态/社区**
  - [Rust Internals Forum — Keyword Generics / Effects](https://internals.rust-lang.org/)
  - [This Week in Rust — Type System](https://this-week-in-rust.org/)

---

## 嵌入式测验

> **Q1**. System F 中 `∀α. α → α` 的任意全函数在语义上等价于什么？
>
> - A. 零函数
> - B. 恒等函数
> - C. 投影函数
> - D. 无法确定
>
> <details><summary>答案</summary>B. 恒等函数（参数性定理）。</details>

> **Q2**. Rust 泛型对应 System F 的哪个性质？
>
> - A. 子类型多态
> - B. 参数多态
> - C. 特设多态
> - D. 强制多态
>
> <details><summary>答案</summary>B. 参数多态。</details>

> **Q3**. 下列哪项会**破坏** Rust 泛型函数的参数性？
>
> - A. 使用 trait bound
> - B. 使用 `unsafe` 和 `transmute`
> - C. 返回输入值
> - D. 使用 `Clone`
>
> <details><summary>答案</summary>B. `unsafe` / `transmute` 允许绕过类型抽象。</details>
