# Rust 类型系统基础指南 / Rust Type System Foundations Guide

> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **论文/会议**: Pierce, *Types and Programming Languages* (MIT Press, 2002); Jung et al., *RustBelt: Securing the Foundations of Rust* (POPL 2018)
> **状态**: ✅ 已提炼归档
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-06-25
> **权威来源**:
>
> [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html),
> [Rust Reference — Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html),
> [TRPL — Traits](https://doc.rust-lang.org/book/ch10-02-traits.html),
> [RustBelt (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/),
> [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/)
>
> **受众**: [专家] / [研究者]
> **内容分级**: [研究者级]

---

> 本文内容来自已归档的 `docs/research_notes/type_theory/10_type_system_foundations.md` 与 `10_trait_system_formalization.md`，经提炼后迁移。

---

## 📋 目录

- [Rust 类型系统基础指南 / Rust Type System Foundations Guide](.#rust-类型系统基础指南--rust-type-system-foundations-guide)
  - [📋 目录](.#-目录)
  - [🎯 学习目标](.#-学习目标)
  - [1. 类型系统总览](.#1-类型系统总览)
  - [2. 代数数据类型](.#2-代数数据类型)
    - [2.1 积类型 (Product Type)](.#21-积类型-product-type)
    - [2.2 和类型 (Sum Type)](.#22-和类型-sum-type)
    - [2.3 Curry-Howard 对应（精简）](.#23-curry-howard-对应精简)
  - [3. 泛型与 System F 直觉](.#3-泛型与-system-f-直觉)
  - [4. 生命周期作为区域变量](.#4-生命周期作为区域变量)
    - [4.1 Outlives 关系](.#41-outlives-关系)
    - [4.2 区域约束求解](.#42-区域约束求解)
  - [5. Trait 系统形式化](.#5-trait-系统形式化)
    - [5.1 Trait 作为方法签名集合](.#51-trait-作为方法签名集合)
    - [5.2 Trait 对象作为存在类型](.#52-trait-对象作为存在类型)
    - [5.3 Trait 求解直觉](.#53-trait-求解直觉)
    - [5.4 Coherence 关键规则](.#54-coherence-关键规则)
  - [6. 型变理论精要](.#6-型变理论精要)
    - [6.1 为什么需要不变](.#61-为什么需要不变)
    - [6.2 型变组合](.#62-型变组合)
  - [7. 类型安全：进展与保持](.#7-类型安全进展与保持)
    - [7.1 进展定理 (Progress)](.#71-进展定理-progress)
    - [7.2 保持定理 (Preservation)](.#72-保持定理-preservation)
    - [7.3 类型安全](.#73-类型安全)
  - [8. 可运行示例](.#8-可运行示例)
    - [示例 1：和类型与模式匹配](.#示例-1和类型与模式匹配)
    - [示例 2：泛型与 Trait 约束](.#示例-2泛型与-trait-约束)
    - [示例 3：生命周期与借用](.#示例-3生命周期与借用)
    - [示例 4：Trait 对象与动态分发](.#示例-4trait-对象与动态分发)
    - [示例 5：PhantomData 与型变声明](.#示例-5phantomdata-与型变声明)
  - [9. 与相关概念文档的连接](.#9-与相关概念文档的连接)
  - [10. 权威来源索引](.#10-权威来源索引)
    - [官方文档](.#官方文档)
    - [学术论文](.#学术论文)
    - [实现与工具](.#实现与工具)

---

## 🎯 学习目标

1. 用类型论语言解释 Rust 核心构造：积类型、和类型、函数类型、泛型与存在类型。
2. 理解生命周期 `'a` 作为**区域变量**的形式化角色。
3. 说明 Trait 约束、关联类型、Trait 对象与 Trait 求解器之间的交互。
4. 判断常见类型构造的**型变**，并解释其与内存安全的关系。
5. 用「进展」与「保持」两个定理直觉地论证 Rust 的类型安全性。

---

## 1. 类型系统总览

Rust 的类型系统处于系统 F 风格多态、子类型/生命周期区域代数与基于 Trait 的特设多态交汇处。类型判断形式为：

$$
\Gamma \vdash e : \tau
$$

编译器在类型检查阶段求解三类约束：

- **类型相等/统一约束**：通过 Hindley-Milner 风格的 unification 求解。
- **Trait 约束**：通过 Trait 求解器（旧 solver / Chalk / 新 trait solver）求解。
- **Outlives/生命周期约束**：通过区域推断系统求解。

> **权威来源**: Rust Reference — Type System; Pierce 2002 — TAPL。

---

## 2. 代数数据类型

Rust 的数据类型直接映射到代数数据类型 (ADT)。

### 2.1 积类型 (Product Type)

对应逻辑**合取 (A ∧ B)**，Rust 形式为元组与结构体：

```rust
struct Point<A, B> { x: A, y: B }
```

### 2.2 和类型 (Sum Type)

对应逻辑**析取 (A ∨ B)**，Rust 形式为 `enum`：

```rust
enum Either<A, B> { Left(A), Right(B) }
```

### 2.3 Curry-Howard 对应（精简）

| 逻辑 | 类型论 | Rust 构造 |
|------|--------|-----------|
| A → B | 函数类型 | `fn(A) -> B` |
| A ∧ B | 积类型 | `(A, B)` / `struct` |
| A ∨ B | 和类型 | `enum` |
| True | 单位类型 | `()` |
| False | 空类型 | `!` |
| ∀x. P(x) | 泛型 | `fn<T>(x: T)` |
| ∃x. P(x) | 存在类型 | `dyn Trait` |

> **权威来源**: Stanford CS242; Pierce 2002 — TAPL。

---

## 3. 泛型与 System F 直觉

Rust 泛型的理论原型是**系统 F (System F)**。System F 多态类型 $\forall \alpha. \tau$ 对应：

```rust
fn identity<T>(x: T) -> T { x }
```

编译器在单态化时将 `T` 替换为具体类型，生成独立机器码。Rust 类型推导基于 Hindley-Milner 算法：

1. **约束生成**：为表达式生成类型方程，如 `e1(e2)` 产生 `τ_e1 = τ_e2 → τ_result`。
2. **统一 (Unification)**：使用最一般统一子 (MGU) 求解类型变量。
3. **泛化**：将未受约束变量提升为多态类型变量。

> Rust 的类型推导比纯 HM 更受限，但核心算法直觉一致。
> **权威来源**: Damas & Milner (POPL 1982); Rust Reference — Type Inference。

---

## 4. 生命周期作为区域变量

Rust 借用检查器将生命周期 `'a` 视为**区域变量 (region variable)**，表示程序执行期间的一段连续作用域。

```rust
&'a T      // 在区域 'a 内有效的不可变引用
&'a mut T  // 在区域 'a 内有效的独占可变引用
```

### 4.1 Outlives 关系

`'long: 'short` 表示「`'long` 不短于 `'short`」。在子类型意义上，较长生命周期是较短生命周期的子类型：

$$
'\text{long} : '\text{short} \Rightarrow \&'\text{long}\, T <: \&'\text{short}\, T
$$

### 4.2 区域约束求解

借用检查器将借用点转换为区域约束，验证：

- 引用不能活得比它指向的数据更长。
- `&mut` 引用在同一区域互斥。

> **权威来源**: RustBelt (POPL 2018); Rust Reference — Lifetime Elision。

---

## 5. Trait 系统形式化

Trait 系统是 Rust 实现特设多态与接口抽象的核心。

### 5.1 Trait 作为方法签名集合

形式化地，Trait $T$ 是方法签名的集合：

$$
T = \{ m_1 : \tau_1 \to \tau_1', \dots, \text{AT}_i : \tau_i, \dots \}
$$

类型 $\tau$ 实现 Trait $T$ 记作 $\tau : T$。关联类型 $\text{AT}_i$ 在类型层面建立从 `Self` 到 `Item` 的函数依赖。

### 5.2 Trait 对象作为存在类型

`dyn Trait` 可形式化为：

$$
\text{dyn } T = \exists \tau. \, (\tau : T) \land \tau
$$

运行时表示为 `(data_ptr, vtable_ptr)`，vtable 存储 Trait 方法指针。

### 5.3 Trait 求解直觉

编译器求解 `T: Trait` 时按优先级尝试：

1. **直接实现**：`impl Trait for T`。
2. **泛型实现**：`impl<U> Trait for Wrapper<U>`。
3. **关联 Trait / 超 Trait**：若 `T: SuperTrait` 且 `SuperTrait: Trait`。
4. **默认实现 / Blanket impl**。

### 5.4 Coherence 关键规则

- **孤儿规则**：`impl T for τ` 中，Trait 与类型至少有一个定义在当前 crate。
- **重叠规则**：两个 impl 不能同时覆盖同一具体类型。
- **Negative impls**（实验性）：`impl !Trait for T` 显式声明不实现。

> **权威来源**: Jones, *Type Classes: An Exploration of the Design Space*; Rust Reference — Traits; Chalk README。

---

## 6. 型变理论精要

型变 (Variance) 描述子类型关系如何通过泛型构造传播。给定 $S <: T$：

| 型变 | 定义 | Rust 例子 |
|------|------|-----------|
| 协变 | $F[S] <: F[T]$ | `Box<T>`、`Vec<T>`、`&'a T` |
| 逆变 | $F[T] <: F[S]$ | `fn(T) -> R` 在参数 `T` 上 |
| 不变 | 无子类型关系 | `&mut T`、`Cell<T>` |

### 6.1 为什么需要不变

`&mut T` 若对 `T` 协变，可构造悬垂引用。实际 Rust 中 `&mut T` 对 `T` 不变，禁止此类转换。

`fn(T) -> R` 参数位置逆变：期待 `fn(S) -> R` 时，可传入 `fn(T) -> R`（其中 $S <: T$），因为该函数能接受更宽输入集合。

### 6.2 型变组合

- 函数 `fn(A) -> B`：参数位置取反，返回位置保持。
- 结构体字段继承字段型变。
- `PhantomData<T>` 用于在类型不包含 `T` 时声明对 `T` 的型变。

```rust
use std::marker::PhantomData;
struct Covariant<T: 'static>(PhantomData<T>); // 协变
struct Invariant<T: 'static>(*mut T);         // 不变
```

> **权威来源**: Rust Reference — Subtyping and Variance; Rustonomicon — Variance。

---

## 7. 类型安全：进展与保持

类型安全由两个经典定理刻画。

### 7.1 进展定理 (Progress)

> 若 $\Gamma \vdash e : \tau$ 且 $\Gamma$ 良形，则 $e$ 要么是值，要么存在 $e'$ 使 $e \to e'$。

**直觉**：良型程序不会「卡住」——要么已完成计算，要么可继续执行一步。

### 7.2 保持定理 (Preservation)

> 若 $\Gamma \vdash e : \tau$ 且 $e \to e'$，则 $\Gamma \vdash e' : \tau$。

**直觉**：求值后类型保持不变，运行时值的类型与静态推断一致。

### 7.3 类型安全

$$
\text{Type Safety} = \text{Progress} + \text{Preservation}
$$

`unsafe` 块是类型系统的信任边界：违反其中不变式会破坏上述保证，导致未定义行为。

> **权威来源**: RustBelt (POPL 2018); Pierce 2002 — TAPL。

---

## 8. 可运行示例

### 示例 1：和类型与模式匹配

```rust
enum Expr {
    Num(i32),
    Add(Box<Expr>, Box<Expr>),
}

fn eval(e: &Expr) -> i32 {
    match e {
        Expr::Num(n) => *n,
        Expr::Add(l, r) => eval(l) + eval(r),
    }
}

fn main() {
    let e = Expr::Add(Box::new(Expr::Num(1)), Box::new(Expr::Num(2)));
    assert_eq!(eval(&e), 3);
}
```

### 示例 2：泛型与 Trait 约束

```rust
trait Summable { fn sum(&self) -> i32; }
impl Summable for [i32] {
    fn sum(&self) -> i32 { self.iter().sum() }
}
fn total<T: AsRef<[i32]>>(x: T) -> i32 { x.as_ref().sum() }

fn main() {
    assert_eq!(total(vec![1, 2, 3]), 6);
}
```

### 示例 3：生命周期与借用

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("long");
    let s2 = String::from("x");
    let result = longest(&s1, &s2);
    println!("{}", result);
}
```

### 示例 4：Trait 对象与动态分发

```rust
trait Greeter { fn greet(&self); }
struct Cat;
impl Greeter for Cat { fn greet(&self) { println!("meow"); } }
struct Dog;
impl Greeter for Dog { fn greet(&self) { println!("woof"); } }

fn main() {
    let greeters: Vec<Box<dyn Greeter>> = vec![Box::new(Cat), Box::new(Dog)];
    for g in &greeters { g.greet(); }
}
```

### 示例 5：PhantomData 与型变声明

```rust
use std::marker::PhantomData;
struct Covariant<T: 'static>(PhantomData<T>);
struct Invariant<T: 'static>(*mut T);

fn main() {
    let _a: Covariant<String> = Covariant(PhantomData);
    let _b: Invariant<String> = Invariant(std::ptr::null_mut());
}
```

---

## 9. 与相关概念文档的连接

| 主题 | 延伸阅读 | 说明 |
|------|----------|------|
| 类型论基础 | [`concept/04_formal/02_type_theory.md`](../../../concept/04_formal/02_type_theory.md) | λ 演算、简单类型、系统 F、Curry-Howard |
| Trait 求解器 | [`concept/04_formal/26_trait_solver_in_rustc.md`](../../../concept/04_formal/26_trait_solver_in_rustc.md) | rustc Trait 求解流程、Chalk、新 solver |
| 类型推断复杂度 | [`concept/04_formal/29_type_inference_complexity.md`](../../../concept/04_formal/29_type_inference_complexity.md) | HM 复杂度、约束求解边界 |
| 型变细节 | [`docs/research_notes/type_theory/10_variance_theory.md`](../../../docs/research_notes/type_theory/10_variance_theory.md) | 完整型变规则、反例、证明树 |
| 生命周期形式化 | [`docs/research_notes/type_theory/10_lifetime_formalization.md`](../../../docs/research_notes/type_theory/10_lifetime_formalization.md) | 区域变量、outlives、借用检查 |

---

## 10. 权威来源索引

### 官方文档

- [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)
- [Rust Reference — Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html)
- [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [The Rust Programming Language](https://doc.rust-lang.org/book/)

### 学术论文

- Benjamin C. Pierce. *Types and Programming Languages*. MIT Press, 2002.
- Ralf Jung et al. *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL 2018.
- Mark P. Jones. *Type Classes: An Exploration of the Design Space*. 1995.
- Luis Damas & Robin Milner. *Principal Type-Schemes for Functional Programs*. POPL 1982.

### 实现与工具

- [Chalk — Rust Trait Solver 形式化模型](https://github.com/rust-lang/chalk)
- [rustc Trait Solving Guide](https://rustc-dev-guide.rust-lang.org/traits.html)
- [Miri](https://github.com/rust-lang/miri)

---

**维护者**: Rust 学习项目
**最后更新**: 2026-06-25
**状态**: ✅ 已提炼归档
