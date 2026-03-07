# 类型理论基础 (Type Theory Foundations)

## 目录

- [类型理论基础 (Type Theory Foundations)](#类型理论基础-type-theory-foundations)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 类型系统的目的](#2-类型系统的目的)
    - [2.1 类型系统的三大功能](#21-类型系统的三大功能)
    - [2.2 类型检查的时机](#22-类型检查的时机)
  - [3. 简单类型系统](#3-简单类型系统)
    - [3.1 基础类型](#31-基础类型)
    - [3.2 函数类型](#32-函数类型)
    - [3.3 积类型 (Product Types)](#33-积类型-product-types)
    - [3.4 和类型 (Sum Types)](#34-和类型-sum-types)
    - [3.5 单位类型与空类型](#35-单位类型与空类型)
  - [4. 子类型理论 (Subtyping)](#4-子类型理论-subtyping)
    - [4.1 子类型关系](#41-子类型关系)
    - [4.2 函数类型的子类型规则](#42-函数类型的子类型规则)
    - [4.3 变型 (Variance)](#43-变型-variance)
    - [4.4 宽度子类型 vs 深度子类型](#44-宽度子类型-vs-深度子类型)
  - [5. 递归类型 (Recursive Types)](#5-递归类型-recursive-types)
    - [5.1 μ-表示法](#51-μ-表示法)
    - [5.2 Iso-recursive vs Equi-recursive](#52-iso-recursive-vs-equi-recursive)
    - [5.3 列表示例](#53-列表示例)
  - [6. 参数多态 (Parametric Polymorphism)](#6-参数多态-parametric-polymorphism)
    - [6.1 全称类型 (System F)](#61-全称类型-system-f)
    - [6.2 参数多态性定理](#62-参数多态性定理)
    - [6.3 Rust 的泛型实现](#63-rust-的泛型实现)
  - [7. 类型推断](#7-类型推断)
    - [7.1 Hindley-Milner 类型推断](#71-hindley-milner-类型推断)
    - [7.2 主要类型 (Principal Type)](#72-主要类型-principal-type)
  - [8. 高级类型系统特性](#8-高级类型系统特性)
    - [8.1 存在类型 (Existential Types)](#81-存在类型-existential-types)
    - [8.2 类型族与关联类型](#82-类型族与关联类型)
    - [8.3 GADT (广义代数数据类型)](#83-gadt-广义代数数据类型)
  - [9. 类型系统性质](#9-类型系统性质)
    - [9.1 类型安全 (Type Safety)](#91-类型安全-type-safety)
    - [9.2 强规范化 (Strong Normalization)](#92-强规范化-strong-normalization)
    - [9.3 一致性 (Consistency)](#93-一致性-consistency)
  - [10. Rust 类型系统全景](#10-rust-类型系统全景)
    - [10.1 Rust 类型系统层次](#101-rust-类型系统层次)
    - [10.2 所有权作为类型系统扩展](#102-所有权作为类型系统扩展)
  - [11. 总结](#11-总结)
  - [参考文献](#参考文献)

## 1. 引言

类型理论是编程语言理论的基石，它为程序提供了数学上的结构，确保计算的正确性。从简单类型到依赖类型，类型系统的发展推动了编程语言的演进。

> **核心思想**: 类型是值的分类，类型系统是在编译时（或运行时）强制执行这些分类的规则集合。

---

## 2. 类型系统的目的

### 2.1 类型系统的三大功能

```
┌─────────────────────────────────────────────────────────────────┐
│                    类型系统的功能                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 错误检测 (Error Detection)                                  │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 在编译时发现错误，而非运行时                           │    │
│     │ "Well-typed programs cannot go wrong" (Milner, 1978)  │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  2. 抽象与文档 (Abstraction & Documentation)                    │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 类型作为接口契约，描述函数的行为                       │    │
│     │ 类型签名即文档                                         │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  3. 优化基础 (Optimization Foundation)                          │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 类型信息指导编译器优化                                 │    │
│     │ 内存布局、调用约定、内联决策                             │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 类型检查的时机

| 类型检查方式 | 描述 | 示例语言 |
|--------------|------|----------|
| **静态类型** | 编译时检查 | Rust, Haskell, Java |
| **动态类型** | 运行时检查 | Python, Ruby, JavaScript |
| **渐进类型** | 可选静态类型 | TypeScript, mypy |
| **依赖类型** | 类型依赖值 | Idris, Coq, Agda |

---

## 3. 简单类型系统

### 3.1 基础类型

$$
B ::= \text{Int} \mid \text{Bool} \mid \text{Unit} \mid \text{String} \mid ...
$$

**Rust 对应**:

```rust
// Int
let x: i32 = 42;

// Bool
let b: bool = true;

// Unit
let u: () = ();

// String
let s: String = String::from("hello");
```

### 3.2 函数类型

$$
\tau_1 \rightarrow \tau_2
$$

表示从类型 $\tau_1$ 到类型 $\tau_2$ 的函数。

**类型判断规则 (回顾)**:

$$
\frac{\Gamma, x:\tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2} \quad (\rightarrow\text{-Intro})
$$

$$
\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1\ e_2 : \tau_2} \quad (\rightarrow\text{-Elim})
$$

### 3.3 积类型 (Product Types)

**语法**:

$$
\tau_1 \times \tau_2
$$

**构造与消去**:

$$
\frac{\Gamma \vdash e_1 : \tau_1 \quad \Gamma \vdash e_2 : \tau_2}{\Gamma \vdash (e_1, e_2) : \tau_1 \times \tau_2} \quad (\times\text{-Intro})
$$

$$
\frac{\Gamma \vdash e : \tau_1 \times \tau_2}{\Gamma \vdash \pi_1(e) : \tau_1} \quad (\times\text{-Elim}_1)
\quad
\frac{\Gamma \vdash e : \tau_1 \times \tau_2}{\Gamma \vdash \pi_2(e) : \tau_2} \quad (\times\text{-Elim}_2)
$$

**Rust 对应**: 元组

```rust
// τ₁ × τ₂
let pair: (i32, bool) = (42, true);

// π₁ (fst)
let first: i32 = pair.0;

// π₂ (snd)
let second: bool = pair.1;
```

**η-规则**:

$$
(\pi_1(e), \pi_2(e)) \equiv e \quad \text{(若 } e: \tau_1 \times \tau_2\text{)}
$$

### 3.4 和类型 (Sum Types)

**语法**:

$$
\tau_1 + \tau_2
$$

表示"要么是 $\tau_1$，要么是 $\tau_2$"的值。

**构造**:

$$
\frac{\Gamma \vdash e : \tau_1}{\Gamma \vdash \text{inl}(e) : \tau_1 + \tau_2} \quad (+\text{-Intro}_1)
\quad
\frac{\Gamma \vdash e : \tau_2}{\Gamma \vdash \text{inr}(e) : \tau_1 + \tau_2} \quad (+\text{-Intro}_2)
$$

**消去 (Case 分析)**:

$$
\frac{\Gamma \vdash e : \tau_1 + \tau_2 \quad \Gamma, x:\tau_1 \vdash e_1 : \tau \quad \Gamma, y:\tau_2 \vdash e_2 : \tau}{\Gamma \vdash \text{case}\ e\ \text{of}\ \text{inl}(x) \Rightarrow e_1 \mid \text{inr}(y) \Rightarrow e_2 : \tau} \quad (+\text{-Elim})
$$

**Rust 对应**: `enum`

```rust
// τ₁ + τ₂
enum Either<T, U> {
    Left(T),   // inl
    Right(U),  // inr
}

// case 分析 (match)
let value: Either<i32, bool> = Either::Left(42);
let result = match value {
    Either::Left(x) => x * 2,      // e₁
    Either::Right(b) => if b { 1 } else { 0 },  // e₂
};
```

### 3.5 单位类型与空类型

**单位类型 (Unit)**:

$$
\text{Unit} = \{\text{()\} \quad \text{(单元素集合)}
$$

**空类型 (Void/Never)**:

$$
\text{Void} = \emptyset \quad \text{(无元素)}
$$

对于任意类型 $\tau$，恰好存在一个函数 $\text{Unit} \rightarrow \tau$（常量函数），而存在零个函数 $\text{Void} \rightarrow \tau$。

**Rust 对应**:

```rust
// Unit: ()
let unit: () = ();

// Never: ! (发散函数返回类型)
fn diverge() -> ! {
    panic!("never returns");
}
```

---

## 4. 子类型理论 (Subtyping)

### 4.1 子类型关系

$$
\tau_1 <: \tau_2 \quad \text{("τ₁ 是 τ₂ 的子类型")}
$$

**语义**: 任何需要 $\tau_2$ 的地方都可以用 $\tau_1$ 替代。

**基本性质**:

- **自反性**: $\tau <: \tau$
- **传递性**: 若 $\tau_1 <: \tau_2$ 且 $\tau_2 <: \tau_3$，则 $\tau_1 <: \tau_3$

### 4.2 函数类型的子类型规则

$$
\frac{\tau_1' <: \tau_1 \quad \tau_2 <: \tau_2'}{\tau_1 \rightarrow \tau_2 <: \tau_1' \rightarrow \tau_2'} \quad (\rightarrow\text{-Sub})
$$

**关键**: 参数类型逆变，返回类型协变。

**直观理解**:

- 函数可以接受"更多"输入（参数逆变）
- 函数保证返回"更少"类型（返回协变）

### 4.3 变型 (Variance)

| 变型 | 定义 | Rust示例 |
|------|------|----------|
| **协变** | $T <: U \Rightarrow C<T> <: C<U>$ | `Box<T>`, `Vec<T>` |
| **逆变** | $T <: U \Rightarrow C<U> <: C<T>$ | `Fn(T) -> U` 的参数 |
| **不变** | $T <: U \nRightarrow C<T> \text{ 与 } C<U>$ 有关系 | `Cell<T>`, `&mut T` |

**Rust 变型推导**:

```rust
// 协变: Box<T>
// 若 Cat <: Animal，则 Box<Cat> <: Box<Animal>

// 逆变: Fn(T) 的参数位置
// 若 Cat <: Animal，则 Fn(Animal) <: Fn(Cat)
// (接受Animal的函数可以接受Cat)

// 不变: &mut T
// 既非协变也非逆变
```

### 4.4 宽度子类型 vs 深度子类型

**结构子类型** (Structural Subtyping):

$$
\frac{\{l_1:\tau_1, ..., l_n:\tau_n, ..., l_m:\tau_m\} \text{ 包含 } \{l_1:\tau_1, ..., l_n:\tau_n\}}{\{l_1:\tau_1, ..., l_m:\tau_m\} <: \{l_1:\tau_1, ..., l_n:\tau_n\}}
$$

**Rust**: 基于 Trait 的子类型，非结构子类型。

---

## 5. 递归类型 (Recursive Types)

### 5.1 μ-表示法

**语法**:

$$
\mu \alpha.\tau
$$

表示满足方程 $\alpha = \tau$ 的最小（或最大）解。

**展开规则**:

$$
\mu \alpha.\tau \equiv \tau[(\mu \alpha.\tau)/\alpha]
$$

### 5.2 Iso-recursive vs Equi-recursive

| 类型 | 特征 | 显式操作 |
|------|------|----------|
| **Iso-recursive** | 递归类型与其展开不同构，需显式转换 | `fold`/`unfold` |
| **Equi-recursive** | 递归类型与其展开等价 | 隐式 |

**Rust 采用**: Iso-recursive（通过显式的构造/解构）

### 5.3 列表示例

**类型定义**:

$$
\text{List}\ \alpha = \mu \beta.(\text{Unit} + (\alpha \times \beta))
$$

展开:

```
List α = Unit + (α × (Unit + (α × (Unit + ...))))
       = Nil | Cons(α, List α)
```

**Rust 实现**:

```rust
// μβ.(Unit + (α × β))
enum List<T> {
    Nil,           // Unit (空)
    Cons(T, Box<List<T>>),  // T × List<T>
}

// fold (构造)
let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));

// unfold (解构/match)
match list {
    List::Nil => println!("空列表"),
    List::Cons(head, tail) => println!("头: {}", head),
}
```

---

## 6. 参数多态 (Parametric Polymorphism)

### 6.1 全称类型 (System F)

**语法**:

$$
\forall \alpha.\tau
$$

表示"对于所有类型 $\alpha$，类型为 $\tau$"的函数。

**类型抽象**:

$$
\frac{\Gamma, \alpha \vdash e : \tau}{\Gamma \vdash \Lambda \alpha.e : \forall \alpha.\tau} \quad (\forall\text{-Intro})
$$

**类型应用**:

$$
\frac{\Gamma \vdash e : \forall \alpha.\tau}{\Gamma \vdash e\ [\sigma] : \tau[\sigma/\alpha]} \quad (\forall\text{-Elim})
$$

### 6.2 参数多态性定理

**定理** (参数性 / Parametricity):

多态函数的行为必须对所有类型一致，不能使用类型特定的操作。

**自由定理 (Free Theorem)** 示例:

对于类型 $\forall \alpha.(\alpha \rightarrow \alpha)$ 的函数 $f$，有：

$$
f_{\tau_2} \circ g = g \circ f_{\tau_1}
$$

对所有函数 $g : \tau_1 \rightarrow \tau_2$ 成立。

**Rust 对应**: 泛型函数的自然性约束

```rust
// ∀α.α → α
fn id<T>(x: T) -> T { x }

// 自然性: id(g(x)) == g(id(x))
let g = |x: i32| x + 1;
assert_eq!(id(g(5)), g(id(5)));
```

### 6.3 Rust 的泛型实现

```rust
// ∀α.α → α
fn identity<T>(x: T) -> T {
    x
}

// ∀α.∀β.α → β → α  (K组合子)
fn first<A, B>(a: A, _b: B) -> A {
    a
}

// 单态化 (Monomorphization)
// identity::<i32> 和 identity::<bool> 是两个不同的函数
```

---

## 7. 类型推断

### 7.1 Hindley-Milner 类型推断

**核心思想**: 通过合一 (Unification) 自动推导最一般的类型。

**算法 W**:

```
输入: 表达式 e 和上下文 Γ
输出: 替换 S 和类型 τ

W(Γ, x) = (id, τ) 若 x:τ ∈ Γ
W(Γ, λx.e) =
  令 α = 新类型变量
  (S, τ) = W(Γ∪{x:α}, e)
  返回 (S, S(α) → τ)
W(Γ, e₁ e₂) =
  (S₁, τ₁) = W(Γ, e₁)
  (S₂, τ₂) = W(S₁(Γ), e₂)
  令 α = 新类型变量
  S₃ = Unify(S₂(τ₁), τ₂ → α)
  返回 (S₃ ∘ S₂ ∘ S₁, S₃(α))
```

### 7.2 主要类型 (Principal Type)

**定义**: 表达式 $e$ 的主要类型是 $e$ 的所有可能类型中最一般的（最抽象的）。

**性质**: Hindley-Milner 系统保证每个良好类型的表达式有唯一的主要类型（模变量重命名）。

**Rust 对应**: Rust 的类型推断是受限制的 HM 推断

```rust
// 类型推断
let x = 5;           // x: i32
let f = |y| y + 1;   // f: impl Fn(i32) -> i32

// 多态 let (let-polymorphism)
let id = |x| x;      // id: impl Fn(T) -> T (对每个调用实例化)
```

---

## 8. 高级类型系统特性

### 8.1 存在类型 (Existential Types)

**语法**:

$$
\exists \alpha.\tau
$$

表示"存在某个类型 $\alpha$ 使得类型为 $\tau$"的值。

**用途**: 信息隐藏、抽象数据类型 (ADT)。

**Rust 对应**: `dyn Trait` 和 `impl Trait`

```rust
// ∃α.(α, α → i32, α → α)  -- 计数器接口
struct Counter {
    state: Box<dyn Any>,
    get: Box<dyn Fn(&dyn Any) -> i32>,
    inc: Box<dyn Fn(&dyn Any) -> Box<dyn Any>>,
}

// impl Trait: 存在类型的一种形式
fn make_counter() -> impl Iterator<Item = i32> {
    0..10
}
```

### 8.2 类型族与关联类型

**类型族**: 从类型到类型的函数。

**Rust 对应**: 关联类型

```rust
trait Iterator {
    type Item;  // 关联类型
    fn next(&mut self) -> Option<Self::Item>;
}

// Item 是 Iterator 的类型族
// Iterator<Item=i32> 指定了具体实例
```

### 8.3 GADT (广义代数数据类型)

**特点**: 构造子的返回类型可以更具体。

**Rust 对应**: 不完全支持，但可用 PhantomData 模拟

```rust
// GADT 风格
enum Expr<T> {
    Int(i32),              // Expr<i32>
    Bool(bool),            // Expr<bool>
    Add(Box<Expr<i32>>, Box<Expr<i32>>),  // Expr<i32>
}
```

---

## 9. 类型系统性质

### 9.1 类型安全 (Type Safety)

**定义**: 类型安全 = 保持性 (Preservation) + 进展性 (Progress)

**保持性**:

$$
\text{若 } \Gamma \vdash e : \tau \text{ 且 } e \rightarrow e' \text{, 则 } \Gamma \vdash e' : \tau
$$

**进展性**:

$$
\text{若 } \vdash e : \tau \text{, 则要么 } e \text{ 是值，要么存在 } e' \text{ 使得 } e \rightarrow e'
$$

**意义**: 良好类型的程序不会"卡住"（不会发生类型错误）。

### 9.2 强规范化 (Strong Normalization)

**定义**: 所有良好类型的项都有有限的归约序列。

**简单类型 λ演算**: 是强规范化的。

**System F**: 是强规范化的（Girard 定理）。

**意义**: 保证程序终止（对总函数）。

### 9.3 一致性 (Consistency)

**类型系统一致性**: 不存在闭合项 $e$ 使得对所有类型 $\tau$ 都有 $\vdash e : \tau$。

**Curry 悖论**: 无限制的自指类型会导致不一致。

---

## 10. Rust 类型系统全景

### 10.1 Rust 类型系统层次

```
┌─────────────────────────────────────────────────────────────┐
│                   Rust 类型系统层次                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Level 4: 依赖类型 (有限支持)                                 │
│  ├── const generics: [T; N]                                 │
│  └── type-level constants                                    │
│                                                             │
│  Level 3: 高阶类型 (Lifetime + Traits)                       │
│  ├── HRTB: for<'a> Trait<'a>                                │
│  └── Higher-Ranked Trait Bounds                              │
│                                                             │
│  Level 2: 参数多态 (Generics)                                │
│  ├── fn id<T>(T) -> T                                       │
│  └── impl<T> Trait for Type<T>                              │
│                                                             │
│  Level 1: 子类型 (Lifetimes)                                 │
│  ├── 'a: 'b (outlives)                                      │
│  └── Variance rules                                          │
│                                                             │
│  Level 0: 简单类型 + 代数数据类型                             │
│  ├── Primitives: i32, bool, ()                              │
│  ├── Products: structs, tuples                              │
│  └── Sums: enums                                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 10.2 所有权作为类型系统扩展

**所有权三规则的类型理论解释**:

1. **唯一所有权** = 线性类型 (Linear Types)
   - 每个值必须且只能使用一次
   - `let x = v; drop(x)`

2. **借用** = 仿射类型 (Affine Types) + 区域
   - &T: 只读共享引用（复制类型）
   - &mut T: 唯一可变引用（线性）

3. **生命周期** = 区域类型 (Region Types)
   - 'a 标记值的存活区域
   - 区域包含关系形成子类型

---

## 11. 总结

| 类型理论概念 | Rust对应 | 重要性 |
|--------------|----------|--------|
| 简单类型 | 基本类型、函数 | ⭐⭐⭐ |
| 积类型 | 元组、结构体 | ⭐⭐⭐ |
| 和类型 | 枚举 (enum) | ⭐⭐⭐ |
| 子类型 | 生命周期子类型 | ⭐⭐⭐ |
| 变型 | 自动推导 | ⭐⭐⭐ |
| 递归类型 | 递归枚举 | ⭐⭐⭐ |
| 参数多态 | 泛型 | ⭐⭐⭐ |
| 类型推断 | let-polymorphism | ⭐⭐ |
| 存在类型 | impl Trait, dyn Trait | ⭐⭐ |
| 线性类型 | 所有权系统 | ⭐⭐⭐ |
| 区域类型 | 生命周期 | ⭐⭐⭐ |

理解这些类型理论概念是深入掌握 Rust 类型系统、借用检查器和所有权模型的关键。

---

## 参考文献

1. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
2. Cardelli, L. (1996). "Type Systems". *ACM Computing Surveys*.
3. Martin-Löf, P. (1984). *Intuitionistic Type Theory*.
4. Girard, J. Y., Taylor, P., & Lafont, Y. (1989). *Proofs and Types*.
5. Harper, R. (2016). *Practical Foundations for Programming Languages*.

---

**难度级别**: 🔴 高级 (理论基础)
**前置知识**: λ演算基础
**后续学习**: 操作语义、线性类型
