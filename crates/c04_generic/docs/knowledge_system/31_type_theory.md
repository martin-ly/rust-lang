# 类型理论 (Type Theory)

> **文档定位**: Rust 泛型系统的类型理论基础和数学模型
> **创建日期**: 2025-10-19  
> **知识类型**: 📐 数学理论 | 🎓 学术分析 | 🔬 形式化基础

---

## 📋 目录

- [类型理论 (Type Theory)](#类型理论-type-theory)
  - [📋 目录](#-目录)
  - [类型理论概述](#类型理论概述)
    - [什么是类型理论？](#什么是类型理论)
    - [Rust 泛型的理论基础](#rust-泛型的理论基础)
  - [System F (多态λ演算)](#system-f-多态λ演算)
    - [System F 简介](#system-f-简介)
      - [核心概念](#核心概念)
      - [语法](#语法)
      - [示例: 多态恒等函数](#示例-多态恒等函数)
    - [System F 类型规则](#system-f-类型规则)
      - [T-TApp (类型应用)](#t-tapp-类型应用)
      - [T-TAbs (类型抽象)](#t-tabs-类型抽象)
  - [Hindley-Milner 类型系统](#hindley-milner-类型系统)
    - [HM 类型系统简介](#hm-类型系统简介)
    - [语法1](#语法1)
    - [let-多态](#let-多态)
    - [类型推导算法 (Algorithm W)](#类型推导算法-algorithm-w)
      - [核心步骤](#核心步骤)
      - [示例: 推导 λf. λx. f (f x)](#示例-推导-λf-λx-f-f-x)
  - [类型类 (Type Classes)](#类型类-type-classes)
    - [类型类简介](#类型类简介)
    - [类型类 vs 泛型](#类型类-vs-泛型)
    - [Haskell 类型类](#haskell-类型类)
    - [Rust Trait (类型类的实现)](#rust-trait-类型类的实现)
    - [类型类约束](#类型类约束)
  - [Rust 类型系统](#rust-类型系统)
    - [Rust 类型系统的组成](#rust-类型系统的组成)
    - [Rust 类型的形式化](#rust-类型的形式化)
      - [类型语法](#类型语法)
      - [类型规则示例: 引用](#类型规则示例-引用)
    - [Rust 类型检查](#rust-类型检查)
      - [类型检查阶段](#类型检查阶段)
  - [类型推导](#类型推导)
    - [Rust 类型推导](#rust-类型推导)
    - [示例 1: 简单推导](#示例-1-简单推导)
    - [示例 2: 泛型推导](#示例-2-泛型推导)
    - [示例 3: 复杂推导](#示例-3-复杂推导)
    - [类型推导限制](#类型推导限制)
      - [限制 1: 闭包不支持 let-多态](#限制-1-闭包不支持-let-多态)
      - [限制 2: 需要显式类型标注](#限制-2-需要显式类型标注)
  - [类型的性质](#类型的性质)
    - [类型健全性 (Type Soundness)](#类型健全性-type-soundness)
    - [类型推导的完备性](#类型推导的完备性)
  - [理论对比总结](#理论对比总结)
  - [📚 相关文档](#-相关文档)
  - [📖 进阶阅读](#-进阶阅读)
    - [经典论文](#经典论文)
    - [Rust 相关](#rust-相关)

---

## 类型理论概述

### 什么是类型理论？

类型理论是研究**类型系统的数学基础**，包括：

- **类型的本质**: 类型是什么？
- **类型规则**: 如何组合类型？
- **类型安全**: 如何保证程序不出错？
- **类型推导**: 如何自动确定类型？

### Rust 泛型的理论基础

```text
Rust Generic System
    │
    ├─[基于]─→ System F (参数多态)
    │          └─ 类型抽象 Λα. e
    │             类型应用 e[τ]
    │
    ├─[基于]─→ Hindley-Milner (类型推导)
    │          └─ let-多态
    │             类型推导算法
    │
    └─[基于]─→ Type Classes (类型类)
               └─ Trait 系统
                  临时多态
```

---

## System F (多态λ演算)

### System F 简介

**System F** (第二类λ演算) 是**参数多态**的理论基础。

#### 核心概念

1. **类型抽象** (Type Abstraction): Λα. e
   - 引入类型变量 α
   - e 是使用 α 的表达式

2. **类型应用** (Type Application): e[τ]
   - 将具体类型 τ 应用到多态表达式 e

#### 语法

```text
类型 τ ::= α                    (类型变量)
        | τ1 → τ2              (函数类型)
        | ∀α. τ                (全称量化)

表达式 e ::= x                  (变量)
          | λx:τ. e            (值抽象)
          | e1 e2              (值应用)
          | Λα. e              (类型抽象)
          | e[τ]               (类型应用)
```

#### 示例: 多态恒等函数

**System F**:

```text
id = Λα. λx:α. x
     ^^^^  ^^^^
     类型  值
     抽象  抽象

使用:
id[Int] 42 = (λx:Int. x) 42 = 42
id[Bool] true = (λx:Bool. x) true = true
```

**Rust 对应**:

```rust
fn id<T>(x: T) -> T {
    //  ^^^类型参数 (对应 Λα)
    x
}

// 使用
id::<i32>(42);      // 类型应用 (对应 [Int])
id::<bool>(true);   // 类型应用 (对应 [Bool])
```

### System F 类型规则

#### T-TApp (类型应用)

```text
Γ ⊢ e : ∀α. τ
────────────────── (T-TApp)
Γ ⊢ e[τ'] : τ[α := τ']
```

**解释**: 如果 e 的类型是 ∀α. τ，那么 e[τ'] 的类型是将 α 替换为 τ' 后的 τ。

**Rust 示例**:

```rust
// e : ∀T. T → T
fn id<T>(x: T) -> T { x }

// e[i32] : i32 → i32
id::<i32>(42)
```

#### T-TAbs (类型抽象)

```text
Γ, α ⊢ e : τ
────────────────── (T-TAbs)
Γ ⊢ Λα. e : ∀α. τ
```

**解释**: 如果在上下文中添加类型变量 α 后，e 的类型是 τ，那么 Λα. e 的类型是 ∀α. τ。

---

## Hindley-Milner 类型系统

### HM 类型系统简介

**Hindley-Milner (HM)** 类型系统是一个支持：

- **类型推导**: 自动推导类型
- **let-多态**: let 绑定可以多态
- **主类型性质**: 每个表达式有最general的类型

### 语法1

```text
类型 τ ::= α                    (类型变量)
        | Int | Bool | ...     (基础类型)
        | τ1 → τ2              (函数类型)

类型方案 σ ::= τ               (单态类型)
            | ∀α. σ           (多态类型)

表达式 e ::= x                  (变量)
          | n | true | ...     (常量)
          | λx. e              (函数)
          | e1 e2              (应用)
          | let x = e1 in e2   (let 绑定)
```

### let-多态

**HM 的关键特性**: let 绑定的变量可以多态使用。

**示例**:

```text
let id = λx. x in
    (id 42, id true)
    ^^^     ^^^
    Int     Bool
```

**Rust 对应**:

```rust
fn example() {
    let id = |x| x;  // ❌ Rust 的闭包不支持 HM let-多态
    
    // id(42);       // 错误: 一旦推导为某个类型，无法改变
    // id(true);
}

// Rust 使用泛型函数实现多态
fn id<T>(x: T) -> T { x }

fn example2() {
    id(42);       // ✅ 每次调用单态化为具体类型
    id(true);     // ✅
}
```

### 类型推导算法 (Algorithm W)

**Algorithm W** 是 HM 类型系统的类型推导算法。

#### 核心步骤

```text
W(Γ, e) = (S, τ)
其中:
  Γ: 类型环境
  e: 表达式
  S: 替换 (Substitution)
  τ: 推导出的类型
```

#### 示例: 推导 λf. λx. f (f x)

**步骤**:

1. **假设类型**:

   ```text
   f : α
   x : β
   ```

2. **推导 f x**:

   ```text
   f : β → γ   (因为 f 应用于 x:β)
   f x : γ
   ```

3. **推导 f (f x)**:

   ```text
   f : γ → δ   (因为 f 应用于 f x:γ)
   f (f x) : δ
   ```

4. **合一 (Unification)**:

   ```text
   α = β → γ
   α = γ → δ
   ⇒ β → γ = γ → δ
   ⇒ β = γ, γ = δ
   ⇒ β = γ = δ
   ```

5. **最终类型**:

   ```text
   λf. λx. f (f x) : (α → α) → α → α
   ```

**Rust 对应**:

```rust
fn twice<T, F>(f: F, x: T) -> T
where
    F: Fn(T) -> T,
{
    f(f(x))
}
// 类型: (T → T) → T → T
```

---

## 类型类 (Type Classes)

### 类型类简介

**类型类** (Type Class) 是 Haskell 提出的概念，支持**临时多态** (Ad-hoc Polymorphism)。

### 类型类 vs 泛型

| 特性 | 参数多态 (Generics) | 临时多态 (Type Classes) |
|------|-------------------|---------------------|
| **行为** | 对所有类型相同 | 对不同类型可以不同 |
| **实现** | 单一实现 | 每个类型一个实现 |
| **示例** | `id<T>(x: T)` | `add<T>(a: T, b: T)` |

### Haskell 类型类

```haskell
-- 类型类定义
class Eq a where
    (==) :: a -> a -> bool

-- 实例 (impl)
instance Eq Int where
    x == y = intEq x y

instance Eq Bool where
    x == y = boolEq x y
```

### Rust Trait (类型类的实现)

```rust
// Trait 定义 (对应类型类)
trait Eq {
    fn eq(&self, other: &Self) -> bool;
}

// impl (对应实例)
impl Eq for i32 {
    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl Eq for bool {
    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}
```

### 类型类约束

**Haskell**:

```haskell
sort :: Ord a => [a] -> [a]
      ^^^^^^^^
      类型类约束
```

**Rust**:

```rust
fn sort<T: Ord>(items: &mut [T])
       ^^^^^^
       Trait 约束 (对应类型类约束)
```

---

## Rust 类型系统

### Rust 类型系统的组成

```text
Rust Type System
│
├── 参数多态 (System F)
│   └── Generic<T>
│
├── 类型类 (Type Classes)
│   └── Trait System
│
├── 区域类型系统 (Region Type System)
│   └── Lifetime 'a
│
├── 仿射类型 (Affine Types)
│   └── Move 语义
│
└── 子结构类型 (Substructural Types)
    ├── Linear Types (变种)
    └── Ownership System
```

### Rust 类型的形式化

#### 类型语法

```text
类型 τ ::= T                     (具体类型)
        | α                     (类型变量)
        | τ1 → τ2              (函数类型)
        | &'a τ                (引用)
        | &'a mut τ            (可变引用)
        | Box<τ>               (堆分配)

        | ∀α. τ                (泛型)
        | τ where τ: Trait     (Trait 约束)
```

#### 类型规则示例: 引用

```text
Γ ⊢ x : τ    'a: 'b
───────────────────── (T-Ref)
Γ ⊢ &'a x : &'a τ


Γ ⊢ x : τ    unique(x)
─────────────────────── (T-MutRef)
Γ ⊢ &'a mut x : &'a mut τ
```

### Rust 类型检查

#### 类型检查阶段

```text
源代码
  │
  ├─[1] 名称解析 (Name Resolution)
  ├─[2] 类型推导 (Type Inference)
  ├─[3] Trait 解析 (Trait Resolution)
  ├─[4] 生命周期推导 (Lifetime Inference)
  ├─[5] 借用检查 (Borrow Checking)
  └─[6] 单态化 (Monomorphization)
  │
  ↓
机器码
```

---

## 类型推导

### Rust 类型推导

Rust 使用**双向类型推导**:

- **从上到下**: 从函数签名推导表达式类型
- **从下到上**: 从表达式使用推导泛型参数

### 示例 1: 简单推导

```rust
let x = 42;  // 推导: x: i32
```

**推导过程**:

```text
1. 字面量 42 → i32 (默认)
2. x = 42 → x: i32
```

### 示例 2: 泛型推导

```rust
let v = Vec::new();
v.push(1);
```

**推导过程**:

```text
1. Vec::new() → Vec<T> (T 未知)
2. v.push(1) → T = i32 (从 push 参数推导)
3. v: Vec<i32>
```

### 示例 3: 复杂推导

```rust
fn example() {
    let mut v = Vec::new();  // Vec<T>
    
    if some_condition {
        v.push(1);            // T = i32
    } else {
        v.push(2);            // 确认 T = i32
    }
    
    // v: Vec<i32>
}
```

### 类型推导限制

#### 限制 1: 闭包不支持 let-多态

```rust
let f = |x| x;  // 类型推导为具体类型，不是 ∀T. T → T

f(42);    // f: Fn(i32) -> i32
// f(true);  // ❌ 错误: 类型不匹配
```

**解决方案**: 使用泛型函数

```rust
fn f<T>(x: T) -> T { x }

f(42);     // ✅
f(true);   // ✅
```

#### 限制 2: 需要显式类型标注

```rust
let v = Vec::new();  // ❌ 无法推导 T
```

**解决方案**:

```rust
let v: Vec<i32> = Vec::new();              // 方案 1
let v = Vec::<i32>::new();                 // 方案 2
let mut v = Vec::new(); v.push(1);         // 方案 3: 从使用推导
```

---

## 类型的性质

### 类型健全性 (Type Soundness)

**定义**: "Well-typed programs don't go wrong"

**形式化**:

```text
如果 ⊢ e : τ 且 e ⟹* v，
那么 ⊢ v : τ (类型保持)
```

**Rust 保证**: Safe Rust 是类型健全的

### 类型推导的完备性

**HM 类型系统**: 推导算法是**完备的**

- 如果表达式可类型化，算法一定能找到类型
- 推导出的类型是**主类型** (最general的类型)

**Rust**: 由于借用检查和生命周期，推导更复杂，需要更多类型标注

---

## 理论对比总结

| 理论 | 核心概念 | Rust 对应 | 应用 |
|------|---------|----------|------|
| **System F** | 参数多态, Λα.e | `Generic<T>` | 泛型函数/结构体 |
| **HM** | 类型推导, let-多态 | 类型推导 | 自动推导类型 |
| **Type Classes** | 临时多态, 类型类 | `Trait` | Trait 系统 |
| **Region Types** | 区域, 生命周期 | `Lifetime 'a` | 借用检查 |
| **Affine Types** | 仿射类型 | `Move` 语义 | 所有权系统 |

---

## 📚 相关文档

- [概念本体](./01_concept_ontology.md) - 概念定义
- [形式语义](./30_formal_semantics.md) - 操作语义
- [Trait系统理论](./32_trait_system_theory.md) - Trait 理论基础
- [健全性性质](./33_soundness_properties.md) - 类型安全证明

---

## 📖 进阶阅读

### 经典论文

1. **Girard (1972)**: System F 的提出
2. **Damas & Milner (1982)**: HM 类型推导算法
3. **Wadler & Blott (1989)**: 类型类的提出
4. **Pierce (2002)**: *Types and Programming Languages* (TAPL)

### Rust 相关

1. **RFC 1214**: Clarify and streamline paths and visibility
2. **RFC 1598**: Generic Associated Types (GATs)
3. **Rustonomicon**: 深入理解 Rust 的内存模型和类型系统

---

**文档版本**: v1.0  
**创建日期**: 2025-10-19  
**最后更新**: 2025-10-19  
**维护状态**: ✅ 持续更新中
