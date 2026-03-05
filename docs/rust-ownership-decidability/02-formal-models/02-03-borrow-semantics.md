# 借用语义的形式化：共享借用与可变借用

> **理论来源**: RustBelt (Jung et al., 2018), Oxide (Weiss et al., 2020)
> **核心原则**: Aliasing XOR Mutation (别名与变异互斥)

---

## 目录

- [借用语义的形式化：共享借用与可变借用](#借用语义的形式化共享借用与可变借用)
  - [目录](#目录)
  - [1. 借用系统概述](#1-借用系统概述)
    - [1.1 借用的动机](#11-借用的动机)
    - [1.2 核心原则](#12-核心原则)
  - [2. 共享借用 \&T 的形式化](#2-共享借用-t-的形式化)
    - [2.1 语义定义](#21-语义定义)
    - [2.2 推导规则](#22-推导规则)
    - [2.3 共享借用的性质](#23-共享借用的性质)
  - [3. 可变借用 \&mut T 的形式化](#3-可变借用-mut-t-的形式化)
    - [3.1 语义定义](#31-语义定义)
    - [3.2 推导规则](#32-推导规则)
    - [3.3 独占性保证](#33-独占性保证)
  - [4. 借用冲突检测](#4-借用冲突检测)
    - [4.1 冲突类型](#41-冲突类型)
    - [4.2 形式化检测算法](#42-形式化检测算法)
  - [5. 重新借用 (Reborrowing)](#5-重新借用-reborrowing)
    - [5.1 概念与语法](#51-概念与语法)
    - [5.2 形式化规则](#52-形式化规则)
  - [6. 部分借用 (Partial Borrowing)](#6-部分借用-partial-borrowing)
    - [6.1 字段级借用](#61-字段级借用)
    - [6.2 形式化](#62-形式化)
  - [7. 与分离逻辑的对应](#7-与分离逻辑的对应)
    - [借用谓词的形式化](#借用谓词的形式化)
    - [资源分离](#资源分离)
  - [8. 类型安全定理](#8-类型安全定理)
    - [借用安全定理](#借用安全定理)
    - [证明概要](#证明概要)
  - [9. 实践应用](#9-实践应用)
    - [迭代器模式](#迭代器模式)
    - [函数式API](#函数式api)
    - [并发访问](#并发访问)
  - [10. 参考文献](#10-参考文献)
  - [附录: 借用规则总结](#附录-借用规则总结)

---

## 1. 借用系统概述

### 1.1 借用的动机

**所有权系统的问题**：Move语义过于严格，导致频繁的所有权转移。

```rust
// 没有借用时的尴尬
fn without_borrow() {
    let s = String::from("hello");
    let (s, len) = calculate_length(s);  // 必须返回所有权
    println!("{}'s length is {}", s, len);
}

fn calculate_length(s: String) -> (String, usize) {
    let len = s.len();
    (s, len)  // 必须返回s才能继续使用
}
```

**借用解决方案**：临时访问而不转移所有权。

```rust
fn with_borrow() {
    let s = String::from("hello");
    let len = calculate_length(&s);  // 借用s
    println!("{}'s length is {}", s, len);  // s仍然可用
}

fn calculate_length(s: &String) -> usize {
    s.len()  // 只读访问
}
```

### 1.2 核心原则

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    借用系统的核心原则                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  在任意给定时刻，只能满足以下条件之一:                                 │
│                                                                     │
│  ┌─────────────────┐          ┌─────────────────┐                   │
│  │  1. 可变借用     │          │  2. 共享借用     │                   │
│  │                 │    XOR   │                 │                   │
│  │  &mut T         │ ◄──────► │  &T, &T, ...    │                   │
│  │  恰好一个       │          │  任意数量       │                   │
│  │  可读写         │          │  只读           │                   │
│  └─────────────────┘          └─────────────────┘                   │
│                                                                     │
│  附加原则: 引用必须始终有效                                          │
│  (引用的值不能在其生命周期结束前被释放)                                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 2. 共享借用 &T 的形式化

### 2.1 语义定义

**基于RustBelt的语义**:

```text
共享借用的所有权谓词:

[[&^α τ]].share(t, [ℓ]) ≡ ∀t'. &^α(∃v̄. ℓ ↦ v̄ * ▷[[τ]].share(t', v̄))

其中:
- α: 生命周期/区域
- t: 当前线程
- ℓ: 堆位置
- v̄: 值列表
- &^α: 在区域α上的借用
- ▷: later modality (用于递归类型)
- ∀t': 对所有线程 (说明是共享的)
```

**直觉解释**:

```text
共享借用 &T 意味着:
1. 可以读取T的值
2. 不能修改T
3. 可以有多个共享借用同时存在
4. 只要至少有一个共享借用存在，原数据不能被修改
```

### 2.2 推导规则

**类型规则**:

```text
共享借用创建 (Borrow-Shared):
Γ ⊢ e : τ    Γ ⊢ uniq(e)    α fresh
─────────────────────────────────────
Γ ⊢ &^α e : &^α τ

其中 uniq(e) 确保e是未借用的路径

共享借用解引用 (Deref-Shared):
Γ ⊢ e : &^α τ
────────────────
Γ ⊢ *e : τ

注意: 解引用共享借用产生的是只读值
```

**生命周期规则**:

```text
子生命周期借用:
Γ ⊢ e : &^α τ    β ⊆ α
────────────────────────
Γ ⊢ &^β *e : &^β τ

(可以从长生命周期借用创建短生命周期借用)
```

### 2.3 共享借用的性质

**性质1: 可复制性**:

```text
&τ 是可复制的 (Copy):

Γ ⊢ x : &τ
────────────────────────
Γ, y:&τ ⊢ copy(x) : &τ

(共享借用可以任意复制，因为不影响所有权)
```

**性质2: 可传递性**:

```rust
// 多级共享借用
fn transitive_borrow() {
    let x = 5;
    let r1 = &x;      // &i32
    let r2 = &r1;     // &&i32
    let r3 = &r2;     // &&&i32
    println!("{}", ***r3);  // 解引用三次
}
```

**性质3: 协变性**:

```text
&^α τ 在 τ 上是协变的:

τ <: τ'  ⊢  &^α τ <: &^α τ'

示例:
&'static str <: &'a str  (因为 'static: 'a)
```

---

## 3. 可变借用 &mut T 的形式化

### 3.1 语义定义

**基于RustBelt的语义**:

```text
可变借用的所有权谓词:

[[&^mut α τ]].own(t, [ℓ]) ≡ &^α(∃v̄. ℓ ↦ v̄ * ▷[[τ]].own(t, v̄))

与共享借用的关键区别:
- own 而非 share: 独占所有权
- t 而非 ∀t': 仅当前线程
```

**直觉解释**:

```text
可变借用 &mut T 意味着:
1. 可以读取和修改T
2. 同时只能有一个可变借用存在
3. 当可变借用存在时，原数据不能被访问
4. 可变借用可以"重新借用"创建更短生命周期的借用
```

### 3.2 推导规则

**类型规则**:

```text
可变借用创建 (Borrow-Mut):
Γ ⊢ e : τ    Γ ⊢ owns(e)    Γ ⊢ uniq(e)    α fresh
───────────────────────────────────────────────────
Γ ⊢ &^mut α e : &^mut α τ

可变借用解引用 (Deref-Mut):
Γ ⊢ e : &^mut α τ
──────────────────
Γ ⊢ *e : τ

可变赋值 (Assign-Mut):
Γ ⊢ e₁ : &^mut α τ    Γ ⊢ e₂ : τ
────────────────────────────────
Γ ⊢ *e₁ = e₂ : ()
```

**注意**: 可变借用不是Copy类型。

### 3.3 独占性保证

**形式化独占性**:

```text
定理 (独占性):
如果 Γ ⊢ r : &^mut α τ，则对于所有 p ∈ Γ，如果 p 可以访问 r 指向的数据，
则 p 必须是 r 本身或由 r 重新借用而来。

形式化:
Γ ⊢ r : &^mut α τ  ∧  Γ ⊢ p : &^β τ'  ∧  paths_overlap(r, p)
  ⊢  p = r  ∨  p = reborrow(r)
```

**Rust代码示例**:

```rust
fn exclusivity_demonstration() {
    let mut data = vec![1, 2, 3];

    let r1 = &mut data;
    // let r2 = &mut data;  // 错误! 不能有两个可变借用

    r1.push(4);

    // r1在这里之后不再使用
    // 可变借用结束，data重新可用

    let r2 = &mut data;  // OK!
    r2.push(5);
}
```

---

## 4. 借用冲突检测

### 4.1 冲突类型

```text
借用冲突的三种类型:

1. 双重可变借用 (Double Mut)
   &mut x 和 &mut x 同时存在

2. 可变+共享借用 (Mut + Shared)
   &mut x 和 &x 同时存在

3. 悬挂引用 (Dangling)
   引用指向已释放的内存
```

### 4.2 形式化检测算法

**借用上下文**:

```text
借用上下文 Λ ::= · | Λ, loan(ℓ, kind, region)

其中:
- ℓ: 借用的路径
- kind: Shared | Mut
- region: 生命周期 α
```

**冲突检测规则**:

```text
冲突定义:

conflict(loan(ℓ₁, k₁, r₁), loan(ℓ₂, k₂, r₂)) ≡
  paths_conflict(ℓ₁, ℓ₂) ∧ regions_overlap(r₁, r₂) ∧ kinds_conflict(k₁, k₂)

其中:
paths_conflict(ℓ₁, ℓ₂) ≡ ℓ₁ 和 ℓ₂ 指向重叠内存

regions_overlap(r₁, r₂) ≡ r₁ ∩ r₂ ≠ ∅

kinds_conflict(k₁, k₂) ≡ (k₁ = Mut) ∨ (k₂ = Mut) ∨ (k₁ ≠ k₂)
```

**类型检查算法**:

```text
检查借用创建:

check_borrow(Γ, Λ, &kind e, region) =
  let ℓ = path(e) in
  for loan(ℓ', kind', region') ∈ Λ do
    if conflict(loan(ℓ, kind, region), loan(ℓ', kind', region')) then
      Error: Borrow conflict
  return Λ, loan(ℓ, kind, region)
```

---

## 5. 重新借用 (Reborrowing)

### 5.1 概念与语法

**重新借用**允许从已有借用创建新的借用。

```rust
fn reborrowing_example() {
    let mut s = String::from("hello");
    let r1 = &mut s;           // 第一个可变借用

    // 从r1重新借用
    let r2 = &mut *r1;         // r1被"冻结"直到r2结束
    r2.push_str(" world");

    // r2作用域结束，r1重新激活
    r1.push_str("!");
}
```

### 5.2 形式化规则

**重新借用的类型规则**:

```text
重新借用 (Reborrow):
Γ ⊢ r : &^α mut τ    β ⊆ α    r ∉ used(Γ)
────────────────────────────────────────────
Γ ⊢ &^β mut *r : &^β mut τ

冻结状态 (Freeze):
当 &^β mut *r 存在时，r 被冻结直到 β 结束
```

**生命周期关系**:

```text
重新借用的生命周期包含关系:

r: &^α mut τ
  └── &^β mut *r : &^β mut τ    where β ⊆ α
      └── &^γ mut **r : &^γ mut τ    where γ ⊆ β ⊆ α

原借用 α 直到所有重新借用 (β, γ, ...) 结束后才重新激活
```

---

## 6. 部分借用 (Partial Borrowing)

### 6.1 字段级借用

Rust允许同时借用结构体的不同字段。

```rust
struct Point { x: i32, y: i32 }

fn partial_borrow() {
    let mut p = Point { x: 0, y: 0 };

    let x = &mut p.x;  // 借用x字段
    let y = &mut p.y;  // 借用y字段 - OK! 不重叠

    *x = 5;
    *y = 10;
}
```

### 6.2 形式化

**路径表示**:

```text
路径表达式:
p ::= x        变量
   |  p.f      字段访问
   |  p[i]     索引访问
   |  *p       解引用

路径重叠:
paths_overlap(p₁, p₂) ≡ p₁ 是 p₂ 的前缀 或 p₂ 是 p₁ 的前缀
```

**部分借用规则**:

```text
部分借用 (Partial):
Γ ⊢ e : τ    fields(τ) = {f₁, ..., fₙ}
─────────────────────────────────────────────
Γ ⊢ &^α e.fᵢ : &^α τᵢ

约束: &^α e.fᵢ 和 &^β e.fⱼ 不冲突当 i ≠ j
```

---

## 7. 与分离逻辑的对应

### 借用谓词的形式化

```text
分离逻辑中的借用表示:

共享借用:
[[&^α τ]].share(t, [ℓ]) ≡ ∀t'. &^α(∃v. ℓ ↦ v * ▷[[τ]].share(t', v))

可变借用:
[[&^mut α τ]].own(t, [ℓ]) ≡ &^α(∃v. ℓ ↦ v * ▷[[τ]].own(t, v))

其中:
- &^α P: 在生命周期α期间暂时持有P
- ℓ ↦ v: 位置ℓ包含值v
- ▷: later modality (用于递归)
```

### 资源分离

```text
共享借用的分离性质:

&^α τ * &^α τ 是有效的 (多个共享借用)

可变借用的分离性质:

&^mut α τ * &^mut α τ 是无效的 (不能有两个可变借用)
&^mut α τ * &^α τ 是无效的 (不能同时有可变和共享)
```

---

## 8. 类型安全定理

### 借用安全定理

```text
定理 (借用安全):
如果 Γ ⊢ e : τ 且 e 归约为 v，则:

1. (无悬挂引用) 所有引用在e执行期间都有效
2. (无数据竞争) 没有并发的读写或写写冲突
3. (内存安全) 所有内存访问都在有效范围内
```

### 证明概要

```text
证明结构:

1. 进展性 (Progress):
   如果 Γ ⊢ e : τ，则 e 是值或可以进一步归约

2. 保持性 (Preservation):
   如果 Γ ⊢ e : τ 且 e ↦ e'，则 Γ' ⊢ e' : τ

3. 借用不变量:
   - 维护借用上下文 Λ
   - 每次借用创建都检查冲突
   - 生命周期结束自动归还借用

4. 终止性:
   借用检查在有限步骤内完成
```

---

## 9. 实践应用

### 迭代器模式

```rust
fn iterator_example() {
    let mut data = vec![1, 2, 3, 4, 5];

    // iter() 创建共享借用
    for item in &data {
        println!("{}", item);
    }

    // iter_mut() 创建可变借用
    for item in &mut data {
        *item *= 2;
    }
}
```

### 函数式API

```rust
fn functional_api() {
    let mut v = vec![1, 2, 3];

    // map 使用共享借用
    let doubled: Vec<_> = v.iter().map(|x| x * 2).collect();

    // 可变迭代器
    for x in v.iter_mut() {
        *x += 1;
    }
}
```

### 并发访问

```rust
use std::thread;

fn concurrent_reads() {
    let data = vec![1, 2, 3, 4, 5];

    let handles: Vec<_> = (0..3)
        .map(|i| {
            // 每个线程获得共享借用
            thread::spawn(move || {
                println!("Thread {}: {:?}", i, &data[i..i+2]);
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

---

## 10. 参考文献

1. **Jung, R., et al.** (2018). *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL 2018.

2. **Weiss, A., Patterson, D., & Ahmed, A.** (2020). *Oxide: The Essence of Rust*. arXiv:1903.00982.

3. **Reynolds, J.C.** (2002). *Separation Logic: A Logic for Shared Mutable Data Structures*. LICS 2002.

4. **Birkedal, L., et al.** (2014). *Step-Indexed Kripke Models over Recursive Worlds*. POPL 2011.

5. **Tofte, M., & Talpin, J.-P.** (1997). *Region-Based Memory Management*. Information and Computation.

6. **Grossman, D., et al.** (2002). *Region-Based Memory Management in Cyclone*. PLDI 2002.

7. **Fluet, M., et al.** (2006). *Linear Regions Are All You Need*. ESOP 2006.

8. **Matsushita, Y., et al.** (2020). *RustHorn: CHC-based Verification for Rust Programs*. TACAS 2020.

---

## 附录: 借用规则总结

```text
┌─────────────────────────────────────────────────────────────────┐
│                      借用规则速查表                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  共享借用 (&T):                                                  │
│  - 可创建多个                                                    │
│  - 只读访问                                                      │
│  - 存在时原数据不可变                                             │
│  - 是Copy类型                                                    │
│                                                                 │
│  可变借用 (&mut T):                                              │
│  - 只能有一个                                                    │
│  - 读写访问                                                      │
│  - 存在时原数据不可用                                             │
│  - 不是Copy类型                                                  │
│  - 可以重新借用                                                   │
│                                                                 │
│  冲突检测:                                                       │
│  - &mut x + &mut x = 错误                                        │
│  - &mut x + &x    = 错误                                        │
│  - &x + &x        = OK                                           │
│                                                                 │
│  生命周期:                                                       │
│  - 借用不能比原数据活得长                                         │
│  - 短生命周期借用可以赋给长生命周期变量                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```
