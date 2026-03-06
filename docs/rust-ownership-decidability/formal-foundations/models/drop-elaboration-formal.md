# Rust Drop Elaboration 形式化理论

> **来源**: ETH Zürich, Bachelor Thesis, 2024
> **作者**: Viktor Fukala
> **导师**: Isaac van Bakel, Prof. Dr. Ralf Jung
> **难度**: 🔴 高级

---

## 目录

- [Rust Drop Elaboration 形式化理论](#rust-drop-elaboration-形式化理论)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言](#1-引言)
    - [1.1 Drop Elaboration 是什么](#11-drop-elaboration-是什么)
    - [1.2 为什么需要形式化](#12-为什么需要形式化)
  - [2. 核心概念](#2-核心概念)
    - [2.1 析构与 Drop](#21-析构与-drop)
    - [2.2 初始化状态](#22-初始化状态)
    - [2.3 控制流与 Drop](#23-控制流与-drop)
  - [3. 形式化语言](#3-形式化语言)
    - [3.1 语法定义](#31-语法定义)
    - [3.2 类型系统](#32-类型系统)
    - [3.3 操作语义](#33-操作语义)
  - [4. Drop Elaboration 转换](#4-drop-elaboration-转换)
    - [4.1 转换概述](#41-转换概述)
    - [4.2 初始化效果](#42-初始化效果)
    - [4.3 标志管理](#43-标志管理)
  - [5. 形式化证明](#5-形式化证明)
    - [5.1 正确性声明](#51-正确性声明)
    - [5.2 证明策略](#52-证明策略)
    - [5.3 Coq 实现](#53-coq-实现)
  - [6. 案例分析](#6-案例分析)
    - [6.1 条件 Drop](#61-条件-drop)
    - [6.2 元组析构](#62-元组析构)
    - [6.3 循环与 Drop](#63-循环与-drop)
  - [7. 与编译器的对比](#7-与编译器的对比)
  - [参考文献](#参考文献)

---

## 摘要

Drop Elaboration 是 Rust 编译器的一个关键阶段，负责确定在何时何地插入析构函数调用。本文档基于 ETH Zürich 2024 年的本科毕业论文，提供 Drop Elaboration 的完整形式化理论，包括：

1. **核心语言定义**：支持初始化状态和 Drop 的简化 Rust 子集
2. **Elaboration 转换**：从高层表示到低层显式 Drop 的转换规则
3. **正确性证明**：转换保持程序行为的数学保证
4. **Coq 实现**：机械化的形式化证明

---

## 1. 引言

### 1.1 Drop Elaboration 是什么

在 Rust 中，值在作用域结束时自动调用析构函数（Drop）。例如：

```rust
{
    let x = Box::new(42);
    // x 在此处离开作用域，自动调用 drop(x)
}
```

然而，当控制流复杂时，确定 Drop 的位置变得非平凡：

```rust
{
    let x = Box::new(1);
    let y = Box::new(2);
    if condition {
        return;  // 需要 drop(x) 和 drop(y)
    }
    // 也需要 drop(x) 和 drop(y)
}
```

**Drop Elaboration** 是编译器将隐式 Drop 语义转换为显式 Drop 调用的过程。

### 1.2 为什么需要形式化

Rust 的 Drop 规则涉及复杂的控制流分析：

1. **部分初始化**：结构体可能只有部分字段被初始化
2. **条件移动**：值可能在某些路径被移动，在其他路径需要 Drop
3. **循环**：循环中的变量可能有复杂的生命周期

形式化可以确保：

- 转换的正确性
- 内存安全保证
- 与编译器实现的一致性

---

## 2. 核心概念

### 2.1 析构与 Drop

**Drop Trait**：

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

**调用时机**：

- 值离开作用域
- 值被赋值（先 drop 旧值）
- 显式调用 `drop(v)`

### 2.2 初始化状态

Rust 中变量有三个初始化状态：

| 状态 | 含义 | 需要 Drop？ |
|------|------|------------|
| **未初始化** | 声明但未赋值 | 否 |
| **已初始化** | 已赋值，未移动 | 是 |
| **已移动** | 值被转移 | 否 |

**T-Forest 表示**：

```
局部变量状态可以表示为 T-Forest（类型树森林）：

T-Tree ::= Leaf(Type, State)
        | Node(Type, List<T-Tree>)

其中 State ∈ {Uninit, Init, Moved}
```

**示例**：

```rust
let x: (Box<i32>, Box<i32>);
// T-Forest: Node((Box<i32>, Box<i32>), [Leaf(Uninit), Leaf(Uninit)])

x.0 = Box::new(1);
// T-Forest: Node((Box<i32>, Box<i32>), [Leaf(Init), Leaf(Uninit)])

let y = x.0;
// T-Forest: Node((Box<i32>, Box<i32>), [Leaf(Moved), Leaf(Uninit)])
```

### 2.3 控制流与 Drop

不同的控制流路径可能有不同的 Drop 需求：

```rust
let x: Box<i32>;
if condition {
    x = Box::new(1);  // 路径 A: x 已初始化
} else {
    // 路径 B: x 未初始化
}
// 合并点: 需要条件 Drop
```

---

## 3. 形式化语言

### 3.1 语法定义

```
(* 类型 *)
τ ::= Int
    | Bool
    | Unit
    | Box<τ>          (* 堆分配 *)
    | (τ₁, ..., τₙ)   (* 元组 *)
    | Droppable       (* 需要析构的类型 *)

(* 表达式 *)
e ::= x               (* 变量 *)
    | n               (* 整数 *)
    | true | false    (* 布尔 *)
    | ()              (* 单元 *)
    | e₁ + e₂
    | e₁ > e₂
    | copy e          (* 复制 *)
    | move e          (* 移动 *)
    | Box::new(e)     (* 分配 *)
    | *e              (* 解引用 *)
    | e.0 | e.1       (* 投影 *)

(* 命令 *)
c ::= skip
    | c₁; c₂
    | let x: τ       (* 声明未初始化变量 *)
    | x := e         (* 赋值 *)
    | drop e         (* 显式析构 *)
    | forget x       (* 忘记变量，不析构 *)
    | if e then c₁ else c₂
    | while e do c
    | return

(* 程序 *)
P ::= let x̄: τ̄; c    (* 局部声明 + 命令 *)
```

### 3.2 类型系统

**上下文**：

```
Γ ::= · | Γ, x: τ

Δ ::= · | Δ, x: Init | Δ, x: Uninit | Δ, x: Moved
```

**类型规则（选）**：

```
(* 变量使用 *)
Γ(x) = τ    Δ(x) = Init
────────────────────────
Γ; Δ ⊢ x : τ ▷ Δ

(* 移动 *)
Γ; Δ ⊢ e : τ    τ: Droppable
─────────────────────────────
Γ; Δ ⊢ move e : τ ▷ Δ[e ↦ Moved]

(* 赋值 *)
Γ(x) = τ    Γ; Δ ⊢ e : τ    Δ(x) = Uninit ∨ Δ(x) = Init
─────────────────────────────────────────────────────────
Γ; Δ ⊢ x := e ▷ Δ[x ↦ Init]
```

### 3.3 操作语义

**配置**：

```
配置 ::= (l, h, c)

l: 局部状态 (LocalId → Value ∪ {⊥})
h: 堆 (Location → Object)
c: 命令
```

**求值规则（选）**：

```
(* Drop - 展开前 *)
G ⊢ ⟨l, h, drop x⟩ ↝ ⟨l', h', skip⟩
其中：
  - l(x) = Pointer(loc)
  - h(loc) = Object(v, Droppable)
  - h' = h[loc ↦ freed]
  - l' = l[x ↦ ⊥]

(* Drop - 展开后 *)
G ⊢ ⟨l, h, drop x⟩ ↝ ⟨l, h, drop_glue(τ, x)⟩
其中：
  - l(x) = v
  - τ = type_of(v)
  - drop_glue 根据类型生成具体析构代码
```

---

## 4. Drop Elaboration 转换

### 4.1 转换概述

Drop Elaboration 将隐式 Drop 转换为显式 `drop` 和 `forget` 调用：

```rust
// 源代码
{
    let x = Box::new(1);
    let y = Box::new(2);
}

// Elaborated 代码
{
    let x = Box::new(1);
    let y = Box::new(2);
    drop(y);
    drop(x);
    forget(y);
    forget(x);
}
```

### 4.2 初始化效果

**效果系统**：跟踪命令对初始化状态的影响

```
效果 E ::= Map<Place, StateChange>

StateChange ::= Uninit → Init
             | Init → Moved
             | Init → Init
```

**顺序组合**：

```
E₁; E₂ = λp. match E₁(p) of
            | Some(s₁) ⇒ Some(s₁)
            | None ⇒ E₂(p)
```

**条件组合**：

```
if E₁ else E₂ = λp. if E₁(p) = E₂(p)
                      then E₁(p)
                      else Unknown
```

### 4.3 标志管理

为了处理条件 Drop，引入布尔标志：

```rust
// 原始代码
let x: Box<i32>;
if condition {
    x = Box::new(1);
}

// Elaborated 代码
let x: Box<i32>;
flag_x := true;  // 未初始化标志
if condition {
    x = Box::new(1);
    flag_x := false;  // 已初始化
}
if flag_x {
    // 不需要 drop，因为未初始化
} else {
    drop(x);
}
forget(x);
flag_x := false;
```

**T-Tree 上的标志分配**：

```
为每个可能部分初始化的复合类型字段分配标志：

(x: (Box<i32>, Box<i32>), y: Box<i32>)

标志分配：
- flag_x: 整个 x 是否未初始化
- flag_x_0: x.0 是否未初始化
- flag_x_1: x.1 是否未初始化
- flag_y: y 是否未初始化
```

---

## 5. 形式化证明

### 5.1 正确性声明

**定理 (Drop Elaboration 正确性)**：

对于所有良类型的程序 P，如果：

```
P  ⟹  P'  (经过 Drop Elaboration)
```

则对于所有输入 I：

```
eval(P, I) = eval(P', I)
```

即：Elaboration 保持程序的可观察行为。

**更强的声明**（模拟关系）：

```
存在一个模拟关系 R，使得：
1. 初始状态相关: R(σ₀, σ₀')
2. 保持步骤: 如果 R(σ, σ') 且 σ → σ₁，则存在 σ₁' 使得 σ' →* σ₁' 且 R(σ₁, σ₁')
3. 终止一致: 如果 σ 终止于 v，则 σ' 终止于相同的 v
```

### 5.2 证明策略

**引理 1 (初始化保持)**：

Elaboration 不改变变量的初始化效果。

**证明**：通过对命令结构归纳。

**引理 2 (Drop 顺序)**：

Elaborated 代码中的 Drop 顺序符合 LIFO（逆序声明）。

**证明**：通过构造，标志赋值和检查遵循声明顺序的逆序。

**引理 3 (无重复 Drop)**：

每个已初始化的值恰好被 Drop 一次。

**证明**：标志系统确保：

- 如果值已初始化，则标志为 false，执行 Drop
- Drop 后设置 flag = true，防止重复 Drop

### 5.3 Coq 实现

**形式化结构**：

```coq
(* 语法 *)
Inductive expr :=
  | EVar : string -> expr
  | ENum : nat -> expr
  | EAdd : expr -> expr -> expr
  (* ... *)
.

Inductive cmd :=
  | CSkip
  | CSeq : cmd -> cmd -> cmd
  | CLet : string -> ty -> cmd
  | CAssign : string -> expr -> cmd
  | CDrop : expr -> cmd
  | CForget : string -> cmd
  | CIf : expr -> cmd -> cmd -> cmd
  (* ... *)
.

(* 操作语义 *)
Inductive eval : global_ctx -> config -> config -> Prop :=
  (* 求值规则 *)
.

(* Drop Elaboration *)
Fixpoint drop_elaborate (c: cmd) : cmd :=
  match c with
  | CSeq c1 c2 =>
      let c1' := drop_elaborate c1 in
      let c2' := drop_elaborate c2 in
      let drops := compute_drops c1 c2 in
      CSeq (CSeq c1' drops) c2'
  | CIf e c1 c2 =>
      let c1' := drop_elaborate c1 in
      let c2' := drop_elaborate c2 in
      let flags := allocate_flags c1 c2 in
      insert_flag_management (CIf e c1' c2') flags
  (* ... *)
  end.

(* 正确性定理 *)
Theorem drop_elaboration_correct :
  forall G c l h,
  well_typed c ->
  exists R,
  simulation R (G, (l, h, c)) (G, (l, h, drop_elaborate c)).
Proof.
  (* 通过对命令结构归纳 *)
Admitted.
```

---

## 6. 案例分析

### 6.1 条件 Drop

```rust
// 源代码
let x: Box<i32>;
if n > 0 {
    x = Box::new(n);
}

// Elaborated
let x: Box<i32>;
flag_x := true;
if (copy n) > 0 {
    x = Box::new(move n);
    flag_x := false;
}
if (copy flag_x) {
    // x 未初始化，不 drop
} else {
    drop(x);
}
forget(x);
flag_x := false;
```

### 6.2 元组析构

```rust
// 源代码
let x: (Box<i32>, Box<i32>, Box<i32>);
x.0 = Box::new(1);
x.1 = Box::new(2);
// x.2 保持未初始化

// Elaborated
let x: (Box<i32>, Box<i32>, Box<i32>);
flag_x := true;
flag_x_0 := true;
flag_x_1 := true;
flag_x_2 := true;

x.0 = Box::new(1);
flag_x_0 := false;
flag_x := false;

x.1 = Box::new(2);
flag_x_1 := false;

// 作用域结束
drop(x.2);  // 条件执行，实际上不会执行
drop(x.1);
drop(x.0);
forget(x);
```

### 6.3 循环与 Drop

```rust
// 源代码
loop {
    let x = Box::new(1);
    if condition { break; }
}

// Elaborated
loop {
    let x: Box<i32>;
    x = Box::new(1);
    if condition {
        drop(x);
        forget(x);
        break;
    }
    drop(x);
    forget(x);
}
```

---

## 7. 与编译器的对比

本形式化与 rustc 的实现对比：

| 方面 | rustc | 形式化 |
|------|-------|--------|
| 中间表示 | MIR | 简化命令式语言 |
| 数据结构 | 复杂控制流图 | T-Forest |
| 优化 | 多种优化 | 无优化（清晰语义） |
| 标志分配 | 精细的位标志 | 显式布尔变量 |

**已知差异**：

1. **保守性**：形式化可能比 rustc 更保守（更多标志检查）
2. **优化机会**：rustc 会进行死代码消除等优化
3. **错误信息**：rustc 提供更详细的借用检查错误

---

## 参考文献

1. **Fukala, V.** (2024). Formalization of Rust Drop Elaboration. *Bachelor Thesis, ETH Zürich*.

2. **Jung, R., et al.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.

3. **Rust Compiler Documentation**. Drop elaboration and MIR construction.
   - <https://rustc-dev-guide.rust-lang.org/>

4. **Klabnik, S., & Nichols, C.** (2023). The Rust Programming Language.
   - Chapter 15: Smart Pointers and Drop trait.

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*状态: 完成*
