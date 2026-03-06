# RefinedRust: 高保证验证的类型系统

> **来源**: PLDI 2024 (ACM SIGPLAN Conference on Programming Language Design and Implementation)
> **作者**: Leon Gahrler, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer
> **难度**: 🔴 高级
> **前置知识**: RustBelt, 霍尔逻辑, 细化类型

---

## 目录

- [RefinedRust: 高保证验证的类型系统](#refinedrust-高保证验证的类型系统)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言](#1-引言)
    - [1.1 动机](#11-动机)
    - [1.2 RefinedRust 概述](#12-refinedrust-概述)
  - [2. 核心概念](#2-核心概念)
    - [2.1 细化类型](#21-细化类型)
    - [2.2 所有权与细化](#22-所有权与细化)
    - [2.3 生命周期多态](#23-生命周期多态)
  - [3. Radium: Rust MIR 的操作语义](#3-radium-rust-mir-的操作语义)
    - [3.1 语法](#31-语法)
    - [3.2 内存模型](#32-内存模型)
    - [3.3 操作语义](#33-操作语义)
  - [4. 类型系统](#4-类型系统)
    - [4.1 细化类型语法](#41-细化类型语法)
    - [4.2 类型规则](#42-类型规则)
    - [4.3 子类型关系](#43-子类型关系)
  - [5. 程序逻辑](#5-程序逻辑)
    - [5.1 Iris 集成](#51-iris-集成)
    - [5.2 霍尔三元组](#52-霍尔三元组)
    - [5.3 所有权推理](#53-所有权推理)
  - [6. 验证流程](#6-验证流程)
    - [6.1 类型检查](#61-类型检查)
    - [6.2 证明生成](#62-证明生成)
    - [6.3 Coq 证明](#63-coq-证明)
  - [7. 案例研究](#7-案例研究)
    - [7.1 安全抽象](#71-安全抽象)
    - [7.2 数据结构](#72-数据结构)
  - [参考文献](#参考文献)

---

## 摘要

RefinedRust 是一个用于高保证验证 Rust 程序的类型系统，结合了：

1. **细化类型**（Refinement Types）：在类型中嵌入谓词约束
2. **所有权类型**：Rust 的所有权和借用系统
3. **分离逻辑**：Iris 框架支持高阶推理

RefinedRust 在 Rust 的 MIR（Mid-level Intermediate Representation）上工作，通过类型系统同时保证内存安全和功能正确性。

---

## 1. 引言

### 1.1 动机

现有 Rust 验证工具的分层：

| 工具 | 保证级别 | 自动化 | 覆盖范围 |
|------|----------|--------|----------|
| Miri | 运行时 UB 检测 | 全自动 | 内存安全 |
| Kani | 模型检查 | 全自动 | 状态空间 |
| Prusti | 契约验证 | 半自动 | 功能正确性 |
| Creusot | 定理证明 | 半自动 | 功能正确性 |
| RefinedRust | 类型细化 | 半自动 | 内存+功能 |

**RefinedRust 的独特之处**：

- 将细化类型与所有权类型统一
- 基于 Iris 的模块化验证
- 支持 unsafe 代码的规范

### 1.2 RefinedRust 概述

```
RefinedRust 架构：

Rust 源码
   ↓ (rustc)
MIR (Mid-level IR)
   ↓ (RefinedRust 前端)
带细化注解的 MIR
   ↓ (类型检查)
类型约束
   ↓ (约束求解)
验证条件 (VC)
   ↑ (SMT 求解器)
证明结果
```

---

## 2. 核心概念

### 2.1 细化类型

**标准类型 vs 细化类型**：

```rust
// 标准类型: i32
// 细化类型: {v: i32 | v > 0}

fn abs(x: i32) -> i32  // 标准类型
fn abs(x: i32) -> {v: i32 | v >= 0 && (v == x || v == -x)}  // 细化类型
```

**RefinedRust 语法**：

```
τ ::= base{b}           (* 细化基础类型 *)
    | &{b} τ           (* 细化共享引用 *)
    | &mut{b} τ        (* 细化可变引用 *)
    | Box<τ>           (* Box 类型 *)
    | (τ₁, ..., τₙ)    (* 元组 *)

b ::= e                (* 布尔表达式 *)
    | b₁ ∧ b₂         (* 合取 *)
    | b₁ ∨ b₂         (* 析取 *)
    | ∀x. b           (* 全称量词 *)
    | ∃x. b           (* 存在量词 *)

e ::= v | x | e₁ + e₂ | e₁ = e₂ | ...  (* 表达式 *)
```

### 2.2 所有权与细化

**所有权传递细化信息**：

```rust
// 值所有权传递细化
let x: {v: i32 | v > 0} = 42;
let y = x;  // y: {v: i32 | v > 0}

// 引用传递细化
fn get_positive(v: &{v: i32 | v > 0}) -> i32 {
    *v  // 返回: {v: i32 | v > 0}
}
```

**可变引用的特殊处理**：

```rust
fn increase(x: &mut {v: i32 | v > 0}) {
    *x += 1;  // 后置条件: {v: i32 | v > 1}
}
```

### 2.3 生命周期多态

**生命周期约束**：

```rust
// 标准 Rust
fn borrow<'a>(x: &'a i32) -> &'a i32

// RefinedRust 扩展
fn borrow<'a>(x: &'a {v: i32 | v > 0})
    -> &'a {v: i32 | v > 0}
```

**生命周期与细化交互**：

```
在生命周期 ℓ 内，引用 &{b} τ 保证：
1. 指向有效的 τ 值
2. τ 满足细化谓词 b
3. 对于可变引用，可以修改值但保持类型
```

---

## 3. Radium: Rust MIR 的操作语义

### 3.1 语法

**Radium 表达式**：

```
(* 值表达式 *)
e ::= v                         (* 值 *)
    | e₁ ⊕ e₂                  (* 二元运算 *)
    | copy p                   (* 复制 *)
    | move p                   (* 移动 *)
    | addr_of p                (* 取地址 *)
    | addr_of_mut p            (* 取可变地址 *)
    | *e                       (* 解引用 *)
    | e as τ                   (* 类型转换 *)

(* 位置表达式 *)
p ::= x                       (* 局部变量 *)
    | p.f                     (* 字段投影 *)
    | p[n]                    (* 索引 *)
    | *p                      (* 解引用位置 *)

(* 值 *)
v ::= n                       (* 整数 *)
    | β                       (* 字节列表 *)
    | loc(ℓ, n)               (* 位置片段 *)
    | poison                  (* 未初始化 *)
```

**语句**：

```
s ::= assign p = e            (* 赋值 *)
    | start_lft(k)           (* 开始生命周期 *)
    | end_lft(k)             (* 结束生命周期 *)
    | call p = f(args)       (* 函数调用 *)
    | return                 (* 返回 *)

bb ::= block { s*; terminator }  (* 基本块 *)

fn ::= fn f(args) -> τ { bb* }   (* 函数 *)
```

### 3.2 内存模型

**内存表示**：

```
堆 H := Map<Location, List<Byte>>

Byte ::= b (0-255)            (* 普通字节 *)
      | loc(ℓ, n)             (* 位置片段 *)
      | poison                (* 毒字节 *)
```

**值布局**：

```
// i32: 4 字节
layout(i32) = [b₁, b₂, b₃, b₄]

// &T (64位): 8 字节，每个是位置片段
layout(&T) = [loc(ℓ,0), loc(ℓ,1), ..., loc(ℓ,7)]
```

### 3.3 操作语义

**加载规则**：

```
H(loc) = [β₁, ..., βₙ]
∀i. βᵢ ≠ poison
─────────────────────────────────────
〈H, *loc〉⇓ v

其中 v 是根据类型布局解释字节的结果
```

**存储规则**：

```
layout(τ) = n bytes
〈H, e〉⇓ v
encode(v, τ) = [β₁, ..., βₙ]
─────────────────────────────────────────
〈H, *loc = e〉→ H[loc ↦ [β₁, ..., βₙ]]
```

**生命周期语义**：

```
(* 开始生命周期 *)
start_lft(k):
  将 k 加入活跃生命周期集合

(* 结束生命周期 *)
end_lft(k):
  从活跃集合移除 k
  失效所有标记为 k 的引用
```

---

## 4. 类型系统

### 4.1 细化类型语法

**类型分层**：

```
(* 基础类型 *)
base ::= i8 | i16 | i32 | i64 | isize
       | u8 | u16 | u32 | u64 | usize
       | bool | ()

(* 完整类型 *)
τ ::= base{φ}                 (* 细化基础类型 *)
    | &{φ}<'a> τ            (* 共享引用 *)
    | &mut{φ}<'a> τ         (* 可变引用 *)
    | Box{φ}<τ>             (* 堆分配 *)
    | [τ; n]                (* 数组 *)
    | (τ₁, ..., τₙ)         (* 元组 *)
    | struct{φ} S<τ̄>        (* 结构体 *)
    | enum{φ} E<τ̄>          (* 枚举 *)

(* 细化谓词 *)
φ ::= e | e₁ = e₂ | e₁ < e₂ | ...
    | φ₁ ∧ φ₂ | φ₁ ∨ φ₂
    | ∀x:τ. φ | ∃x:τ. φ
```

### 4.2 类型规则

**细化基础类型**：

```
Γ ⊢ e : base
Γ ⊢ φ[e/v]  (* φ 在 e 处成立 *)
───────────────────────────────
Γ ⊢ e : base{v. φ}
```

**共享引用**：

```
Γ ⊢ p : τ
Γ ⊢ φ[p/v]
───────────────────────────────────
Γ ⊢ &p : &{v. φ}<'a> τ
```

**可变引用**：

```
Γ ⊢ p : τ
Γ ⊢ φ[p/v]
───────────────────────────────────
Γ ⊢ &mut p : &mut{φ_in}{φ_out}<'a> τ

其中：
  φ_in: 借用时的条件
  φ_out: 归还时的条件
```

**赋值**：

```
Γ ⊢ p : &mut{φ_in}{φ_out}<'a> τ
Γ ⊢ e : τ
Γ ⊢ φ_in[e/v]
─────────────────────────────────────────
Γ ⊢ *p = e : ()  ▷  Γ[p ↦ &mut{φ_in}{φ_out[e/v]}<'a> τ]
```

### 4.3 子类型关系

**细化蕴含**：

```
Γ ⊢ φ₁ ⇒ φ₂       (* φ1 蕴含 φ2 *)
───────────────────────────────────
Γ ⊢ base{v. φ₁} <: base{v. φ₂}
```

**引用子类型**：

```
Γ ⊢ τ₁ <: τ₂
Γ ⊢ φ₂ ⇒ φ₁      (* 逆变 *)
─────────────────────────────────────────
Γ ⊢ &{φ₁}<'a> τ₁ <: &{φ₂}<'a> τ₂
```

**生命周期子类型**：

```
'a : 'b    (* 'a 包含 'b *)
───────────────────────────────────
Γ ⊢ &'a τ <: &'b τ
```

---

## 5. 程序逻辑

### 5.1 Iris 集成

RefinedRust 基于 Iris 框架构建：

```
Iris 资源代数：

Own(ℓ, v, τ)       (* 对位置 ℓ 的所有权，存储值 v，类型 τ *)
Borrow(ℓ, k, τ)    (* 对 ℓ 的借用，生命周期 k *)
Loan(ℓ, k, τ)      (* ℓ 的贷款，被生命周期 k 的借用冻结 *)
```

**细化谓词作为 Iris 命题**：

```
{v: τ | φ}  ⟼  λv. Own(ℓ, v, τ) ∗ ⌜φ[v]⌝
```

### 5.2 霍尔三元组

**霍尔三元组语法**：

```
{P} e {v. Q}      (* 前置条件 P，表达式 e，后置条件 Q *)
```

**规则示例**：

```
(* 赋值 *)
{Own(ℓ, _, τ) ∗ Q[v/x]} *ℓ = v {Own(ℓ, v, τ) ∗ Q}

(* 借用创建 *)
{Own(ℓ, v, τ)} &ℓ {p. Borrow(p, ℓ, k, τ) ∗ Loan(ℓ, k, τ, v)}

(* 解引用 *)
{Borrow(p, ℓ, k, τ)} *p {v. Borrow(p, ℓ, k, τ) ∗ v = ℓ.contents}
```

### 5.3 所有权推理

**Framing 规则**：

```
{P} e {v. Q}
────────────────────────────
{P ∗ R} e {v. Q ∗ R}

（R 中不包含 e 修改的位置）
```

**生命周期打开/关闭**：

```
(* 打开 *)
Loan(ℓ, k, τ, v) ∗ k active
────────────────────────────
Own(ℓ, v, τ)

(* 关闭 *)
Own(ℓ, v, τ)
────────────────────────────
Loan(ℓ, k, τ, v)
```

---

## 6. 验证流程

### 6.1 类型检查

RefinedRust 类型检查器：

```rust
// 输入: MIR + 细化注解
// 输出: 类型约束集合

fn type_check(mir: MIR, annotations: Annotations) -> Constraints {
    // 1. 构建类型环境
    let mut env = TypeEnv::new();

    // 2. 对每个基本块进行类型检查
    for bb in mir.basic_blocks {
        for stmt in bb.statements {
            let constraints = check_stmt(&mut env, stmt);
            constraints.add(constraints);
        }
    }

    // 3. 返回约束集合
    constraints
}
```

### 6.2 证明生成

**验证条件生成**：

```
类型约束 ──▶ SMT-LIB 公式 ──▶ SMT 求解器 ──▶ 证明/反例
```

**需要证明的义务**：

1. **细化蕴含**：子类型关系的有效性
2. **算术约束**：数组索引不越界
3. **内存安全**：指针有效性

### 6.3 Coq 证明

对于复杂属性，生成 Coq 证明脚本：

```coq
(* 生成的 RefinedRust 证明 *)
Lemma array_index_safe :
  forall (a: array{i32 | len = 10}) (i: usize{i < 10}),
  {v: i32 | v = a[i]}.
Proof.
  intros a i.
  unfold array_index.
  apply array_index_spec.
  assumption.
Qed.
```

---

## 7. 案例研究

### 7.1 安全抽象

**Vec::push 验证**：

```rust
#[refinedrust::spec]
fn push(&mut self, value: T)
    requires self.len < self.capacity
    ensures self.len == old(self.len) + 1
    ensures self[self.len-1] == value
{
    // 实现...
}
```

### 7.2 数据结构

**链表不变式**：

```rust
#[refinedrust::invariant]
struct List<T> {
    // 链表长度等于实际元素数
    len: usize{len == nodes.count},
    // 所有节点可达
    head: Option<Box<Node<T>>>{all_reachable(head, nodes)}
}
```

---

## 参考文献

1. **Gahrler, L., Sammler, M., Jung, R., Krebbers, R., & Dreyer, D.** (2024). RefinedRust: A Type System for High-Assurance Verification of Rust Programs. *PLDI '24*.

2. **Jung, R., et al.** (2018). Iris from the ground up: A modular foundation for higher-order concurrent separation logic. *Journal of Functional Programming*.

3. **Vazou, N., et al.** (2014). Refinement types for Haskell. *ICFP '14*.

4. **Swamy, N., et al.** (2016). Dependent types and multi-monadic effects in F*. *POPL '16*.

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*状态: 完成*
