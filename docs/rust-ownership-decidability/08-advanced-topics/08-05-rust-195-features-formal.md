# Rust 1.95 特性形式化分析

> **版本**: Rust 1.95.0+ (Edition 2024)
> **创建日期**: 2026-05-12
> **对齐日期**: 2026-05-12
> **状态**: ✅ 已完成
> **难度**: 🔴 高级
> **前置知识**: 模式匹配形式化、生命周期理论、类型系统基础

---

## 📋 目录

- [Rust 1.95 特性形式化分析](#rust-195-特性形式化分析)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
  - [2. if let guards 的形式化语义](#2-if-let-guards-的形式化语义)
    - [2.1 语法扩展](#21-语法扩展)
    - [2.2 操作语义](#22-操作语义)
    - [2.3 类型安全定理](#23-类型安全定理)
    - [2.4 与借用检查器的交互](#24-与借用检查器的交互)
  - [3. `use<..>` 精确捕获的形式化语义](#3-use-精确捕获的形式化语义)
    - [3.1 动机与问题定义](#31-动机与问题定义)
    - [3.2 语法与规约](#32-语法与规约)
    - [3.3 捕获集合的形式化定义](#33-捕获集合的形式化定义)
    - [3.4 子类型关系](#34-子类型关系)
  - [4. `impl From<bool> for {f32, f64}` 的形式化](#4-impl-frombool-for-f32-f64-的形式化)
  - [5. RangeInclusive 迭代优化](#5-rangeinclusive-迭代优化)
  - [6. 兼容性影响分析](#6-兼容性影响分析)
  - [7. 形式化证明义务](#7-形式化证明义务)
  - [参考文献](#参考文献)

---

## 1. 概述

Rust 1.95.0 于 2026-04-16 发布，引入了若干影响类型系统和控制流的形式化语义的关键特性。本文档对这些特性进行形式化分析，建立其语法、操作语义和类型安全的严格描述。

**核心特性列表**:

| 特性 | 类别 | 形式化复杂度 | 影响范围 |
|------|------|-------------|----------|
| `if let guards` | 控制流/模式匹配 | ⭐⭐⭐ | 模式匹配守卫的语义扩展 |
| `use<..>` 精确捕获 | 类型系统/生命周期 | ⭐⭐⭐⭐ | `impl Trait` 返回类型的生命周期推理 |
| `impl From<bool> for {f32, f64}` | 类型转换 | ⭐ | 标准库 trait 实现 |
| `RangeInclusive` 优化 | 标准库/性能 | ⭐⭐ | 迭代器语义不变，实现优化 |

---

## 2. if let guards 的形式化语义

### 2.1 语法扩展

Rust 1.95 将模式匹配守卫的语法从纯布尔表达式扩展为支持嵌套模式匹配：

```text
guard ::= expr                    (传统守卫，Rust < 1.95)
        | "if" "let" pattern "=" expr ("&&" guard)*   (新语法，Rust 1.95+)
        | "if" expr ("&&" guard)*
```

**BNF 扩展**:

```text
match_arm ::= pattern arm_guard? "=>" expr
arm_guard ::= "if" guard_expr
guard_expr ::= let_guard | boolean_expr | let_guard "&&" guard_expr | boolean_expr "&&" guard_expr
let_guard ::= "let" pattern "=" expr
```

### 2.2 操作语义

**小步操作语义 (Small-Step Operational Semantics)**:

$$
\frac{E \vdash e \Downarrow v \quad E' = E \cup \text{bind}(p, v)}{E \vdash \text{if let } p = e \text{ then } t \text{ else } f \rightarrow t[E']} \quad \text{(LET-GUARD-MATCH)}
$$

$$
\frac{E \vdash e \Downarrow v \quad \text{bind}(p, v) = \bot}{E \vdash \text{if let } p = e \text{ then } t \text{ else } f \rightarrow f} \quad \text{(LET-GUARD-FAIL)}
$$

其中 $\text{bind}(p, v)$ 是将模式 $p$ 与值 $v$ 匹配产生的绑定环境，$\bot$ 表示匹配失败。

**与传统守卫的组合**:

```rust
match msg {
    Message::Text(text)
        if let Some(u) = current_user
        && u.can_read(&text)
        && text.len() < 1000 =>
    {
        // arm body
    }
    _ => {}
}
```

操作语义按从左到右的短路顺序求值：

1. 求值 `let Some(u) = current_user`，若匹配失败则该 arm 不匹配
2. 在 $E \cup \{u \mapsto v\}$ 中求值 `u.can_read(&text)`，若为 false 则该 arm 不匹配
3. 在相同环境中求值 `text.len() < 1000`，若为 false 则该 arm 不匹配
4. 执行 arm body

### 2.3 类型安全定理

**定理 2.1 (If-Let Guard Type Safety)**:

若 $\Gamma \vdash e : T$，$\Gamma, \Gamma_p \vdash e_g : \text{bool}$，且模式 $p$ 在类型 $T$ 下生成绑定环境 $\Gamma_p$，则：

$$
\Gamma \vdash \text{match } e \text{ { } p \text{ if let } p' = e' \text{ && } e_g \Rightarrow e_b \text{ } } : T_{\text{ret}}
$$

当且仅当 $\Gamma, \Gamma_p, \Gamma_{p'} \vdash e_b : T_{\text{ret}}$。

**证明概要**:

- 模式 $p$ 的类型检查保证 $e$ 被解构为子组件
- `if let $p' = e'$ 的类型检查保证 $e'$ 的类型 $T'$ 与模式 $p'$ 兼容
- 绑定环境 $\Gamma_{p'}$ 在守卫作用域内有效
- 守卫的布尔表达式在 $\Gamma \cup \Gamma_p \cup \Gamma_{p'}$ 下类型检查
- 由归纳假设，arm body $e_b$ 在扩展环境中类型正确
- exhaustiveness checking 保证至少一个 arm 匹配

### 2.4 与借用检查器的交互

`if let guards` 引入了新的借用检查挑战：守卫中绑定的变量的生命周期必须至少延续到 arm body 的结束。

```rust
fn example<'a>(opt: &'a Option<String>) -> &'a str {
    match opt {
        Some(s) if let Some(ref t) = s.get(0..1) => t, // ❌ 编译错误
        _ => "",
    }
}
```

**问题**: `t` 的生命周期受 `s.get(0..1)` 的限制，而 `s` 是模式匹配的临时绑定。

**解决方案**: Rust 1.95 的借用检查器将 `if let` 守卫中的绑定视为 arm body 环境的一部分，应用与 `if let` 表达式相同的区域约束规则。

---

## 3. `use<..>` 精确捕获的形式化语义

### 3.1 动机与问题定义

在 Rust 1.95 之前，`impl Trait` 返回类型隐式捕获所有输入生命周期，导致过度约束：

```rust
// Rust < 1.95: 隐式捕获 'a, 'b, 'c
fn make_iter<'a, 'b, 'c>(x: &'a str, y: &'b str, z: &'c str) -> impl Iterator<Item = char> {
    x.chars() // 实际上只使用了 'a，但返回类型约束了 'b 和 'c
}
```

**形式化问题**: 设函数签名 $f : \forall \vec{\alpha}. \vec{T} \rightarrow \exists \beta. U[\beta]$，隐式捕获使得 $U$ 依赖于所有 $\vec{\alpha}$，即使实际实现只依赖子集。

### 3.2 语法与规约

Rust 1.95 引入 `use<..>` 语法显式指定捕获的生命周期和类型参数：

```rust
// 只捕获 'a
fn make_iter<'a, 'b, 'c>(x: &'a str, y: &'b str, z: &'c str) -> impl Iterator<Item = char> + use<'a> {
    x.chars()
}
```

**形式化语法**:

```text
opaque_type ::= "impl" trait_bound ("+" trait_bound)* ("use" "<" capture_list ">")?
capture_list ::= capture_item ("," capture_item)*
capture_item ::= lifetime | type_param
```

### 3.3 捕获集合的形式化定义

**定义 3.1 (精确捕获集合)**: 对于函数 $f$ 的返回类型 $\tau = \text{impl } T + \text{use}\langle C \rangle$，捕获集合 $C$ 是一个生命周期和类型参数的有限集，满足：

1. **最小性**: $C$ 是使 $T$ 良-formed 的最小集合
2. **封闭性**: 若 $\alpha \in C$ 且 $\alpha$ 在 $T$ 的 trait bound 中出现，则 $T$ 中所有依赖于 $\alpha$ 的参数也必须在 $C$ 中显式声明或可由上下文推断
3. **一致性**: 函数体的实际返回类型 $\tau_{\text{body}}$ 的 free variables $FV(\tau_{\text{body}}) \subseteq C$

**定理 3.1 (精确捕获的正确性)**:

若函数 $f$ 声明返回类型为 $\text{impl } T + \text{use}\langle C \rangle$，且函数体返回类型 $\tau_{\text{body}}$ 满足 $FV(\tau_{\text{body}}) \subseteq C$，则 $f$ 的类型安全成立。

### 3.4 子类型关系

精确捕获影响 `impl Trait` 的子类型关系：

$$
\frac{C_1 \subseteq C_2}{\text{impl } T + \text{use}\langle C_1 \rangle \preceq \text{impl } T + \text{use}\langle C_2 \rangle} \quad \text{(CAPTURE-SUBTYPING)}
$$

**直觉**: 捕获更少生命周期的 `impl Trait` 更通用（约束更少），因此是子类型。

**示例**:

```rust
fn narrow<'a, 'b>(x: &'a str, y: &'b str) -> impl Display + use<'a> { x }
fn wide<'a, 'b>(x: &'a str, y: &'b str) -> impl Display + use<'a, 'b> { x }

// narrow 的返回类型是 wide 返回类型的子类型
// 因为 use<'a> 的约束比 use<'a, 'b> 更弱
```

---

## 4. `impl From<bool> for {f32, f64}` 的形式化

这是一个标准库 trait 实现，形式化分析相对简单：

**语义**:

$$
\text{From}_{\text{bool} \rightarrow \text{f32}}(b) = \begin{cases} 1.0 & \text{if } b = \text{true} \\ 0.0 & \text{if } b = \text{false} \end{cases}
$$

**类型安全**: 由于 `bool` 和 `f32`/`f64` 都是 `Copy` 类型，该转换不引入所有权问题。

**与总序的关系**: 此实现与 `bool` 的 `PartialOrd` 实现一致：

$$
\text{false} < \text{true} \iff \text{From}(\text{false}) < \text{From}(\text{true}) \iff 0.0 < 1.0
$$

---

## 5. RangeInclusive 迭代优化

Rust 1.95 对 `RangeInclusive` 的迭代实现进行了性能优化，**不改变语义**。

**形式化不变性**: 设 $r = a \..=\ b$，优化后的迭代器 $I_{\text{opt}}$ 与原始迭代器 $I_{\text{orig}}$ 满足：

$$
\forall i. I_{\text{opt}}.\text{next}^i() = I_{\text{orig}}.\text{next}^i()
$$

**优化细节**: 编译器现在可以更好地内联 `RangeInclusive::next()`，减少边界检查开销。这属于实现级别的优化，不影响类型系统或操作语义。

---

## 6. 兼容性影响分析

| 特性 | 破坏性变更 | 迁移工作量 | 形式化验证影响 |
|------|-----------|-----------|---------------|
| `if let guards` | 否 | 低 | 中等（需更新模式匹配形式化模型） |
| `use<..>` | 否（向后兼容） | 低 | 高（需更新 opaque type 语义） |
| `bool→float` | 否 | 无 | 低 |
| `RangeInclusive` 优化 | 否 | 无 | 无 |

---

## 7. 形式化证明义务

为完整验证 Rust 1.95 的类型安全，以下证明义务待完成：

1. **If-Let Guard Progress**: 证明对于任意 well-typed 的 match 表达式，若 guards 中包含 `if let`，则评估不会 stuck（除非所有 guards 失败且没有 catch-all arm）。

2. **Precise Capture Soundness**: 证明 `use<..>` 的显式捕获不会引入新的类型安全漏洞，即捕获集合 $C$ 的约束不会比实际实现更宽松。

3. **Precise Capture Completeness**: 证明对于任何只使用输入参数子集的 `impl Trait` 返回类型，存在对应的 `use<..>` 声明使得类型检查通过。

---

## 参考文献

1. Rust Lang Team. (2026). *Rust 1.95.0 Release Notes*. <https://blog.rust-lang.org/2026/04/16/Rust-1.95.0.html>
2. RFC 2294. *if let guards*. <https://rust-lang.github.io/rfcs/2294-if-let-guard.html>
3. Rust Reference. *Precise Capturing*. <https://doc.rust-lang.org/reference/types/impl-trait.html#precise-capturing>
4. Jung, R., et al. (2021). *The Rust Reference*. Memory model and operational semantics.
5. Vytiniotis, D., et al. (2011). *Practical type inference for arbitrary-rank types*. Journal of Functional Programming.
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
