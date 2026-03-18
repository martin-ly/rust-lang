# Oxide 形式语义详细补充

> 本文档大幅扩展Oxide形式语义分析，补充完整的类型规则、来源集算法和贷款机制
> 基于 Weiss et al. "Oxide: The Essence of Rust" (2019/2021)

---

## 目录

- [Oxide 形式语义详细补充](#oxide-形式语义详细补充)
  - [目录](#目录)
  - [1. Oxide 核心语言语法](#1-oxide-核心语言语法)
    - [1.1 完整语法定义](#11-完整语法定义)
  - [2. 来源集（Provenance）理论](#2-来源集provenance理论)
    - [2.1 来源集定义](#21-来源集定义)
    - [2.2 来源集近似算法](#22-来源集近似算法)
  - [3. 贷款环境（Loan Context）Θ](#3-贷款环境loan-contextθ)
    - [3.1 贷款记录定义](#31-贷款记录定义)
    - [3.2 贷款操作规则](#32-贷款操作规则)
    - [3.3 贷款冲突检查](#33-贷款冲突检查)
  - [4. 完整类型判断规则](#4-完整类型判断规则)
    - [4.1 规则记号说明](#41-规则记号说明)
    - [4.2 变量规则](#42-变量规则)
    - [4.3 借用规则](#43-借用规则)
    - [4.4 解引用规则](#44-解引用规则)
    - [4.5 赋值规则](#45-赋值规则)
    - [4.6 let绑定规则](#46-let绑定规则)
    - [4.7 装箱规则](#47-装箱规则)
    - [4.8 序列规则](#48-序列规则)
  - [5. 泛型与特质边界](#5-泛型与特质边界)
    - [5.1 泛型函数类型](#51-泛型函数类型)
    - [5.2 特质边界](#52-特质边界)
  - [6. 生命周期约束求解](#6-生命周期约束求解)
    - [6.1 Outlives约束](#61-outlives约束)
    - [6.2 约束求解算法](#62-约束求解算法)
  - [7. 与Rust编译器的对应关系](#7-与rust编译器的对应关系)
    - [7.1 MIR到Oxide的映射](#71-mir到oxide的映射)
    - [7.2 NLL与Oxide的对比](#72-nll与oxide的对比)
  - [8. Oxide形式化属性](#8-oxide形式化属性)
    - [8.1 类型保持定理](#81-类型保持定理)
    - [8.2 借用安全性定理](#82-借用安全性定理)
  - [9. 完整示例推导](#9-完整示例推导)
    - [9.1 示例：简单借用](#91-示例简单借用)
    - [9.2 示例：借用冲突检测](#92-示例借用冲突检测)
  - [参考文献](#参考文献)

## 1. Oxide 核心语言语法

### 1.1 完整语法定义

```text
═══════════════════════════════════════════════════════════════════
                        类型 (Types)
═══════════════════════════════════════════════════════════════════

τ ::=
  | T                            (基本类型: i32, bool, (), ...)
  | Box<τ>                       (堆分配所有权)
  | &ρ ω τ                       (引用: 区域ρ, 权限ω, 类型τ)
  | τ₁ × τ₂                      (元组)
  | !                            (发散类型 never)

ω ::= shrd | uniq                (权限: 共享/唯一)

ρ ::= 'a | 'b | ...              (生命周期/区域变量)

═══════════════════════════════════════════════════════════════════
                        表达式 (Expressions)
═══════════════════════════════════════════════════════════════════

e ::=
  | x                            (变量)
  | n | true | false | ()        (字面量)
  | box e                        (装箱)
  | &ρ ω e                       (借用)
  | *e                           (解引用)
  | e.f                          (字段投影)
  | (e₁, e₂)                     (元组构造)
  | let x = e₁ in e₂             (let绑定)
  | e₁; e2                       (序列)
  | f::<ρ⃗,τ⃗>(e)                  (泛型函数调用)
  | if e₁ then e₂ else e₃        (条件)
  | while e₁ do e₂               (循环)
  | return e                     (返回)

═══════════════════════════════════════════════════════════════════
                        值 (Values)
═══════════════════════════════════════════════════════════════════

v ::=
  | n | true | false | ()        (基本值)
  | ℓ                            (内存位置)
  | &ρ ω ℓ                       (引用值)
  | (v₁, v₂)                     (元组值)
```

---

## 2. 来源集（Provenance）理论

### 2.1 来源集定义

**直观定义**：来源集是一个生命周期变量的集合，表示引用可能有效的所有程序点。

**形式化定义**：

$$
\text{Provenance} = \mathcal{P}(\text{Region})
$$

对于每个引用 `&ρ ω τ`，其来源集为 $\{\rho\}$ 或更复杂的集合。

### 2.2 来源集近似算法

Oxide使用**保守近似**来计算表达式结果的来源集。

**算法：prov(Γ, e) - 计算表达式e的来源集**

```
function prov(Γ, e):
    match e:
        case x (变量):
            return Γ.prov(x)   // 从环境查找

        case &ρ ω e':
            return {ρ}         // 借用创建新来源

        case *e':
            return prov(Γ, e') // 解引用继承来源

        case (e₁, e₂):
            return prov(Γ, e₁) ∪ prov(Γ, e₂)  // 元组合并

        case e'.f:
            return prov(Γ, e') // 投影继承来源

        case box e':
            return ∅           // Box创建新所有权，无来源约束

        case f::<ρ⃗>(e'):
            // 替换形参来源为实参
            return subst(prov(Γ, e'), formal_regions(f), ρ⃗)
```

**保守性定理**：

$$
\text{prov\_oxide}(\Gamma, e) \supseteq \text{prov\_exact}(\Gamma, e)
$$

（Oxide计算的来源集是精确来源集的超集）

---

## 3. 贷款环境（Loan Context）Θ

### 3.1 贷款记录定义

贷款环境 $\Theta$ 跟踪当前活跃的借用：

$$
\Theta ::= \emptyset \mid \Theta, \text{loan}(\rho, \omega, \ell)
$$

其中：

- $\rho$：借用的生命周期/来源
- $\omega$：借用权限（shrd/uniq）
- $\ell$：被借用的内存位置

### 3.2 贷款操作规则

**贷款创建**：

创建借用 `&ρ ω x` 时：

$$
\Theta' = \Theta \cup \{\text{loan}(\rho, \omega, \ell)\} \quad \text{其中 } \Gamma(x) = \ell
$$

**贷款过期**：

当生命周期 $\rho$ 结束时：

$$
\Theta' = \Theta \setminus \{\text{loan}(\rho, \omega, \ell) \mid \forall \omega, \ell\}
$$

### 3.3 贷款冲突检查

**冲突定义**：

两个贷款冲突如果：

$$
\text{conflict}(\text{loan}(\rho_1, \omega_1, \ell_1), \text{loan}(\rho_2, \omega_2, \ell_2)) \triangleq
\ell_1 = \ell_2 \land (\omega_1 = \text{uniq} \lor \omega_2 = \text{uniq})
$$

**有效性检查**：

$$
\text{valid}(\Theta) \triangleq \forall l_1, l_2 \in \Theta. \neg\text{conflict}(l_1, l_2)
$$

---

## 4. 完整类型判断规则

### 4.1 规则记号说明

$$
\Sigma; \Delta; \Gamma; \Theta \vdash e : \tau \dashv \Theta'
$$

其中：

- $\Sigma$：函数签名环境
- $\Delta$：生命周期约束环境
- $\Gamma$：变量类型环境
- $\Theta$：输入贷款环境
- $\Theta'$：输出贷款环境

### 4.2 变量规则

$$
\frac{x : \tau \in \Gamma}{\Sigma; \Delta; \Gamma; \Theta \vdash x : \tau \dashv \Theta} \quad \text{[T-VAR]}
$$

### 4.3 借用规则

**共享借用**：

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e : \tau \dashv \Theta_1 \quad \rho \in \text{prov}(\Gamma, e)}{\Sigma;
\Delta; \Gamma;
\Theta \vdash \&\rho \text{ shrd } e : \&\rho \text{ shrd } \tau \dashv \Theta_1} \quad \text{[T-BORROW-SHRD]}
$$

**可变借用**：

$$
\frac{\Sigma; \Delta; \Gamma;
\Theta \vdash e : \tau \dashv \Theta_1 \quad \rho \in \text{prov}(\Gamma, e) \quad \neg\text{borrowed}(\Theta_1, e)}{\Sigma; \Delta; \Gamma; \Theta \vdash \&\rho \text{ uniq } e : \&\rho \text{ uniq } \tau \dashv \Theta_1 \cup \{\text{loan}(\rho, \text{uniq}, \text{loc}(e))\}} \quad \text{[T-BORROW-UNIQ]}
$$

### 4.4 解引用规则

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e : \&\rho \omega \tau \dashv \Theta_1 \quad \text{loan}(\rho, \omega, \ell) \in \Theta_1}{\Sigma; \Delta; \Gamma; \Theta \vdash *e : \tau \dashv \Theta_1} \quad \text{[T-DEREF]}
$$

### 4.5 赋值规则

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e_1 : \&\rho \text{ uniq } \tau \dashv \Theta_1 \quad \Sigma; \Delta; \Gamma; \Theta_1 \vdash e_2 : \tau \dashv \Theta_2}{\Sigma; \Delta; \Gamma; \Theta \vdash *e_1 = e_2 : () \dashv \Theta_2} \quad \text{[T-ASSIGN]}
$$

### 4.6 let绑定规则

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e_1 : \tau_1 \dashv \Theta_1 \quad \Sigma; \Delta; \Gamma, x:\tau_1; \Theta_1 \vdash e_2 : \tau_2 \dashv \Theta_2}{\Sigma; \Delta; \Gamma; \Theta \vdash \text{let } x = e_1 \text{ in } e_2 : \tau_2 \dashv \Theta_2 \setminus x} \quad \text{[T-LET]}
$$

### 4.7 装箱规则

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e : \tau \dashv \Theta_1}{\Sigma; \Delta; \Gamma; \Theta \vdash \text{box } e : \text{Box}\langle \tau \rangle \dashv \Theta_1} \quad \text{[T-BOX]}
$$

### 4.8 序列规则

$$
\frac{\Sigma; \Delta; \Gamma; \Theta \vdash e_1 : \tau_1 \dashv \Theta_1 \quad \Sigma; \Delta; \Gamma; \Theta_1 \vdash e_2 : \tau_2 \dashv \Theta_2}{\Sigma; \Delta; \Gamma; \Theta \vdash e_1; e_2 : \tau_2 \dashv \Theta_2} \quad \text{[T-SEQ]}
$$

---

## 5. 泛型与特质边界

### 5.1 泛型函数类型

```
fn f<'a, 'b, T, U>(x: &'a T, y: &'b U) -> &'a T
```

形式化表示：

$$
\Sigma(f) = \forall \rho_1, \rho_2, \tau_1, \tau_2. \&\rho_1 \tau_1 \times \&\rho_2 \tau_2 \to \&\rho_1 \tau_1
$$

### 5.2 特质边界

**Copy特质边界**：

$$
\frac{\text{Copy}(\tau)}{\Sigma; \Delta; \Gamma; \Theta \vdash x : \tau \dashv \Theta \quad \text{after move: } x \text{ still valid}} \quad \text{[T-COPY]}
$$

**Drop特质边界**：

$$
\frac{\text{Drop}(\tau)}{\text{at end of scope}(x) \Rightarrow \text{drop}(x)} \quad \text{[DROP-CALL]}
$$

---

## 6. 生命周期约束求解

### 6.1 Outlives约束

**定义**：

$$
\rho_1 : \rho_2 \triangleq \text{lifetime}(\rho_1) \supseteq \text{lifetime}(\rho_2)
$$

**约束收集**：

```
// 示例: fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32
// 返回类型要求 'a 必须比返回值生命周期长

约束收集规则:
- 输入引用: 参数生命周期必须包含函数体
- 输出引用: 返回值生命周期必须被某个输入生命周期包含
```

### 6.2 约束求解算法

**算法：生命周期约束求解**

```
输入: 约束集合 C = {ρ₁: ρ₂, ρ₃: ρ₄, ...}
输出: 满足约束的区域赋值

步骤:
1. 构建约束图 G = (V, E)
   - V = 所有生命周期变量
   - E = {(ρ₁, ρ₂) | ρ₁: ρ₂ ∈ C}  // ρ₁ 必须包含 ρ₂

2. 计算传递闭包

3. 检查循环（除自环外）
   - 若存在 ρ₁: ρ₂ 且 ρ₂: ρ₁ 且 ρ₁ ≠ ρ₂，报错

4. 计算最小解
   - 每个 ρ 赋值为包含所有约束的最小区域
```

---

## 7. 与Rust编译器的对应关系

### 7.1 MIR到Oxide的映射

| MIR构造 | Oxide表达式 | 说明 |
|---------|-------------|------|
| `_1 = _2` | `let _1 = _2 in ...` | 赋值/绑定 |
| `&_1` | `&ρ shrd _1` | 共享借用 |
| `&mut _1` | `&ρ uniq _1` | 可变借用 |
| `*_1` | `*_1` | 解引用 |
| `drop(_1)` | 隐式作用域结束 | 析构 |

### 7.2 NLL与Oxide的对比

| 特性 | NLL (rustc) | Oxide |
|------|-------------|-------|
| 分析粒度 | 基于MIR | 基于核心语言 |
| 约束表示 | 数据流约束 | 类型规则 |
| 求解算法 | 数据流迭代 | 约束求解 |
| 贷款记录 | 活跃借用集 | Θ环境 |

---

## 8. Oxide形式化属性

### 8.1 类型保持定理

**定理（类型保持）**：

若 $\Sigma; \Delta; \Gamma; \Theta \vdash e : \tau \dashv \Theta'$ 且 $e \to e'$，则 $\Sigma; \Delta; \Gamma; \Theta \vdash e' : \tau \dashv \Theta''$。

### 8.2 借用安全性定理

**定理（Oxide借用安全）**：

对于所有良类型程序，执行过程中 $\Theta$ 始终满足：

$$
\forall \text{loan}(\rho_1, \omega_1, \ell), \text{loan}(\rho_2, \omega_2, \ell) \in \Theta.
\omega_1 = \text{shrd} \land \omega_2 = \text{shrd}
$$

（同一位置最多只有一个可变借用）

---

## 9. 完整示例推导

### 9.1 示例：简单借用

```rust
let x = box 5;
let r = &uniq x;
*r
```

**类型推导过程**：

```
步骤 1: x = box 5
  Γ = {x: Box<i32>}
  Θ = ∅

步骤 2: r = &uniq x
  prov(Γ, x) = {'a}  // 新来源
  检查: x 未被借用 ✓
  Γ = {x: Box<i32>, r: &'a uniq Box<i32>}
  Θ = {loan('a, uniq, x)}

步骤 3: *r
  检查: loan('a, uniq, x) ∈ Θ ✓
  结果类型: Box<i32>
```

### 9.2 示例：借用冲突检测

```rust
let mut x = 5;
let r1 = &mut x;
let r2 = &mut x;  // 错误！
```

**类型推导过程**：

```
步骤 1: x = 5
  Γ = {x: i32}
  Θ = ∅

步骤 2: r1 = &mut x
  Γ = {x: i32, r1: &'a uniq i32}
  Θ = {loan('a, uniq, x)}

步骤 3: r2 = &mut x
  检查: x 是否已被借用？
  loan('a, uniq, x) ∈ Θ ✗
  错误: 不能创建可变借用，x 已被可变借用！
```

---

## 参考文献

1. Weiss, A., Patterson, D., Ahmed, A. (2021). Oxide: The Essence of Rust. arXiv:1903.00982.
2. Rust Compiler Team. (2024). Non-Lexical Lifetimes (NLL). Rust Compiler Development Guide.
3. Vytiniotis, D., Peyton Jones, S., Schrijvers, T. (2010). Let should not be generalized. TLDI.

---

*本文档是《Rust所有权与可判定性》项目的学术对齐补充材料*
