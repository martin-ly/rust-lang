# λ演算基础 (Lambda Calculus Foundations)

## 目录

- [λ演算基础 (Lambda Calculus Foundations)](#λ演算基础-lambda-calculus-foundations)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 无类型 λ演算 (Untyped Lambda Calculus)](#2-无类型-λ演算-untyped-lambda-calculus)
    - [2.1 语法定义](#21-语法定义)
    - [2.2 变量与绑定](#22-变量与绑定)
    - [2.3 α-等价 (Alpha Equivalence)](#23-α-等价-alpha-equivalence)
  - [3. 替换 (Substitution)](#3-替换-substitution)
    - [3.1 捕获避免的替换](#31-捕获避免的替换)
    - [3.2 替换的数学性质](#32-替换的数学性质)
  - [4. β-归约 (Beta Reduction)](#4-β-归约-beta-reduction)
    - [4.1 基本归约规则](#41-基本归约规则)
    - [4.2 归约策略](#42-归约策略)
      - [4.2.1 调用按值 (Call-by-Value, CBV)](#421-调用按值-call-by-value-cbv)
      - [4.2.2 调用按名 (Call-by-Name, CBN)](#422-调用按名-call-by-name-cbn)
      - [4.2.3 正规序 (Normal Order)](#423-正规序-normal-order)
      - [4.2.4 应用序 (Applicative Order)](#424-应用序-applicative-order)
  - [5. η-转换 (Eta Conversion)](#5-η-转换-eta-conversion)
  - [6. 正规形式与合流性](#6-正规形式与合流性)
    - [6.1 正规形式](#61-正规形式)
    - [6.2 Church-Rosser 定理（合流性）](#62-church-rosser-定理合流性)
    - [6.3 标准化定理](#63-标准化定理)
  - [7. 不可判定性与停机问题](#7-不可判定性与停机问题)
    - [7.1 Y 组合子与递归](#71-y-组合子与递归)
    - [7.2 停机问题](#72-停机问题)
  - [8. 组合子逻辑 (Combinatory Logic)](#8-组合子逻辑-combinatory-logic)
    - [8.1 SKI 组合子](#81-ski-组合子)
    - [8.2 从 λ到组合子](#82-从-λ到组合子)
  - [9. 简单类型 λ演算 (Simply Typed Lambda Calculus)](#9-简单类型-λ演算-simply-typed-lambda-calculus)
    - [9.1 类型语法](#91-类型语法)
    - [9.2 类型判断规则](#92-类型判断规则)
    - [9.3 类型安全定理](#93-类型安全定理)
    - [9.4 与 Rust 的关联](#94-与-rust-的关联)
  - [10. 高级主题](#10-高级主题)
    - [10.1 多态 λ演算 (System F)](#101-多态-λ演算-system-f)
    - [10.2 递归类型](#102-递归类型)
    - [10.3 Curry-Howard 同构](#103-curry-howard-同构)
  - [11. 总结](#11-总结)
  - [参考文献](#参考文献)

## 1. 引言

λ演算（Lambda Calculus）由 Alonzo Church 于 1930 年代提出，是计算理论的基础模型，与图灵机等价。它是函数式编程语言的理论基础，也是理解 Rust 类型系统、闭包和所有权语义的关键。

> **核心地位**: λ演算是所有类型理论的基石。理解 λ演算对于掌握 Rust 的类型系统、生命周期和借用检查器至关重要。

---

## 2. 无类型 λ演算 (Untyped Lambda Calculus)

### 2.1 语法定义

λ演算的语法极其简洁，仅包含三种构造：

```
<expression> ::= <variable>                    -- 变量
               | "λ" <variable> "." <expression>  -- 抽象 (函数定义)
               | <expression> <expression>        -- 应用 (函数调用)
```

**BNF 形式化定义:**

$$
e \in \text{Expr} ::= x \mid \lambda x.e \mid e_1\ e_2
$$

其中：

- $x$ 是变量（来自可数无限集合 $Var$）
- $\lambda x.e$ 是 lambda 抽象（函数定义）
- $e_1\ e_2$ 是函数应用

### 2.2 变量与绑定

```
变量分类:

  λx. λy. x y
  ↑    ↑   ↑
  │    │   └── 自由变量 (在x,y的作用域内)
  │    └────── 绑定变量 y
  └─────────── 绑定变量 x
```

**形式化定义:**

**自由变量 (Free Variables)**:

$$
\begin{aligned}
FV(x) &= \{x\} \\
FV(\lambda x.e) &= FV(e) \setminus \{x\} \\
FV(e_1\ e_2) &= FV(e_1) \cup FV(e_2)
\end{aligned}
$$

**绑定变量 (Bound Variables)**:

$$
\begin{aligned}
BV(x) &= \emptyset \\
BV(\lambda x.e) &= BV(e) \cup \{x\} \\
BV(e_1\ e_2) &= BV(e_1) \cup BV(e_2)
\end{aligned}
$$

**闭项 (Closed Term/Combinator)**: $FV(e) = \emptyset$

### 2.3 α-等价 (Alpha Equivalence)

绑定变量的名称不重要，可以安全重命名：

$$
\lambda x.e \equiv_\alpha \lambda y.e[y/x] \quad \text{(若 } y \notin FV(e)\text{)}
$$

**α-转换规则:**

$$
\frac{y \notin FV(e)}{\lambda x.e \equiv_\alpha \lambda y.e[y/x]} \quad (\alpha)
$$

其中 $e[y/x]$ 表示将 $e$ 中所有自由出现的 $x$ 替换为 $y$。

**示例:**

```
λx.x           ≡α  λy.y           ≡α  λz.z          (恒等函数)
λx.λy.x        ≡α  λy.λx.y        ≡α  λa.λb.a      (K组合子)
λx.λy.x y      ≡α  λa.λb.a b                      (应用函数)
```

**Rust 对应**: α-等价对应于变量名的无关性

```rust
// 以下闭包在语义上等价（α-等价）
let f1 = |x| x;      // λx.x
let f2 = |y| y;      // λy.y  ≡α  λx.x
let f3 = |z| z;      // λz.z  ≡α  λx.x
```

---

## 3. 替换 (Substitution)

### 3.1 捕获避免的替换

替换是 λ演算的核心操作，需要小心处理以避免变量捕获。

**定义**: $e[v/x]$ 表示将 $e$ 中所有自由出现的 $x$ 替换为 $v$

$$
\begin{aligned}
x[v/x] &= v \\
y[v/x] &= y \quad \text{(若 } y \neq x\text{)} \\
(e_1\ e_2)[v/x] &= (e_1[v/x])\ (e_2[v/x]) \\
(\lambda y.e)[v/x] &= \lambda y.(e[v/x]) \quad \text{(若 } y \neq x \text{ 且 } y \notin FV(v)\text{)}
\end{aligned}
$$

**变量捕获问题:**

```
(λx.λy.x y)[y/x]  错误! 若直接替换会得到 λy.y y，捕获了y
```

**解决方案** - 先进行 α-转换：

```
(λx.λy.x y)[y/x]
= (λx.λz.x z)[y/x]    -- α-转换: y → z
= λz.y z               -- 安全替换
```

### 3.2 替换的数学性质

**引理 3.1** (替换与自由变量):
若 $y \notin FV(v)$，则 $y \in FV(e[v/x])$ 当且仅当 $(y \in FV(e) \text{ 且 } y \neq x)$ 或 $(y \in FV(v) \text{ 且 } x \in FV(e))$

**引理 3.2** (替换的交换):
若 $x \neq y$ 且 $x \notin FV(w)$，则 $e[v/x][w/y] = e[w/y][v[w/y]/x]$

---

## 4. β-归约 (Beta Reduction)

### 4.1 基本归约规则

β-归约是 λ演算的计算规则，描述函数应用的求值过程。

**β-归约规则:**

$$
(\lambda x.e)\ v \rightarrow_\beta e[v/x]
$$

**形式化定义:**

$$
\frac{}{(\lambda x.e)\ v \rightarrow_\beta e[v/x]} \quad (\beta)
$$

**示例:**

```
(λx.x) y          →β  y
(λx.λy.x) a b     →β  (λy.a) b  →β  a
(λf.λx.f (f x)) g →β  λx.g (g x)
```

**Rust 对应**: β-归约对应于函数调用/闭包应用

```rust
// (λx.x+1) 5 → 6
let f = |x| x + 1;
let result = f(5);  // β-归约: 5+1 = 6

// (λf.λx.f(f x)) (|y| y*2)
// → λx.(|y| y*2)((|y| y*2) x)
// → λx.(x*2)*2 = λx.x*4
```

### 4.2 归约策略

λ演算支持多种求值策略：

#### 4.2.1 调用按值 (Call-by-Value, CBV)

**规则**: 先求值参数，再应用函数

$$
\frac{e_1 \rightarrow e_1'}{e_1\ e_2 \rightarrow e_1'\ e_2} \quad
\frac{e_2 \rightarrow e_2'}{v_1\ e_2 \rightarrow v_1\ e_2'} \quad
\frac{}{(\lambda x.e)\ v \rightarrow e[v/x]}
$$

**特性**:

- 参数仅求值一次
- 是大多数编程语言（包括 Rust）采用的策略
- 保证终止性（若存在）

**Rust 示例**:

```rust
let x = { println!("eval"); 5 };  // 先求值
let f = |a| a * 2;
f(x);  // x 已求值为 5，然后应用
```

#### 4.2.2 调用按名 (Call-by-Name, CBN)

**规则**: 直接替换，不求值参数

$$
\frac{e_1 \rightarrow e_1'}{e_1\ e_2 \rightarrow e_1'\ e_2} \quad
\frac{}{(\lambda x.e)\ e_2 \rightarrow e[e_2/x]}
$$

**特性**:

- 延迟求值（Lazy Evaluation）
- 参数可能被多次求值
- Haskell 采用的策略

#### 4.2.3 正规序 (Normal Order)

**规则**: 最左最外优先归约

**特性**:

- 若归约存在，正规序必能找到
- 产生正规形式（若存在）

#### 4.2.4 应用序 (Applicative Order)

**规则**: 最左最内优先归约

**特性**:

- 类似调用按值
- 可能不终止，即使正规序会终止

**对比示例**:

```
表达式: (λx.y) ((λx.x x) (λx.x x))

正规序 (最外优先):
  (λx.y) ((λx.x x) (λx.x x)) → y     (终止)

应用序 (最内优先):
  (λx.y) ((λx.x x) (λx.x x))
  → (λx.y) ((λx.x x) (λx.x x))       (无限循环)
```

---

## 5. η-转换 (Eta Conversion)

η-转换表达了外延等价性：若两个函数对所有输入产生相同输出，则它们等价。

**η-展开**:

$$
e \rightarrow_\eta \lambda x.(e\ x) \quad \text{(若 } x \notin FV(e)\text{)}
$$

**η-归约**:

$$
\lambda x.(e\ x) \rightarrow_\eta e \quad \text{(若 } x \notin FV(e)\text{)}
$$

**直观**: 一个函数 $f$ 与 $\lambda x.f(x)$ 等价

**Rust 对应**: η-归约对应于函数/闭包的外延等价

```rust
let f = |x| x + 1;
let g = |y| f(y);  // η-展开形式
// f 和 g 外延等价
```

---

## 6. 正规形式与合流性

### 6.1 正规形式

**定义**: 表达式 $e$ 是：

- **β-正规形式**: 不包含任何 β-可归约子项（$(\lambda x.e_1)\ e_2$ 形式）
- **正规形式**: 不包含任何可归约子项（β 或 η）

**示例:**

```
λx.x                    -- 正规形式
λx.λy.x y               -- 正规形式
(λx.x) y                -- 非正规形式（可β归约）
```

### 6.2 Church-Rosser 定理（合流性）

**定理 6.1** (Church-Rosser / 合流性):

若 $e \rightarrow^* e_1$ 且 $e \rightarrow^* e_2$，则存在 $e'$ 使得 $e_1 \rightarrow^* e'$ 且 $e_2 \rightarrow^* e'$。

```
图示:
      e
     / \
    ↓   ↓
   e₁   e₂
    \   /
     ↓ ↓
      e'
```

**推论 6.2**: 若 $e$ 有正规形式，则该形式唯一（模 α-等价）。

### 6.3 标准化定理

**定理 6.3** (Standardization / 标准化):

若 $e$ 有正规形式，则正规序归约必能找到它。

**意义**: 提供了实现解释器的理论基础。

---

## 7. 不可判定性与停机问题

### 7.1 Y 组合子与递归

λ演算本身不支持显式递归，但可以通过 Y 组合子实现：

**Y 组合子定义**:

$$
Y = \lambda f.(\lambda x.f\ (x\ x))\ (\lambda x.f\ (x\ x))
$$

**性质**: $Y\ f \rightarrow_\beta f\ (Y\ f)$

**示例** - 阶乘函数:

```
FACT = Y (λf.λn.IF (ISZERO n) 1 (MULT n (f (PRED n))))
```

**Rust 对应**: Y组合子对应于递归函数定义

```rust
// 直接递归
fn fact(n: u64) -> u64 {
    if n == 0 { 1 } else { n * fact(n - 1) }
}

// 使用高阶函数的Y组合子风格
let fix = |f: &dyn Fn(&dyn Fn(u64) -> u64, u64) -> u64| {
    move |n| f(&|m| fix(f)(m), n)
};
```

### 7.2 停机问题

**定理 7.1** (不可判定性):

不存在算法能判定任意 λ项是否有正规形式。

**证明概要**: 通过对角线论证，与图灵机等价。

---

## 8. 组合子逻辑 (Combinatory Logic)

### 8.1 SKI 组合子

λ演算可简化为三个基本组合子：

| 组合子 | λ定义 | 作用 |
|--------|-------|------|
| **S** | $\lambda f.\lambda g.\lambda x.f\ x\ (g\ x)$ | 应用组合 |
| **K** | $\lambda x.\lambda y.x$ | 常量选择 |
| **I** | $\lambda x.x$ | 恒等函数 |

**性质**: 任何 λ项都可以用 S、K、I 表示。

**转换规则**:

- $I\ x \rightarrow x$
- $K\ x\ y \rightarrow x$
- $S\ f\ g\ x \rightarrow f\ x\ (g\ x)$

### 8.2 从 λ到组合子

**消除规则**:

$$
\begin{aligned}
T[x] &= x \\
T[\lambda x.e] &= [x]e \\
T[e_1\ e_2] &= T[e_1]\ T[e_2] \\
[x]x &= I \\
[x]e &= K\ e \quad \text{(若 } x \notin FV(e)\text{)} \\
[x](e_1\ e_2) &= S\ ([x]e_1)\ ([x]e_2)
\end{aligned}
$$

---

## 9. 简单类型 λ演算 (Simply Typed Lambda Calculus)

### 9.1 类型语法

在 λ演算基础上添加类型系统：

$$
\tau ::= B \mid \tau_1 \rightarrow \tau_2
$$

其中：

- $B$ 是基础类型（如 Int, Bool）
- $\tau_1 \rightarrow \tau_2$ 是函数类型

### 9.2 类型判断规则

**类型上下文** $\Gamma$ 是变量到类型的映射：$\Gamma = \{x_1:\tau_1, ..., x_n:\tau_n\}$

**类型判断**: $\Gamma \vdash e : \tau$ 表示在上下文 $\Gamma$ 中，$e$ 具有类型 $\tau$

$$
\begin{aligned}
&\frac{x:\tau \in \Gamma}{\Gamma \vdash x : \tau} \quad (T\text{-}Var) \\[10pt]
&\frac{\Gamma, x:\tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2} \quad (T\text{-}Abs) \\[10pt]
&\frac{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1\ e_2 : \tau_2} \quad (T\text{-}App)
\end{aligned}
$$

### 9.3 类型安全定理

**定理 9.1** (保持性 / Preservation / Subject Reduction):

若 $\Gamma \vdash e : \tau$ 且 $e \rightarrow e'$，则 $\Gamma \vdash e' : \tau$。

**定理 9.2** (进展性 / Progress):

若 $\vdash e : \tau$ 且 $e$ 是闭项，则要么 $e$ 是值，要么存在 $e'$ 使得 $e \rightarrow e'$。

**定理 9.3** (类型安全):

保持性 + 进展性 = 类型安全

**意义**: 良好类型的程序不会"卡住"（不会到达非值且无法归约的状态）。

### 9.4 与 Rust 的关联

**Rust 类型系统可以看作 λ演算的扩展**:

| λ演算概念 | Rust对应 |
|-----------|----------|
| 变量 $x$ | 变量绑定 |
| 抽象 $\lambda x.e$ | 闭包 `|x| e` |
| 应用 $e_1\ e_2$ | 函数调用 `f(x)` |
| 函数类型 $\tau_1 \rightarrow \tau_2$ | `Fn(T1) -> T2` |
| 类型环境 $\Gamma$ | 作用域中的类型绑定 |
| 类型判断 $\Gamma \vdash e : \tau$ | 类型检查 |

---

## 10. 高级主题

### 10.1 多态 λ演算 (System F)

**类型抽象**:

$$
e ::= ... \mid \Lambda \alpha.e \mid e\ [\tau]
$$

**类型规则**:

$$
\frac{\Gamma \vdash e : \forall \alpha.\tau}{\Gamma \vdash e\ [\sigma] : \tau[\sigma/\alpha]} \quad (T\text{-}TypeApp)
$$

**Rust 对应**: System F 对应 Rust 的泛型

```rust
// Λα.λx.x : ∀α.α → α
fn id<T>(x: T) -> T { x }

// 类型应用: id[i32] 5
id::<i32>(5);
```

### 10.2 递归类型

**μ-类型**:

$$
\tau ::= ... \mid \mu \alpha.\tau
$$

**展开规则**: $\mu \alpha.\tau \equiv \tau[(\mu \alpha.\tau)/\alpha]$

**Rust 对应**: 递归类型对应 Rust 的递归数据结构

```rust
// μα.1 + (Int × α)  -- 链表类型
enum List {
    Nil,                    -- 1 (单位类型)
    Cons(i32, Box<List>),   -- Int × α
}
```

### 10.3 Curry-Howard 同构

**对应关系**:

| 逻辑 | 类型 | 证明 | 程序 |
|------|------|------|------|
| $A \rightarrow B$ | $A \rightarrow B$ | 蕴含引入/消去 | 抽象/应用 |
| $A \land B$ | $A \times B$ | 合取 | 元组 |
| $A \lor B$ | $A + B$ | 析取 | 枚举/和类型 |
| $\forall x.A$ | $\forall \alpha.\tau$ | 全称量词 | 多态函数 |
| $\exists x.A$ | $\exists \alpha.\tau$ | 存在量词 | 抽象数据类型 |
| 证明 | - | 类型推导 | 类型检查 |

**意义**: 类型是命题，程序是证明。

---

## 11. 总结

λ演算是理解现代编程语言类型系统的理论基础：

| 概念 | λ演算 | Rust对应 |
|------|-------|----------|
| 变量 | $x$ | 变量绑定 |
| 抽象 | $\lambda x.e$ | 闭包/函数 |
| 应用 | $e_1\ e_2$ | 函数调用 |
| α-等价 | 变量重命名 | 变量名无关 |
| β-归约 | 函数应用 | 求值 |
| η-转换 | 外延等价 | 函数等价 |
| 类型安全 | 保持性+进展性 | 编译期类型检查 |
| 多态 | System F | 泛型 |
| 递归 | μ-类型 | 递归类型/Traits |

掌握 λ演算有助于深入理解 Rust 的类型系统、借用检查器和所有权模型的理论基础。

---

## 参考文献

1. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
2. Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
3. Church, A. (1936). "An unsolvable problem of elementary number theory"
4. Curry, H. B., & Feys, R. (1958). *Combinatory Logic*
5. Girard, J. Y. (1972). "Interprétation fonctionnelle et élimination des coupures"

---

**难度级别**: 🔴 高级 (理论基础)
**前置知识**: 离散数学、基本逻辑
**后续学习**: 类型理论基础、操作语义
