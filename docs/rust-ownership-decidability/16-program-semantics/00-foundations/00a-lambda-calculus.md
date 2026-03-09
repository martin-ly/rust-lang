# λ演算基础 (Lambda Calculus Foundations)

> **难度**: 🔴 高级
> **预计阅读时间**: 3-4 小时
> **前置知识**: 基础离散数学

---

## 1. 引言

λ演算（Lambda Calculus）由 Alonzo Church 于 1930 年代提出，是计算理论的基础模型。
它与图灵机等价，但更加简洁，是函数式编程语言（包括 Rust 的闭包和泛型系统）的理论基础。

---

## 2. 无类型 λ演算 (Untyped Lambda Calculus)

### 2.1 语法定义

**定义 2.1** (λ项的语法)

```
M, N ::= x         (变量)
       | λx.M     (抽象 - 函数定义)
       | M N      (应用 - 函数调用)
```

**Rust 对应**:

```rust
// 变量
let x = 42;

// 抽象 (λx.M 对应 |x| M)
let f = |x| x + 1;  // λx.x+1

// 应用 (M N 对应 f(x))
let result = f(5);  // (λx.x+1) 5
```

### 2.2 变量与绑定

**定义 2.2** (自由变量与绑定变量)

在 λx.M 中：

- `x` 是**绑定变量**（bound variable）
- M 中除 x 外的变量是**自由变量**（free variables）

形式化定义：

```
FV(x) = {x}
FV(λx.M) = FV(M) \ {x}
FV(M N) = FV(M) ∪ FV(N)
```

**Rust 示例**:

```rust
fn example() {
    let y = 10;  // y 是自由变量（相对于内部闭包）
    let f = |x| {  // x 是绑定变量
        x + y     // y 从外部环境捕获
    };
}
```

### 2.3 α-等价 (Alpha Equivalence)

**定义 2.3** (α-转换)

绑定变量可以安全地重命名：

```
λx.M ≡α λy.M[y/x]   (y ∉ FV(M))
```

**示例**:

```
λx.x+1 ≡α λy.y+1 ≡α λz.z+1
```

**Rust 对应**:

```rust
// 以下三个闭包在语义上等价
let f1 = |x| x + 1;
let f2 = |y| y + 1;
let f3 = |z| z + 1;
```

### 2.4 β-归约 (Beta Reduction)

**定义 2.4** (β-归约)

函数应用的基本计算规则：

```
(λx.M) N →β M[N/x]
```

读作：将 M 中所有 x 替换为 N。

**示例**:

```
(λx.x+1) 5 →β 5+1 → 6

(λx.λy.x+y) 3 →β λy.3+y
```

**Rust 对应**:

```rust
// (λx.x+1) 5
let f = |x| x + 1;
let result = f(5);  // → 6

// (λx.λy.x+y) 3
let make_adder = |x: i32| {
    move |y: i32| x + y  // λy.x+y，x 被捕获
};
let add3 = make_adder(3);  // λy.3+y
```

### 2.5 求值策略

**定义 2.5** (求值策略)

| 策略 | 名称 | 规则 |
|------|------|------|
| CBV | Call-by-Value | 先求值参数，再代入 |
| CBN | Call-by-Name | 直接代入，按需求值 |
| CBV | Call-by-Need | 代入并记忆结果 (惰性求值) |

**Rust 采用 CBV**:

```rust
// CBV: 先求值 2+3=5，再传入
let f = |x| x * 2;
f({ println!("evaluated!"); 2 + 3 });  // 立即打印 "evaluated!"

// 对比 CBN (Haskell 风格):
// f({ println!("evaluated!"); 2 + 3 })
// 只有使用 x 时才求值
```

---

## 3. 简单类型 λ演算 (Simply Typed Lambda Calculus)

### 3.1 类型语法

**定义 3.1** (类型)

```
τ ::= Bool | Int | ...    (基本类型)
    | τ₁ → τ₂            (函数类型)
```

**Rust 对应**:

```rust
// τ₁ → τ₂ 对应 fn(T1) -> T2 或 Fn(T1) -> T2
fn example(x: i32) -> bool { x > 0 }  // Int → Bool

// 高阶函数: (Int → Bool) → [Int] → [Int]
fn filter<F>(pred: F, list: Vec<i32>) -> Vec<i32>
where
    F: Fn(i32) -> bool
{ ... }
```

### 3.2 类型规则

**定义 3.2** (类型判断)

Γ ⊢ M : τ 表示"在上下文 Γ 中，项 M 具有类型 τ"。

```
(T-Var)  Γ, x:τ ⊢ x : τ

(T-Abs)  Γ, x:τ₁ ⊢ M : τ₂
         -------------------
         Γ ⊢ λx.M : τ₁ → τ₂

(T-App)  Γ ⊢ M : τ₁ → τ₂    Γ ⊢ N : τ₁
         ------------------------------
         Γ ⊢ M N : τ₂
```

**Rust 类型检查示例**:

```rust
// T-Abs: λx:Int.x+1 : Int → Int
let f = |x: i32| x + 1;  // 类型: impl Fn(i32) -> i32

// T-App: f 5 : Int
let result = f(5);  // 类型: i32

// 类型错误示例 (会被编译器拒绝):
// let bad = f(true);  // 错误: expected i32, found bool
```

### 3.3 Curry-Howard 对应

**定理 3.3** (Curry-Howard 同构)

类型与逻辑命题之间存在对应关系：

| 逻辑 | 类型 |
|------|------|
| 命题 A → B | 函数类型 A → B |
| 证明 | 程序/项 |
| 合取 A ∧ B | 积类型 (A, B) |
| 析取 A ∨ B | 和类型 Either<A, B> |
| 假 | 空类型 ! |

**Rust 对应**:

```rust
// A → B: 函数即蕴含的证明
fn modus_ponens<A, B>(f: impl Fn(A) -> B, a: A) -> B {
    f(a)  // 应用函数 = 演绎推理
}

// A ∧ B: 元组即合取
struct And<A, B>(A, B);

// A ∨ B: 枚举即析取
enum Or<A, B> {
    Left(A),
    Right(B),
}
```

---

## 4. 归约与范式

### 4.1 归约关系

**定义 4.1** (归约关系 →)

```
(λx.M) N → M[N/x]                    (β)
M → M'                               (cong-1)
-------------
M N → M' N

N → N'                               (cong-2)
-------------
M N → M N'

M → M'                               (cong-λ)
---------------
λx.M → λx.M'
```

### 4.2 Church-Rosser 定理

**定理 4.2** (Church-Rosser / 合流性)

如果 M →*M₁ 且 M →* M₂，则存在 N 使得 M₁ →*N 且 M₂ →* N。

```
    M
   / \
  /   \
 M₁   M₂
  \   /
   \ /
    N
```

**意义**: 无论选择何种归约顺序，最终结果都相同（如果存在）。

### 4.3 范式

**定义 4.3** (β-范式)

如果不能继续 β-归约，则称项为 **β-范式**。

**示例**:

```
(λx.x) y → y        (y 是范式)
(λx.x x)(λx.x x)    (无限归约，无范式)
```

---

## 5. 与 Rust 的深层联系

### 5.1 闭包即 λ抽象

```rust
// Rust 闭包 = λ演算中的抽象 + 环境
let env = 10;
let closure = |x| x + env;  // λx.x+env，其中 env 来自环境

// 等价于 λ演算中的: λx.x+y，其中 y=10
```

### 5.2 泛型即多态

```rust
// 多态函数: ∀T. T → T
fn identity<T>(x: T) -> T { x }

// 对应 λ演算: ΛT.λx:T.x (System F)
```

### 5.3 所有权即线性类型

λ演算的线性版本（Linear Logic）与 Rust 的所有权系统直接对应：

```rust
// 线性使用: 值只能使用一次
let x = vec![1, 2, 3];
let y = x;  // x 被移动，不能再使用
// drop(x);  // 错误: value used here after move
```

---

## 6. 形式化总结

### 6.1 核心概念速查

| 概念 | λ演算 | Rust |
|------|-------|------|
| 变量 | x | x |
| 抽象 | λx.M | \|x\| M |
| 应用 | M N | M(N) |
| 类型 | τ₁ → τ₂ | Fn(T1) -> T2 |
| 归约 | β | 函数调用 |
| 绑定 | λx | \|x\| |
| 自由变量 | FV(M) | 捕获变量 |

### 6.2 推荐阅读

1. *Types and Programming Languages* - Benjamin C. Pierce (TAPL)
2. *Semantics Engineering with PLT Redex* - Felleisen et al.
3. *Category Theory for Programmers* - Bartosz Milewski

---

**文档大小**: ~25 KB
**状态**: ✅ 完整形式化定义
**最后更新**: 2026-03-08
