> **内容分级**: [专家级]

# 计算的数学函数（Mathematical Functions of Computation）

> **EN**: Mathematical Functions of Computation
> **Summary**: Computable functions as mathematical objects — λ-definability, μ-recursion, partial recursive functions, and their connection to denotational semantics via Scott domains.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 把可计算函数视为数学对象，连接 λ 可定义性、μ-递归、部分递归函数与指称语义中的 Scott 域，并通过 Rust 函数/闭包/迭代器展示理论与实现的对应与张力。
> **前置概念**: [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) · [Computability Theory](02_computability_theory.md)
> **后置概念**: [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md) · [Equivalence of Computational Models](05_equivalence_of_computational_models.md)

---

## 📑 目录

- [计算的数学函数（Mathematical Functions of Computation）](#计算的数学函数mathematical-functions-of-computation)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 函数作为输入-输出对的集合](#11-函数作为输入-输出对的集合)
    - [1.2 λ-可定义函数](#12-λ-可定义函数)
    - [1.3 μ-递归函数](#13-μ-递归函数)
    - [1.4 部分递归函数 = 图灵可计算函数](#14-部分递归函数--图灵可计算函数)
    - [1.5 Scott 域与指称语义](#15-scott-域与指称语义)
  - [二、Rust 中的函数与数学函数](#二rust-中的函数与数学函数)
    - [2.1 闭包作为部分函数](#21-闭包作为部分函数)
    - [2.2 `fn` 的全性 vs 部分性](#22-fn-的全性-vs-部分性)
    - [2.3 `Iterator` 作为余归纳对象](#23-iterator-作为余归纳对象)
  - [三、反命题与边界分析](#三反命题与边界分析)
  - [四、相关概念](#四相关概念)
  - [五、嵌入式测验（Embedded Quiz）](#五嵌入式测验embedded-quiz)
    - [测验 1：λ-可定义函数与可计算性（理解层）](#测验-1λ-可定义函数与可计算性理解层)
    - [测验 2：Rust 函数与全函数（应用层）](#测验-2rust-函数与全函数应用层)
    - [测验 3：Scott 域解决的核心问题（分析层）](#测验-3scott-域解决的核心问题分析层)
  - [六、权威来源索引](#六权威来源索引)
  - [七、🧭 思维导图（Mindmap）](#七-思维导图mindmap)

---

## 一、核心概念

### 1.1 函数作为输入-输出对的集合

在数学中，函数 `f : A → B` 可以等价地看作集合 `A × B` 的一个子集，满足对每个 `a ∈ A` 至多有一个 `b ∈ B` 使得 `(a, b) ∈ f`。

```text
函数 vs 算法：
├── 函数：输入与输出的静态关系
│   └── 例：f(n) = n! 是一个数学函数
├── 算法：计算函数的具体步骤
│   └── 例：阶乘可以用递归、循环或查表实现
└── 同一函数可由多种算法实现
```

> **认知要点**：可计算性理论研究的是「哪些函数存在算法」，而不是「某个具体算法是否正确」。

---

### 1.2 λ-可定义函数

Church 证明了一个函数是 **λ-可定义**的，当且仅当它可以被无类型 λ 演算中的项表达。

```text
Church 定理（直觉表述）：
  一个数论函数是 λ-可定义的  ⇔  它是部分递归的  ⇔  它是图灵可计算的

例子：
  加法：add = λm.λn.λf.λx. m f (n f x)
  乘法：mul = λm.λn.λf. m (n f)
```

Church 编码把数据（数、布尔值、序对）直接编码为高阶函数，从而说明 λ 演算无需原生数据类型即可表达任意可计算函数。

---

### 1.3 μ-递归函数

μ-递归函数通过基本函数和三种规则构造所有可计算函数：

```text
基本函数：
  零函数    : Z(x) = 0
  后继函数  : S(x) = x + 1
  投影函数  : P_i^n(x₁,...,x_n) = x_i

构造规则：
  组合        : h(x) = f(g₁(x), ..., g_k(x))
  原始递归    : f(0, x) = g(x)
                f(n+1, x) = h(n, x, f(n, x))
  无界极小化  : f(x) = μy. g(x, y) = 0
                （若不存在这样的 y，则 f(x) 无定义）
```

原始递归函数对应保证终止的循环；加入 μ 算子后得到**部分递归函数**，对应可能不终止的通用计算。

---

### 1.4 部分递归函数 = 图灵可计算函数

以下三个概念刻画的是同一类函数：

```text
等价链：
  部分递归函数  =  λ-可定义函数  =  图灵可计算函数
```

这正是 Church-Turing 论题的强形式。它说明「可计算函数」这一直观概念具有惊人的稳定性：无论用递归函数、λ 演算还是图灵机形式化，得到的集合都相同。

---

### 1.5 Scott 域与指称语义

无类型 λ 演算中的自应用（如 `x x`）无法直接用普通集合论函数解释，因为不存在集合 `D` 使得 `D ≅ D → D`。Dana Scott 引入了**Scott 域**来解决这一问题。

```text
Scott 域的关键思想：
├── 在域上引入偏序关系 ⊑（信息序）
├── 元素可以是「部分定义」的（⊥ 表示无信息）
├── 只考虑连续函数（continuous functions）
└── 存在域 D 使得 D ≅ [D → D]（连续函数空间）

不动点定理：
  对任意连续函数 f : D → D，存在最小不动点 fix(f) = ⊔{fⁿ(⊥) | n ≥ 0}
  这为递归定义提供了数学基础。
```

> **来源**: [Scott 1982 — Domains for Denotational Semantics](https://www.cs.ox.ac.uk/files/3287/PRG19.pdf) · [Scott & Strachey — Toward a Mathematical Semantics](https://www.cs.ox.ac.uk/files/3232/PRG06.pdf)

---

## 二、Rust 中的函数与数学函数

### 2.1 闭包作为部分函数

Rust 闭包在运行时可能 panic 或无限循环，因此它们对应的是**部分函数**而非全函数：

```rust
fn reciprocal(x: f64) -> f64 {
    if x == 0.0 {
        panic!("division by zero")
    } else {
        1.0 / x
    }
}

fn main() {
    assert_eq!(reciprocal(2.0), 0.5);
}
```

从数学上看，`reciprocal` 在 `0.0` 处无定义（⊥）。Rust 选择 panic 来表示这种无定义，而不是像指称语义那样把结果映射为 ⊥。

### 2.2 `fn` 的全性 vs 部分性

Rust 不保证函数对所有输入都终止或都不 panic。因此 Rust 函数类型 `fn(T) -> U` 更准确地说是**部分函数**的承诺：对合法输入返回 `U`，对非法输入可能 panic 或发散。

```rust
fn diverges() -> ! {
    loop {}
}

fn main() {
    // diverges() 永远不会返回，对应数学函数中的 ⊥
}
```

### 2.3 `Iterator` 作为余归纳对象

Rust 的 `Iterator` trait 可以被看作一个**余归纳（coinductive）**对象：它通过反复调用 `next` 产生潜在无限的元素流。

```rust
fn main() {
    let naturals = std::iter::successors(Some(0), |n| Some(n + 1));
    let first_five: Vec<_> = naturals.take(5).collect();
    assert_eq!(first_five, vec![0, 1, 2, 3, 4]);
}
```

从指称语义看，无限流是最终余代数（final coalgebra）的元素；从操作语义看，它是按需生成下一个元素的过程。

> **来源**: [Rust Reference — Closures](https://doc.rust-lang.org/reference/types/closure.html) · [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)

---

## 三、反命题与边界分析

常见误判：**「每个 Rust 函数都对应一个全数学函数」**。

这是错误的。Rust 函数可能因为以下原因对应部分函数：

1. **panic**：如 `reciprocal(0.0)` 在数学上无定义，Rust 用 panic 表示 ⊥。
2. **发散**：如 `diverges()` 永远不返回，对应无定义。
3. **副作用与 IO**：数学函数是纯映射，Rust 函数可以读写外部状态。
4. **非确定性**：多线程或随机数函数在相同输入下可能产生不同输出。

```text
边界极限：
├── Rust 函数 ≈ 部分数学函数 + 副作用 + 资源管理
├── panic/divergence 对应数学中的 ⊥
├── 闭包捕获环境使函数带有隐式参数
└── 迭代器/流引入余归纳对象，超越有限集合论函数
```

---

## 四、相关概念

- [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) — λ 演算与函数抽象
- [Computability Theory](02_computability_theory.md) — 可计算性理论与部分递归函数
- [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md) — 程序到数学对象的映射
- [Type Semantics](../00_type_theory/06_type_semantics.md) — 类型作为语义分类
- [Equivalence of Computational Models](05_equivalence_of_computational_models.md) — 模型等价与表达力

---

## 五、嵌入式测验（Embedded Quiz）

### 测验 1：λ-可定义函数与可计算性（理解层）

一个数论函数是 λ-可定义的，当且仅当它是：

- A. 原始递归的
- B. 图灵可计算的
- C. 多项式时间可计算的
- D. 全递归的

<details>
<summary>✅ 答案</summary>

**B. 图灵可计算的**。Church 定理说明 λ-可定义函数、部分递归函数和图灵可计算函数三者等价。
</details>

---

### 测验 2：Rust 函数与全函数（应用层）

下面的 Rust 函数 `reciprocal` 对应数学上的什么？

```rust
fn reciprocal(x: f64) -> f64 {
    if x == 0.0 { panic!("zero") } else { 1.0 / x }
}
```

- A. 全函数，对所有 f64 有定义
- B. 部分函数，在 0.0 处无定义
- C. 多值函数，对 0.0 返回多个值
- D. 常量函数

<details>
<summary>✅ 答案</summary>

**B. 部分函数，在 0.0 处无定义**。panic 表示该输入在数学上对应 ⊥。
</details>

---

### 测验 3：Scott 域解决的核心问题（分析层）

Scott 域引入连续函数和偏序的主要目的是什么？

- A. 让无类型 λ 演算可以被普通集合论解释
- B. 让自引用类型（如 `D ≅ D → D`）有一致的数学模型
- C. 提高程序运行速度
- D. 简化类型检查算法

<details>
<summary>✅ 答案</summary>

**B. 让自引用类型（如 `D ≅ D → D`）有一致的数学模型**。普通集合论中不存在这样的集合，Scott 域通过信息序和连续函数解决这一矛盾。
</details>

---

## 六、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Church 1941 — The Calculi of Lambda-Conversion](https://doi.org/10.2307/2267173) | ✅ 一级 | λ 可定义性 |
| [Kleene 1943 — Recursive Predicates and Quantifiers](https://doi.org/10.2307/2268819) | ✅ 一级 | μ-递归函数 |
| [Scott 1982 — Domains for Denotational Semantics](https://www.cs.ox.ac.uk/files/3287/PRG19.pdf) | ✅ 一级 | Scott 域 |
| [Scott & Strachey — Denotational Semantics](https://www.cs.ox.ac.uk/files/3232/PRG06.pdf) | ✅ 一级 | 指称语义奠基 |
| [Rust Reference — Closures](https://doc.rust-lang.org/reference/types/closure.html) | ✅ 一级 | Rust 闭包 |
| [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) | ✅ 一级 | Rust 迭代器 |

---

## 七、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((计算的数学函数))
    函数作为集合
      输入-输出对
      函数 vs 算法
    λ-可定义性
      Church 定理
      Church 编码
    μ-递归函数
      基本函数
      原始递归
      无界极小化
    等价链
      部分递归 = λ-可定义 = 图灵可计算
    Scott 域
      信息序
      连续函数
      最小不动点
    Rust 实例
      闭包作为部分函数
      panic/divergence 对应 ⊥
      Iterator 作为余归纳对象
```
