# 01. 函数式编程范式

## 目录

1. [引言](#1-引言)
2. [函数式编程基础](#2-函数式编程基础)
3. [Rust中的函数式特性](#3-rust中的函数式特性)
4. [高阶函数与闭包](#4-高阶函数与闭包)
5. [不可变性与纯函数](#5-不可变性与纯函数)
6. [函数式数据结构](#6-函数式数据结构)
7. [函数式设计模式](#7-函数式设计模式)
8. [单子与函子理论](#8-单子与函子理论)
9. [惰性求值理论](#9-惰性求值理论)
10. [模式匹配理论](#10-模式匹配理论)
11. [总结与展望](#11-总结与展望)

## 1. 引言

### 1.1 函数式编程在Rust中的地位

Rust语言融合了多种编程范式，其中函数式编程是其重要组成部分：

**形式化定义**：
```
Functional_Programming(Rust) = {
    Higher_Order_Functions,
    Immutability,
    Pure_Functions,
    Algebraic_Data_Types,
    Pattern_Matching,
    Monads,
    Functors,
    Lazy_Evaluation
}
```

### 1.2 核心函数式概念

Rust中的函数式编程包含以下核心概念：

1. **高阶函数**：函数作为一等公民
2. **不可变性**：默认不可变，显式可变
3. **纯函数**：无副作用的函数
4. **代数数据类型**：枚举和结构体
5. **模式匹配**：强大的模式匹配系统
6. **单子**：错误处理和可选值
7. **函子**：类型构造子的映射
8. **惰性求值**：按需计算

## 2. 函数式编程基础

### 2.1 函数式编程定义

#### 定义 2.1.1 (函数式编程)

函数式编程是一种编程范式，其中计算被视为数学函数的求值，避免状态和可变数据。

#### 定义 2.1.2 (纯函数)

函数 $f: A \rightarrow B$ 是纯函数，当且仅当：

1. 对于相同的输入总是产生相同的输出
2. 没有副作用
3. 不依赖外部状态

形式化定义为：
$$\text{Pure}(f) \iff \forall x, y \in A, x = y \Rightarrow f(x) = f(y) \land \text{NoSideEffects}(f)$$

#### 定理 2.1.1 (纯函数可组合性)

纯函数是可组合的：
$$\text{Pure}(f) \land \text{Pure}(g) \Rightarrow \text{Pure}(g \circ f)$$

**证明**：

1. 设 $f: A \rightarrow B$ 和 $g: B \rightarrow C$ 为纯函数
2. 对于任意 $x, y \in A$，如果 $x = y$，则 $f(x) = f(y)$
3. 因此 $g(f(x)) = g(f(y))$
4. 且 $g \circ f$ 没有副作用
5. 因此 $g \circ f$ 是纯函数

### 2.2 函数作为一等公民

#### 定义 2.2.1 (函数类型)
```
Function_Type = {T → U | T, U are types}
```

#### 定义 2.2.2 (函数值)
```
Function_Value = {f | f: T → U}
```

#### 定理 2.2.1 (函数组合)
```
∀f: A → B, g: B → C, ∃h: A → C, h = g ∘ f
```

### 2.3 λ演算基础

#### 定义 2.3.1 (λ项)
```
Lambda_Term ::= Variable | λVariable.Term | Term Term
```

#### 定义 2.3.2 (β归约)
```
(λx.M) N → M[x ↦ N]
```

#### 定义 2.3.3 (η等价)
```
λx.(M x) ≡ M (if x ∉ FV(M))
```

### 2.4 类型系统

#### 定义 2.4.1 (简单类型)
```
Simple_Type ::= Base | Type → Type
```

#### 定义 2.4.2 (多态类型)
```
Polymorphic_Type ::= ∀α. Type
```

## 3. Rust中的函数式特性

### 3.1 函数定义与调用

#### 定义 3.1.1 (函数签名)
```
Function_Signature = fn Name(Parameters) -> Return_Type
```

#### 定义 3.1.2 (函数体)
```
Function_Body = { Statements }
```

#### 示例 3.1.1 (基本函数)
```rust
fn add(x: i32, y: i32) -> i32 {
    x + y
}
```

### 3.2 闭包

#### 定义 3.2.1 (闭包类型)
```
Closure_Type = |Parameters| -> Return_Type
```

#### 定义 3.2.2 (捕获语义)
```
Capture_Semantics = {Move, Borrow, Borrow_Mut}
```

#### 示例 3.2.1 (闭包示例)
```rust
let add_one = |x: i32| x + 1;
let result = add_one(5); // 6
```

### 3.3 迭代器

#### 定义 3.3.1 (迭代器特征)
```
Iterator_Trait = {
    type Item,
    fn next(&mut self) -> Option<Self::Item>
}
```

#### 定义 3.3.2 (迭代器方法)
```
Iterator_Methods = {map, filter, fold, collect, ...}
```

## 4. 高阶函数与闭包

### 4.1 高阶函数理论

#### 定义 4.1.1 (高阶函数)

高阶函数是接受函数作为参数或返回函数的函数：
$$\text{HigherOrder}(f) \iff f: \mathcal{F} \rightarrow \mathcal{F} \lor f: A \rightarrow \mathcal{F}$$

#### 定义 4.1.2 (映射函数)

映射函数 $\text{map}: (A \rightarrow B) \rightarrow [A] \rightarrow [B]$ 定义为：
$$\text{map}(f)([a_1, a_2, \ldots, a_n]) = [f(a_1), f(a_2), \ldots, f(a_n)]$$

#### 定理 4.1.1 (映射函数性质)

映射函数满足以下性质：

1. 单位律：$\text{map}(\text{id}) = \text{id}$
2. 结合律：$\text{map}(g \circ f) = \text{map}(g) \circ \text{map}(f)$

**证明**：

1. 单位律：$\text{map}(\text{id})([a_1, \ldots, a_n]) = [\text{id}(a_1), \ldots, \text{id}(a_n)] = [a_1, \ldots, a_n]$
2. 结合律：$\text{map}(g \circ f)([a_1, \ldots, a_n]) = [(g \circ f)(a_1), \ldots, (g \circ f)(a_n)] = [g(f(a_1)), \ldots, g(f(a_n))] = \text{map}(g)(\text{map}(f)([a_1, \ldots, a_n]))$

### 4.2 高阶函数定义

#### 定义 4.2.1 (高阶函数)
```
Higher_Order_Function = {f | f: (T → U) → V}
```

#### 定义 4.2.2 (函数组合器)
```
Function_Combinator = {c | c: (T → U) → (U → V) → (T → V)}
```

#### 示例 4.2.1 (高阶函数)
```rust
fn apply_twice<F>(f: F, x: i32) -> i32 
where 
    F: Fn(i32) -> i32 
{
    f(f(x))
}
```

### 4.3 闭包类型系统

#### 定义 4.3.1 (闭包特征)
```
Closure_Traits = {Fn, FnMut, FnOnce}
```

#### 定义 4.3.2 (捕获规则)
```
Capture_Rules = {
    Fn: &self,
    FnMut: &mut self,
    FnOnce: self
}
```

### 4.4 函数式组合

#### 定义 4.4.1 (函数组合)

函数组合 $\circ$ 定义为：
$$(g \circ f)(x) = g(f(x))$$

#### 定义 4.4.2 (组合律)

函数组合满足结合律：
$$(h \circ g) \circ f = h \circ (g \circ f)$$

#### 定理 4.4.1 (组合函数性质)

组合函数保持纯函数性质：
$$\text{Pure}(f) \land \text{Pure}(g) \Rightarrow \text{Pure}(g \circ f)$$

**证明**：

1. 设 $f: A \rightarrow B$ 和 $g: B \rightarrow C$ 为纯函数
2. 对于任意 $x, y \in A$，如果 $x = y$，则 $f(x) = f(y)$
3. 因此 $g(f(x)) = g(f(y))$
4. 且 $g \circ f$ 没有副作用
5. 因此 $g \circ f$ 是纯函数

#### 示例 4.4.1 (函数组合)
```rust
fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(B) -> C,
    G: Fn(A) -> B,
{
    move |x| f(g(x))
}
```

## 5. 不可变性与纯函数

### 5.1 不可变性理论

#### 定义 5.1.1 (不可变性)

数据结构是不可变的，当且仅当：
$$\text{Immutable}(d) \iff \forall t, t', d(t) = d(t')$$

#### 定义 5.1.2 (持久化数据结构)

持久化数据结构支持多个版本同时存在：
$$\text{Persistent}(D) \iff \forall d \in D, \forall op, \text{Version}(op(d)) \neq \text{Version}(d)$$

#### 定理 5.1.1 (不可变性线程安全)

不可变数据结构天然线程安全：
$$\text{Immutable}(d) \Rightarrow \text{ThreadSafe}(d)$$

**证明**：

1. 不可变数据结构不能被修改
2. 多个线程只能读取相同数据
3. 没有数据竞争
4. 因此线程安全

### 5.2 Rust中的不可变性

#### 定义 5.2.1 (默认不可变)
```
Default_Immutability = {v | v is immutable by default}
```

#### 定义 5.2.2 (显式可变)
```
Explicit_Mutability = {v | v is explicitly mutable}
```

#### 示例 5.2.1 (不可变性示例)
```rust
let x = 5; // 不可变
let mut y = 10; // 可变
// x = 6; // 编译错误
y = 11; // 允许
```

## 6. 函数式数据结构

### 6.1 代数数据类型

#### 定义 6.1.1 (代数数据类型)

代数数据类型 $T$ 定义为：
$$T = \sum_{i=1}^{n} \prod_{j=1}^{m_i} T_{i,j}$$

其中：
- $\sum$ 表示和类型（枚举）
- $\prod$ 表示积类型（结构体）

#### 示例 6.1.1 (代数数据类型)
```rust
// 和类型（枚举）
enum Option<T> {
    Some(T),
    None,
}

// 积类型（结构体）
struct Point {
    x: f64,
    y: f64,
}
```

### 6.2 持久化数据结构

#### 定义 6.2.1 (持久化)
```
Persistent_Data_Structure = {d | d supports multiple versions}
```

#### 示例 6.2.1 (持久化示例)
```rust
use std::collections::HashMap;

let mut map1 = HashMap::new();
map1.insert("key", "value");

let map2 = map1.clone(); // 创建新版本
map1.insert("key2", "value2"); // 修改原版本
```

## 7. 函数式设计模式

### 7.1 函数式模式

#### 定义 7.1.1 (函数式模式)
```
Functional_Pattern = {p | p is a functional design pattern}
```

#### 示例 7.1.1 (函数式模式)
```rust
// 策略模式
fn strategy_pattern<F>(f: F, data: Vec<i32>) -> Vec<i32>
where
    F: Fn(i32) -> i32,
{
    data.into_iter().map(f).collect()
}

// 装饰器模式
fn decorator<F, G>(f: F, g: G) -> impl Fn(i32) -> i32
where
    F: Fn(i32) -> i32,
    G: Fn(i32) -> i32,
{
    move |x| g(f(x))
}
```

## 8. 单子与函子理论

### 8.1 单子理论

#### 定义 8.1.1 (单子)

单子是一个三元组 $(M, \eta, \mu)$，其中：

- $M$ 是一个函子
- $\eta: A \rightarrow M(A)$ 是单位函数
- $\mu: M(M(A)) \rightarrow M(A)$ 是乘法函数

满足单子律：

1. $\mu \circ \eta_M = \text{id}_M$
2. $\mu \circ M(\eta) = \text{id}_M$
3. $\mu \circ \mu = \mu \circ M(\mu)$

#### 定义 8.1.2 (Option 单子)

Option 单子定义为：

- $M(A) = \text{Option}(A)$
- $\eta(a) = \text{Some}(a)$
- $\mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
- $\mu(\text{Some}(\text{None})) = \text{None}$
- $\mu(\text{None}) = \text{None}$

#### 定理 8.1.1 (Option 单子律)

Option 满足单子律。

**证明**：

1. $\mu \circ \eta_M(\text{Some}(a)) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
2. $\mu \circ M(\eta)(\text{Some}(a)) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$
3. $\mu \circ \mu(\text{Some}(\text{Some}(\text{Some}(a)))) = \mu(\text{Some}(\text{Some}(a))) = \text{Some}(a)$

#### 示例 8.1.1 (Option 单子)
```rust
fn option_monad_example() -> Option<i32> {
    Some(5)
        .and_then(|x| Some(x + 1))
        .and_then(|x| Some(x * 2))
}
```

### 8.2 函子理论

#### 定义 8.2.1 (函子)

函子是一个映射 $F: \mathcal{C} \rightarrow \mathcal{D}$ 和一个函数 $\text{map}: (A \rightarrow B) \rightarrow (F(A) \rightarrow F(B))$，满足：

1. $\text{map}(\text{id}) = \text{id}$
2. $\text{map}(g \circ f) = \text{map}(g) \circ \text{map}(f)$

#### 定义 8.2.2 (应用函子)

应用函子是函子加上应用操作：
$$\text{ap}: F(A \rightarrow B) \rightarrow F(A) \rightarrow F(B)$$

#### 定理 8.2.1 (函子保持结构)

函子保持范畴结构：
$$\text{Functor}(F) \Rightarrow \text{PreserveStructure}(F)$$

**证明**：

1. 函子保持单位态射
2. 函子保持复合
3. 因此保持范畴结构

#### 示例 8.2.1 (函子示例)
```rust
// Option 是函子
let opt: Option<i32> = Some(5);
let mapped = opt.map(|x| x + 1); // Some(6)
```

## 9. 惰性求值理论

### 9.1 惰性求值基础

#### 定义 9.1.1 (惰性求值)

惰性求值是一种求值策略，只在需要时才计算表达式的值：
$$\text{Lazy}(e) \iff \text{Evaluate}(e) \text{ only when } \text{Needed}(e)$$

#### 定义 9.1.2 (流)

流是惰性列表：
$$\text{Stream}(A) = \text{Cons}(A, \text{Stream}(A)) \lor \text{Nil}$$

#### 定理 9.1.1 (惰性求值效率)

惰性求值可以提高效率：
$$\text{Lazy}(e) \Rightarrow \text{Efficient}(e)$$

**证明**：

1. 惰性求值避免不必要的计算
2. 只在需要时计算
3. 因此提高效率

### 9.2 Rust中的惰性求值

#### 定义 9.2.1 (迭代器惰性)
```
Iterator_Lazy = {i | i evaluates only when consumed}
```

#### 示例 9.2.1 (惰性求值)
```rust
let numbers = 1..1000;
let filtered = numbers.filter(|&x| x % 2 == 0); // 不计算
let result: Vec<_> = filtered.take(5).collect(); // 只计算前5个
```

## 10. 模式匹配理论

### 10.1 模式匹配基础

#### 定义 10.1.1 (模式匹配)

模式匹配是函数式编程中的控制结构：
$$\text{Match}(e, p_1 \rightarrow e_1, p_2 \rightarrow e_2, \ldots, p_n \rightarrow e_n)$$

#### 定义 10.1.2 (模式)

模式是值的结构描述：
$$\text{Pattern} = \text{Constructor}(\text{Pattern}_1, \text{Pattern}_2, \ldots, \text{Pattern}_n)$$

### 10.2 Rust中的模式匹配

#### 定义 10.2.1 (匹配表达式)
```
Match_Expression = match Expression { Pattern => Expression, ... }
```

#### 示例 10.2.1 (模式匹配)
```rust
fn pattern_match_example(opt: Option<i32>) -> String {
    match opt {
        Some(x) if x > 0 => format!("Positive: {}", x),
        Some(0) => "Zero".to_string(),
        Some(_) => "Negative".to_string(),
        None => "No value".to_string(),
    }
}
```

## 11. 总结与展望

### 11.1 函数式编程总结

Rust 的函数式编程特性提供了强大的抽象能力和安全性保证。通过纯函数、不可变性、高阶函数、单子等概念，Rust 实现了函数式编程的核心思想。

### 11.2 未来发展方向

1. **形式化验证的扩展**：进一步完善函数式特性的形式化验证
2. **性能优化的深化**：探索函数式编程的性能优化技术
3. **工程实践的优化**：将函数式编程更好地应用于工程实践

---

**参考文献**：

1. Pierce, B. C. (2002). Types and Programming Languages. MIT Press.
2. Wadler, P. (1992). Monads for functional programming. Advanced Functional Programming, 24-52.
3. Peyton Jones, S. (2003). The Haskell 98 Language and Libraries. Journal of Functional Programming, 13(1), 0-255. 