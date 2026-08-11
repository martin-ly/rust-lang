> **内容分级**: [专家级]

# 范畴论与 Rust：作为计算模型的结构语义（Category Theory and Rust: Structural Semantics as a Computational Model）

> **EN**: Category Theory and Rust: Structural Semantics as a Computational Model
> **Summary**: Treats category theory as a computational model for Rust's type system, mapping Cartesian closed categories, limits/colimits, exponentials, and monads to Rust's product/sum/function types, ownership constraints, and effectful computations, while distinguishing categorical semantics from programming-pattern analogies.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**计算模型**视角把范畴论当作 Rust 类型系统的**结构语义**：不停留在「Functor/Monad 编程模式」，而是说明积类型、和类型、函数类型、初始/终止对象如何在范畴论语义中构成一个可推理的计算模型，并为 [模态逻辑与 Rust 计算效应](11_modal_logic_and_rust_effects.md) 提供范畴基础。
> **前置概念**:
> [Type Theory and Rust](07_type_theory_and_rust.md) ·
> [Category Theory (Type Theory Perspective)](../00_type_theory/04_category_theory.md) ·
> [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) ·
> [Computational Semantics Framework](01_computational_semantics_framework.md)
> **后置概念**:
> [Modal Logic and Rust Effects](11_modal_logic_and_rust_effects.md) ·
> [Algebraic Effects](../07_concurrency_semantics/04_algebraic_effects.md) ·
> [Computational Equivalence in Rust](06_computational_equivalence_in_rust.md) ·
> [RustBelt](../02_separation_logic/01_rustbelt.md) ·
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) ·
> [Async/Await](../../03_advanced/01_async/01_async.md)

---

## 📑 目录

- [范畴论与 Rust：作为计算模型的结构语义（Category Theory and Rust: Structural Semantics as a Computational Model）](#范畴论与-rust作为计算模型的结构语义category-theory-and-rust-structural-semantics-as-a-computational-model)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 范畴论作为计算模型](#11-范畴论作为计算模型)
    - [1.2 Rust 类型范畴：对象、态射与组合](#12-rust-类型范畴对象态射与组合)
    - [1.3 积与和：结构体 / 枚举的范畴语义](#13-积与和结构体--枚举的范畴语义)
    - [1.4 指数对象：函数类型与 Currying](#14-指数对象函数类型与-currying)
    - [1.5 初始对象与终止对象：`!` 与 `()`](#15-初始对象与终止对象-与-)
    - [1.6 函子：类型构造子作为结构保持映射](#16-函子类型构造子作为结构保持映射)
    - [1.7 单子：效应的组合模型](#17-单子效应的组合模型)
    - [1.8 所有权与线性的范畴直觉](#18-所有权与线性的范畴直觉)
  - [二、形式化属性矩阵](#二形式化属性矩阵)
  - [三、正向示例](#三正向示例)
    - [示例 1：积类型满足泛性质](#示例-1积类型满足泛性质)
    - [示例 2：和类型满足泛性质](#示例-2和类型满足泛性质)
    - [示例 3：函数类型作为指数对象](#示例-3函数类型作为指数对象)
    - [示例 4：Option 满足单子定律](#示例-4option-满足单子定律)
  - [四、反例与边界测试](#四反例与边界测试)
    - [反例 1：Rust 没有高阶类型，无法抽象任意 Functor](#反例-1rust-没有高阶类型无法抽象任意-functor)
    - [反例 2：非法的单子 trait 定义](#反例-2非法的单子-trait-定义)
    - [反例 3：把 `()` 当作初始对象](#反例-3把--当作初始对象)
  - [五、反命题决策树](#五反命题决策树)
    - [命题：「Rust 类型系统构成一个笛卡尔闭范畴」](#命题rust-类型系统构成一个笛卡尔闭范畴)
    - [命题：「Functor 就是实现了 map 的类型」](#命题functor-就是实现了-map-的类型)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
    - [测验 1：Rust 中哪个类型对应范畴论的终止对象？](#测验-1rust-中哪个类型对应范畴论的终止对象)
    - [测验 2：`Result<T, E>` 最接近哪个范畴构造？](#测验-2resultt-e-最接近哪个范畴构造)
    - [测验 3：Currying 在 Rust 中对应什么？](#测验-3currying-在-rust-中对应什么)
  - [七、权威来源 / International Authority References](#七权威来源--international-authority-references)
  - [八、🧭 思维导图（Mindmap）](#八-思维导图mindmap)

---

## 一、核心概念

### 1.1 范畴论作为计算模型

范畴论（category theory）通常被介绍为「研究结构的数学」。从**计算模型**视角看，它提供了一套**语法无关的语义框架**：不管具体语言语法如何，只要程序可以组织成「对象」与「态射」，就可以用范畴论工具描述其复合、等价与泛性质。

```text
范畴论作为计算模型
├── 对象（Objects）: 类型 / 程序状态 / 计算上下文
├── 态射（Morphisms）: 程序/函数/转换  A → B
├── 组合（Composition）: g ∘ f，对应「先 f 后 g」
├── 恒等（Identity）: id_A，对应「什么都不做」
└── 泛性质（Universal Properties）: 积、和、指数等构造的唯一性刻画
```

与图灵机/λ 演算不同，范畴论不直接回答「能计算什么函数」，而是回答「计算结构如何组合」以及「哪些组合是典范的」。这使得它特别适合作为**类型系统的语义模型**：Rust 的类型构造子（`struct`、`enum`、`fn`）恰好对应范畴论中的基本极限与余极限。

> **来源**: [Milewski, *Category Theory for Programmers*](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) · [Awodey, *Category Theory*](https://doi.org/10.1093/acprof:oso/9780198568612.001.0001)

---

### 1.2 Rust 类型范畴：对象、态射与组合

在 Rust 的**纯类型范畴**（忽略生命周期与所有权细节时）中：

| 范畴论概念 | Rust 对应 | 说明 |
|:---|:---|:---|
| 对象 | 具体类型 `A`、`B`、`C` | 如 `i32`、`String`、`Vec<T>` |
| 态射 | 纯函数 `fn(A) -> B` | 类型正确的函数 |
| 恒等 | `fn id<T>(x: T) -> T { x }` | 保持对象不变 |
| 组合 | `|x| g(f(x))` 或显式 `compose` | 满足结合律与恒等律 |

```rust
fn id<T>(x: T) -> T { x }

fn compose<A, B, C>(f: impl Fn(A) -> B, g: impl Fn(B) -> C) -> impl Fn(A) -> C {
    move |x| g(f(x))
}

fn main() {
    let f = |x: i32| x + 1;
    let g = |x: i32| x * 2;
    let h = compose(f, g);
    assert_eq!(h(5), 12); // (5 + 1) * 2
}
```

> **关键洞察**: Rust 的函数类型、泛型与闭包已经编码了范畴论的基本骨架。范畴论的价值在于把这些分散机制统一到「对象-态射-组合」语言中，从而判断哪些 API 设计是**典范的**（canonical）——即由泛性质唯一确定的。

---

### 1.3 积与和：结构体 / 枚举的范畴语义

**积（Product）**是范畴论中用投影与配对唯一刻画的构造。Rust 的**元组**和**结构体**正是积类型：

```text
积的泛性质
  给定 A × B，存在投影 π₁ : A × B → A, π₂ : A × B → B
  对任意 C 与 f: C → A, g: C → B，存在唯一 ⟨f, g⟩: C → A × B
  使得 π₁ ∘ ⟨f, g⟩ = f 且 π₂ ∘ ⟨f, g⟩ = g
```

```rust
fn pair_from<A, B, C: Clone>(f: impl Fn(C) -> A, g: impl Fn(C) -> B, c: C) -> (A, B) {
    (f(c.clone()), g(c))
}

fn main() {
    let c = 5;
    let p = pair_from(|x| x + 1, |x| x * 2, c);
    assert_eq!(p, (6, 10));
}
```

**和（Coproduct / Sum）**是积的对偶构造。Rust 的 `enum`（特别是 `Either<A, B>`、`Option<T>`、`Result<T, E>`）是和类型：

```text
和的泛性质
  给定 A + B，存在入射 i₁ : A → A + B, i₂ : B → A + B
  对任意 C 与 f: A → C, g: B → C，存在唯一 [f, g]: A + B → C
```

```rust
enum Either<A, B> { Left(A), Right(B) }

fn fold_either<A, B, C>(e: Either<A, B>, f: impl Fn(A) -> C, g: impl Fn(B) -> C) -> C {
    match e {
        Either::Left(a) => f(a),
        Either::Right(b) => g(b),
    }
}

fn main() {
    let e: Either<i32, &str> = Either::Left(42);
    let r = fold_either(e, |x| x.to_string(), |s| s.to_string());
    assert_eq!(r, "42");
}
```

> **来源**: [Pierce, *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Leinster, *Basic Category Theory*](https://arxiv.org/abs/1612.09375)

---

### 1.4 指数对象：函数类型与 Currying

**笛卡尔闭范畴（Cartesian Closed Category, CCC）**要求范畴有积，并且每个对象都可以作为「指数对象」`B^A`，使得：

```text
Hom(C × A, B) ≅ Hom(C, B^A)
```

即「从 C × A 到 B 的态射」与「从 C 到 B^A 的态射」一一对应。在 Rust 中，这就是**Currying**：

```rust
fn uncurried(a: i32, b: i32) -> i32 { a + b }

fn curried(a: i32) -> impl Fn(i32) -> i32 {
    move |b| a + b
}

fn main() {
    let add_five = curried(5);
    assert_eq!(add_five(3), 8);
}
```

> **关键洞察**: Rust 的 `fn(A, B) -> C` 与 `fn(A) -> fn(B) -> C`（在闭包形式下）的等价性，正是 CCC 中指数对象的工程实现。这也意味着 Rust 的纯类型片段可以嵌入一个 CCC 语义模型。

---

### 1.5 初始对象与终止对象：`!` 与 `()`

- **终止对象（Terminal Object）** `1`：对任意对象 `A`，存在唯一态射 `A → 1`。Rust 中对应 `()`（unit type）。
- **初始对象（Initial Object）** `0`：对任意对象 `A`，存在唯一态射 `0 → A`。Rust 中对应 `!`（never type）或空 `enum Void {}`。

```rust
fn to_unit<T>(_: T) -> () { () }

enum Void {}

fn from_void<T>(v: Void) -> T {
    match v {}
}

fn main() {
    let _ = to_unit(42);
}
```

> **范畴直觉**: `()` 是「没有信息」的类型，任何值都可以被丢弃到 `()`；`!` 是「不可能存在」的类型，因此从它出发可以做任意推论（ex falso quodlibet）。

---

### 1.6 函子：类型构造子作为结构保持映射

函子 `F: C → D` 把对象映射到对象、态射映射到态射，并保持恒等和组合。Rust 中常见的类型构造子都是**自函子**（endofunctor）`F: Rust → Rust`：

```text
Option : A ↦ Option<A>   且   f: A → B  ↦  Option::map(f): Option<A> → Option<B>
Vec    : A ↦ Vec<A>      且   f: A → B  ↦  Vec::iter().map(f)
Result : A ↦ Result<A, E> 且  f: A → B  ↦  Result::map(f)
```

```rust
fn main() {
    let x: Option<i32> = Some(5);
    let f = |v| v + 1;
    let g = |v| v * 2;

    // 函子定律 1: map(id) = id
    assert_eq!(x.map(|v| v), x);

    // 函子定律 2: map(g ∘ f) = map(g) ∘ map(f)
    assert_eq!(x.map(|v| g(f(v))), x.map(f).map(g));
}
```

> **关键区别**: [范畴论与 Rust：从函子到单子](../00_type_theory/04_category_theory.md) 从**编程模式**角度介绍 Functor/Monad；本页强调函子作为**计算模型的结构保持映射**，为后续「单子 = 效应模型」奠定语义基础。

---

### 1.7 单子：效应的组合模型

在范畴论语义中，**单子（Monad）**是三元组 `(M, η, μ)`，其中 `M` 是自函子，`η: Id ⇒ M` 是单位自然变换，`μ: M² ⇒ M` 是乘法自然变换。它给出了一种**组合带效应计算**的通用模型：

```text
Rust 中的单子实例
  Option:  η(x) = Some(x),   μ(None) = None, μ(Some(Some(x))) = Some(x)
  Result:  η(x) = Ok(x),      μ(Ok(Ok(x))) = Ok(x), μ(Ok(Err(e))) = Err(e)
  Vec:     η(x) = vec![x],    μ 对应 flatten
  Future:  η(x) = async { x },μ 对应 .await 的隐式展平
```

```rust
fn main() {
    let x: Option<i32> = Some(5);

    // η: A → M<A>
    let _unit: Option<i32> = Some(5);

    // μ: M<M<A>> → M<A>，Rust 中通过 and_then 显式展平
    let nested: Option<Option<i32>> = Some(Some(5));
    let flat = nested.and_then(|inner| inner);
    assert_eq!(flat, Some(5));

    // bind: M<A> → (A → M<B>) → M<B>
    let bound = x.and_then(|v| if v > 0 { Some(v * 2) } else { None });
    assert_eq!(bound, Some(10));
}
```

> **来源**: [Moggi, *Notions of Computation and Monads*](https://doi.org/10.1016/0890-5401(91)90052-4) · [Plotkin & Power, *Notions of Computation Determine Monads*](https://doi.org/10.1007/3-540-45931-6_24)

---

### 1.8 所有权与线性的范畴直觉

范畴论还可以为 Rust 的**所有权模型**提供高层直觉。在线性/仿射类型系统中，对象是「资源」，态射是「资源变换」，组合必须遵守资源守恒。Rust 的所有权规则可以被看作一个**仿射范畴**（affine category）的约束：

```text
仿射范畴直觉
  非 Copy 值: 从 A 到 B 的态射「消耗」A 并「产出」B
  move:       资源从 s 转移到 t，s 不再有效
  borrow:     资源被临时出借，借用结束后回归原所有者
  drop:       资源被销毁，对应于到终止对象的唯一映射
```

```rust
fn consume(s: String) -> usize { s.len() }

fn main() {
    let s = String::from("resource");
    let n = consume(s); // s 被消耗，态射 String → usize
    assert_eq!(n, 8);
    // println!("{}", s); // ❌ 违反仿射规则
}
```

> **关键洞察**: 范畴论不直接证明借用检查器正确，但它提供了一种**资源即态射**的思维方式：每个值在生命周期中都是一条从创建点到销毁点的「资源流」。这与分离逻辑中的资源观（own / shr）以及线性逻辑（⊗, ⊸）是一致的。

---

## 二、形式化属性矩阵

| 范畴论概念 | Rust 工程机制 | 形式化含义 | 权威来源 |
|:---|:---|:---|:---|
| 对象 | 类型 `A`、`B` | 语义域中的点 | Awodey 2010 |
| 态射 | `fn(A) -> B` | 类型保持的计算 | Milewski 2014 |
| 积 `A × B` | `(A, B)` / `struct` | 投影与配对的泛性质 | Pierce 2002 |
| 和 `A + B` | `enum` / `Either` | 入射与匹配的泛性质 | Pierce 2002 |
| 指数 `B^A` | `fn(A) -> B` | Currying / 求值-转置 | Lambek & Scott 1986 |
| 终止对象 `1` | `()` | 唯一到 unit 的映射 | Leinster 2014 |
| 初始对象 `0` | `!` / `enum Void {}` | ex falso / 不可能值 | Leinster 2014 |
| 自函子 | `Option<T>`、`Vec<T>`、`Result<T,E>` | 结构保持的类型构造子 | Mac Lane 1998 |
| 单子 `(M, η, μ)` | `Some`/`and_then`、`Ok`/`?`、`async`/`await` | 效应的组合模型 | Moggi 1991 |
| 仿射范畴 | 所有权 / move / borrow | 资源不可复制但可丢弃 | Wadler 1990 |

---

## 三、正向示例

### 示例 1：积类型满足泛性质

```rust
fn pair<A, B>(a: A, b: B) -> (A, B) { (a, b) }
fn fst<A, B>(p: (A, B)) -> A { p.0 }
fn snd<A, B>(p: (A, B)) -> B { p.1 }

fn main() {
    let p = pair("x", 42);
    assert_eq!(fst(p), "x");
    assert_eq!(snd(p), 42);
}
```

### 示例 2：和类型满足泛性质

```rust
enum Either<A, B> { Left(A), Right(B) }

fn left<A, B>(a: A) -> Either<A, B> { Either::Left(a) }
fn right<A, B>(b: B) -> Either<A, B> { Either::Right(b) }

fn main() {
    let e: Either<i32, &str> = left(42);
    let s = match e {
        Either::Left(n) => n.to_string(),
        Either::Right(t) => t.to_string(),
    };
    assert_eq!(s, "42");
}
```

### 示例 3：函数类型作为指数对象

```rust
fn curry<A: Clone + 'static, B: Clone + 'static, C: Clone + 'static>(
    f: impl Fn(A, B) -> C + Clone + 'static,
) -> impl Fn(A) -> Box<dyn Fn(B) -> C> {
    move |a| {
        let f = f.clone();
        Box::new(move |b| f(a.clone(), b.clone()))
    }
}

fn uncurry<A, B, C>(f: impl Fn(A) -> Box<dyn Fn(B) -> C>) -> impl Fn(A, B) -> C {
    move |a, b| f(a)(b)
}

fn main() {
    let add = |a: i32, b: i32| a + b;
    let curried_add = curry(add);
    assert_eq!(curried_add(3)(4), 7);
    assert_eq!(uncurry(curried_add)(3, 4), 7);
}
```

### 示例 4：Option 满足单子定律

```rust
fn main() {
    let x = 5;
    let f = |v: i32| Some(v + 1);
    let g = |v: i32| Some(v * 2);

    // 左单位元: η(x) >>= f = f(x)
    assert_eq!(Some(x).and_then(f), f(x));

    // 右单位元: m >>= η = m
    let m: Option<i32> = Some(5);
    assert_eq!(m.and_then(|v| Some(v)), m);

    // 结合律: (m >>= f) >>= g = m >>= (|x| f(x) >>= g)
    let lhs = m.and_then(f).and_then(g);
    let rhs = m.and_then(|x| f(x).and_then(g));
    assert_eq!(lhs, rhs);
}
```

---

## 四、反例与边界测试

### 反例 1：Rust 没有高阶类型，无法抽象任意 Functor

```rust,compile_fail
// Rust 不支持 "F<A>" 作为类型参数，因此无法定义跨 Option/Result/Vec 的通用 Functor
trait Functor<F<A>> {
    fn map<B>(self, f: impl Fn(A) -> B) -> F<B>;
}
```

> **错误诊断**: 解析器直接拒绝 `F<A>` 这种「类型构造子作为类型参数」的语法；Rust 不支持高阶类型（HKT）。
> **修正**: Rust 通过 GAT（Generic Associated Types）可以表达部分高阶构造，但无法写出完全通用的 `Functor` trait。每个类型构造子独立实现 `map`/`and_then`。

### 反例 2：非法的单子 trait 定义

```rust,compile_fail
// 同样因为缺少 HKT，无法定义通用 Monad trait
trait Monad<M<A>> {
    fn bind<B, F>(self, f: F) -> M<B>
    where F: Fn(A) -> M<B>;
}
```

> **修正**: 使用具体类型的 `and_then`/`?`/`async/await`，或借助宏/过程宏生成重复代码。

### 反例 3：把 `()` 当作初始对象

```rust,compile_fail
fn from_unit_to_any<T>(x: ()) -> T {
    // () 不是初始对象：无法通过穷尽匹配从 unit 构造任意 T
    match x {}
}
```

> **错误诊断**: `error[E0005]: refutable pattern in local binding:`()`not covered`。终止对象 `()` 有从任意类型到它的唯一映射；**初始对象**才是有从它到任意类型的唯一映射。Rust 中的初始对象是 `!`（never type）或空枚举 `Void {}`。
> **修正**: 使用 `enum Void {}` 配合 `match v {}` 实现 ex falso。

---

## 五、反命题决策树

### 命题：「Rust 类型系统构成一个笛卡尔闭范畴」

```text
该命题成立吗？
├── 是 → 不完全。Rust 的纯类型片段（忽略生命周期、unsafe、运行时副作用）确实近似 CCC：
│   ├── 有积类型 (struct, tuple)
│   ├── 有和类型 (enum)
│   ├── 有指数对象 (fn)
│   └── 有终止对象 ()
└── 否 → 更准确。完整 Rust 还有：
    ├── 生命周期构成的偏序范畴（不是 CCC）
    ├── unsafe 打破类型安全保证
    ├── 副作用/IO 不在纯 CCC 语义中
    └── 所有权约束使其更像仿射范畴而非普通 CCC
```

### 命题：「Functor 就是实现了 map 的类型」

```text
该命题成立吗？
├── 是 → 表层相似。真正的函子必须满足两条定律：
│   ├── map(id) = id
│   └── map(g ∘ f) = map(g) ∘ map(f)
│   Rust 中 Option/Result/Iterator 的实现确实满足。
└── 否 → 更准确。Rust 没有统一的 Functor trait；
    └── "有 map 方法"不等于"函子"，还需验证结构保持定律。
```

---

## 六、嵌入式测验（Embedded Quiz）

### 测验 1：Rust 中哪个类型对应范畴论的终止对象？

A. `!`
B. `()`
C. `bool`
D. `Option<()>`

<details>
<summary>✅ 答案</summary>

**B. `()`**。终止对象要求从任意对象到它有且仅有一个态射。`fn to_unit<T>(_: T) -> () { () }` 是唯一的。

</details>

### 测验 2：`Result<T, E>` 最接近哪个范畴构造？

A. 积 `T × E`
B. 和 `T + E`
C. 指数 `E^T`
D. 终止对象

<details>
<summary>✅ 答案</summary>

**B. 和 `T + E`**。`Result<T, E>` 要么是 `T` 的证明（`Ok`），要么是 `E` 的证明（`Err`），对应范畴和类型。

</details>

### 测验 3：Currying 在 Rust 中对应什么？

A. 把 `fn(A, B) -> C` 变成 `fn(A) -> fn(B) -> C`
B. 把 `fn(A) -> B` 变成 `fn(A, B)`
C. 把 `enum` 变成 `struct`
D. 把 `Vec<T>` 变成 `Option<T>`

<details>
<summary>✅ 答案</summary>

**A. 把 `fn(A, B) -> C` 变成 `fn(A) -> fn(B) -> C`**。这正是笛卡尔闭范畴中指数对象的 Curry-Howard 对应，也是 `curry` / `uncurry` 的语义来源。

</details>

---

## 七、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Milewski, *Category Theory for Programmers*](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) | ✅ 一级 | 程序员视角的范畴论，覆盖 CCC、Functor、Monad |
| [Awodey, *Category Theory*](https://doi.org/10.1093/acprof:oso/9780198568612.001.0001) | ✅ 一级 | 标准范畴论教材 |
| [Leinster, *Basic Category Theory*](https://arxiv.org/abs/1612.09375) | ✅ 一级 | 简洁的范畴论入门，积/和/指数对象 |
| [Mac Lane, *Categories for the Working Mathematician*](https://doi.org/10.1007/978-1-4757-4721-8) | ✅ 一级 | 范畴论经典参考书 |
| [Lambek & Scott, *Introduction to Higher-Order Categorical Logic*](https://doi.org/10.1017/S0017089500008149) | ✅ 一级 | CCC 与类型论 / λ 演算的联系 |
| [Pierce, *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 一级 | 类型系统、积/和/函数类型 |
| [Moggi, *Notions of Computation and Monads*](https://doi.org/10.1016/0890-5401(91)90052-4) | ✅ 一级 | 单子作为计算模型的奠基论文 |
| [Plotkin & Power, *Notions of Computation Determine Monads*](https://doi.org/10.1007/3-540-45931-6_24) | ✅ 一级 | 代数效应与单子的等价视角 |
| [Wadler, *Linear Types can Change the World!*](https://homepages.inf.ed.ac.uk/wadler/papers/lineartypes/lineartypes.pdf) | ✅ 一级 | 线性/仿射类型资源视角 |
| [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html) | ✅ P0 | Rust 官方类型参考 |
| [frunk on docs.rs](https://docs.rs/frunk/) | ✅ P2 | Rust 函数式编程库（HList、Generic、Semigroupoid 等范畴构造） |
| [GATs Stabilization — Rust Blog](https://blog.rust-lang.org/2022/10/28/gats-stabilization.html) | ✅ P2 | GAT 稳定化与 Rust 中高阶类型能力边界 |

---

## 八、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((范畴论与 Rust 计算模型))
    范畴作为计算模型
      对象 = 类型
      态射 = 函数
      组合 = 函数复合
      泛性质
    积与和
      积 = struct / tuple
      和 = enum / Result / Option
      泛性质刻画
    指数对象
      fn(A) -> B
      Currying
      CCC
    初始/终止对象
      终止对象 = ()
      初始对象 = ! / Void
    函子
      Option / Vec / Result
      结构保持映射
      函子定律
    单子
      η = Some / Ok / async
      μ = and_then / ? / await
      效应组合模型
    所有权直觉
      仿射范畴
      move / borrow / drop
    权威来源
      Category Theory for Programmers
      MLTT / CCC
      Moggi / Plotkin & Power
```
