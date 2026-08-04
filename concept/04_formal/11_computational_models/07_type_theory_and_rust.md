> **内容分级**: [专家级]

# 类型论与 Rust：作为计算模型的类型系统（Type Theory and Rust）

> **EN**: Type Theory and Rust: The Type System as a Computational Model
> **Summary**: Examines Rust's type system as a substructural computational model spanning affine/linear ownership, System Fω-style polymorphism, lifetimes as modal constraints, and the Curry-Howard correspondence, and maps these formal foundations to mechanized verification frameworks such as Iris and RustBelt.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**计算模型**视角重新组织类型论与 Rust 的关系：不把类型系统仅当作「分类工具」，而是把它看作一个对程序状态空间进行语法裁剪的**重写/约束系统**，为 [Separation Logic for Rust](08_separation_logic_for_rust.md) 与 [Concurrency Models](09_concurrency_models_actors_csp.md) 提供形式化入口。
> **前置概念**:
> [Type Theory](../00_type_theory/01_type_theory.md) ·
> [Linear Logic](../01_ownership_logic/01_linear_logic.md) ·
> [Ownership Formalization](../01_ownership_logic/02_ownership_formal.md) ·
> [System F](../00_type_theory/17_system_f.md) ·
> [Operational Semantics](../03_operational_semantics/03_operational_semantics.md)
> **后置概念**:
> [Separation Logic for Rust](08_separation_logic_for_rust.md) ·
> [RustBelt](../02_separation_logic/01_rustbelt.md) ·
> [Concurrency Models](09_concurrency_models_actors_csp.md) ·
> [Computational Equivalence in Rust](06_computational_equivalence_in_rust.md) ·
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md)

---

## 📑 目录

- [类型论与 Rust：作为计算模型的类型系统（Type Theory and Rust）](#类型论与-rust作为计算模型的类型系统type-theory-and-rust)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 类型系统不只是分类：它是一个计算模型](#11-类型系统不只是分类它是一个计算模型)
    - [1.2 仿射/线性类型：所有权即资源](#12-仿射线性类型所有权即资源)
    - [1.3 System Fω 与 Rust 泛型：类型层面的 λ 演算](#13-system-fω-与-rust-泛型类型层面的-λ-演算)
    - [1.4 生命周期作为模态/区域约束](#14-生命周期作为模态区域约束)
    - [1.5 Curry-Howard 同构：类型即命题，程序即证明](#15-curry-howard-同构类型即命题程序即证明)
    - [1.6 类型级计算与可判定性边界](#16-类型级计算与可判定性边界)
    - [1.7 从类型模型到机械证明](#17-从类型模型到机械证明)
  - [二、形式化属性矩阵](#二形式化属性矩阵)
  - [三、正向示例](#三正向示例)
    - [示例 1：仿射资源与独占借用](#示例-1仿射资源与独占借用)
    - [示例 2：生命周期子类型](#示例-2生命周期子类型)
    - [示例 3：Curry-Howard 的「假 ⇒ 任意命题」](#示例-3curry-howard-的假--任意命题)
  - [四、反例与边界测试](#四反例与边界测试)
    - [反例 1：仿射资源被二次使用（E0382）](#反例-1仿射资源被二次使用e0382)
    - [反例 2：生命周期不足导致悬垂引用（E0106 / E0597）](#反例-2生命周期不足导致悬垂引用e0106--e0597)
    - [反例 3：生命周期选择不满足子类型](#反例-3生命周期选择不满足子类型)
  - [五、反命题决策树](#五反命题决策树)
    - [命题：「Rust 类型系统可以阻止所有运行时错误」](#命题rust-类型系统可以阻止所有运行时错误)
    - [命题：「Rust 类型系统是线性类型系统」](#命题rust-类型系统是线性类型系统)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
    - [测验 1：Rust 的所有权系统最接近哪种类型系统？](#测验-1rust-的所有权系统最接近哪种类型系统)
    - [测验 2：生命周期 `'a: 'b` 的最合适形式化解释是？](#测验-2生命周期-a-b-的最合适形式化解释是)
    - [测验 3：`enum Either<A, B>` 在 Curry-Howard 中对应什么逻辑连接词？](#测验-3enum-eithera-b-在-curry-howard-中对应什么逻辑连接词)
  - [七、权威来源 / International Authority References](#七权威来源--international-authority-references)
  - [八、🧭 思维导图（Mindmap）](#八-思维导图mindmap)

---

## 一、核心概念

### 1.1 类型系统不只是分类：它是一个计算模型

传统教材把类型系统定义为「对项进行分类的语法方法」（Pierce, 2002）。从**计算模型**角度看，类型系统还是一个**在编译期运行的约束求解器**，它把程序可到达的状态空间切分成「良构」与「非良构」两个集合，并通过类型检查拒绝后者。

```text
Rust 类型系统作为计算模型
├── 项（terms）    : 表达式、值、函数
├── 类型（types）  : 项的状态分类
├── 判断（judgment）: Γ; Σ ⊢ e : τ   （上下文 Γ、所有权状态 Σ 下 e 具有类型 τ）
├── 规则（rules）  : 类型推导/检查规则
└── 计算（computation）: trait 求解、生命周期约束、借用检查
```

这与图灵机、λ 演算等不同：图灵机回答「能算什么」，类型系统回答「哪些程序状态转移被允许」。但两者都是**形式化的计算模型**——类型检查本身就是一个可判定的（或受控不可判定的）计算过程。

> **来源**: [Pierce 2002, *Types and Programming Languages*, Ch.1](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

### 1.2 仿射/线性类型：所有权即资源

Rust 的所有权系统可以被精确地建模为**仿射类型系统（affine type system）**：每个非 `Copy` 值在任一时刻只能有一个**独占**所有者，所有者离开作用域时资源被释放（drop）。这与**线性类型**的区别在于：线性类型要求资源**必须**被使用，而仿射类型允许资源被静默丢弃。

```text
线性逻辑记号    Rust 语义
────────────    ─────────────────
A ⊗ B           组合资源 (a, b)
A ⊸ B           消耗 A 产出 B 的函数
!A              Copy / 共享借用 &T
&A              只读共享引用（可复制）
&mut A          独占借用（不可复制）
```

```rust
fn main() {
    let s = String::from("affine"); // own(String)
    let t = s;                       // own(String) 从 s 转移到 t
    println!("{}", t);               // ✅ t 拥有资源
    // println!("{}", s);            // ❌ 若取消注释：error[E0382] value used here after move
}
```

`&mut T` 的独占性正是**线性/仿射资源**的工程化实现：同一时刻只能存在一个 `&mut T`，这对应于分离逻辑中的 `own(T)` 断言不可被复制。

> **来源**: [Wadler 1990, *Linear Types can Change the World!*](https://homepages.inf.ed.ac.uk/wadler/papers/lineartypes/lineartypes.pdf) · [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html)

---

### 1.3 System Fω 与 Rust 泛型：类型层面的 λ 演算

Rust 泛型可以定位在 **System Fω** 的受限子集：支持类型抽象 `∀α.τ`（`fn foo<T>()`）、类型构造子 `* → *`（`Vec<T>`、 `Option<T>`），以及受限的**高阶类型**（Generic Associated Types, GATs）。

```text
System Fω 层级            Rust 对应
─────────────────────────────────────────────────
λ→  简单类型 λ 演算        无泛型函数
λ2  System F               fn id<T>(x: T) -> T
λω  类型构造子             trait Container<T> { type Item; }
λΠ  依赖类型               const N: usize
```

下面的代码展示了**类型级 Peano 算术**，说明 Rust 类型系统可以把计算从项层面提升到类型层面：

```rust
use std::marker::PhantomData;

struct Z;
struct S<N>(PhantomData<N>);

trait Add<Rhs> {
    type Sum;
}

impl<Rhs> Add<Rhs> for Z {
    type Sum = Rhs;
}

impl<N, Rhs> Add<Rhs> for S<N>
where
    N: Add<Rhs>,
{
    type Sum = S<N::Sum>;
}

type One   = S<Z>;
type Two   = S<One>;
type Three = <One as Add<Two>>::Sum;

fn assert_three(_: Three) {}

fn main() {}
```

> **关键洞察**: 类型级计算是 Rust 类型系统「图灵完备」的来源之一，但编译器通过 trait 递归深度上限把这一能力约束在工程可接受范围内。

---

### 1.4 生命周期作为模态/区域约束

Rust 的生命周期 `'a` 不是普通类型，而是对**引用有效范围**的约束。形式化上可把它看作一种**区域（region）**或**Kripke 可能世界**中的模态：

```text
'a: 'b   ⇔   区域 a 包含区域 b   ⇔   在任何 a 有效的世界里 b 也有效
&'a T   ⇔   一个在未来所有 a-世界里都指向 T 的 box（□T）
&'a mut T ⇔  在未来所有 a-世界里独占持有 T
```

```rust
fn longer<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("hello");
    let s2 = String::from("world!");
    let r = longer(&s1, &s2);
    println!("{}", r);
}
```

生命周期的子类型关系 `'a: 'b` 是**协变**的：返回的引用必须至少与输入引用活得一样长。这与 System F 的子类型不同，它把**时间维度**引入了类型判断。

> **来源**: [Weiss, Patterson & Ahmed 2018, *Rust Distilled*](https://arxiv.org/abs/1806.02693)

---

### 1.5 Curry-Howard 同构：类型即命题，程序即证明

Curry-Howard 同构指出：类型对应逻辑命题，程序对应证明。Rust 类型系统中充满了这一同构的实例：

| 逻辑 | 类型 | Rust 例子 |
|:---|:---|:---|
| 真 ⊤ | 单元类型 `()` | `fn unit() -> () { () }` |
| 假 ⊥ | 空类型 `!` / `Void` | `enum Void {}` 后 `fn absurd(x: Void) -> T { match x {} }` |
| 蕴含 A ⇒ B | 函数 `A -> B` | `fn imply(a: A) -> B` |
| 合取 A ∧ B | 积类型 `(A, B)` | `(a, b)` |
| 析取 A ∨ B | 和类型 `Either<A,B>` | `enum Either<A,B> { Left(A), Right(B) }` |
| 全称 ∀ | 泛型 `fn f<T>()` | `fn id<T>(x: T) -> T { x }` |

```rust
enum Either<A, B> {
    Left(A),
    Right(B),
}

enum Void {}

fn absurd<T>(x: Void) -> T {
    match x {}
}

fn main() {
    let truth: () = ();
    let proof: Either<i32, String> = Either::Left(42);
    let _ = (truth, proof);
}
```

Rust 的 `Result<T, E>` 和 `Option<T>` 也可以读作**可证明的异常处理**：`Ok(v)` 是「成功」的证明，`Err(e)` 是「失败」的证明；`match` 必须覆盖两个分支，对应于析取消去规则（proof by cases）。

---

### 1.6 类型级计算与可判定性边界

Rust 类型系统同时具备两个看似矛盾的属性：

1. **理论上图灵完备**：通过 trait 关联类型、const generics 和类型递归，可以编码任意可计算函数（见 [Computational Equivalence in Rust](06_computational_equivalence_in_rust.md)）。
2. **工程上可判定**：编译器设置了 trait 递归深度、CTFE 步数、monomorphization 限制，确保普通程序在合理时间内完成类型检查。

```rust
fn main() {
    // 1 + 1 在类型检查期求值
    const N: usize = 1 + 1;
    let arr: [i32; N] = [0; N];
    assert_eq!(arr.len(), 2);
}
```

```text
类型系统计算边界
├── 可判定片段：HM 推断、生命周期约束、基本泛型
├── 受控不可判定：深度递归 trait（E0275 / E0080）
└── 完全不可判定：停机问题在类型级同样不可判定
```

---

### 1.7 从类型模型到机械证明

Rust 类型系统的形式化模型是多个验证工具的基础：

| 形式化框架 | 关注的类型论层面 | 与 Rust 的关系 |
|:---|:---|:---|
| **Coq / Lean** | 依赖类型、归纳证明 | 机械验证 Rust 子集语义 |
| **Iris** | 高阶分离逻辑 | 为 RustBelt 提供断言语言 |
| **RustBelt** | λRust + Iris | 证明 safe Rust 内存安全且无数据竞争 |
| **Aeneas** | 纯函数式翻译 | 将 Rust 翻译成可证明的函数式程序 |
| **Flux** | 精炼类型 | 在 Rust 类型上附加 SMT 可解约束 |

这些工具的共同点是：把 Rust 的类型系统当作**一个可推理的计算模型**，而不是仅当作编译器实现细节。

> **来源**: [RustBelt Project](https://plv.mpi-sws.org/rustbelt/) · [Iris Project](https://iris-project.org/) · [Aeneas](https://github.com/AeneasVerif/aeneas) · [Flux](https://flux-rs.github.io/flux/)

---

## 二、形式化属性矩阵

| 类型论概念 | Rust 工程机制 | 形式化含义 | 权威来源 |
|:---|:---|:---|:---|
| 仿射类型 | `let t = s;` 后 `s` 失效 | 独占资源不可复制 | Wadler 1990 |
| 线性/共享 | `&T` vs `&mut T` | 只读共享 vs 独占借用 | Rust Reference |
| System Fω | 泛型、`trait Assoc` | ∀ 量化与类型构造子 | Pierce 2002 |
| 依赖类型 | `const N: usize` | 值进入类型 | Rust const generics |
| 区域/模态 | 生命周期 `'a` | 引用有效范围约束 | Rust Distilled 2018 |
| Curry-Howard | `()` / `!` / `fn` / `enum` | 命题与证明同构 | Howard 1980 |
| 类型级计算 | trait 关联类型递归 | 编译期图灵完备片段 | Rust Reference |

---

## 三、正向示例

### 示例 1：仿射资源与独占借用

```rust
fn consume(s: String) -> usize {
    s.len()
}

fn main() {
    let s = String::from("exclusive");
    let n = consume(s); // own(String) 被 consume 消费
    println!("length = {}", n);
}
```

### 示例 2：生命周期子类型

```rust
fn choose<'a, 'b: 'a>(x: &'a i32, y: &'b i32) -> &'a i32 {
    if *x > *y { x } else { y }
}

fn main() {
    let a = 1;
    let b = 2;
    let r = choose(&a, &b);
    println!("{}", r);
}
```

### 示例 3：Curry-Howard 的「假 ⇒ 任意命题」

```rust
enum Void {}

fn ex_falso<T>(x: Void) -> T {
    match x {}
}

fn main() {}
```

---

## 四、反例与边界测试

### 反例 1：仿射资源被二次使用（E0382）

```rust,compile_fail,E0382
fn main() {
    let s = String::from("affine");
    let t = s;
    println!("{}", s);
}
```

> **错误诊断**: `error[E0382]: borrow of moved value: s`。
> **修正**: 使用 `clone()` 共享数据，或使用引用 `&s`。
> **反推**: 若出现 E0382 ⟸ 检查是否把独占资源当作 `Copy` 类型使用。

### 反例 2：生命周期不足导致悬垂引用（E0106 / E0597）

```rust,compile_fail,E0106
fn dangling() -> &i32 {
    let x = 42;
    &x
}

fn main() {
    let r = dangling();
    println!("{}", r);
}
```

> **错误诊断**: `error[E0106]: missing lifetime specifier`（后续展开才会出现 E0597）。
> **修正**: 返回 owned 值，或将生命周期与输入参数绑定。

### 反例 3：生命周期选择不满足子类型

```rust,compile_fail
fn choose<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 {
    if *x > *y { x } else { y }
}

fn main() {
    let a = 1;
    let b = 2;
    let r = choose(&a, &b);
    println!("{}", r);
}
```

> **错误诊断**: `error: lifetime may not live long enough`（返回 `'b` 数据但要求 `'a`）。
> **修正**: 添加 `'b: 'a` 约束。

---

## 五、反命题决策树

### 命题：「Rust 类型系统可以阻止所有运行时错误」

```text
该命题成立吗？
├── 是 → 错误。Rust 类型系统保证内存安全与数据竞争自由，但不保证：
│   ├── 逻辑错误（如 1 + 1 = 3）
│   ├── 死锁、活锁
│   ├── 资源泄漏（除非使用 RAII 封装）
│   └── 业务规则违反
└── 否 → 正确。类型系统只保证**类型安全**语义子集内的属性。
```

### 命题：「Rust 类型系统是线性类型系统」

```text
该命题成立吗？
├── 是 → 不完全。Rust 是**仿射（affine）**而非严格线性：
│   └── 资源可以被 drop，不要求必须被使用。
└── 否 → 更准确。`&mut T` 的行为接近线性资源，但 `Copy` 类型与 `&T`
    允许共享，突破了纯线性逻辑。
```

---

## 六、嵌入式测验（Embedded Quiz）

### 测验 1：Rust 的所有权系统最接近哪种类型系统？

A. 简单类型 λ 演算（λ→）
B. 线性类型系统
C. 仿射类型系统
D. 依赖类型系统

<details>
<summary>✅ 答案</summary>

**C. 仿射类型系统**。Rust 允许资源被静默丢弃（drop），这是仿射类型的特征；严格线性类型要求资源必须被使用。

</details>

### 测验 2：生命周期 `'a: 'b` 的最合适形式化解释是？

A. 类型 `'a` 是 `'b` 的子类型
B. 区域 `'a` 包含区域 `'b`
C. `'a` 比 `'b` 短
D. `'a` 和 `'b` 必须相等

<details>
<summary>✅ 答案</summary>

**B. 区域 `'a` 包含区域 `'b`**。`'a: 'b` 表示 `'a` 至少和 `'b` 一样长，即 `'a` 对应的区域包含 `'b` 对应的区域。

</details>

### 测验 3：`enum Either<A, B>` 在 Curry-Howard 中对应什么逻辑连接词？

A. 合取 ∧
B. 析取 ∨
C. 蕴含 ⇒
D. 否定 ¬

<details>
<summary>✅ 答案</summary>

**B. 析取 ∨**。`Either<A, B>` 要么是 `A` 的证明，要么是 `B` 的证明，对应逻辑析取。

</details>

---

## 七、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Pierce 2002, *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 一级 | 类型系统与 System Fω 标准教材 |
| [Cardelli & Wegner 1985, *On Understanding Types*](https://dl.acm.org/doi/10.1145/6041.6042) | ✅ 一级 | 多态与类型系统分类奠基 |
| [Barendregt 1991, *Introduction to Generalized Type Systems*](https://doi.org/10.1016/0304-3975(91)90167-B) | ✅ 一级 | λ 立方与依赖类型框架 |
| [Wadler 1990, *Linear Types can Change the World!*](https://homepages.inf.ed.ac.uk/wadler/papers/lineartypes/lineartypes.pdf) | ✅ 一级 | 线性/仿射类型资源视角 |
| [Weiss, Patterson & Ahmed 2018, *Rust Distilled*](https://arxiv.org/abs/1806.02693) | ✅ 一级 | Rust 类型系统形式化语义塔 |
| [Jung et al. 2018, RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | ✅ 一级 | Rust unsafe 的 Iris 机械证明 |
| [Iris Project](https://iris-project.org/) | ✅ 一级 | 高阶并发分离逻辑框架 |
| [Rust Reference — Type System](https://doc.rust-lang.org/reference/type-system.html) | ✅ P0 | Rust 官方类型系统参考 |

---

## 八、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((类型论与 Rust))
    类型系统作为计算模型
      判断 Γ; Σ ⊢ e : τ
      状态空间裁剪
      编译期约束求解
    仿射/线性资源
      own τ
      &mut T 独占
      &T 共享复制
      drop 允许
    System Fω
      ∀α.τ 泛型
      类型构造子
      GAT 受限高阶类型
    生命周期
      区域约束
      协变子类型
      模态/Kripke 解释
    Curry-Howard
      () = ⊤
      ! = ⊥
      fn = ⇒
      enum = ∨
      struct = ∧
    类型级计算
      Peano 类型算术
      const generics
      trait 递归深度上限
    机械证明
      Iris
      RustBelt
      Aeneas
      Flux
```
