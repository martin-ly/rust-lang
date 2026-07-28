# Flux：Rust 的 Liquid 细化类型

> **EN**: Flux: Liquid Refinement Types for Rust
> **Summary**: Flux is a research refinement-type checker for Rust that layers liquid refinements on top of Rust's ownership types to verify array bounds, integer properties, and container invariants at compile time with SMT-backed inference.
> **Rust 版本**: nightly toolchain pinned by Flux (stable Rust 1.97.0 不支持)
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **受众**: [研究者]
> **内容分级**: [综述级]
> **前置概念**: [Dependent Types and Refinement Types](10_dependent_refinement_types.md) · [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Generics](../../02_intermediate/01_generics/01_generics.md)
> **后置概念**: [Modern Verification Tools](../04_model_checking/04_modern_verification_tools.md) · [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md)
> **主要来源**: [Flux GitHub](https://github.com/flux-rs/flux) · [Flux Documentation](https://flux-rs.github.io/flux/) · [Lehmann et al., PLDI 2023 — Flux: Liquid Types for Rust](https://ranjitjhala.github.io/static/flux-pldi23.pdf) · [Lehmann et al., OOPSLA 2022 — Flux: Liquid Types for Rust](https://arxiv.org/pdf/2207.04034.pdf)

---

> **声明**: 本页使用形式化符号辅助直觉理解，所呈现的“定理/规则/推论”为**教学类比**，非经机器验证的严格数学证明。Flux 是一个研究原型；其语法、支持的 Rust 子集和安装方式以 [Flux 官方仓库](https://github.com/flux-rs/flux) 与 [Flux 文档](https://flux-rs.github.io/flux/) 为准。

---

## 🧠 知识结构图

```mermaid
mindmap
  root((Flux Liquid 细化类型))
    核心机制
      索引类型 i32[n]
      细化参数 @n
      存在类型 i32{v: v > 0}
      SMT 后端 Z3
    所有权集成
      独占所有权强更新
      &mut T 弱更新
      &strg T 强引用
      ensures 子句
    证明能力
      数组边界
      整数溢出
      向量长度
      元素级不变量
    限制与状态
      nightly rustc 必需
      仅 safe Rust
      不可判定谓词受限
      研究原型
    工具对比
      依赖类型
      Verus Kani Creusot
      Liquid Haskell
```

## 📑 目录

- [Flux：Rust 的 Liquid 细化类型](#fluxrust-的-liquid-细化类型)
  - [🧠 知识结构图](#-知识结构图)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 Flux 是什么](#11-flux-是什么)
    - [1.2 索引类型：把值放进类型](#12-索引类型把值放进类型)
    - [1.3 细化参数：`@n` 与幽灵变量](#13-细化参数n-与幽灵变量)
    - [1.4 存在类型：用谓词约束值的集合](#14-存在类型用谓词约束值的集合)
  - [二、注解语法与所有权集成](#二注解语法与所有权集成)
    - [2.1 函数签名注解 `#[flux::sig(...)]`](#21-函数签名注解-fluxsig)
    - [2.2 `#[flux::spec(...)]` 与 `flux-rs` 宏](#22-fluxspec-与-flux-rs-宏)
    - [2.3 独占所有权与强更新](#23-独占所有权与强更新)
    - [2.4 可变引用 `&mut T`：弱更新](#24-可变引用-mut-t-弱更新)
    - [2.5 强引用 `&strg T` 与 `ensures`](#25-强引用-strg-t-与-ensures)
    - [2.6 自定义类型：`refined_by` 与 `variant`](#26-自定义类型refined_by-与-variant)
  - [三、可验证性质与典型示例](#三可验证性质与典型示例)
    - [3.1 数组/向量边界](#31-数组向量边界)
    - [3.2 整数溢出与非零约束](#32-整数溢出与非零约束)
    - [3.3 容器元素级不变量](#33-容器元素级不变量)
    - [3.4 递归数据结构：带长度的链表](#34-递归数据结构带长度的链表)
  - [四、当前状态与限制](#四当前状态与限制)
  - [五、与相关技术的对比](#五与相关技术的对比)
    - [5.1 Flux vs Rust 原生类型系统](#51-flux-vs-rust-原生类型系统)
    - [5.2 Flux vs 依赖类型](#52-flux-vs-依赖类型)
    - [5.3 Flux vs Verus / Kani / Creusot](#53-flux-vs-verus--kani--creusot)
    - [5.4 Flux vs Liquid Haskell](#54-flux-vs-liquid-haskell)
  - [六、反例与边界](#六反例与边界)
    - [6.1 反例：Flux 不验证 unsafe 代码](#61-反例flux-不验证-unsafe-代码)
    - [6.2 反例： Flux 不能表达任意归纳性质](#62-反例-flux-不能表达任意归纳性质)
    - [6.3 反例：细化谓词超出 SMT 片段会失败](#63-反例细化谓词超出-smt-片段会失败)
    - [6.4 反例：需要 nightly 工具链](#64-反例需要-nightly-工具链)
  - [七、来源与延伸阅读](#七来源与延伸阅读)
  - [对应测验](#对应测验)

---

## 一、核心概念

### 1.1 Flux 是什么

**Flux** 是 UC San Diego 开发的一个 Rust 编译器插件，它在 Rust 类型系统之上增加**细化类型（refinement types）**，并在编译期用 SMT 求解器自动验证这些细化约束。与把 Rust 改写成依赖类型语言不同，Flux 通过注解（attributes）把逻辑谓词附加到现有 Rust 类型上，不改变 Rust 的核心类型规则或运行时语义。

> **[Flux 官方文档](https://flux-rs.github.io/flux/)**: Flux is a refinement type checker plugin for Rust that lets you specify a range of correctness properties and have them be verified at compile time.

Flux 的核心设计直觉是：**利用 Rust 的所有权机制解决命令式/堆内存设置下细化类型的别名和可变性问题**。传统上，细化类型在纯函数式语言（如 Liquid Haskell）中工作良好，因为值不会被修改；而在有可变引用和别名的命令式语言中，一个位置的值改变会影响所有指向它的引用。Flux 的做法不是重新实现一套别名/借用检查，而是把 Rust 已经提供的所有权保证当作前提：

- 独占所有权（exclusive ownership） ⇒ 可以做**强更新（strong update）**，即更新后该位置的细化类型可以改变；
- 共享引用（`&T`） ⇒ 只能读取，不能改变类型；
- 可变引用（`&mut T`） ⇒ 借用期间类型不变（弱更新），从而保证引用归还后原变量仍满足原不变量；
- 强引用（`&strg T`，Flux 扩展） ⇒ 借用期间允许强更新，函数返回后原位置的细化类型按 `ensures` 子句改变。

### 1.2 索引类型：把值放进类型

Flux 的**索引类型（indexed type）**在 Rust 基础类型上附加一个细化值。例如 `i32[n]` 表示“恰好等于 `n` 的 32 位有符号整数”，`bool[b]` 表示“恰好等于布尔值 `b` 的布尔量”。

```rust,ignore
// Flux 可以验证 1 + 2 + 3 的类型为 i32[6]
// 以及 1 + 2 + 3 <= 10 的类型为 bool[true]
```

索引不一定表示单例。`RVec<T>[n]` 表示长度为 `n` 的可增长向量（`RVec` 是 Flux 提供的细化向量类型）。二维矩阵可以有两个索引，如 `Matrix<T>[r][c]`。

### 1.3 细化参数：`@n` 与幽灵变量

函数签名可以用 `@n` 引入**细化参数（refinement parameter）**。这些参数只存在于验证逻辑中，不生成运行时代码，类似幽灵变量（ghost variables）。Flux 在调用点根据实参自动实例化它们。

```rust,ignore
#[flux::sig(fn(i32[@n]) -> bool[n > 0])]
fn is_pos(n: i32) -> bool {
    n > 0
}
```

这里 `i32[@n]` 把输入值绑定到逻辑变量 `n`，返回类型 `bool[n > 0]` 表示返回的布尔值等于谓词 `n > 0` 的真值。

### 1.4 存在类型：用谓词约束值的集合

当只知道值满足某个谓词而不知其精确值时，使用**存在类型（existential type）** `{v. B[v] | p}`，通常简写为 `B{v: p}`。

```rust,ignore
// 正整数
i32{v: v > 0}

// 非空向量
RVec<T>{v: v > 0}

// nat 是 i32{v: v >= 0} 的缩写
```

例如 `abs` 函数可以说明返回值非负且绝对值不小于输入：

```rust,ignore
#[flux::sig(fn(x: i32) -> i32{v: v >= 0 && v >= x})]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

> **注意**: 上面的 `abs` 在 `x == i32::MIN` 时可能溢出。Flux 可以在启用溢出检查时拒绝这类实现；为简短起见，部分论文示例假设运行时溢出检查已开启。

---

## 二、注解语法与所有权集成

### 2.1 函数签名注解 `#[flux::sig(...)]`

Flux 最核心的注解是 `#[flux::sig(...)]`，它把普通 Rust 函数签名改写成细化签名。典型模式：

```rust,ignore
#[flux::sig(fn(x: i32[@n]) -> bool[n > 0])]
fn is_pos(n: i32) -> bool { ... }
```

当直接用 `flux` 命令检查单文件时，使用 `#[flux::sig(...)]` 或 `#[flux::spec(...)]`；在 Cargo 项目中通过 `flux-rs` crate 导入时，可以使用 `#[sig(...)]` / `#[spec(...)]`。

### 2.2 `#[flux::spec(...)]` 与 `flux-rs` 宏

根据 [Flux 安装文档](https://flux-rs.github.io/flux/guide/install.html)，Cargo 项目依赖 `flux-rs` 后：

```rust,ignore
use flux_rs::attrs::*;

#[spec(fn(x: i32) -> i32{v: x < v})]
fn inc(x: i32) -> i32 {
    x + 1
}
```

单文件模式下则写：

```rust,ignore
#[flux::spec(fn(x: i32) -> i32{v: x < v})]
pub fn inc(x: i32) -> i32 {
    x + 1
}
```

文档中的 `spec` 宏与论文中的 `sig` 宏在功能上对应：都用于把细化签名附加到 Rust 函数。

### 2.3 独占所有权与强更新

当一个值被唯一拥有时，Flux 允许**强更新**——更新后该变量可以拥有不同的细化类型。

```rust,ignore
fn strong_update_demo() {
    let mut x = 0;        // x: i32[0]
    x += 1;               // x: i32[1]
    x *= 2;               // x: i32[2]
    // Flux 可以静态验证 x 现在等于 2
}
```

### 2.4 可变引用 `&mut T`：弱更新

Rust 的 `&mut T` 保证在借用期间没有其他别名可以访问该位置。Flux 利用这一点：通过 `&mut T` 修改值时，**类型 `T` 本身不能改变**，只能做弱更新。这确保引用归还后原变量仍满足原不变量。

```rust,ignore
#[flux::sig(fn(x: &mut i32{v: v >= 0}))]
fn decr(x: &mut i32) {
    if *x > 0 {
        *x -= 1;        // 仅在 x > 0 时减一，保持 x >= 0
    }
}
```

输入类型 `&mut i32{v: v >= 0}` 对函数施加了义务：任何通过 `x` 的修改都必须保持该位置仍为非负整数。由于 `&mut` 是弱更新，函数返回后调用者知道原变量仍然 `>= 0`。

### 2.5 强引用 `&strg T` 与 `ensures`

有时需要把值借给函数，让函数在返回时改变其细化类型。Flux 引入**强引用** `&strg T`，并用 `ensures *x: ...` 指定返回后该位置的类型。

```rust,ignore
#[flux::sig(fn(x: &strg i32[@n]) ensures *x: i32[n + 1])]
fn incr(x: &mut i32) {
    *x += 1;
}

fn client() {
    let mut x = 1;       // x: i32[1]
    incr(&mut x);        // 调用后 x: i32[2]
}
```

`&strg` 在运行时就是普通的 `&mut`，但 Flux 在类型层面允许它改变索引。

### 2.6 自定义类型：`refined_by` 与 `variant`

自定义类型可以用 `#[flux::refined_by(...)]` 声明索引，用 `#[flux::variant(...)]` 为每个构造子声明细化签名。

```rust,ignore
#[flux::refined_by(len: int)]
enum List<T> {
    #[flux::variant(List<T>[0])]
    Nil,
    #[flux::variant((T, Box<List<T>[@n]>) -> List<T>[n + 1])]
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    #[flux::sig(fn(self: &strg List<T>[@n], other: List<T>[@m])
                 ensures *self: List<T>[n + m])]
    fn append(&mut self, other: List<T>) {
        match self {
            List::Cons(_, tl) => tl.append(other),
            List::Nil => *self = other,
        }
    }
}
```

这个例子展示了：

1. `List<T>` 被索引为长度 `len`；
2. `Nil` 构造长度为 `0` 的列表；
3. `Cons` 接受一个元素和一个长度为 `n` 的列表，返回长度为 `n + 1` 的列表；
4. `append` 通过强引用把第一个列表的长度从 `n` 更新为 `n + m`。

---

## 三、可验证性质与典型示例

### 3.1 数组/向量边界

数组越界是 Rust 中常见的 panic 来源。Flux 可以把索引约束进类型，从而把越界错误转化为编译期类型错误。

```rust,ignore
#[flux::sig(fn(vec: &RVec<i32>[@n], idx: usize{idx < n}) -> &i32)]
fn safe_get(vec: &RVec<i32>, idx: usize) -> &i32 {
    vec.get(idx)          // Flux 保证 idx 在 [0, n) 内
}
```

`RVec<T>[@n]` 表示长度为 `n` 的向量，`usize{idx < n}` 表示小于 `n` 的索引。任何传入 `idx >= n` 的调用都会在 Flux 检查时报错。

### 3.2 整数溢出与非零约束

Flux 可以把“非零”“非负”“有界”等约束编码进类型。

```rust,ignore
#[flux::sig(fn(x: i32, y: i32{v: v != 0}) -> i32)]
fn safe_div(x: i32, y: i32) -> i32 {
    x / y                 // Flux 保证 y 不为零
}
```

在启用溢出检查选项时，Flux 还能验证某些加减乘不会溢出。

### 3.3 容器元素级不变量

Flux 通过多态实例化把元素级约束传播到整个容器。

```rust,ignore
// 所有元素都为正的整数向量
#[flux::sig(fn() -> RVec<i32{v: v > 0}>)]
fn positives() -> RVec<i32> {
    let mut v = RVec::new();
    v.push(1);
    v.push(2);
    v
}

// 长度为 n 的浮点向量
#[flux::sig(fn(n: usize[@n]) -> RVec<f32>[n])]
fn init_zeros(n: usize) -> RVec<f32> {
    let mut vec = RVec::new();
    let mut i = 0;
    while i < n {
        vec.push(0.0);
        i += 1;
    }
    vec
}
```

`RVec<RVec<f32>[n]>[k]` 可以紧凑地表示“`k` 个中心点，每个中心点都是 `n` 维向量”。在程序逻辑方法中，这通常需要手写全称量化的循环不变量；Flux 的细化类型通过类型多态自动推断这类量化的容器不变量。

### 3.4 递归数据结构：带长度的链表

见 §2.6 的 `List<T>` 示例。通过 `refined_by` 和 `variant`，Flux 支持用户自定义的递归类型，并把长度、高度、大小等度量索引进类型。

---

## 四、当前状态与限制

Flux 截至 2025–2026 年仍处于**研究原型**阶段，使用前需要了解以下限制：

1. **需要 nightly Rust**: Flux 是 rustc 驱动插件，必须安装其 `rust-toolchain.toml` 指定的 nightly 版本，不能直接在 stable Rust 1.97.0 上运行。
2. **仅支持 safe Rust**: Flux 的形式化基础是 Rust 的 safe 子集，不验证 `unsafe` 块内的内存布局、裸指针、FFI 等。
3. **细化逻辑片段受限**: 为保证 SMT 自动求解，细化谓词被限制在可判定片段（量词受限的线性算术、未解释函数、集合/映射操作等）。超出该片段的谓词可能导致验证失败或超时。
4. **API 不稳定**: 属性宏名、语法、支持的 Rust 子集都可能随版本变化。
5. **编译时间开销**: 作为外部验证层，Flux 检查显著慢于普通 `cargo check`。
6. **深度功能正确性有限**: Flux 适合轻量、普遍的属性（边界、长度、非零、元素级不变量）。对于排序、复杂协议状态机、完整功能正确性，程序逻辑工具（Verus、Creusot）或证明助手通常更合适。

> **[Flux GitHub](https://github.com/flux-rs/flux)**: Flux is a refinement type checker for Rust. (Experimental / research)

---

## 五、与相关技术的对比

### 5.1 Flux vs Rust 原生类型系统

Rust 的原生类型系统通过所有权、借用、生命周期在编译期排除 use-after-free、double-free 和数据竞争，但不验证任意数值谓词。

| 能力 | Rust 原生 | Flux |
|:---|:---|:---|
| 内存安全 + 数据竞争自由 | ✅ | ✅（继承 Rust） |
| 数组索引越界 | ❌（运行时 panic） | ✅（编译期拒绝） |
| 整数溢出 | ⚠️（debug panic / release wrap） | ✅（可静态验证部分场景） |
| 除零 | ❌（运行时 panic） | ✅（编译期拒绝） |
| 向量长度约束 | ❌ | ✅ |

Flux 不是替代 Rust 类型系统，而是**在其上叠加验证层**。

### 5.2 Flux vs 依赖类型

依赖类型（Idris、Agda、Coq/Lean）允许任意值进入类型，并把类型检查与定理证明统一。Flux 的细化类型是依赖类型的一个**受限、自动化子集**。

| 维度 | 依赖类型 | Flux |
|:---|:---|:---|
| 值进类型 | ✅ 任意值 | ⚠️ 仅索引/谓词 |
| 自动验证 | 部分/交互式 | ✅ SMT 自动 |
| 证明义务 | 可能需要人工 | 通常无（谓词在可判定片段） |
| 运行时影响 | 可能需要携带证据 | 零开销（细化擦除） |
| 学习曲线 | 陡峭 | 相对平缓 |

### 5.3 Flux vs Verus / Kani / Creusot

| 工具 | 方法 | 最适合 | 对比 Flux |
|:---|:---|:---|:---|
| **Verus** | SMT + `requires/ensures/invariant` | 系统代码、并发、数据结构 | 表达能力更强，但需要更多规范 |
| **Kani** | 有界模型检查 | unsafe 代码、协议 | 可验证 unsafe，但有界；无需写谓词 |
| **Creusot** | Why3/WhyML 演绎验证 | 任意功能正确性 | 可处理复杂归纳证明，规范更重 |
| **Flux** | 细化类型 + 液体推断 | 轻量边界/长度/元素不变量 | 注解最少，自动推断循环不变量 |

### 5.4 Flux vs Liquid Haskell

Liquid Haskell 通过注释为 Haskell 添加细化类型，不改变 GHC 核心类型系统。Flux 与 Liquid Haskell 技术路线相似，但关键差异在于处理**命令式更新和别名**：

- Liquid Haskell 面向纯函数式代码，没有可变引用；
- Flux 利用 Rust 的所有权机制，把强更新、弱更新、强引用等形式化地整合进细化类型系统。

因此 Flux 可以验证向量 `push`、`append` 等会改变堆状态的命令式代码，而 Liquid Haskell 通常处理不可变数据结构。

---

## 六、反例与边界

### 6.1 反例：Flux 不验证 unsafe 代码

```rust,ignore
#[flux::sig(fn(*const i32) -> i32)]
unsafe fn deref_raw(ptr: *const i32) -> i32 {
    *ptr  // Flux 无法验证 ptr 是否有效、是否对齐
}
```

> **修正**: Flux 的形式化基础是 safe Rust。对于 `unsafe` 块、裸指针、FFI，需要使用 Kani（有界模型检查）、Miri（动态检测）或 Verus（带内存模型的演绎验证）。

### 6.2 反例： Flux 不能表达任意归纳性质

```rust,ignore
// Flux 无法直接证明“列表已排序”这类需要任意归纳推理的性质
#[flux::sig(fn(&RVec<i32>) -> bool)]
fn is_sorted(_vec: &RVec<i32>) -> bool {
    todo!()
}
```

> **修正**: 排序、复杂状态机等功能正确性需要程序逻辑或证明助手。Prusti、Creusot、Verus 可以表达这类性质，但规范负担更重。

### 6.3 反例：细化谓词超出 SMT 片段会失败

```rust,ignore
// 涉及非线性算术、量词或复杂数据结构的谓词可能无法自动求解
#[flux::sig(fn(n: i32) -> i32{v: v * v == n})]
fn sqrt(n: i32) -> i32 {
    todo!()
}
```

> **修正**: Flux 的自动化基于可判定逻辑片段。超出该范围的谓词会导致 SMT 超时或需要用户介入。

### 6.4 反例：需要 nightly 工具链

```text
# 在 stable Rust 1.97.0 上无法安装 Flux
$ cargo install --git https://github.com/flux-rs/flux
error: Flux requires a nightly rustc toolchain pinned in rust-toolchain.toml
```

> **修正**: Flux 是 rustc 驱动插件，依赖编译器内部 API，因此必须使用项目指定的 nightly 工具链。这限制了它在生产 CI 中的直接使用。

---

## 七、来源与延伸阅读

### 权威来源

- [Flux GitHub](https://github.com/flux-rs/flux)
- [Flux 官方文档](https://flux-rs.github.io/flux/)
- [Flux 在线演示](https://flux-rs.github.io/flux/playground.html)
- [Flux Demo 仓库](https://github.com/flux-rs/flux-demo)

### 关键论文

- Lehmann, N., Geller, A. T., Vazou, N., & Jhala, R. (2023). *Flux: Liquid Types for Rust*. Proc. ACM Program. Lang., 7, PLDI, Article 169. [PDF](https://ranjitjhala.github.io/static/flux-pldi23.pdf)
- Lehmann, N., Geller, A., Vazou, N., & Jhala, R. (2022). *Flux: Liquid Types for Rust*. arXiv:2207.04034. [PDF](https://arxiv.org/pdf/2207.04034.pdf)
- Lehmann, N., et al. (2025). *Generic Refinement Types*. POPL 2025. [ACM DL](https://dl.acm.org/doi/10.1145/3704886)

### 相关概念页

- [Dependent Types and Refinement Types](10_dependent_refinement_types.md)
- [Modern Verification Tools](../04_model_checking/04_modern_verification_tools.md)
- [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md)
- [Kani：Rust 有界模型检查器](../04_model_checking/09_kani.md)
- [Miri：Rust 未定义行为动态检测器](../04_model_checking/08_miri.md)

---

> **最后更新**: 2026-07-28
> **维护者注意**: Flux 是活跃研究项目，语法与支持 Rust 子集可能快速变化；请以 [Flux GitHub](https://github.com/flux-rs/flux) 与 [Flux 文档](https://flux-rs.github.io/flux/) 为最新事实源。

---

## 对应测验

完成 [L3 语义模型与跨语言对比测验](../../03_advanced/00_concurrency/10_quiz_semantic_models.md) 验证对依赖/细化类型、语言语义模型矩阵的掌握程度。
