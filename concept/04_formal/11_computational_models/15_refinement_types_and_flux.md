> **内容分级**: [专家级]

# 精化类型与 Flux：作为计算模型的约束演算（Refinement Types and Flux: Constraint Calculus as a Computational Model）

> **EN**: Refinement Types and Flux: Constraint Calculus as a Computational Model
> **Summary**: Treats refinement types as a computational model for Rust's value-level constraints, mapping dependent refinements, liquid types, strong/weak updates, and ownership-aware verification to Flux's SMT-backed type system and its integration with Rust's ownership discipline.

> **Rust 版本**: 1.97.0+ (Edition 2024)；Flux 需 nightly toolchain
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**计算模型**视角把精化类型当作 Rust 类型系统的**约束扩展**：说明如何在现有类型上叠加逻辑谓词，把「值满足某性质」编码为类型，并说明 Flux 如何利用 Rust 所有权解决命令式语言中精化类型的别名/可变性问题，与 [Effect Handlers and Rust Limited Effects](14_effect_handlers_and_rust_limited_effects.md) 形成「效应模型 → 约束模型」的递进。
> **前置概念**:
> [Dependent Types and Refinement Types](../00_type_theory/10_dependent_refinement_types.md) ·
> [Flux](../00_type_theory/14_flux.md) ·
> [Type Theory and Rust](07_type_theory_and_rust.md) ·
> [Linear Logic and Ownership](12_linear_logic_and_ownership.md)
> **后置概念**:
> [RustBelt Ownership Logic](16_rustbelt_ownership_logic.md) ·
> [Aeneas Verification Pipeline](17_aeneas_verification_pipeline.md) ·
> [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) ·
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md)

---

## 📑 目录

- [精化类型与 Flux：作为计算模型的约束演算（Refinement Types and Flux: Constraint Calculus as a Computational Model）](#精化类型与-flux作为计算模型的约束演算refinement-types-and-flux-constraint-calculus-as-a-computational-model)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 精化类型作为计算模型](#11-精化类型作为计算模型)
    - [1.2 精化类型的形式化语法](#12-精化类型的形式化语法)
    - [1.3 Liquid Types 与 SMT 后端](#13-liquid-types-与-smt-后端)
    - [1.4 Flux 的所有权感知精化](#14-flux-的所有权感知精化)
    - [1.5 强更新与弱更新](#15-强更新与弱更新)
    - [1.6 索引类型与存在类型](#16-索引类型与存在类型)
    - [1.7 精化类型作为霍尔逻辑的轻量版](#17-精化类型作为霍尔逻辑的轻量版)
  - [二、形式化属性矩阵](#二形式化属性矩阵)
  - [三、正向示例](#三正向示例)
    - [示例 1：数组边界安全](#示例-1数组边界安全)
    - [示例 2：非空向量保证](#示例-2非空向量保证)
    - [示例 3：单调计数器](#示例-3单调计数器)
  - [四、反例与边界测试](#四反例与边界测试)
    - [反例 1：超出 SMT 片段的谓词](#反例-1超出-smt-片段的谓词)
    - [反例 2：unsafe 代码不被 Flux 验证](#反例-2unsafe-代码不被-flux-验证)
    - [反例 3：强更新与可变引用的冲突](#反例-3强更新与可变引用的冲突)
  - [五、反命题决策树](#五反命题决策树)
    - [命题：「精化类型等于依赖类型」](#命题精化类型等于依赖类型)
    - [命题：「Flux 能验证所有 Rust 程序」](#命题flux-能验证所有-rust-程序)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
    - [测验 1：精化类型 `{v: i32 | v > 0}` 表示什么？](#测验-1精化类型-v-i32--v--0-表示什么)
    - [测验 2：Flux 的 `&strg T` 强引用允许什么？](#测验-2flux-的-strg-t-强引用允许什么)
    - [测验 3：Flux 为什么不能验证 unsafe 代码？](#测验-3flux-为什么不能验证-unsafe-代码)
  - [七、权威来源 / International Authority References](#七权威来源--international-authority-references)
  - [八、🧭 思维导图（Mindmap）](#八-思维导图mindmap)

---

## 一、核心概念

### 1.1 精化类型作为计算模型

精化类型（Refinement Types）是一种**把逻辑谓词附加到类型**的类型系统扩展。与传统类型系统只回答「x 是 i32」不同，精化类型回答「x 是大于 0 的 i32」。从计算模型视角，它把程序验证的一部分从运行时测试前移到编译期，把「值满足某性质」编码为类型判断。

```text
精化类型作为计算模型
├── 基础类型 B: i32, bool, ...
├── 精化类型 {v: B | φ(v)}: 满足谓词 φ 的 B 值
├── 函数类型 (x: {v | φ}) -> {v | ψ}: 输入满足 φ 则输出满足 ψ
├── 索引类型 B[i]: 把值作为类型索引（如 i32[n]）
└── SMT 求解器: 自动验证谓词的可满足性
```

Rust 的原生类型系统不直接支持精化类型，但 **Flux** 在 Rust 之上实现了精化类型检查，并与 Rust 的所有权机制深度集成。

> **来源**: [Freeman & Pfenning 1991, *Refinement Types for ML*](https://doi.org/10.1145/115865.115880) · [Rondon, Kawaguchi & Jhala 2008, *Liquid Types*](https://doi.org/10.1145/1375581.1375602)

---

### 1.2 精化类型的形式化语法

一个典型的精化类型可以写成：

```text
{x: τ | P(x)}
```

表示「类型为 τ 且满足谓词 P 的所有值 x」。例如：

```text
{v: i32 | v > 0}        正整数
{v: i32 | v >= 0}       自然数
{v: Vec<i32> | v.len() > 0}  非空向量
```

函数签名则表示为前置条件与后置条件：

```text
f : (x: {v: i32 | v > 0}) -> {v: i32 | v > x}
```

读作：「如果输入是正整数，输出是大于输入的整数」。

---

### 1.3 Liquid Types 与 SMT 后端

**Liquid Types** 是精化类型的一个自动推断变体，由 Rondon、Kawaguchi 和 Jhala 提出。其核心思想：

1. 程序员提供**限定谓词模板**（qualifiers）。
2. 类型检查器通过**SMT 求解器**（如 Z3）自动推断满足这些模板的最强/最弱谓词。
3. 验证过程归结为**约束求解**：每个程序点生成一组逻辑约束，SMT 检查其可满足性。

```text
Liquid Types 流程
  源码 + 类型注解
    ↓
  生成 Horn 子句约束
    ↓
  SMT 求解器（Z3）
    ↓
  SAT → 验证通过
  UNSAT → 报告反例/失败位置
```

Flux 使用类似的 SMT 后端，但特别处理了 Rust 的**所有权、借用和内部可变性**。

> **来源**: [Rondon, Kawaguchi & Jhala 2008, *Liquid Types*](https://doi.org/10.1145/1375581.1375602) · [Vazou 2016, *Liquid Haskell*](https://doi.org/10.1145/2951913.2951916)

---

### 1.4 Flux 的所有权感知精化

Flux 的核心创新是**把 Rust 的所有权机制作为精化类型推理的前提**，从而解决命令式语言中精化类型的两个经典难题：

1. **别名问题**：多个引用指向同一内存，一个引用更新会影响其他引用的精化类型。
2. **可变性**：可变引用允许强更新，共享引用只允许只读观察。

Flux 的解决方案：

| Rust 所有权 | Flux 精化语义 |
|---|---|
| `let x = ...`（独占所有权） | 可以做**强更新**：`x` 的精化类型可以改变 |
| `&T`（共享引用） | 只能读取，精化类型保持不变 |
| `&mut T`（可变引用） | 借用期间精化类型不变（弱更新），归还后恢复原不变量 |
| `&strg T`（Flux 扩展） | 借用期间允许强更新，返回后按 `ensures` 更新原变量类型 |

```rust,ignore
// Flux 示例：强更新
#[flux::sig(fn(x: i32{v: v > 0}) -> i32{v: v > x})]
fn inc(x: i32) -> i32 {
    x + 1
}
```

> **来源**: [Lehmann et al., PLDI 2023 — Flux: Liquid Types for Rust](https://ranjitjhala.github.io/static/flux-pldi23.pdf) · [Lehmann et al., OOPSLA 2022 — Flux: Liquid Types for Rust](https://arxiv.org/pdf/2207.04034.pdf)

---

### 1.5 强更新与弱更新

在命令式程序验证中，**强更新**指赋值后变量的断言可以完全改变；**弱更新**指只能断言「新值满足某个不变量」，不能精确知道具体值。

```text
强更新:
  x: i32{5}
  x = 7
  x: i32{7}    ← 类型完全改变

弱更新:
  x: i32{v > 0}
  x += 1
  x: i32{v > 0}  ← 只知道仍为正
```

Flux 利用 Rust 所有权决定何时强更新：

```rust,ignore
#[flux::sig(fn(x: &strg i32, y: i32) ensures x: i32{v: v == y})]
fn set(x: &mut i32, y: i32) {
    *x = y;
}
```

这里 `&strg T` 是 Flux 引入的**强引用**，允许函数返回后更新原变量的精化类型。

---

### 1.6 索引类型与存在类型

Flux 支持两种核心精化类型构造：

**索引类型（Indexed Types）**：把值作为类型索引。

```rust,ignore
#[flux::sig(fn(x: i32[@n]) -> i32{v: v == n + 1})]
fn succ(n: i32) -> i32 {
    n + 1
}
```

**存在类型（Existential Types）**：只知道值满足某谓词，不知道具体值。

```rust,ignore
#[flux::sig(fn() -> i32{v: v > 0})]
fn one() -> i32 {
    1
}
```

索引类型用于**精确等量推理**，存在类型用于**抽象性质推理**。两者结合使 Flux 既能验证数组边界等具体属性，又能验证抽象不变量。

---

### 1.7 精化类型作为霍尔逻辑的轻量版

精化类型可以被看作**霍尔逻辑（Hoare Logic）的轻量、可自动化片段**：

| 霍尔逻辑 | 精化类型对应 |
|---|---|
| 前置条件 `{P} C` | 函数参数类型 `{v: τ | P(v)}` |
| 后置条件 `C {Q}` | 函数返回类型 `{v: τ | Q(v)}` |
| 循环不变量 | 递归/迭代中的类型不变量 |
| 框架规则 | 所有权保证的局部推理 |

Flux 的 `ensures` 子句直接对应霍尔逻辑的后置条件：

```rust,ignore
#[flux::sig(fn(x: &strg i32, y: i32) ensures x: i32{v: v == old(x) + y})]
fn add(x: &mut i32, y: i32) {
    *x += y;
}
```

不同的是，Flux 的验证是**完全自动化的**（SMT 驱动），而完整霍尔逻辑通常需要交互式证明助手。

---

## 二、形式化属性矩阵

| 精化类型概念 | Rust/Flux 工程机制 | 形式化含义 | 权威来源 |
|:---|:---|:---|:---|
| `{v: τ | φ}` | `i32{v: v > 0}` | 满足谓词的值集合 | Freeman & Pfenning 1991 |
| 索引类型 `τ[i]` | `i32[@n]` / `RVec<T>[n]` | 把值作为类型索引 | Liquid Types |
| 存在类型 | `i32{v: φ}` | 抽象性质 | Liquid Types |
| 前置条件 | 函数参数精化 | 霍尔逻辑前置 | Hoare Logic |
| 后置条件 | `ensures` / 返回类型精化 | 霍尔逻辑后置 | Hoare Logic |
| 强更新 | `&strg T` / 独占所有权 | 变量断言完全改变 | Flux PLDI 2023 |
| 弱更新 | `&mut T` | 借用期间不变量保持 | Flux PLDI 2023 |
| SMT 求解 | Z3 后端 | 自动约束求解 | Z3 |
| 别名处理 | Rust 借用检查 | 防止重叠可变引用 | RustBelt POPL 2018 |

---

## 三、正向示例

### 示例 1：数组边界安全

```rust,ignore
// Flux 可验证：索引 i 在向量长度内
#[flux::sig(fn(vec: &RVec<i32>, i: usize{i < vec.len()}) -> i32)]
fn get(vec: &RVec<i32>, i: usize) -> i32 {
    vec[i]
}
```

### 示例 2：非空向量保证

```rust,ignore
#[flux::sig(fn(vec: &RVec<i32>{v: v.len() > 0}) -> i32)]
fn first(vec: &RVec<i32>) -> i32 {
    vec[0] // Flux 保证不会越界
}
```

### 示例 3：单调计数器

```rust
struct Counter { value: i32 }

impl Counter {
    fn new() -> Self { Counter { value: 0 } }
    fn increment(&mut self) { self.value += 1; }
}

fn main() {
    let mut c = Counter::new();
    c.increment();
    c.increment();
    assert_eq!(c.value, 2);
}
```

> 注意：上面的 Rust 代码本身不携带精化类型。Flux 中可以进一步注解 `Counter` 的 `value` 永远非负，并在 `increment` 中保持单调性。

---

## 四、反例与边界测试

### 反例 1：超出 SMT 片段的谓词

```rust,ignore
// 假设 Flux 遇到非线性或量化的谓词
#[flux::sig(fn(x: i32) -> i32{v: forall y. y * y != v})]
fn impossible(x: i32) -> i32 {
    x
}
```

> **错误诊断**: Flux/SMT 无法验证任意高阶或量化谓词。SMT 求解器对非线性算术、高阶量词等片段的支持有限。
> **修正**: 限制谓词在 SMT 可判定的片段内（如线性算术、未解释函数、数组理论）。

### 反例 2：unsafe 代码不被 Flux 验证

```rust
fn main() {
    let mut x = 5;
    let r = &mut x as *mut i32;
    unsafe {
        *r = 42; // Flux 不分析 unsafe 块
    }
    assert_eq!(x, 42);
}
```

> **错误诊断**: Flux 仅验证 safe Rust 子集。`unsafe` 块内的指针操作、类型转换等不在 Flux 的分析范围内。
> **修正**: 把 unsafe 代码封装在安全抽象中，并对 safe 接口提供 Flux 规格；unsafe 内部依赖人工审计或其他工具（如 Miri、Kani）。

### 反例 3：强更新与可变引用的冲突

```rust,compile_fail,E0502
fn main() {
    let mut x = 5;
    let r1 = &x;
    let r2 = &mut x; // ❌ 共享引用与可变引用共存
    println!("{} {}", r1, r2);
}
```

> **错误诊断**: `error[E0502]: cannot borrow`x`as mutable because it is also borrowed as immutable`。Flux 依赖 Rust 借用检查器阻止这种别名冲突，否则无法安全地做强更新。
> **修正**: 确保在需要强更新时没有活跃的共享引用。

---

## 五、反命题决策树

### 命题：「精化类型等于依赖类型」

```text
该命题成立吗？
├── 是 → 不完全。两者都允许类型依赖于值：
│   ├── 精化类型：{v: τ | φ} 在已有类型上加谓词
│   └── 依赖类型：Vec A n 中 n 是类型的一部分
└── 否 → 更准确。精化类型是依赖类型的受限形式：
    ├── 基础类型固定，只添加谓词
    ├── 通常由 SMT 自动验证
    └── 表达能力弱于完整依赖类型，但更自动化
```

### 命题：「Flux 能验证所有 Rust 程序」

```text
该命题成立吗？
├── 是 → 错误。Flux 的限制包括：
│   ├── 仅支持 safe Rust 子集
│   ├── 需要 nightly 工具链
│   ├── 谓词必须在 SMT 可判定片段内
│   └── 不支持 unsafe、某些高级 trait、部分标准库
└── 否 → 正确。Flux 是研究原型，适合验证数组边界、整数性质、
    容器不变量等特定属性，不是通用程序验证器。
```

---

## 六、嵌入式测验（Embedded Quiz）

### 测验 1：精化类型 `{v: i32 | v > 0}` 表示什么？

A. 所有 i32 值
B. 所有大于 0 的 i32 值
C. 一个具体的 i32 值
D. 一个布尔类型

<details>
<summary>✅ 答案</summary>

**B. 所有大于 0 的 i32 值**。花括号内的 `v > 0` 是谓词，表示该类型包含所有满足此谓词的 i32 值。

</details>

### 测验 2：Flux 的 `&strg T` 强引用允许什么？

A. 任意复制引用
B. 借用期间强更新原变量的精化类型
C. 绕过 Rust 借用检查
D. 运行时类型检查

<details>
<summary>✅ 答案</summary>

**B. 借用期间强更新原变量的精化类型**。`&strg T` 是 Flux 的扩展，允许函数返回后按 `ensures` 改变原变量的精化类型。

</details>

### 测验 3：Flux 为什么不能验证 unsafe 代码？

A. Flux 不支持指针语义和非类型安全操作
B. unsafe 代码运行太快
C. Flux 只能验证函数式代码
D. unsafe 代码没有类型

<details>
<summary>✅ 答案</summary>

**A. Flux 不支持指针语义和非类型安全操作**。Flux 建立在 Rust 类型系统之上，unsafe 块打破了这些假设，因此不在 Flux 验证范围内。

</details>

---

## 七、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Freeman & Pfenning 1991, *Refinement Types for ML*](https://doi.org/10.1145/115865.115880) | ✅ 一级 | 精化类型奠基论文 |
| [Rondon, Kawaguchi & Jhala 2008, *Liquid Types*](https://doi.org/10.1145/1375581.1375602) | ✅ 一级 | Liquid Types 与自动推断 |
| [Vazou 2016, *Liquid Haskell*](https://doi.org/10.1145/2951913.2951916) | ✅ 一级 | Liquid Types 在 Haskell 中的实现 |
| [Lehmann et al., PLDI 2023 — Flux: Liquid Types for Rust](https://ranjitjhala.github.io/static/flux-pldi23.pdf) | ✅ 一级 | Flux 论文，所有权感知精化 |
| [Lehmann et al., OOPSLA 2022 — Flux: Liquid Types for Rust](https://arxiv.org/pdf/2207.04034.pdf) | ✅ 一级 | Flux 早期论文 |
| [Flux GitHub](https://github.com/flux-rs/flux) | ✅ P0 | Flux 官方仓库 |
| [Flux Documentation](https://flux-rs.github.io/flux/) | ✅ P0 | Flux 官方文档 |
| [Z3 Theorem Prover](https://github.com/Z3Prover/z3) | ✅ P2 | Flux 的 SMT 后端 |
| [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html) | ✅ P0 | Rust 官方类型参考 |

---

## 八、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((精化类型与 Flux 计算模型))
    精化类型作为约束演算
      {v: τ | φ}
      索引类型 τ[i]
      存在类型
    Liquid Types
      限定谓词模板
      Horn 子句约束
      SMT / Z3 求解
    Flux 所有权集成
      独占所有权 = 强更新
      &mut = 弱更新
      &strg = 强引用
    强更新 vs 弱更新
      强更新改变精确类型
      弱更新保持抽象不变量
    霍尔逻辑轻量版
      前置条件 = 参数精化
      后置条件 = ensures / 返回精化
    边界
      仅 safe Rust
      需要 nightly
      SMT 片段限制
    权威来源
      Freeman & Pfenning 1991
      Liquid Types 2008
      Flux PLDI 2023
```

## 来源与延伸阅读

### P1（学术/形式化）

- [Freeman & Pfenning 1991, *Refinement Types for ML*](https://dl.acm.org/doi/10.1145/115865.115880) — 精化类型奠基论文
- [Rondon, Kawaguchi & Jhala 2008, *Liquid Types*](https://dl.acm.org/doi/10.1145/1375581.1375602) — Liquid Types 自动推断
- [Vazou et al. 2014, *Liquid Haskell*](https://dl.acm.org/doi/10.1145/2628136.2628160) — Liquid Types 在 Haskell 中的实现
- [Lehmann et al. 2022, *Flux: Liquid Types for Rust*](https://arxiv.org/pdf/2207.04034.pdf) — Flux 早期论文
- [Lehmann et al. 2023, *Flux: Liquid Types for Rust*, PLDI](https://ranjitjhala.github.io/static/flux-pldi23.pdf) — Flux PLDI 论文

### P2（社区/生态）

- [Flux GitHub](https://github.com/flux-rs/flux) — Flux 官方仓库
- [Verus](https://github.com/verus-lang/verus) — Rust 自动化验证工具
- [Creusot](https://github.com/creusot-rs/creusot) — Rust 演绎验证器
- [Rocq of Rust / formal.land](https://github.com/formal-land/coq-of-rust) — Rust → Rocq 形式化翻译
- [refinement crate](https://crates.io/crates/refinement) — 轻量精化类型库
- [refinement docs](https://docs.rs/refinement/latest/refinement/) — docs.rs 文档
