# RefinedRust 深度解析

> **RefinedRust: A Type System for High-Assurance Verification of Rust Programs**
> PLDI 2024 (Programming Language Design and Implementation)
> 作者: Lennard Gaher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer
> 机构: MPI-SWS, ETH Zurich, Radboud University Nijmegen

---

## 目录

- [RefinedRust 深度解析](#refinedrust-深度解析)
  - [目录](#目录)
  - [1. 引言与背景](#1-引言与背景)
    - [1.1 研究动机](#11-研究动机)
    - [1.2 核心贡献](#12-核心贡献)
  - [2. 理论基础](#2-理论基础)
    - [2.1 精细化所有权类型](#21-精细化所有权类型)
    - [2.2 分离逻辑与 Iris](#22-分离逻辑与-iris)
    - [2.3 生命周期逻辑](#23-生命周期逻辑)
  - [3. 核心技术](#3-核心技术)
    - [3.1 Borrow Names: 可变引用的数学建模](#31-borrow-names-可变引用的数学建模)
    - [3.2 Place Types: 位置的精细化类型](#32-place-types-位置的精细化类型)
    - [3.3 Blocked 类型与固定借用](#33-blocked-类型与固定借用)
  - [4. 类型系统详解](#4-类型系统详解)
    - [4.1 类型语法](#41-类型语法)
    - [4.2 类型规则](#42-类型规则)
    - [4.3 分层策略 (Stratify)](#43-分层策略-stratify)
  - [5. 验证流程](#5-验证流程)
    - [5.1 前端架构](#51-前端架构)
    - [5.2 Radium 中间表示](#52-radium-中间表示)
    - [5.3 Lithium 证明引擎](#53-lithium-证明引擎)
  - [6. 实际案例: Vec 验证](#6-实际案例-vec-验证)
    - [6.1 Vec 表示不变量](#61-vec-表示不变量)
    - [6.2 get\_unchecked\_mut 验证](#62-get_unchecked_mut-验证)
    - [6.3 push/pop 操作验证](#63-pushpop-操作验证)
  - [7. 与其他工具对比](#7-与其他工具对比)
    - [7.1 工具对比矩阵](#71-工具对比矩阵)
    - [7.2 与 RustBelt 的关系](#72-与-rustbelt-的关系)
    - [7.3 与 Creusot/Prusti 的对比](#73-与-creusotprusti-的对比)
  - [8. 限制与未来工作](#8-限制与未来工作)
    - [8.1 当前限制](#81-当前限制)
    - [8.2 未来研究方向](#82-未来研究方向)
  - [9. 实践指南](#9-实践指南)
    - [9.1 何时使用 RefinedRust](#91-何时使用-refinedrust)
    - [9.2 入门资源](#92-入门资源)
  - [参考文献](#参考文献)

---

## 1. 引言与背景

### 1.1 研究动机

Rust 的所有权类型系统在编译时静态保证内存安全，使其特别适合安全关键系统。
近年来，出现了许多自动化演绎验证工具来建立 Rust 代码的功能正确性。
然而，**所有现有工具都存在两个关键限制**:

1. **非基础性证明**: 没有工具产生可在通用证明助理中机器检查的基础性证明
2. **仅限于 Safe Rust**: 所有工具都仅限于 Rust 的安全子集

这是一个严重问题，因为绝大多数 Rust 程序在关键点使用 unsafe 代码，例如广泛使用的 API 实现中。

**RefinedRust 的目标**: 建立一个在 Coq 证明助理中证明可靠的精细化类型系统，实现 safe 和 unsafe Rust 代码的基础性半自动化功能正确性验证。

### 1.2 核心贡献

RefinedRust 做出了以下关键贡献:

| 贡献 | 说明 |
|------|------|
| **首个基础性 unsafe 验证** | 第一个同时支持 safe 和 unsafe Rust 的基础性验证工具 |
| **精细化所有权类型** | 结合精细化类型与 RustBelt 启发的语义模型 |
| **Place Type System** | 支持实际 Rust 代码验证的位置类型系统，包括处理借用位置的类型 |
| **Blocked 类型** | 引入 "固定借用" (pinned borrows) 概念，允许在可变引用下临时弱化类型 |
| **Polonius 集成** | 利用实验性 Polonius 借用检查器提取生命周期信息 |
| **Vec 验证案例** | 成功验证 Rust 标准库 Vec 实现的变体 |

---

## 2. 理论基础

### 2.1 精细化所有权类型

RefinedRust 的核心是**精细化所有权类型** (Refined Ownership Types)，结合了:

1. **精细化类型** (Refinement Types): 在基本类型上添加逻辑谓词
2. **所有权类型** (Ownership Types): 描述资源的所有权和生命周期

**数学值建模**:

所有 RefinedRust 类型都关联一个**数学值** (mathematical value) 概念:

```rust
// Box<i32> 的数学值是整数 (ℤ)
// 表示为: Box<i32> refined by z ∈ ℤ

#[rr::params("x: int")]
#[rr::args("#x")]  // # 表示注入
#[rr::requires("x + 42 ∈ i32")]
#[rr::returns("x + 42")]
fn box_add_42(r: Box<i32>) -> Box<i32> {
    *r += 42;
    r
}
```

### 2.2 分离逻辑与 Iris

RefinedRust 在 **Iris 分离逻辑框架**中构建语义模型:

```text
语义模型层次:
┌─────────────────────────────────────┐
│  RefinedRust 类型和类型判断          │
│  (定义为分离逻辑谓词)                │
├─────────────────────────────────────┤
│  Iris 分离逻辑框架                   │
│  (高阶并发分离逻辑)                  │
├─────────────────────────────────────┤
│  Coq 证明助理                        │
│  (机器检查证明)                      │
└─────────────────────────────────────┘
```

**关键特性**:

- 所有类型和类型判断定义为分离逻辑谓词
- 每条类型规则表述为分离逻辑引理
- 在 Coq 中证明可靠性

### 2.3 生命周期逻辑

RefinedRust 扩展了 RustBelt 的**生命周期逻辑** (Lifetime Logic):

**核心概念**: 所有权可以在生命周期期间拆分:

- **期间所有权**: 在生命周期内拥有
- **之后所有权**: 生命周期结束后恢复

```rust
// 可变引用的生命周期逻辑
let mut z = 1;
{
    let r = &mut z;  // 'a 生命周期开始
    *r += 42;        // 在 'a 期间拥有修改权
}                    // 'a 结束，所有权归还 z
// z 现在等于 43
```

---

## 3. 核心技术

### 3.1 Borrow Names: 可变引用的数学建模

**关键创新**: 使用 **borrow names** (借用名) 处理可变引用。

可变引用 `&mut T` 的数学值是一个**对** `(x, y)`:

- `x`: 当前数学值 (类型 T)
- `y`: borrow name，用于通信引用的最终值

**示例: mut_ref_add_42**

```rust
#[rr::params("x: int", "y: borrow_name")]
#[rr::args("(x, y)")]  // 数学值对
#[rr::requires("x + 42 ∈ i32")]
#[rr::ensures("Res y (x + 42)")]  // 解析 y 为 x + 42
fn mut_ref_add_42(r: &mut i32) {
    *r += 42;
}

// 使用
let mut z = 1;           // z 的数学值: 1
mut_ref_add_42(&mut z);  // 创建引用，数学值 (1, y)
                         // z 的数学值变为 *y
assert!(z == 43);        // RefinedRust 解析 *y 为 43
```

**Res 断言**: `Res y v` 表示 borrow name `y` 最终解析为值 `v`。

### 3.2 Place Types: 位置的精细化类型

Rust 的一个独特特性是 **places** (位置，也称为 lvalues):

```rust
// x.f 是一个 place，表示变量 x 的 f 字段的内存位置
let p = &mut x.f;  // 对 place x.f 取地址
```

RefinedRust 引入 **place types** 来建模这种结构:

```text
Place Type 层次:
┌────────────────────────────────────────┐
│  PlaceType                             │
│  ├── BaseType: 基本类型                 │
│  ├── FieldAccess: 字段访问              │
│  ├── ArrayAccess: 数组索引              │
│  └── Deref: 解引用                      │
└────────────────────────────────────────┘
```

**重要性**:

- RustBelt (λRust) 不处理一般 places，需要手动转换
- RefinedRust 原生支持 places，反映真实 Rust 源代码结构

### 3.3 Blocked 类型与固定借用

**问题场景**: 当从 Vec 借用元素时，需要临时"阻塞"对 Vec 的部分访问。

**解决方案**: `blocked<'b, T>` 类型

```rust
// get_unchecked_mut 的类型签名
#[rr::params("xs: list T", "i: int", "α: lifetime")]
#[rr::args("Vec(xs)", "#i")]
#[rr::requires("0 ≤ i < |xs|")]
#[rr::returns("&mut α (xs[i])")]
#[rr::observe("α : Vec(blocked(α, xs[i]), xs[:i] ++ xs[i+1:]))")]
fn get_unchecked_mut<'a, T>(
    self: &'a mut Vec<T>,
    i: usize
) -> &'a mut T;
```

**关键点**:

- `blocked<'b, T>` 表示在生命周期 `'b` 期间被阻塞的类型
- 当 `'b` 结束后，可以重新获得完整所有权
- 这使得在借用元素的同时保持 Vec 的不变量成为可能

---

## 4. 类型系统详解

### 4.1 类型语法

```ocaml
(* 数学值 *)
v ::= z                 (* 整数 *)
    | b                 (* 布尔值 *)
    | (v₁, v₂)          (* 元组 *)
    | injᵢ(v)           (* 枚举变体 *)
    | γ                 (* borrow name *)

(* 类型 *)
τ ::= int               (* 整数 *)
    | bool              (* 布尔值 *)
    | Box<τ>            (* 拥有的指针 *)
    | &ρ τ              (* 共享引用 *)
    | &mut ρ τ          (* 可变引用 *)
    | τ₁ × τ₂           (* 元组 *)
    | τ₁ + τ₂           (* 枚举 *)

(* 位置类型 *)
place_type ::=
    | #v @ place_τ      (* 值 v 在位置类型 place_τ *)
    | blocked(ρ, τ)     (* 在生命周期 ρ 期间阻塞的类型 *)
```

### 4.2 类型规则

**可变借用检查** (chk-mut-borrow):

```text
Γ ⊢ l₀ : τ₀    Γ ⊢ chk-place-access(l₀, P) = (lᵢ, κ_min, xᵢ @ ρᵢ, ρ[·])
κ_min = Owned    stratify(ρᵢ, xᵢ) = (place_τᵢ, vᵢ)
Γ ⊢ new_borrow_name() = γ
-----------------------------------------------------------
Γ ⊢ &mut P : (#(vᵢ, γ) @ &mut ρ(place_τᵢ)) ⋆ blocked(ρ, τ)
```

**关键步骤**:

1. `chk-place-access`: 检查 place 访问序列的有效性
2. `stratify`: 将类型分层为基本形状
3. 创建新的 borrow name `γ`
4. 返回可变引用类型 + blocked 类型

### 4.3 分层策略 (Stratify)

`stratify` 过程将类型转换为标准形状 `#v @ place_τ`:

```rust
// 示例: 分层 Box<i32>
stratify(place_int, #0) = (place_int, 0)

// 示例: 分层元组
stratify(place_(int × int), #(1, 2)) = (place_(int × int), (1, 2))
```

**目的**: 统一处理不同类型的内存布局，支持精确的指针操作验证。

---

## 5. 验证流程

### 5.1 前端架构

```text
RefinedRust 验证流程:
┌─────────────────────────────────────────────────────────────┐
│  Rust 源代码 (.rs)                                          │
│  + RefinedRust 注解 (#[rr::...])                            │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  rustc 编译器                                               │
│  ├── 解析 (Parsing)                                         │
│  ├── 类型检查 (Type Checking)                               │
│  ├── 借用检查 (Borrow Checking)                             │
│  └── MIR 生成                                               │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  RefinedRust 前端 (rustc 插件)                              │
│  ├── MIR → Radium 转换                                      │
│  ├── Polonius 生命周期信息提取                              │
│  ├── 注解解析                                               │
│  └── 证明义务生成                                           │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  Coq 证明助理                                               │
│  ├── Radium 语义模型                                        │
│  ├── Lithium 证明引擎                                       │
│  └── 自动化类型检查                                         │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 Radium 中间表示

Radium 是基于 RefinedC 的 Caesium 操作语义的 Rust 形式化:

**设计决策**:

- 准确反映 Rust 数据在内存中的表示
- 支持整数溢出检查 (与 λRust 的无限整数不同)
- 处理复合类型的内存布局

**非平凡方面**:

- 对齐 Polonius 的 "loans" 概念与 RustBelt 的 "lifetimes"
- 利用 Prusti 实现中的生命周期提取工具

### 5.3 Lithium 证明引擎

Lithium 是 Iris 分离逻辑的一个片段，专门设计用于高效证明搜索:

**特性**:

- 无回溯的证明搜索
- 自动化应用 RefinedRust 类型规则
- 生成纯 Coq 副作用条件

**验证性能** (Vec API):

- 总验证时间: 约 6 分钟 (wall time)
- CPU 时间: 22 分钟
- Vec::pop 类型系统步骤: 约 3,000 步自动所有权推理
- 纯 Coq 副作用条件: 100 个 (95 个自动解决)

---

## 6. 实际案例: Vec 验证

### 6.1 Vec 表示不变量

`Vec<T>` 的 RefinedRust 表示:

```rust
#[rr::refined_by("xs: list T")]
#[rr::invariant("self.len ≤ self.cap")]
#[rr::invariant("self.len = |xs|")]
struct Vec<T> {
    ptr: Unique<T>,
    len: usize,
    cap: usize,
}
```

**表示不变量**:

- `xs`: 数学列表，表示 Vec 中的逻辑内容
- `len ≤ cap`: 长度不超过容量
- `len = |xs|`: 长度等于逻辑列表长度

### 6.2 get_unchecked_mut 验证

```rust
#[rr::params("xs: list T", "i: int", "α: lifetime")]
#[rr::args("Vec(xs)", "#i")]
#[rr::requires("0 ≤ i < |xs|")]
#[rr::returns("&mut α (xs[i])")]
#[rr::observe("α : Vec(blocked(α, xs[i]),
                      xs[:i] ++ xs[i+1:])")]
unsafe fn get_unchecked_mut<'a, T>(
    self: &'a mut Vec<T>,
    i: usize
) -> &'a mut T {
    let p = self.ptr.as_ptr().add(i);
    &mut *p
}
```

**验证步骤**:

1. 计算元素指针偏移 (`add`)
2. 证明访问在分配内存范围内
3. 从上下文中找到元素的所有权
4. 创建新引用，生命周期为新的符号生命周期 `'b`
5. 返回引用，将 `'b` 扩展为 `'a`

**关键挑战**:

- 创建引用时，`blocked<'b>` 类型暂时借用数组元素的所有权
- 当 `'b` 结束后，可以将所有权重新组合回 Vec

### 6.3 push/pop 操作验证

**Vec::pop 验证统计**:

- 自动所有权推理步骤: ~3,000
- 生成的纯 Coq 副作用条件: 100
- 自动解决: 95
- 需手动证明: 5 (约 20 行 Coq 代码)

---

## 7. 与其他工具对比

### 7.1 工具对比矩阵

| 特性 | RefinedRust | RustBelt | Creusot | Prusti | Verus | Kani | Aeneas |
|------|-------------|----------|---------|--------|-------|------|--------|
| **功能正确性** | ✅ | ○ | ✅ | ✅ | ✅ | ○ | ✅ |
| **基础性证明** | ✅ | ✅ | ○ | ○ | ○ | ○ | ◐ |
| **Unsafe 支持** | ✅ | ✅ | ○ | ○ | ◐ | ✅ | ○ |
| **详细内存模型** | ✅ | ○ | ○ | ○ | ○ | ✅ | ○ |
| **自动化** | ◐ | ○ | ✅ | ✅ | ✅ | ✅ | ◐ |
| **机器检查** | ✅ (Coq) | ✅ (Coq) | ○ | ○ | ○ | ○ | ◐ (Lean) |

**图例**:

- ✅ 完全支持
- ◐ 部分支持
- ○ 不支持/有限

### 7.2 与 RustBelt 的关系

**RustBelt** (Jung et al., POPL 2018):

- 首个 Rust 基础性形式化
- 使用 λRust (理想化中间语言)
- 完全手动证明

**RefinedRust 的改进**:

1. **真实 Rust 代码**: 处理 surface Rust，而非 λRust
2. **Places 支持**: 原生支持 Rust 的 place 表达式
3. **自动化**: 使用 Lithium 引擎实现半自动化
4. **验证工具**: 从证明框架发展为验证工具

```text
关系图:
RustBelt (2018)
    ├── λRust (理想化语言)
    ├── 手动 Coq 证明
    └── 核心语言特性

RefinedRust (2024)
    ├── Surface Rust (真实代码)
    ├── Radium (详细内存模型)
    ├── 半自动化验证
    └── 扩展: places, 整数溢出, 布局
```

### 7.3 与 Creusot/Prusti 的对比

**Creusot**:

- 方法: 预言变量 (prophecy variables)
- 后端: Why3
- 优势: 高度自动化
- 限制: 非基础性，不支持 unsafe

**Prusti**:

- 方法: 分离逻辑，分数权限
- 后端: Viper
- 优势: 模块化验证
- 限制: 非基础性，不支持 unsafe，维护模式

**RefinedRust**:

- 方法: Borrow names + 分离逻辑
- 后端: Coq (Iris)
- 优势: 基础性证明，支持 unsafe
- 限制: 自动化程度较低

---

## 8. 限制与未来工作

### 8.1 当前限制

RefinedRust 原型目前**不支持**:

| 特性 | 状态 | 说明 |
|------|------|------|
| 并发 | ❌ | 不支持并发/并行代码 |
| 递归类型 | ❌ | 不支持递归数据结构 |
| Traits | ❌ | 不支持 trait 系统 |
| 闭包 | ❌ | 不支持闭包 |
| 不定大小类型 | ❌ | 不支持 DST |
| 布局优化 | ⚠️ | 不完全支持 niche 优化 |
| 指针-整数转换 | ⚠️ | 不完全支持 |

### 8.2 未来研究方向

1. **扩展语言支持**:
   - 添加 traits 和泛型支持
   - 支持闭包和递归类型
   - 处理并发和并行代码

2. **提高自动化**:
   - 集成 SMT 求解器作为可信预言
   - 改进 Lithium 引擎的启发式

3. **扩展验证范围**:
   - 验证更多标准库数据结构
   - 支持异步 Rust
   - 处理 FFI 边界

4. **工业应用**:
   - 与 Rust 编译器更紧密集成
   - 开发 IDE 插件
   - 建立验证模式库

---

## 9. 实践指南

### 9.1 何时使用 RefinedRust

**推荐使用**:

- ✅ 需要基础性证明的安全关键代码
- ✅ 涉及 unsafe 指针操作的验证
- ✅ 学术研究或形式化方法教学

**不建议使用** (目前):

- ❌ 生产环境大规模验证 (自动化程度有限)
- ❌ 需要使用 traits/闭包的代码
- ❌ 并发代码验证

### 9.2 入门资源

1. **论文**: RefinedRust (PLDI 2024)
   - PDF: <https://iris-project.org/pdfs/2024-pldi-refinedrust.pdf>

2. **项目网站**: <https://plv.mpi-sws.org/refinedrust/>

3. **相关技术**:
   - Iris: <https://iris-project.org/>
   - RefinedC: <https://plv.mpi-sws.org/refinedc/>
   - Coq: <https://coq.inria.fr/>

---

## 参考文献

1. Gaher, L., Sammler, M., Jung, R., Krebbers, R., & Dreyer, D. (2024). **RefinedRust: A Type System for High-Assurance Verification of Rust Programs**. *PLDI 2024*.

2. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2018). **RustBelt: Securing the Foundations of the Rust Programming Language**. *POPL 2018*.

3. Sammler, M., Lepigre, R., Krebbers, R., Memarian, K., Dreyer, D., & Garg, D. (2021). **RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types**. *PLDI 2021*.

4. Jung, R., Krebbers, R., Jourdan, J. H., Bizjak, A., Birkedal, L., & Dreyer, D. (2018). **Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic**. *JFP 2018*.

5. Denis, X., Jourdan, J. H., & Marché, C. (2022). **Creusot: A Foundry for the Deductive Verification of Rust Programs**. *ICFEM 2022*.

6. Astrauskas, V., Müller, P., Poli, F., & Summers, A. J. (2019). **Leveraging Rust Types for Modular Specification and Verification**. *OOPSLA 2019*.

---

**文档状态**: 初稿 (基于 PLDI 2024 论文)
**最后更新**: 2026-03-12
**维护者**: Rust 所有权可判定性研究项目
