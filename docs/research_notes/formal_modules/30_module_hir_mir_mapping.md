# 模块结构到 HIR / MIR 的映射 {#模块结构到-hir-mir-的映射}

> **EN**: Module Hir MIR Mapping
> **Summary**: 模块结构到 HIR / MIR 的映射 Module Hir MIR Mapping.
> **概念族**: 形式化模块（Module）
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录 {#目录}

- [模块结构到 HIR / MIR 的映射 {#模块结构到-hir-mir-的映射}](#模块结构到-hir--mir-的映射-模块结构到-hir-mir-的映射)
  - [目录 {#目录}](#目录-目录)
  - [研究目标 {#研究目标}](#研究目标-研究目标)
  - [概念定义 {#概念定义}](#概念定义-概念定义)
  - [属性关系 {#属性关系}](#属性关系-属性关系)
  - [解释与论证 {#解释与论证}](#解释与论证-解释与论证)
    - [为什么 MIR 不保留模块结构 {#为什么-mir-不保留模块结构}](#为什么-mir-不保留模块结构-为什么-mir-不保留模块结构)
    - [HIR 中 `use` 的去向 {#hir-中-use-的去向}](#hir-中-use-的去向-hir-中-use-的去向)
    - [`DefPath` 如何编码模块层级 {#defpath-如何编码模块层级}](#defpath-如何编码模块层级-defpath-如何编码模块层级)
  - [Rust 示例 {#rust-示例}](#rust-示例-rust-示例)
    - [1. 源模块结构 {#1-源模块结构}](#1-源模块结构-1-源模块结构)
    - [2. 概念上的 HIR ItemTree 表示 {#2-概念上的-hir-itemtree-表示}](#2-概念上的-hir-itemtree-表示-2-概念上的-hir-itemtree-表示)
    - [3. MIR 视角 {#3-mir-视角}](#3-mir-视角-3-mir-视角)
  - [反例与边界 {#反例与边界}](#反例与边界-反例与边界)
  - [权威来源对照表 {#权威来源对照表}](#权威来源对照表-权威来源对照表)
  - [学术/社区来源参考 {#学术社区来源参考}](#学术社区来源参考-学术社区来源参考)

---

## 研究目标 {#研究目标}

描述 Rust 模块树在编译器前端如何被降维为 HIR（High-level Intermediate Representation）的 ItemTree，以及 MIR 如何保留模块边界与可见性信息，为理解编译期名称解析、宏（Macro）展开和 borrow check 提供中间层视角。

---

## 概念定义 {#概念定义}

| 术语 | 定义 |
| :--- | :--- |
| **HIR** | Rust 编译器在 AST 宏展开与名称解析之后生成的高级中间表示。HIR 保留了大部分源语言结构，是类型检查、trait 解析和 borrow check 的输入。 |
| **ItemTree** | rustc 中用于表示模块内所有 item 索引的轻量结构，按模块组织，存储 item 的 `DefId`、名称、可见性等元数据，便于延迟加载。 |
| **MIR** | Mid-level Intermediate Representation，基于控制流图（CFG）的表示，用于 borrow check、优化和代码生成。MIR 中的函数体、静态项等以 `Body` 形式存在。 |
| **DefId** | 编译器内部用于全局唯一标识一个 definition 的索引。每个 item、impl、variant 等都有一个 `DefId`，其模块层级通过 `DefPath` 编码。 |
| **Resolver / Name Resolution** | 名称解析阶段将路径映射到具体的 `DefId`，同时检查可见性约束。解析结果以 `Res` 形式写入 HIR。 |

> **来源:** [rustc-dev-guide – HIR](https://rustc-dev-guide.rust-lang.org/hir.html)
>
> **来源:** [rustc-dev-guide – The Parser and HIR Lowering](https://rustc-dev-guide.rust-lang.org/syntax-intro.html)
>
> **来源:** [rustc-dev-guide – MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html)

---

## 属性关系 {#属性关系}

```text
Source AST

├── Macro Expansion

│   └── 所有 macro / derive 展开完成

├── Name Resolution

│   ├── 路径 → Res → DefId

│   ├── 可见性检查

│   └── import 解析（use / extern crate）

└── HIR Lowering

    ├── Crate HIR

    │   └── root module 对应 crate root

    ├── Module HIR

    │   ├── ItemTree（模块内 item 索引）

    │   ├── items: fn / struct / enum / trait / impl / use / extern crate / static / const

    │   └── visibility 字段保留

    └── Body HIR（函数体等可执行结构）

        └── 后续 lowering 为 MIR Body

            ├── Basic Blocks

            ├── Statements / Terminators

            └── 模块边界已消失，仅保留 DefId 引用
```

**关键关系：**

1. **模块边界在 HIR 中保留，在 MIR 中淡化**：HIR 仍按模块组织 item，方便 crate 级分析和增量编译；MIR 只关注函数/闭包（Closures）体，模块信息通过 `DefId` 的 `DefPath` 间接保留。
2. **ItemTree 是模块的“目录”**：它不存储完整 AST/HIR 节点，而是存储 item 的元数据索引，使 rustc 可以按需解析模块内容，降低内存占用。
3. **可见性在 HIR 中显式编码**：每个 item 的 `Visibility` 字段被保留，用于后续 privacy 检查与 lint（如私有 item 未被使用警告）。

> **来源:** [rustc-dev-guide – Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html)

---

## 解释与论证 {#解释与论证}

### 为什么 MIR 不保留模块结构 {#为什么-mir-不保留模块结构}

MIR 的设计目标是程序分析与代码生成，其基本单元是函数体（`Body`）和常量求值。模块属于“命名空间组织”概念，在运行时（Runtime）不存在；因此模块边界被消解为 `DefId` 引用（Reference），borrow checker 和优化器无需关心 item 定义在哪个模块。

### HIR 中 `use` 的去向 {#hir-中-use-的去向}

`use` 声明在 HIR 中仍然作为 item 存在，但名称解析阶段已经把它“展开”为具体的导入目标。`pub use` 的可见性信息保留在 HIR 中，用于隐私检查；实际代码生成阶段，`use` 不产生任何 runtime 产物。

### `DefPath` 如何编码模块层级 {#defpath-如何编码模块层级}

`DefPath` 由 crate number + 路径段组成，每个段对应一个 item 或模块。例如 `crate::foo::bar::MyStruct` 会编码为 crate + `foo` + `bar` + `MyStruct`。这种编码使得即使 MIR 中没有显式模块节点，也能通过 `DefId` 追溯到源模块。

> **来源:** [rustc-dev-guide – DefId and DefPath](https://rustc-dev-guide.rust-lang.org/hir.html#defid-and-the-hir-map)

---

## Rust 示例 {#rust-示例}

### 1. 源模块结构 {#1-源模块结构}

```rust
// src/lib.rs

pub mod network {

    pub struct Config;

    pub mod tcp {

        pub fn connect() {}

    }

}

fn private_helper() {}
```

### 2. 概念上的 HIR ItemTree 表示 {#2-概念上的-hir-itemtree-表示}

```text
Crate (DefId 0)

└── Module "crate"

    ├── Item: Mod "network" (pub)

    │   ├── Item: Struct "Config" (pub)

    │   └── Item: Mod "tcp" (pub)

    │       └── Item: Fn "connect" (pub)

    └── Item: Fn "private_helper" (private)
```

### 3. MIR 视角 {#3-mir-视角}

```text
Body of crate::network::tcp::connect

├── bb0

│   ├── start

│   └── return
```

MIR 不再出现 `network` 或 `tcp` 节点，函数通过 `DefId` 引用；模块层级信息退化为 `DefPath` 中的字符串段。

---

## 反例与边界 {#反例与边界}

| 场景 | 说明 | 结果 |
| :--- | :--- | :--- |
| `use` 在 HIR 中生成代码 | `use std::vec::Vec;` | 不生成 MIR body；仅在名称解析和隐私检查中生效 |
| 模块边界影响 borrow check | 跨模块借用（Borrowing） | borrow check 只关注 lifetime 与所有权（Ownership），不关心模块；但跨模块可见性影响能否写出该借用 |
| `#[cfg]` 与模块 | `#[cfg(feature = "x")] mod m;` | 在 AST/HIR 转换前由 cfg 处理，未启用模块不会进入 HIR |
| 泛型（Generics）函数在 MIR 中 | `fn f<T>(x: T) {}` | MIR 保存泛型体，单态化在 monomorphization 阶段生成具体实例 |

> **来源:** [rustc-dev-guide – Queries](https://rustc-dev-guide.rust-lang.org/query.html)

---

## 权威来源对照表 {#权威来源对照表}

| 概念 | rustc-dev-guide | 对应rustc源码 | 备注 |
| :--- | :--- | :--- | :--- |
| HIR 结构与 lowering | [HIR](https://rustc-dev-guide.rust-lang.org/hir.html) | `rustc_hir` crate | 描述 AST → HIR 转换 |
| ItemTree | [Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html) | `rustc_resolve::Resolver` | 模块内 item 索引与解析 |
| MIR 结构 | [MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) | `rustc_middle::mir` | CFG、BasicBlock、Terminator |
| DefId / DefPath | [HIR Map](https://rustc-dev-guide.rust-lang.org/hir.html#defid-and-the-hir-map) | `rustc_hir_def` | 全局唯一标识 |
| Name Resolution | [Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html) | `rustc_resolve` | import、可见性、路径解析 |

---

> **权威来源**: [rustc-dev-guide – HIR](https://rustc-dev-guide.rust-lang.org/hir.html) | [rustc-dev-guide – MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) | [rustc-dev-guide – Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html) | [rustc-dev-guide – Queries](https://rustc-dev-guide.rust-lang.org/query.html)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **来源**: [Aeneas](https://aeneas-verification.github.io/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
