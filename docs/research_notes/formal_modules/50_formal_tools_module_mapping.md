# 形式化工具中的模块与私有性映射

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录

- [形式化工具中的模块与私有性映射](#形式化工具中的模块与私有性映射)
  - [目录](#目录)
  - [研究目标](#研究目标)
  - [概念定义](#概念定义)
  - [属性关系](#属性关系)
  - [解释与论证](#解释与论证)
    - [为什么形式化工具需要处理模块边界](#为什么形式化工具需要处理模块边界)
    - [Aeneas 中的模块处理](#aeneas-中的模块处理)
    - [coq-of-rust 中的模块处理](#coq-of-rust-中的模块处理)
    - [RustBelt 中的抽象与封装](#rustbelt-中的抽象与封装)
  - [Rust 示例](#rust-示例)
    - [1. 抽象后的公开 API（Aeneas 风格）](#1-抽象后的公开-apiaeneas-风格)
    - [2. coq-of-rust 翻译概念](#2-coq-of-rust-翻译概念)
    - [3. RustBelt 风格的规范](#3-rustbelt-风格的规范)
  - [反例与边界](#反例与边界)
  - [权威来源对照表](#权威来源对照表)

---

## 研究目标

对照 Rust 形式化验证生态中的主流工具——Aeneas、coq-of-rust、RustBelt——分析它们如何处理 crate、module 与 visibility 等封装边界，明确这些工具在证明中对外部上下文的假设与限制。

---

## 概念定义

| 术语 | 定义 |
| :--- | :--- |
| **Aeneas** | 基于 Rust 的 borrow-checker 语义（LLBC）生成为 Lean 证明助手的函数式翻译，专注于 safe Rust 子集，保留生命周期与所有权信息。 |
| **coq-of-rust** | 将 Rust 代码翻译为 Coq 形式的工具，覆盖较大的 Rust 语法子集，通过生成的 Coq 定义进行证明。 |
| **RustBelt** | MPI-SWS 提出的 Rust 逻辑关系模型，使用 Iris（高阶分离逻辑）在 Coq 中证明 unsafe 代码的安全性，核心概念是协议（protocol）与资源（resource）。 |
| **Modularity in Proofs** | 形式化工具中如何复用已证明的模块/函数，通常通过接口规范（interface specification）隐藏实现细节。 |
| **Visibility as Proof Boundary** | 在形式化验证中，私有 item 的实现细节可被抽象，只需为公开 API 提供规范；这与 Rust 的可见性系统天然对应。 |

> **来源:** [Aeneas – GitHub](https://github.com/AeneasVerif/aeneas)
>
> **来源:** [coq-of-rust – GitHub](https://github.com/formal-land/coq-of-rust)
>
> **来源:** [RustBelt – Project Page](https://plv.mpi-sws.org/rustbelt/)

---

## 属性关系

```text
Rust Source
├── Crate / Module Tree
│   ├── Public API        → 形式化工具需要完整规范
│   ├── pub(crate)        → 可能在 crate 级证明中被抽象
│   └── Private items     → 可被隐藏，仅影响局部证明
├── Formalization Tool
│   ├── Aeneas
│   │   ├── 输入: safe Rust + 生命周期
│   │   ├── 输出: Lean 函数式定义
│   │   └── 模块边界: 翻译为命名空间/模块，依赖 LLBC 中的 DefId 层级
│   ├── coq-of-rust
│   │   ├── 输入: 较大 Rust 子集（含部分 unsafe）
│   │   ├── 输出: Coq 翻译
│   │   └── 模块边界: 保留 crate/module 结构到 Coq module
│   └── RustBelt
│       ├── 输入: 核心 unsafe Rust 片段
│       ├── 输出: Iris / Coq 逻辑关系证明
│       └── 模块边界: 通过抽象谓词隐藏私有状态，公开 API 以 Hoare triple 描述
└── Proof Strategy
    ├── Modular spec      → 只验证 public functions 的契约
    └── Whole-crate proof → 可能展开内部实现，但利用可见性降低复杂度
```

**关键关系：**

1. **形式化工具通常将可见性视为证明抽象边界**：公开 API 必须有完整的前后置条件；私有函数可以仅被局部验证，不需要对外暴露规范。
2. **Aeneas 的 LLBC 保留 DefId 层级**：模块结构在 Aeneas 的中间语言 LLBC 中对应命名空间，函数调用通过全局名称解析。
3. **RustBelt 使用逻辑资源模拟封装**：私有字段对应不可共享的内部资源，公开方法通过 ghost state 与 protocol 描述其对外可见行为。

> **来源:** [Aeneas – LLBC Paper](https://arxiv.org/abs/2207.09467)

---

## 解释与论证

### 为什么形式化工具需要处理模块边界

Rust 的模块系统不仅是代码组织工具，更是安全契约的载体。形式化验证若要证明“crate 的公开 API 安全”，必须知道哪些函数/类型是外部可调用的。可见性信息帮助工具确定证明义务的范围：

- **Public items**：需要给出可被外部依赖的规范。
- **Private items**：只要保证不破坏 public items 的不变式即可，内部细节可被抽象。

### Aeneas 中的模块处理

Aeneas 对 Rust 进行 borrow-checker 语义提取，生成 Low-Level Borrow Calculus（LLBC）。在 LLBC 中，crate 被表示为若干模块，每个函数有唯一的全局名称。Aeneas 目前主要处理 safe Rust，unsafe 代码需要被建模为外部函数（opaque）或手动给出规范。

### coq-of-rust 中的模块处理

coq-of-rust 将 Rust 代码几乎一一对应地翻译为 Coq。Rust 的 `mod` 结构被保留为 Coq 的 `Module`，`use` 被处理为 Coq 的 `Import`。由于 Coq 本身也有模块系统，这种映射相对自然。私有性在 Coq 中不完全强制，但工具生成的接口层可以通过参数化类型模拟可见性约束。

### RustBelt 中的抽象与封装

RustBelt 的核心贡献是证明标准库中 unsafe 代码的安全性。它不直接处理整个 crate，而是聚焦于关键抽象（如 `Rc`、`Arc`、`Cell`、`Mutex`）。私有字段在 Iris 中被建模为内部资源，公开 API 提供获取/释放这些资源的规则。模块可见性在这里体现为：外部证明只能使用公开 API 的规范，不能窥探私有资源。

> **来源:** [RustBelt Paper (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/)

---

## Rust 示例

### 1. 抽象后的公开 API（Aeneas 风格）

```rust
pub struct BoundedCounter {
    value: u32, // 私有
}

impl BoundedCounter {
    pub fn new() -> Self {
        BoundedCounter { value: 0 }
    }

    pub fn increment(&mut self) -> bool {
        if self.value < 100 {
            self.value += 1;
            true
        } else {
            false
        }
    }

    pub fn get(&self) -> u32 {
        self.value
    }
}
```

Aeneas 可为此生成 Lean 函数，后置条件包括 `value <= 100`；私有字段 `value` 在规范中被抽象为 ghost state。

### 2. coq-of-rust 翻译概念

```coq
(* 概念性翻译，非真实生成结果 *)
Module BoundedCounter.
  Definition t := { value : u32 }.

  Definition new : M t := ...
  Definition increment (self : mut_ref t) : M bool := ...
  Definition get (self : ref t) : M u32 := ...
End BoundedCounter.
```

### 3. RustBelt 风格的规范

```text
{ True }
  BoundedCounter::new()
{ c. c ↦ BoundedCounter(0) * BoundedCounter_inv(c, 0) }

{ c ↦ BoundedCounter(n) * n < 100 }
  c.increment()
{ b. if b then c ↦ BoundedCounter(n+1) else c ↦ BoundedCounter(n) }
```

私有字段 `value` 通过 `BoundedCounter` 谓词封装，外部证明只能使用这些 Hoare triple。

---

## 反例与边界

| 场景 | 工具 | 限制 |
| :--- | :--- | :--- |
| 公开 unsafe fn | Aeneas | 通常作为 opaque/external，需要手动规范 |
| 泛型单态化 | coq-of-rust | 需要为每个单态实例生成 Coq 定义，规模可能爆炸 |
| 跨 crate  trait 实现 | RustBelt | 需要为每个实现点建立协议兼容性 |
| `pub(crate)` 作为公开边界 | 所有工具 | 工具通常以 crate 为单位验证，此时 `pub(crate)` 视为公开 |
| 宏生成代码 | coq-of-rust / Aeneas | 通常先由 rustc 展开，工具处理展开后的代码 |

> **来源:** [Aeneas – Limitations](https://github.com/AeneasVerif/aeneas/blob/main/PROGRESS.md)

---

## 权威来源对照表

| 工具 | 论文/文档 | 处理方式 | 模块/私有性映射 |
| :--- | :--- | :--- | :--- |
| Aeneas | [LLBC Paper](https://arxiv.org/abs/2207.09467) | borrow-checker 语义 → Lean | 保留 DefId/模块层级；public API 需规范 |
| coq-of-rust | [GitHub / Examples](https://github.com/formal-land/coq-of-rust) | Rust → Coq 翻译 | Rust `mod` → Coq `Module`；`use` → `Import` |
| RustBelt | [POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Iris 逻辑关系 | 私有状态 → 内部资源；public API → Hoare triple |
| Miri | [Miri Docs](https://github.com/rust-lang/miri) | 解释执行检测 UB | 不直接形式化模块，但受可见性约束的 safe API 是其验证对象 |

---

> **权威来源**: [Aeneas – GitHub](https://github.com/AeneasVerif/aeneas) | [coq-of-rust – GitHub](https://github.com/formal-land/coq-of-rust) | [RustBelt – POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | [Aeneas – LLBC Paper](https://arxiv.org/abs/2207.09467)
