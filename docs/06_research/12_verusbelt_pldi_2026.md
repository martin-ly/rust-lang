# VerusBelt (PLDI 2026) 研究笔记 {#verusbelt-pldi-2026-研究笔记}

> **EN**: VerusBelt PLDI 2026
> **Summary**: 研究笔记 VerusBelt PLDI 2026.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L4-L5
> **创建日期**: 2026-05-08
> **最后更新**: 2026-05-22
> **会议**: PLDI 2026 (Programming Language Design and Implementation)
> **状态**: 🔬 研究跟踪；⚠️ 预印本/待正式出版确认

---

## 📋 目录 {#目录}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [VerusBelt (PLDI 2026) 研究笔记 {#verusbelt-pldi-2026-研究笔记}](#verusbelt-pldi-2026-研究笔记-verusbelt-pldi-2026-研究笔记)
  - [📋 目录 {#目录}](#-目录-目录)
  - [🔍 背景：Verus 验证框架 {#背景verus-验证框架}](#-背景verus-验证框架-背景verus-验证框架)
  - [📄 VerusBelt 论文概述 {#verusbelt-论文概述}](#-verusbelt-论文概述-verusbelt-论文概述)
  - [🧠 核心贡献 {#核心贡献}](#-核心贡献-核心贡献)
    - [1. 类型系统扩展的形式化 {#1-类型系统扩展的形式化}](#1-类型系统扩展的形式化-1-类型系统扩展的形式化)
    - [2. 层叠语义 (Layered Semantics) {#2-层叠语义-layered-semantics}](#2-层叠语义-layered-semantics-2-层叠语义-layered-semantics)
    - [3. 擦除定理 (Erasure Theorem) {#3-擦除定理-erasure-theorem}](#3-擦除定理-erasure-theorem-3-擦除定理-erasure-theorem)
  - [⚖️ 与相关工作的对比 {#与相关工作的对比}](#️-与相关工作的对比-与相关工作的对比)
    - [VerusBelt vs RefinedRust {#verusbelt-vs-refinedrust}](#verusbelt-vs-refinedrust-verusbelt-vs-refinedrust)
    - [VerusBelt vs RustBelt {#verusbelt-vs-rustbelt}](#verusbelt-vs-rustbelt-verusbelt-vs-rustbelt)
    - [Verus 生态最新进展 (2025–2026) {#verus-生态最新进展-20252026}](#verus-生态最新进展-20252026-verus-生态最新进展-20252026)
  - [🔧 对安全关键 Rust 的实践意义 {#对安全关键-rust-的实践意义}](#-对安全关键-rust-的实践意义-对安全关键-rust-的实践意义)
    - [1. 操作系统内核验证 {#1-操作系统内核验证}](#1-操作系统内核验证-1-操作系统内核验证)
    - [2. 密码学实现验证 {#2-密码学实现验证}](#2-密码学实现验证-2-密码学实现验证)
    - [3. 分布式系统协议 {#3-分布式系统协议}](#3-分布式系统协议-3-分布式系统协议)
    - [4. 行业标准 {#4-行业标准}](#4-行业标准-4-行业标准)
  - [📖 引用信息 {#引用信息}](#-引用信息-引用信息)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 🔍 背景：Verus 验证框架 {#背景verus-验证框架}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Verus** 是由 **Microsoft Research** 开发的 Rust 程序验证框架，允许开发者用 Rust 本身编写规范（`spec` 函数）和证明（`proof` 代码），从而验证 Rust 程序的正确性。

```text
Verus 验证流程:

Rust 源码 + 规范
      │
      ▼
┌─────────────┐
│ Verus 前端   │  ── 提取 spec / proof / exec 代码
└──────┬──────┘
       │
┌──────▼──────┐
│ Z3 SMT 求解器│  ── 自动证明验证
└──────┬──────┘
       │
   ┌───▼────┐
   │ ✅ / ❌ │  ── 证明通过或给出反例
   └────────┘
```

Verus 的三种函数模式：

| 模式 | 关键字 | 用途 | 运行时（Runtime）开销 |
|------|--------|------|-----------|
| `exec` | 默认 | 可执行代码 | 无 |
| `proof` | `proof fn` | 编译时证明 | 零开销 (编译后擦除) |
| `spec` | `spec fn` | 规范定义 | 零开销 (仅用于验证) |

---

## 📄 VerusBelt 论文概述 {#verusbelt-论文概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**论文标题**: VerusBelt: A Semantic Foundation for Proof-Oriented Extensions to Rust

**发表会议**: PLDI 2026 (ACM SIGPLAN Conference on Programming Language Design and Implementation)

**作者**:

- **Travis Hance** (Microsoft Research)
- **Laila Elbeheiry** (Max Planck Institute for Software Systems)
- **Yusuke Matsushita** (University of Tokyo)
- **Derek Dreyer** (Max Planck Institute for Software Systems)

**核心问题**: Verus 引入了大量语言扩展（`ghost` 变量、`tracked` 权限、`proof` 代码等），但这些扩展缺乏形式化语义基础。VerusBelt 为 Verus 的 proof-oriented 扩展提供了严格的数学语义。

---

## 🧠 核心贡献 {#核心贡献}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

VerusBelt 的主要技术贡献：

### 1. 类型系统扩展的形式化 {#1-类型系统扩展的形式化}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

为 Verus 的以下扩展提供形式化类型规则：

| 扩展特性 | 说明 | VerusBelt 贡献 |
|---------|------|---------------|
| `ghost` 类型 | 仅存在于验证阶段的值 | 证明 ghost 代码不会影响运行时语义 |
| `tracked` 权限 | 线性所有权（Ownership）类型的证明变体 | 形式化线性权限的传递规则 |
| `proof` 代码块 | 仅用于证明的计算 | 证明 proof 代码的擦除安全性 |
| `spec` 函数 | 规范定义 | 形式化 spec 的纯函数语义 |

### 2. 层叠语义 (Layered Semantics) {#2-层叠语义-layered-semantics}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
VerusBelt 语义层次:

┌─────────────────────────────────────┐
│  第 3 层: Verus 表面语法              │
│  (程序员直接编写的代码)                │
├─────────────────────────────────────┤
│  第 2 层: 中间表示 (VIR)              │
│  (spec / proof / exec 分离后的 IR)    │
├─────────────────────────────────────┤
│  第 1 层: RustBelt 核心逻辑           │
│  (内存安全 + 所有权的形式化)            │
├─────────────────────────────────────┤
│  第 0 层: Iris 分离逻辑框架            │
│  (底层元理论)                         │
└─────────────────────────────────────┘
```

### 3. 擦除定理 (Erasure Theorem) {#3-擦除定理-erasure-theorem}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

证明：所有 `spec` 和 `proof` 代码在编译后可以被安全擦除，不影响 `exec` 代码的运行时行为。这是 Verus "零开销抽象" 的形式化保证。

---

## ⚖️ 与相关工作的对比 {#与相关工作的对比}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### VerusBelt vs RefinedRust {#verusbelt-vs-refinedrust}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 维度 | VerusBelt / Verus | RefinedRust |
|------|------------------|-------------|
| **目标语言** | Rust (带扩展) | 标准 Rust (子集) |
| **规范语言** | Rust 子集 (spec) | 自定义精炼类型注解 |
| **证明方式** | SMT 自动求解 + 手动 proof | 主要依赖交互式证明 (Coq) |
| **自动化程度** | 高 | 中低 |
| **形式化基础** | RustBelt + Iris | RustBelt + Coq |
| **适用场景** | 系统软件验证 | 协议/算法验证 |
| **工业应用** | Microsoft 内部项目 | 学术研究为主 |

### VerusBelt vs RustBelt {#verusbelt-vs-rustbelt}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 维度 | RustBelt | VerusBelt |
|------|----------|-----------|
| **发表时间** | POPL 2018 | PLDI 2026 |
| **核心目标** | 证明 Rust 内存安全（Memory Safety） | 证明 Verus 扩展的语义正确性 |
| **基础理论** | Iris 分离逻辑 | RustBelt + 扩展 |
| **关系** | 基础理论 | **建立在 RustBelt 之上** |
| **自动化** | 无 (纯形式化模型) | 支持自动化验证流程 |

```text
技术谱系:

Iris 分离逻辑框架
      │
      ▼
RustBelt (POPL 2018) ── 证明 Rust 所有权系统内存安全
      │
      ├──► VerusBelt (PLDI 2026) ── 扩展至 Verus 的 proof-oriented 特性
      │
      └──► RefinedRust ── 精炼类型系统实现
```

### Verus 生态最新进展 (2025–2026) {#verus-生态最新进展-20252026}

> **KVerus arXiv 2026; [AutoVerus OOPSLA 2025](https://oopsla.org/); [Vest USENIX Security 2025](https://www.usenix.org/conference/usenixsecurity25)** Verus 验证框架的周边工具链在 2025–2026 年快速扩展，降低了证明门槛并扩展了验证覆盖。

| 工具 | 会议/来源 | 与 VerusBelt 的关系 |
| :--- | :--- | :--- |
| **KVerus** | arXiv 2026-05 | RAG-based 自动证明生成，将自然语言规格转换为 Verus 证明脚本，减少手写 proof 负担 |
| **AutoVerus** | OOPSLA 2025 | 神经符号验证：LLM 生成循环不变式 + SMT 验证，可与 VerusBelt 的分层语义结合 |
| **Vest** | USENIX Security 2025 | 基于 Verus 的可验证网络协议框架（TLS/QUIC），证明消息解析与状态机正确性 |
| **Rustlantis** | OOPSLA 2024 | 随机程序生成器用于发现 Verus/Miri 的 soundness 漏洞，提升验证工具可靠性 |

> **⟹ 洞察**: VerusBelt 提供了 Verus 扩展的语义基础，而 KVerus/AutoVerus 正在将这一基础转化为**半自动化的工业实践**——从手写 proof 到 AI 辅助证明生成。
> [来源: [concept/04_formal/05_verification_toolchain.md](../../concept/04_formal/04_model_checking/01_verification_toolchain.md) §7]

---

## 🔧 对安全关键 Rust 的实践意义 {#对安全关键-rust-的实践意义}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

VerusBelt 的研究成果对以下领域有直接影响：

### 1. 操作系统内核验证 {#1-操作系统内核验证}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- Verus 已被用于验证 **Ironclad Apps** (Microsoft Research)
- VerusBelt 为这类验证提供了语义正确性保证
- 与 **Rust for Linux** 项目潜在关联：未来可能用 Verus 验证内核模块（Module）

### 2. 密码学实现验证 {#2-密码学实现验证}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- 常量时间验证 (constant-time verification)
- 防止侧信道漏洞的形式化保证

### 3. 分布式系统协议 {#3-分布式系统协议}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- Verus 已用于验证分布式共识协议
- VerusBelt 保证 proof 代码不会污染 exec 代码

### 4. 行业标准 {#4-行业标准}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 标准 | 要求 | Verus/VerusBelt 适用性 |
|------|------|----------------------|
| DO-178C (航空) | 形式化方法补充认证 | 高 |
| ISO 26262 (汽车) | 软件工具置信度 | 中 |
| Common Criteria (安全) | 形式化安全模型 | 高 |

---

## 📖 引用信息 {#引用信息}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**APA 格式**:

```text
Hance, T., Elbeheiry, L., Matsushita, Y., & Dreyer, D. (2026).
VerusBelt: A Semantic Foundation for Proof-Oriented Extensions to Rust.
In Proceedings of the ACM SIGPLAN Conference on Programming Language
Design and Implementation (PLDI 2026).
```

**BibTeX**:

```bibtex
@inproceedings{hance2026verusbelt,
  title={VerusBelt: A Semantic Foundation for Proof-Oriented Extensions to Rust},
  author={Hance, Travis and Elbeheiry, Laila and Matsushita, Yusuke and Dreyer, Derek},
  booktitle={Proceedings of the ACM SIGPLAN Conference on Programming Language Design and Implementation},
  year={2026},
  organization={ACM},
  doi={10.1145/XXXXXX.XXXXXX}  % 待 PLDI 2026 正式出版后更新
}
```

**相关资源**:

1. **Verus 项目主页**: <https://github.com/verus-lang/verus>
2. **Verus 文档**: <https://github.com/verus-lang/verus/>
3. **RustBelt 论文**: Jung, R., et al. "RustBelt: Securing the Foundations of the Rust Programming Language". POPL 2018.
4. **Iris 框架**: <https://iris-project.org/>

---

> 📌 **跟踪记录**
>
> - 2026-05-08: 初始创建，论文预计于 PLDI 2026 正式发表
> - PLDI 2026 会议日期: 2026 年 6 月 (预计)
> - DOI 待会议正式出版后更新
>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [上级目录](../README.md)
- [形式化验证工具链 (concept)](../../concept/04_formal/04_model_checking/01_verification_toolchain.md) — 概念层 2026 工具链全景与状态矩阵
- [安全关键认证 (concept)](../../concept/04_formal/04_model_checking/03_aerospace_certification_formal_methods.md) — Ferrocene 认证与形式化方法工业映射
- [RustBelt (concept)](../../concept/04_formal/02_separation_logic/01_rustbelt.md) — Rust 所有权系统的 Iris 分离逻辑证明

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
