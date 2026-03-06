# Rust 所有权系统元模型

> **Rust 版本**: 1.94+ (Edition 2024)
> **难度级别**: 🔴 高级
> **目标**: 提供 Rust 所有权系统的严格数学基础

---

## 📋 目录

- [Rust 所有权系统元模型](#rust-所有权系统元模型)
  - [📋 目录](#-目录)
  - [🎯 元模型概述](#-元模型概述)
  - [📁 文档导航](#-文档导航)
    - [核心文档](#核心文档)
    - [Rust 1.94 对齐](#rust-194-对齐)
  - [🔗 与其他模块的关联](#-与其他模块的关联)
  - [🧮 形式化基础](#-形式化基础)
    - [抽象语法 (Abstract Syntax)](#抽象语法-abstract-syntax)
    - [核心判断 (Core Judgments)](#核心判断-core-judgments)
    - [语义域 (Semantic Domains)](#语义域-semantic-domains)
  - [📚 阅读指南](#-阅读指南)
    - [推荐阅读顺序](#推荐阅读顺序)
    - [前置知识](#前置知识)
    - [关联阅读](#关联阅读)

---

## 🎯 元模型概述

元模型（Meta-Model）是 Rust 所有权系统的数学基础，提供：

1. **抽象语法** - 形式化定义 Rust 子集的语法结构
2. **语义域** - 定义值、位置、状态等数学域
3. **判断形式** - 类型判断、所有权安全判断、生命周期判断
4. **Rust 1.94 对齐** - 与现代 Rust 特性的对齐分析

---

## 📁 文档导航

### 核心文档

| 文档 | 主题 | 难度 | 关键内容 |
|:-----|:-----|:----:|:---------|
| [`01_abstract_syntax.md`](01_abstract_syntax.md) | 抽象语法 | 🔴 | BNF 文法、类型语法、表达式语法 |
| [`02_semantic_domains.md`](02_semantic_domains.md) | 语义域 | 🔴 | 内存位置、值域、状态、堆栈模型 |
| [`03_judgments.md`](03_judgments.md) | 判断形式 | 🔴 | 类型判断、所有权安全、生命周期约束 |

### Rust 1.94 对齐

| 文档 | 主题 | 说明 |
|:-----|:-----|:-----|
| [`rust-194-alignment.md`](rust-194-alignment.md) | Rust 1.94 对齐分析 | 元模型与现代 Rust 的差异和适配 |
| [`RUST_194_COMPREHENSIVE_GUIDE.md`](RUST_194_COMPREHENSIVE_GUIDE.md) | Rust 1.94 完整指南 | 新特性的形式化描述 |

---

## 🔗 与其他模块的关联

```text
meta-model/
    │
    ├── 为 formal-foundations/semantics/ 提供基础
    │   └── 操作语义的定义依赖于语义域和判断形式
    │
    ├── 为 formal-foundations/models/ 提供语法
    │   └── 所有权类型、借用语义的形式化模型
    │
    ├── 为 coq-formalization/ 提供规范
    │   └── Coq 中的语法和语义定义基于此元模型
    │
    └── 为 16-program-semantics/ 提供理论支撑
        └── 程序语义分析的数学基础
```

---

## 🧮 形式化基础

### 抽象语法 (Abstract Syntax)

```bnf
τ ::=                         (* 类型 *)
  | B                         (* 基础类型 *)
  | &ρ ω τ                    (* 引用类型 *)
  | Box τ                     (* 唯一指针 *)
  | (τ₁, ..., τₙ)             (* 元组类型 *)
  | struct_name<...>          (* 结构体 *)
  | enum_name<...>            (* 枚举 *)

ω ::= uniq | shrd             (* 可变性 *)
ρ ::= static | r | 'a         (* 生命周期 *)
```

### 核心判断 (Core Judgments)

| 判断 | 含义 | 形式 |
|:-----|:-----|:-----|
| 类型判断 | 表达式具有给定类型 | `Δ; Γ; Θ ⊢ e : τ` |
| 所有权安全 | 访问路径安全 | `Δ; Γ; Θ ⊢ω p ⇒ {ω'p'}` |
| 生命周期包含 | 生命周期约束 | `Δ ⊢ ρ₁ ⊑ ρ₂` |
| 良形式 | 类型是良形式的 | `Δ ⊢ τ ok` |

### 语义域 (Semantic Domains)

```text
Loc ≜ {ℓ₁, ℓ₂, ℓ₃, ...}           内存位置 (可数无限)
Val ≜ Unit + Bool + Int + Loc     值域
Store ≜ Loc → Val                 存储 (堆)
Stack ≜ Frame*                    调用栈
```

---

## 📚 阅读指南

### 推荐阅读顺序

```
1. 01_abstract_syntax.md
   └── 理解 Rust 子集的语法结构

2. 02_semantic_domains.md
   └── 理解值、位置、状态的数学定义

3. 03_judgments.md
   └── 理解类型系统和所有权规则的数学表达

4. rust-194-alignment.md
   └── 理解与现代 Rust 的对齐
```

### 前置知识

- 形式化方法基础
- 类型理论
- 操作语义基础
- 一阶逻辑

### 关联阅读

- [formal-foundations/semantics/operational-semantics.md](../formal-foundations/semantics/operational-semantics.md)
- [formal-foundations/models/ownership-types.md](../formal-foundations/models/02-02-ownership-types.md)
- [coq-formalization/README.md](../coq-formalization/README.md)

---

**最后更新**: 2026-03-07
**状态**: ✅ 完成
