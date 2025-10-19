# 形式化方法

> **语义模型与形式化验证**，提供程序正确性的理论基础和验证工具

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

---

## 📋 目录

- [形式化方法](#形式化方法)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [📚 文档列表](#-文档列表)
    - [1. 语言语义学](#1-语言语义学)
    - [2. 语义模型综合 ⭐](#2-语义模型综合-)
  - [🔬 核心方法](#-核心方法)
    - [1. 操作语义 (Operational Semantics)](#1-操作语义-operational-semantics)
    - [2. 指称语义 (Denotational Semantics)](#2-指称语义-denotational-semantics)
    - [3. 公理语义 (Axiomatic Semantics)](#3-公理语义-axiomatic-semantics)
    - [4. 模型检查 (Model Checking)](#4-模型检查-model-checking)
  - [🎯 Rust 1.90 特性映射](#-rust-190-特性映射)
    - [所有权与借用](#所有权与借用)
    - [并发内存模型](#并发内存模型)
    - [异步语义](#异步语义)
  - [📖 学习路径](#-学习路径)
    - [初学者路径](#初学者路径)
    - [中级路径](#中级路径)
    - [高级路径](#高级路径)
  - [💡 实践应用](#-实践应用)
    - [并发协议验证](#并发协议验证)
    - [状态机设计](#状态机设计)
    - [等价性验证](#等价性验证)
  - [🔗 相关资源](#-相关资源)
    - [项目内文档](#项目内文档)
    - [推荐工具](#推荐工具)
    - [推荐书籍](#推荐书籍)
    - [在线资源](#在线资源)

---

## 📋 概述

本目录包含形式化方法的理论背景、证明思路与工具链，补充 API 之外的理论深度。涵盖语义模型、模型检查、等价性验证等核心主题。

---

## 📚 文档列表

### 1. [语言语义学](./language-semantics.md)

**内容概要**:

- 语义三分法（操作/指称/公理）
- Rust 特性的形式化映射
- 所有权、借用、生命周期的语义
- `Send`/`Sync`/`Pin` 的形式化理解
- 并发内存模型

**适合人群**: 编译器开发者、程序验证工程师

**关键概念**:

- 小步语义与大步语义
- 类型系统与内存安全
- 原子序与数据竞争
- 异步状态机语义

**Rust 1.90 对齐**:

- `async/await` 的语义模型
- `Pin`/`Unpin` 的内存保证
- 常量泛型的类型承载
- 结构化并发的取消语义

### 2. [语义模型综合](./semantic-models-comprehensive.md) ⭐

**内容概要**:

- 完整的语义模型体系
- 形式化验证方法
- 时序逻辑 (LTL/CTL)
- 等价性理论
- 抽象与精化

**适合人群**: 研究者、形式化验证专家

**关键概念**:

- Kripke 结构
- 双模拟与弱双模拟
- 模型检查算法
- 定理证明
- 抽象解释

---

## 🔬 核心方法

### 1. 操作语义 (Operational Semantics)

**定义**: 通过状态转移规则描述程序执行过程。

**两种风格**:

**小步语义 (Small-Step)**:

- 每次执行一步
- 精确描述执行顺序
- 适合并发建模

```text
⟨e₁, σ⟩ → ⟨e₂, σ'⟩
```

**大步语义 (Big-Step)**:

- 一次执行到结果
- 简洁直观
- 适合函数式语言

```text
⟨e, σ⟩ ⇓ ⟨v, σ'⟩
```

**Rust应用**:

- 移动语义的转移规则
- 借用检查器的推理规则
- `async/await` 的状态机转换

**文档**: [language-semantics.md](./language-semantics.md)

### 2. 指称语义 (Denotational Semantics)

**定义**: 将程序映射为数学对象（函数、域）。

**核心思想**:

- 程序即函数
- 组合性原则
- 语义域理论

**数学基础**:

```text
⟦P⟧: State → State
⟦if e then P₁ else P₂⟧ = λσ. if ⟦e⟧σ then ⟦P₁⟧σ else ⟦P₂⟧σ
```

**Rust应用**:

- 类型推断的语义基础
- 生命周期的域理论
- 所有权转移的数学模型

### 3. 公理语义 (Axiomatic Semantics)

**定义**: 通过断言与推理规则描述程序性质。

**Hoare 逻辑**:

```text
{P} C {Q}
前置条件 P，执行 C，后置条件 Q
```

**推理规则示例**:

```text
{P} C₁ {Q}  {Q} C₂ {R}
─────────────────────── (顺序组合)
    {P} C₁;C₂ {R}
```

**Rust应用**:

- 所有权不变式
- 借用规则的公理化
- 契约式编程

**文档**: [semantic-models-comprehensive.md](./semantic-models-comprehensive.md)

### 4. 模型检查 (Model Checking)

**定义**: 自动化验证系统是否满足给定性质。

**核心组件**:

1. **Kripke 结构** - 状态转移系统
2. **时序逻辑** - 性质描述（LTL/CTL）
3. **验证算法** - DFS/BFS、BDD、SAT

**时序逻辑示例**:

```text
- AG p    : 所有路径上 p 始终成立（安全性）
- AF p    : 所有路径上最终 p 成立（活性）
- EF p    : 存在路径最终 p 成立（可达性）
```

**Rust应用**:

- 并发协议验证
- 无死锁检查
- 内存安全验证
- 使用 `loom` 进行模型检查

---

## 🎯 Rust 1.90 特性映射

### 所有权与借用

**公理语义视角**:

```text
{owned(x)} move(x) to y {owned(y) ∧ ¬owned(x)}
{owned(x)} borrow(&x) {borrowed(&x) ∧ owned(x)}
```

**操作语义视角**:

```text
⟨x, σ[x ↦ v]⟩ --move--> ⟨y, σ[y ↦ v, x ↦ ⊥]⟩
```

### 并发内存模型

**原子序 (Memory Ordering)**:

- **Relaxed**: 最弱保证，仅原子性
- **Acquire/Release**: 建立happens-before关系
- **SeqCst**: 顺序一致性，全局顺序

**工具**:

- `loom`: 在小状态空间内穷举并发执行
- 检测弱内存序导致的竞态

### 异步语义

**状态机模型**:

```text
async fn f() -> T  ≈  impl Future<Output = T>

状态 = {Initial, Polling, Ready(T)}
await点 = 状态转移边界
Waker = 进度驱动机制
```

**等价性**:

- 可观测等价：trace equivalence
- 双模拟：bisimulation
- 通过时序逻辑验证活性

---

## 📖 学习路径

### 初学者路径

**目标**: 理解形式化方法的基本思想

1. **入门** (1-2周)
   - 阅读 [语言语义学](./language-semantics.md)
   - 理解三种语义模型
   - 学习基本的Hoare逻辑

2. **实践**
   - 为简单程序写前后置条件
   - 理解Rust的所有权规则
   - 练习推理规则

### 中级路径

**目标**: 掌握形式化验证方法

1. **深入理论** (2-4周)
   - [语义模型综合](./semantic-models-comprehensive.md)
   - Kripke结构与可达性
   - LTL/CTL时序逻辑
   - 双模拟理论

2. **工具实践**
   - 使用 `loom` 检查并发程序
   - 学习模型检查器（如 SPIN、TLA+）
   - 验证小型协议

### 高级路径

**目标**: 研究级别的形式化方法

1. **高级主题** (4-8周)
   - 抽象解释
   - 定理证明器（Coq、Isabelle）
   - 程序合成
   - 组合验证

2. **研究方向**
   - Rust的形式化语义
   - 异步程序验证
   - 学术论文阅读
   - 工具开发

---

## 💡 实践应用

### 并发协议验证

使用形式化方法验证：

- 无死锁
- 无数据竞争
- 顺序一致性
- 线性化性

### 状态机设计

从状态机到协议验证：

1. 定义状态空间
2. 建立转移规则
3. 描述时序性质
4. 模型检查验证

**文档**: [fsm-to-protocol.md](../guides/fsm-to-protocol.md)

### 等价性验证

验证同步/异步实现的等价性：

- Trace equivalence
- Bisimulation
- 可观测等价

---

## 🔗 相关资源

### 项目内文档

- [并发模型](../concurrency/) - 并发语义
- [分布式系统](../distributed/) - 分布式算法验证
- [API参考](../api/formal-models.md) - 形式化API
- [使用指南](../guides/fsm-to-protocol.md) - 实践指南

### 推荐工具

- **Loom**: Rust并发模型检查器
- **MIRI**: Rust的解释器，检测UB
- **Kani**: Rust的形式化验证工具
- **TLA+**: 高层次系统规约
- **SPIN**: 模型检查器

### 推荐书籍

- 《程序设计语言的形式语义》- Glynn Winskel
- 《Model Checking》- Clarke, Grumberg, Peled
- 《Types and Programming Languages》- Benjamin Pierce
- 《The Calculus of Computation》- Bradley, Manna

### 在线资源

- [Rust形式化小组](https://rust-formal.github.io/)
- [FMCAD会议论文集](https://fmcad.org/)
- [CAV会议论文集](http://www.i-cav.org/)

---

**形式化方法维护**: 项目维护团队  
**最后更新**: 2025-10-19  
**反馈**: [GitHub Issues](https://github.com/rust-lang/rust-lang/issues)

---

**开始探索**: 从语义模型开始，深入形式化验证！ 🔬
