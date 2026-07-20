# 统一数学符号指南 - Unified Mathematical Notation Guide

## 📊 目录

- [统一数学符号指南 - Unified Mathematical Notation Guide](#统一数学符号指南---unified-mathematical-notation-guide)
  - [📊 目录](#-目录)
  - [1. 概述 - Overview](#1-概述---overview)
  - [2. 基本符号 - Basic Notations](#2-基本符号---basic-notations)
    - [2.1 集合论符号 - Set Theory Notations](#21-集合论符号---set-theory-notations)
    - [2.2 逻辑符号 - Logical Notations](#22-逻辑符号---logical-notations)
  - [3. 类型系统符号 - Type System Notations](#3-类型系统符号---type-system-notations)
    - [3.1 基本类型符号 - Basic Type Notations](#31-基本类型符号---basic-type-notations)
    - [3.2 类型判断符号 - Type Judgment Notations](#32-类型判断符号---type-judgment-notations)
  - [4. 所有权和借用符号 - Ownership and Borrowing Notations](#4-所有权和借用符号---ownership-and-borrowing-notations)
    - [4.1 所有权符号 - Ownership Notations](#41-所有权符号---ownership-notations)
    - [4.2 借用符号 - Borrowing Notations](#42-借用符号---borrowing-notations)
  - [5. 操作语义符号 - Operational Semantics Notations](#5-操作语义符号---operational-semantics-notations)
    - [5.1 小步语义符号 - Small-Step Semantics Notations](#51-小步语义符号---small-step-semantics-notations)
    - [5.2 大步语义符号 - Big-Step Semantics Notations](#52-大步语义符号---big-step-semantics-notations)
  - [6. 并发和异步符号 - Concurrency and Async Notations](#6-并发和异步符号---concurrency-and-async-notations)
    - [6.1 并发符号 - Concurrency Notations](#61-并发符号---concurrency-notations)
    - [6.2 异步符号 - Async Notations](#62-异步符号---async-notations)
  - [7. 形式验证符号 - Formal Verification Notations](#7-形式验证符号---formal-verification-notations)
    - [7.1 霍尔逻辑符号 - Hoare Logic Notations](#71-霍尔逻辑符号---hoare-logic-notations)
    - [7.2 分离逻辑符号 - Separation Logic Notations](#72-分离逻辑符号---separation-logic-notations)
  - [8. 特征和泛型符号 - Traits and Generics Notations](#8-特征和泛型符号---traits-and-generics-notations)
    - [8.1 特征符号 - Trait Notations](#81-特征符号---trait-notations)
    - [8.2 泛型符号 - Generic Notations](#82-泛型符号---generic-notations)
  - [9. 使用指南 - Usage Guidelines](#9-使用指南---usage-guidelines)
  - [10. 符号扩展流程 - Notation Extension Process](#10-符号扩展流程---notation-extension-process)
  - [11. 参考资料 - References](#11-参考资料---references)

## 1. 概述 - Overview

本指南提供了Rust形式化理论项目中使用的所有数学符号的标准定义和使用规范。统一的符号系统对于确保理论的一致性、可读性和严谨性至关重要。

This guide provides standard definitions and usage specifications for all mathematical notations used in the Rust Formal Theory Project. A unified notation system is essential for ensuring consistency, readability, and rigor in theoretical work.

## 2. 基本符号 - Basic Notations

### 2.1 集合论符号 - Set Theory Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\in$ | 属于 - Element of | $x \in S$ | 表示元素x属于集合S - Indicates element x is in set S |
| $\notin$ | 不属于 - Not an element of | $x \notin S$ | 表示元素x不属于集合S - Indicates element x is not in set S |
| $\subset$ | 真子集 - Proper subset | $A \subset B$ | A是B的真子集（A≠B）- A is a proper subset of B (A≠B) |
| $\subseteq$ | 子集 - Subset | $A \subseteq B$ | A是B的子集（可能A=B）- A is a subset of B (possibly A=B) |
| $\cup$ | 并集 - Union | $A \cup B$ | A和B的并集 - Union of A and B |
| $\cap$ | 交集 - Intersection | $A \cap B$ | A和B的交集 - Intersection of A and B |
| $\emptyset$ | 空集 - Empty set | $A = \emptyset$ | 表示集合A为空 - Indicates set A is empty |
| $\mathbb{N}$ | 自然数集 - Set of natural numbers | $n \in \mathbb{N}$ | 包括0 - Including 0 |
| $\mathbb{Z}$ | 整数集 - Set of integers | $z \in \mathbb{Z}$ | |
| $\mathbb{R}$ | 实数集 - Set of real numbers | $r \in \mathbb{R}$ | |
| $\mathbb{B}$ | 布尔值集 - Set of boolean values | $b \in \mathbb{B}$ | $\mathbb{B} = \{\text{true}, \text{false}\}$ |
| $\{x \mid P(x)\}$ | 集合构建 - Set builder | $\{n \in \mathbb{N} \mid n > 5\}$ | 满足条件P(x)的所有x的集合 - Set of all x satisfying condition P(x) |

### 2.2 逻辑符号 - Logical Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\land$ | 逻辑与 - Logical AND | $P \land Q$ | P和Q都为真 - Both P and Q are true |
| $\lor$ | 逻辑或 - Logical OR | $P \lor Q$ | P或Q至少一个为真 - At least one of P or Q is true |
| $\lnot$ | 逻辑非 - Logical NOT | $\lnot P$ | P的否定 - Negation of P |
| $\Rightarrow$ | 蕴含 - Implies | $P \Rightarrow Q$ | 如果P为真，则Q为真 - If P is true, then Q is true |
| $\Leftarrow$ | 被蕴含 - Is implied by | $P \Leftarrow Q$ | 如果Q为真，则P为真 - If Q is true, then P is true |
| $\iff$ | 当且仅当 - If and only if | $P \iff Q$ | P为真当且仅当Q为真 - P is true if and only if Q is true |
| $\forall$ | 全称量词 - Universal quantifier | $\forall x. P(x)$ | 对所有x，P(x)为真 - For all x, P(x) is true |
| $\exists$ | 存在量词 - Existential quantifier | $\exists x. P(x)$ | 存在x使P(x)为真 - There exists an x such that P(x) is true |
| $\exists!$ | 唯一存在量词 - Unique existence | $\exists! x. P(x)$ | 存在唯一的x使P(x)为真 - There exists a unique x such that P(x) is true |

## 3. 类型系统符号 - Type System Notations

### 3.1 基本类型符号 - Basic Type Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\tau, \sigma$ | 类型变量 - Type variables | $\tau \to \sigma$ | 表示任意类型 - Represents arbitrary types |
| $T, S$ | 具体类型 - Concrete types | $\text{Vec}<T>$ | 表示特定类型 - Represents specific types |
| $\to$ | 函数类型 - Function type | $\tau \to \sigma$ | 从类型τ到类型σ的函数 - Function from type τ to type σ |
| $\times$ | 积类型 - Product type | $\tau \times \sigma$ | 类型τ和σ的笛卡尔积 - Cartesian product of types τ and σ |
| $+$ | 和类型 - Sum type | $\tau + \sigma$ | 类型τ或σ的并集 - Union of types τ and σ |
| $\mu X. \tau$ | 递归类型 - Recursive type | $\mu X. 1 + (T \times X)$ | 定义递归类型，如列表 - Defines recursive types like lists |
| $\bot$ | 底类型 - Bottom type | $\bot$ | 没有值的类型，如never - Type with no values, like never |
| $\top$ | 顶类型 - Top type | $\top$ | 包含所有值的类型 - Type containing all values |
| $\text{Option}<T>$ | 可选类型 - Option type | $\text{Option}<\text{i32}>$ | 可能包含T类型值或空值 - May contain a value of type T or nothing |
| $\text{Result}<T, E>$ | 结果类型 - Result type | $\text{Result}<\text{i32}, \text{Error}>$ | 包含T类型的成功值或E类型的错误值 - Contains a success value of type T or an error of type E |

### 3.2 类型判断符号 - Type Judgment Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\Gamma$ | 类型环境 - Type environment | $\Gamma = x: \tau, y: \sigma$ | 变量到类型的映射 - Mapping from variables to types |
| $\Gamma \vdash e : \tau$ | 类型判断 - Type judgment | $\Gamma \vdash x + 1 : \text{i32}$ | 在环境Γ下，表达式e的类型为τ - In environment Γ, expression e has type τ |
| $\Gamma \vdash \tau <: \sigma$ | 子类型判断 - Subtyping judgment | $\Gamma \vdash \text{i32} <: \text{i64}$ | 在环境Γ下，τ是σ的子类型 - In environment Γ, τ is a subtype of σ |
| $\tau \sim \sigma$ | 类型等价 - Type equivalence | $\text{Vec}<\text{i32}> \sim [\text{i32}]$ | 类型τ和σ等价 - Types τ and σ are equivalent |

## 4. 所有权和借用符号 - Ownership and Borrowing Notations

### 4.1 所有权符号 - Ownership Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\text{own}(x)$ | x的所有权 - Ownership of x | $\text{own}(x) \in \Gamma$ | 表示变量x在环境中拥有所有权 - Indicates variable x has ownership in the environment |
| $\text{move}(x)$ | 移动x的所有权 - Move ownership of x | $\text{move}(x) \Rightarrow \lnot \text{own}(x)$ | 表示x的所有权被移动 - Indicates ownership of x is moved |
| $\text{copy}(x)$ | 复制x的值 - Copy value of x | $\text{copy}(x) \land \text{own}(x)$ | 表示x的值被复制且x仍有所有权 - Indicates value of x is copied and x still has ownership |
| $\text{drop}(x)$ | 丢弃x - Drop x | $\text{drop}(x) \Rightarrow \lnot \text{own}(x)$ | 表示x被丢弃且失去所有权 - Indicates x is dropped and loses ownership |

### 4.2 借用符号 - Borrowing Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\&T$ | 不可变引用类型 - Immutable reference type | $\&\text{i32}$ | T类型的不可变引用 - Immutable reference to type T |
| $\&\text{mut}\ T$ | 可变引用类型 - Mutable reference type | $\&\text{mut}\ \text{Vec}<\text{i32}>$ | T类型的可变引用 - Mutable reference to type T |
| $\text{borrow}(x)$ | 借用x - Borrow x | $\text{borrow}(x) \Rightarrow \&x$ | 创建x的不可变引用 - Creates an immutable reference to x |
| $\text{borrow\_mut}(x)$ | 可变借用x - Mutably borrow x | $\text{borrow\_mut}(x) \Rightarrow \&\text{mut}\ x$ | 创建x的可变引用 - Creates a mutable reference to x |
| $\rho$ | 区域（生命周期）- Region (lifetime) | $\&^{\rho}T$ | 表示引用的生命周期 - Represents the lifetime of a reference |
| $\rho_1 \sqsubseteq \rho_2$ | 生命周期包含 - Lifetime inclusion | $\rho_1 \sqsubseteq \rho_2$ | 生命周期ρ₁包含在ρ₂中 - Lifetime ρ₁ is included in ρ₂ |

## 5. 操作语义符号 - Operational Semantics Notations

### 5.1 小步语义符号 - Small-Step Semantics Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $e \to e'$ | 单步归约 - Single-step reduction | $(\lambda x. x + 1)\ 2 \to 2 + 1$ | 表达式e归约到e' - Expression e reduces to e' |
| $\to^*$ | 多步归约 - Multi-step reduction | $e \to^* e'$ | e经过零步或多步归约到e' - e reduces to e' in zero or more steps |
| $e \Downarrow v$ | 求值 - Evaluation | $e \Downarrow v$ | 表达式e求值为值v - Expression e evaluates to value v |
| $e \Uparrow$ | 发散 - Divergence | $e \Uparrow$ | 表达式e的求值不终止 - Evaluation of expression e does not terminate |

### 5.2 大步语义符号 - Big-Step Semantics Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\langle e, \sigma \rangle \Rightarrow \langle v, \sigma' \rangle$ | 状态转换 - State transition | $\langle x := 1, \sigma \rangle \Rightarrow \langle (), \sigma[x \mapsto 1] \rangle$ | 在状态σ下执行e得到值v和新状态σ' - Executing e in state σ yields value v and new state σ' |
| $\sigma$ | 存储 - Store | $\sigma = \{x \mapsto 1, y \mapsto 2\}$ | 变量到值的映射 - Mapping from variables to values |
| $\sigma[x \mapsto v]$ | 存储更新 - Store update | $\sigma[x \mapsto 42]$ | 将变量x在存储中的值更新为v - Updates the value of variable x to v in the store |

## 6. 并发和异步符号 - Concurrency and Async Notations

### 6.1 并发符号 - Concurrency Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $e_1 \parallel e_2$ | 并行执行 - Parallel execution | $e_1 \parallel e_2$ | 表达式e₁和e₂并行执行 - Expressions e₁ and e₂ execute in parallel |
| $\text{spawn}(e)$ | 创建线程 - Spawn thread | $\text{spawn}(e) \to \text{tid}$ | 创建新线程执行e，返回线程ID - Creates a new thread executing e, returns thread ID |
| $\text{atomic}(e)$ | 原子执行 - Atomic execution | $\text{atomic}(e)$ | 原子地执行e - Executes e atomically |
| $\text{lock}(l)$ | 获取锁 - Acquire lock | $\text{lock}(l)$ | 获取锁l - Acquires lock l |
| $\text{unlock}(l)$ | 释放锁 - Release lock | $\text{unlock}(l)$ | 释放锁l - Releases lock l |

### 6.2 异步符号 - Async Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\text{Future}<T>$ | 未来值值值值类型 - Future type | $\text{Future}<\text{i32}>$ | 表示将来可能产生T类型值的计算 - Represents a computation that may produce a value of type T in the future |
| $\text{async}\ e$ | 异步表达式 - Async expression | $\text{async}\ \{f(x)\}$ | 创建异步计算 - Creates an asynchronous computation |
| $\text{await}\ e$ | 等待表达式 - Await expression | $\text{await}\ f$ | 等待异步计算完成 - Waits for an asynchronous computation to complete |
| $\text{Poll::Ready}(v)$ | 就绪状态 - Ready state | $\text{Poll::Ready}(42)$ | 表示异步计算已完成，值为v - Indicates async computation is complete with value v |
| $\text{Poll::Pending}$ | 挂起状态 - Pending state | $\text{Poll::Pending}$ | 表示异步计算尚未完成 - Indicates async computation is not yet complete |

## 7. 形式验证符号 - Formal Verification Notations

### 7.1 霍尔逻辑符号 - Hoare Logic Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\{P\}\ e\ \{Q\}$ | 霍尔三元组 - Hoare triple | $\{x > 0\}\ y := x + 1\ \{y > 1\}$ | 前置条件P，执行e后满足后置条件Q - Precondition P, executing e establishes postcondition Q |
| $\{P\}\ e\ \{Q\}_{\text{partial}}$ | 部分正确性 - Partial correctness | $\{P\}\ e\ \{Q\}_{\text{partial}}$ | 如果e终止，则满足Q - If e terminates, then Q holds |
| $\{P\}\ e\ \{Q\}_{\text{total}}$ | 完全正确性 - Total correctness | $\{P\}\ e\ \{Q\}_{\text{total}}$ | e终止且满足Q - e terminates and Q holds |
| $\text{inv}(I)$ | 循环不变量 - Loop invariant | $\text{inv}(0 \leq i \leq n)$ | 循环执行过程中保持不变的条件I - Condition I that remains true throughout loop execution |

### 7.2 分离逻辑符号 - Separation Logic Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $P * Q$ | 分离合取 - Separating conjunction | $x \mapsto v_1 * y \mapsto v_2$ | P和Q在不相交的堆区域上成立 - P and Q hold on disjoint heap regions |
| $P -* Q$ | 分离蕴含 - Separating implication | $P -* Q$ | 如果与P在不相交区域上的状态合并，则Q成立 - If merged with a state satisfying P on a disjoint region, then Q holds |
| $x \mapsto v$ | 指针断言 - Points-to assertion | $x \mapsto 42$ | 地址x存储值v - Address x stores value v |
| $\text{emp}$ | 空堆断言 - Empty heap assertion | $\text{emp}$ | 堆为空 - Heap is empty |

## 8. 特征和泛型符号 - Traits and Generics Notations

### 8.1 特征符号 - Trait Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $\text{trait}\ T$ | 特征定义 - Trait definition | $\text{trait}\ \text{Display}$ | 定义特征T - Defines trait T |
| $T : \tau$ | 特征约束 - Trait constraint | $T : \text{Display}$ | 类型T实现了特征τ - Type T implements trait τ |
| $\tau_1 + \tau_2$ | 特征组合 - Trait combination | $\text{Display} + \text{Debug}$ | 类型必须同时实现特征τ₁和τ₂ - Type must implement both traits τ₁ and τ₂ |
| $\text{impl}\ \tau\ \text{for}\ T$ | 特征实现 - Trait implementation | $\text{impl}\ \text{Display}\ \text{for}\ \text{i32}$ | 为类型T实现特征τ - Implements trait τ for type T |

### 8.2 泛型符号 - Generic Notations

| 符号 - Symbol | 含义 - Meaning | 示例 - Example | 注意事项 - Notes |
|--------------|---------------|---------------|----------------|
| $T<\tau>$ | 泛型类型 - Generic type | $\text{Vec}<\text{i32}>$ | 具有类型参数τ的泛型类型T - Generic type T with type parameter τ |
| $\forall \alpha. \tau$ | 通用量化 - Universal quantification | $\forall \alpha. \alpha \to \alpha$ | 对所有类型α，类型表达式τ - For all types α, the type expression τ |
| $\exists \alpha. \tau$ | 存在量化 - Existential quantification | $\exists \alpha. \alpha \times (\alpha \to \text{bool})$ | 存在类型α使得类型表达式τ成立 - There exists a type α such that the type expression τ holds |
| $\Lambda \alpha. e$ | 类型抽象 - Type abstraction | $\Lambda \alpha. \lambda x:\alpha. x$ | 创建泛型函数 - Creates a generic function |
| $e[\tau]$ | 类型应用 - Type application | $[\Lambda \alpha. \lambda x:\alpha. x](\text{i32})$ | 将泛型函数应用于具体类型 - Applies a generic function to a concrete type |

## 9. 使用指南 - Usage Guidelines

1. **一致性原则 - Consistency Principle**:
   - 在整个项目中使用相同的符号表示相同的概念
   - 避免重载符号，除非有明确的上下文区分

2. **清晰性原则 - Clarity Principle**:
   - 优先使用标准符号，避免创造新符号
   - 在引入新符号时提供明确的定义和解释

3. **上下文原则 - Context Principle**:
   - 在每个文档的开始明确使用的符号系统
   - 在需要时提供符号表或引用本指南

4. **可读性原则 - Readability Principle**:
   - 避免过度使用符号导致可读性下降
   - 在复杂表达式中使用适当的空格和分组

5. **双语表示原则 - Bilingual Representation Principle**:
   - 确保所有符号在中英文环境中有一致的解释
   - 在需要时提供符号的中英文对照解释

## 10. 符号扩展流程 - Notation Extension Process

当需要引入新符号或修改现有符号时，请遵循以下流程：

1. **提案 - Proposal**:
   - 提交新符号或修改的正式提案
   - 包括符号的定义、用法和理由

2. **评审 - Review**:
   - 由理论专家组进行评审
   - 检查与现有符号系统的一致性和兼容性

3. **试用 - Trial**:
   - 在有限作用域内试用新符号
   - 收集使用反馈和改进建议

4. **标准化 - Standardization**:
   - 将批准的符号添加到本指南
   - 更新相关文档以使用新符号

5. **传播 - Dissemination**:
   - 通知所有项目参与者符号变更
   - 提供必要的培训和支持

## 11. 参考资料 - References

1. Pierce, B.C. (2002). Types and Programming Languages. MIT Press.
2. Harper, R. (2016). Practical Foundations for Programming Languages. Cambridge University Press.
3. Reynolds, J.C. (2002). Separation Logic: A Logic for Shared Mutable Data Structures. LICS '02.
4. Rust Reference (2023). The Rust Programming Language Reference.
5. Jung, R., et al. (2018). RustBelt: Securing the foundations of the Rust programming language. POPL 2018.

---

*Version: 1.0*  
*Last Updated: 2025-03-01*  
*Status: Official Standard*  
*Maintainer: Theoretical Foundations Team*
