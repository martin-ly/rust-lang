> **Summary**:
>
> Rust Effect System Boundary Analysis. Core Rust concept.
>
# Rust 效应系统（Effect System）与其语言边界的分析论证
>
> **EN**: Rust Effect System Boundary Analysis
> **文档性质**：形式化分析论证 | **对齐标准**：PLDI、POPL、ICFP 等国际顶会学术传统
> **核心问题**：Rust 的类型系统（Type System）是否构成效应系统？其边界在哪里？与代数效应、能力系统、所有权（Ownership）系统的本质差异为何？
>
> **来源**: [Rust RFCs](https://github.com/rust-lang/rfcs) · [Rust Blog](https://blog.rust-lang.org/)
> **前置概念**: N/A
> **后置概念**: N/A
---

## 目录

- [Rust 效应系统（Effect System）与其语言边界的分析论证](#rust-效应系统effect-system与其语言边界的分析论证)
  - [目录](#目录)
  - [一、术语澄清与概念谱系](#一术语澄清与概念谱系)
    - [1.1 效应系统的学术定义](#11-效应系统的学术定义)
    - [1.2 资源所有权系统的独立范畴](#12-资源所有权系统的独立范畴)
    - [1.3 对象能力模型（Object Capability Model）](#13-对象能力模型object-capability-model)
  - [二、Rust 的"准效应系统"：五种控制流效应](#二rust-的准效应系统五种控制流效应)
    - [2.1 效应的枚举与分类](#21-效应的枚举与分类)
    - [2.2 Carried vs. Uncarried Effects 的边界](#22-carried-vs-uncarried-effects-的边界)
  - [三、Rust 的内存安全效应：所有权与借用](#三rust-的内存安全效应所有权与借用)
    - [3.1 所有权作为内存效应管理器](#31-所有权作为内存效应管理器)
    - [3.2 所有权系统与效应系统的本质差异](#32-所有权系统与效应系统的本质差异)
    - [3.3 基本所有权纪律的形式化描述](#33-基本所有权纪律的形式化描述)
  - [四、控制流效应的边界：Rust 的设计约束](#四控制流效应的边界rust-的设计约束)
    - [4.1 三种核心控制流效应](#41-三种核心控制流效应)
    - [4.2 零成本抽象约束下的效应边界](#42-零成本抽象约束下的效应边界)
    - [4.3 可挂起计算的边界选择](#43-可挂起计算的边界选择)
  - [五、跨语言边界对比矩阵](#五跨语言边界对比矩阵)
    - [5.1 效应系统的四种学术范式](#51-效应系统的四种学术范式)
    - [5.2 Rust 与 Scala 3 Capture Checking 的深层对比](#52-rust-与-scala-3-capture-checking-的深层对比)
  - [六、形式化边界论证：为何 Rust 无法拥有通用效应系统](#六形式化边界论证为何-rust-无法拥有通用效应系统)
    - [6.1 定理一：零成本抽象与通用效应处理器的不相容性](#61-定理一零成本抽象与通用效应处理器的不相容性)
    - [6.2 定理二：Uncarried Effects 的类型系统不可组合性](#62-定理二uncarried-effects-的类型系统不可组合性)
    - [6.3 定理三：所有权纪律与效应追踪的不可通约性](#63-定理三所有权纪律与效应追踪的不可通约性)
  - [七、unsafe 边界的特殊地位：能力逃逸通道](#七unsafe-边界的特殊地位能力逃逸通道)
    - [7.1 unsafe 作为元效应](#71-unsafe-作为元效应)
    - [7.2 unsafe 的模块化封装论证](#72-unsafe-的模块化封装论证)
  - [八、结论：Rust 效应系统的三重边界](#八结论rust-效应系统的三重边界)
    - [8.1 边界一：内存效应 vs. 控制流效应的分裂](#81-边界一内存效应-vs-控制流效应的分裂)
    - [8.2 边界二：Carried vs. Uncarried 的类型系统断层](#82-边界二carried-vs-uncarried-的类型系统断层)
    - [8.3 边界三：零成本抽象 vs. 通用效应表达的不相容](#83-边界三零成本抽象-vs-通用效应表达的不相容)
    - [8.4 工程哲学总结](#84-工程哲学总结)
  - [参考文献索引](#参考文献索引)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：《Rust 效应系统（Effect System）与其语言边界的分析论证》是一份归档文件。归档文件在知识体系中有什么作用？（理解层）](#测验-1rust-效应系统effect-system与其语言边界的分析论证是一份归档文件归档文件在知识体系中有什么作用理解层)
    - [测验 2：阅读归档文件时应该注意什么？（理解层）](#测验-2阅读归档文件时应该注意什么理解层)
    - [测验 3：归档文件与活跃概念文件的主要区别是什么？（理解层）](#测验-3归档文件与活跃概念文件的主要区别是什么理解层)

## 一、术语澄清与概念谱系

### 1.1 效应系统的学术定义

根据 EPFL 博士论文对形式化安全语言的分类框架citeweb_search:1#0，效应系统（Type-and-Effect System）的核心判据是：

> **typing judgement 同时赋予项（term）一个类型（type）和一个效应（effect）**。早期效应系统追踪可变状态访问（Lucassen & Gifford, 1988），后扩展至异常抛出、发散性（divergence）等可观察效应（Leijen, 2014）。代数效应与效应处理器（Plotkin & Power, 2003；Plotkin & Pretnar, 2013）则提供了用户自定义效应的强表达能力。

### 1.2 资源所有权系统的独立范畴

同一文献明确将 Rust 归类为**资源所有权系统（Resource Ownership System）**，而非效应系统：

> "Rust is perhaps the most widely known such system, especially if we take into account its industry mindshare."citeweb_search:1#0

资源所有权系统的核心机制是：

- 通过**身份或来源（identity / provenance）**追踪资源
- 限制资源的**别名方式（aliasing discipline）**
- 在堆上强制特定拓扑结构（如线性类型 Wadler, 1990）

### 1.3 对象能力模型（Object Capability Model）

作为第三类安全机制，对象能力模型声明：敏感功能只能通过调用**能力对象（capability objects）**的方法访问，且能力安全代码不应拥有**环境权威（ambient authority）**（Miller, 2006）citeweb_search:1#0。此模型与 Rust 的 `unsafe` 边界存在概念映射，但属于不同范式。

---

## 二、Rust 的"准效应系统"：五种控制流效应

### 2.1 效应的枚举与分类

根据 Rust 语言设计博客的权威梳理，Rust 当前存在五种效应citeweb_search:1#2：

| 效应 | 语法形式 | 类型系统表现 | 完成度 | 分类 |
|------|----------|--------------|--------|------|
| `async` | `async fn`, `async {}` | **Carried**：desugar 为 `impl Future` | 稳定 | 控制流效应 |
| `unsafe` | `unsafe fn`, `unsafe {}` | **Uncarried**：仅向编译器传递信息，无对应类型 | 稳定 | 能力/权限效应 |
| `const` | `const fn` | **Uncarried**：编译期求值约束，无运行时（Runtime）类型 | 部分稳定（trait 支持尚不稳定） | 阶段效应 |
| `try` | `?` 运算符，`try {}`（不稳定） | **Carried**：与 `Result` 类型强关联 | 部分稳定 | 控制流效应 |
| `generators` | `|| { yield }`（不稳定） | **Carried**：desugar 为状态机 | 完全不稳定 | 控制流效应 |

### 2.2 Carried vs. Uncarried Effects 的边界

这是 Rust 效应系统的**第一条核心边界**：

> **Carried effects** 在类型系统中有具体 lowering 目标（如 `async fn` → `impl Future<Output = T>`）。**Uncarried effects** 仅作为编译器内部信息传递，不进入类型系统的可组合层citeweb_search:1#2。

此边界导致 Rust 的效应**不可在类型层面进行高阶抽象组合**。例如，`const` 和 `unsafe` 无法像 `async` 那样通过 trait bound 进行泛化编程。

---

## 三、Rust 的内存安全效应：所有权与借用

### 3.1 所有权作为内存效应管理器

Rust 语言核心贡献者 boats 明确指出：

> "Rust has an excellent system for managing effects related to mutation and memory: this is what ownership and borrowing is all about, and it beautifully guarantees soundness even in the presence of concurrent mutation."citeweb_search:1#13

所有权系统管理的是**内存效应（memory effects）**：

- **突变（mutation）**
- **别名（aliasing）**
- **生命周期（lifetime）**
- **并发访问（concurrent access）**

### 3.2 所有权系统与效应系统的本质差异

| 维度 | 代数效应系统（Koka / Eff） | Rust 所有权系统 |
|------|---------------------------|-----------------|
| **追踪目标** | 可观察计算效应（IO、状态、异常、非确定性） | 资源生命周期（Lifetimes）与别名拓扑 |
| **抽象机制** | 效应处理器（effect handlers），高阶组合 | 借用（Borrowing）检查器（borrow checker），局部推理 |
| **可扩展性** | 用户可定义新效应 | 用户无法定义新所有权规则（仅通过 `unsafe` 绕过） |
| **组合方式** | 效应行多态（row polymorphism） | 生命周期（Lifetimes）参数化（lifetime parametrization） |
| **运行时（Runtime）表现** | 通常需要运行时支持（continuation 捕获/恢复） | 零成本抽象（Zero-Cost Abstraction），纯编译期消除 |

### 3.3 基本所有权纪律的形式化描述

根据 RustBelt 论文（Jung et al., POPL 2018）citeweb_search:1#3：

> "The basic ownership discipline enforced by Rust's type system is a simple one: If ownership of an object (of type T) is shared between multiple aliases ('shared references' of type `&T`), then none of them can be used to directly mutate it."

此纪律消除了 use-after-free、data races、iterator invalidation 等错误类，但对依赖别名可变状态的数据结构过于严格。因此标准库广泛使用 `unsafe` 操作扩展表达能力，形成**安全边界内的模块（Module）化松弛**。

---

## 四、控制流效应的边界：Rust 的设计约束

### 4.1 三种核心控制流效应

boats 将 Rust 中的控制流效应归纳为三类citeweb_search:1#13：

1. **Fallibility（可失败性）**：代码段无法完成并求值到预期结果 → `Result<T, E>`
2. **Multiplicity（多重性）**：代码段被求值多次 → `Iterator` / 循环
3. **Asynchrony（异步（Async）性）**：代码段在无法立即进展时让出控制流 → `Future`

### 4.2 零成本抽象约束下的效应边界

Rust 对更强效应设施的排斥有**充分理由**：

> "The primary cause is Rust's commitment to 'zero-cost' abstractions, which must be highly optimizable, be local in their performance impact, and give a high degree of control to the programmer. None of the elements of stronger effect facilities in widespread use (unwinding, greenthreads, internal iteration, boxed callbacks, etc) were able to meet this constraint."citeweb_search:1#13

这意味着 Rust 的效应系统边界由**性能契约**严格划定：

- 不允许运行时（Runtime） continuation 捕获（如代数效应处理器通常所需）
- 不允许隐式分配（如 green threads 或 boxed closures）
- 效应传播必须是局部可优化的（如 `?` 运算符和 `async/await` 的语法糖）

### 4.3 可挂起计算的边界选择

Abubalay 的分析揭示了 Rust 与典型代数效应语言在**计算边界**上的根本差异citeweb_search:1#9：

> "Typical languages with effects treat the whole chain of stack frames between handler and operation as a single computation to be suspended and resumed all at once... Rust instead treats individual function bodies and blocks as distinct computations to be handled individually."

这导致 Rust 的 `async` 效应：**函数体是效应边界的最小单元**，而非跨函数的调用链。`?` 运算符因此表现为一种"no-op handler"，立即重新执行效应以跨计算单元传播，而非在运行时（Runtime）捕获 continuation。

---

## 五、跨语言边界对比矩阵

### 5.1 效应系统的四种学术范式

| 语言/系统 | 效应模型 | 所有权（Ownership）/能力 | 运行时（Runtime）成本 | 用户可扩展性 | 与 Rust 的边界关系 |
|-----------|----------|-------------|------------|--------------|-------------------|
| **Haskell** | Monad / Monad Transformer | 无（GC 管理） | 高（ thunk 求值 + 运行时栈） | 高（自定义 Monad） | Rust 拒绝 Monad 作为默认抽象，因其非零成本 |
| **Koka / Eff** | 代数效应 + 处理器 | 无 | 中（continuation 捕获） | 极高（用户定义效应 + 处理器） | Rust 的 `async` 可视为受限代数效应，但无通用处理器 |
| **Scala 3** | Capture Checking（能力捕获） | 能力系统（capability-based） | 低（编译期擦除） | 中（通过 `using` 子句） | 与 Rust 的 Send/Sync trait bounds 概念接近，但 Scala 3 是显式能力传递 |
| **Swift** | 结构化并发 + 异步函数 | ARC（引用（Reference）计数） | 低 | 低（内置效应） | 与 Rust async 最相似，但 Swift 有隐式 executor 切换 |
| **Rust** | 语法糖 + 类型 lowering | 所有权 + 借用（Borrowing） + unsafe 边界 | 零成本 | 低（仅语言内置效应） | **本文分析对象** |

### 5.2 Rust 与 Scala 3 Capture Checking 的深层对比

Scala 3 的 capture checking（Odersky et al., 2022-2024）尝试在 JVM 生态中引入类似 Rust 的能力追踪，但关键差异在于：

- **Rust**：能力通过类型系统隐式追踪（`Send`、`Sync`、`'static`），错误表现为生命周期（Lifetimes）不匹配
- **Scala 3**：能力通过 `^{Cap}` 语法显式标注，保留 JVM 的 GC 和运行时灵活性

Rust 的边界更严格：能力即类型约束，无运行时能力对象。

---

## 六、形式化边界论证：为何 Rust 无法拥有通用效应系统

### 6.1 定理一：零成本抽象与通用效应处理器的不相容性

**命题**：在 Rust 的零成本抽象（Zero-Cost Abstraction）约束下，通用代数效应处理器（general-purpose algebraic effect handlers）不可实现。

**论证**：

1. 通用效应处理器需要**捕获并恢复 continuation**，这要求运行时保存调用栈片段（stack fragments）或堆分配闭包（Closures）。
2. Rust 的零成本抽象要求：抽象不引入超出手写汇编的额外运行时开销（Sutter 的 "pay only for what you use" 原则）。
3. continuation 捕获的最低成本是**栈切换或堆分配**，这与 Rust 的局部性能控制契约冲突。
4. 因此，Rust 只能实现**静态可消除的效应**（如 `async` → 状态机 lowering，`try` → `Result` 传播），而无法实现动态 handlers。

### 6.2 定理二：Uncarried Effects 的类型系统不可组合性

**命题**：`const` 与 `unsafe` 作为 uncarried effects，无法在 Rust 类型系统中进行高阶泛化。

**论证**：

1. Carried effects（`async`, `try`）有对应的类型构造器（`Future`, `Result`），因此可通过 trait bound 抽象（`T: Future`, `T: Try`）。
2. Uncarried effects 无类型构造器，仅作为函数修饰符存在。
3. Rust 的类型系统基于参数化多态（parametric polymorphism），要求抽象变量具有**kind * 或更高 kind**。
4. 由于 `const`/`unsafe` 不对应类型，无法参数化，导致**效应泛型（effect generics）** 需引入新的类型系统层级（如 `#[maybe(async)]` 的语法实验citeweb_search:1#2）。

### 6.3 定理三：所有权纪律与效应追踪的不可通约性

**命题**：Rust 的所有权系统与标准效应系统在数学结构上不可归约（irreducible）。

**论证**：

1. 效应系统的语义通常基于**可观察性（observability）**：一个效应是计算与外部环境的交互（Plotkin & Power 的代数效应语义）。
2. Rust 的所有权纪律基于**资源拓扑（resource topology）**：关注的是内存位置的可访问性图（accessibility graph），而非计算与环境的交互。
3. 虽然数据竞争可视为一种"并发效应"，但 Rust 通过**别名限制**而非**效应追踪**消除它。
4. 因此，所有权系统是**空间安全（spatial safety）**机制，效应系统是**行为安全（behavioral safety）**机制，二者属于正交维度。

---

## 七、unsafe 边界的特殊地位：能力逃逸通道

### 7.1 unsafe 作为元效应

`unsafe` 在 Rust 中扮演独特角色：它不是追踪某种计算效应，而是**解除类型系统的保证**。这使其更接近**对象能力模型**中的特权操作：

> "Capability-safe code should additionally have no ambient authority... an object should only be able to access pre-existing capabilities if it receives them from another object."citeweb_search:1#0

`unsafe` 块可视为一种**显式能力声明**：程序员在此区域内获得了绕过借用（Borrowing）检查器的能力，但必须自行维护不变量。

### 7.2 unsafe 的模块化封装论证

RustBelt 形式化验证了 `unsafe` 的标准库使用模式citeweb_search:1#3：

> "These libraries extend the expressive power of Rust's type system by loosening its ownership discipline on aliased mutable state in a modular, controlled fashion... Even though a shared reference of type `&T` may not be used to directly mutate the contents of the reference, it may nonetheless be used to indirectly mutate them by passing it to one of the observably 'safe' (but internally unsafe) methods."

这形成了 Rust 的**安全边界定理**：safe Rust 的程序行为仅依赖于 safe API 的契约，unsafe 实现的内部细节被模块（Module）化隔离。

---

## 八、结论：Rust 效应系统的三重边界

### 8.1 边界一：内存效应 vs. 控制流效应的分裂

Rust 的所有权系统卓越地管理**内存效应**，但控制流效应（async/try/iterators）通过独立的语法糖和类型 lowering 管理，二者无统一抽象框架。

### 8.2 边界二：Carried vs. Uncarried 的类型系统断层

`async` 和 `try` 可进入类型系统，`const`、`unsafe` 和 `generators` 不能，导致效应的**可组合性边界**泾渭分明。效应泛型（effect generics）是 Rust 语言团队正在探索的跨越此边界的方案citeweb_search:1#2。

### 8.3 边界三：零成本抽象 vs. 通用效应表达的不相容

Rust 拒绝运行时 continuation 捕获和隐式分配，这从根本上排除了通用代数效应处理器。Rust 的效应系统因此是**静态可消除效应的闭包（Closures）**，而非开放的用户可扩展框架。

### 8.4 工程哲学总结

Rust 的效应系统边界不是技术债务，而是**有意识的工程哲学选择**：

> "Rust experimented with all of these concepts at some point in its history, it wasn't out of ignorance that they were excluded."citeweb_search:1#13

Rust 在**表达能力**与**性能可控性**之间选择了后者，通过将效应限制为编译期可消除的语法结构，维持了系统编程语言的核心承诺。这一边界使 Rust 区别于 Koka、Eff、Haskell 等以效应为首要抽象的语言，也区别于 Scala 3 等尝试在托管运行时中融合能力系统的语言。

---

## 参考文献索引

| 引用（Reference） | 来源 | 权威性 |
|------|------|--------|
| EPFL 博士论文 | 形式化安全语言分类框架 | S（学术机构） |
| boats 博客 | "The problem of effects in Rust" | 高（Rust 语言核心贡献者） |
| Yoshua Wuyts 博客 | "Extending Rust's Effect System" | 高（Rust 异步（Async）生态核心维护者） |
| Abubalay 博客 | "A universal lowering strategy for control effects in Rust" | 中（独立 PL 研究） |
| Jung et al., POPL 2018 | RustBelt: Securing the Foundations of the Rust Programming Language | S（顶级会议论文） |
| Plotkin & Power, 2003 | Algebraic Operations and Generic Effects | S（代数效应奠基论文） |
| Lucassen & Gifford, 1988 | Polymorphic Effect Systems | S（效应系统奠基论文） |
| Leijen, 2014 | Koka: Programming with Row Polymorphic Effect Types | S（行多态效应类型） |

---

*文档生成时间：2026-06-02*
*对齐标准：POPL / PLDI / ICFP / OOPSLA 学术传统*
*论证方法：形式化定义 → 边界枚举（Enum） → 跨语言对比 → 定理论证 → 工程哲学总结*

## 嵌入式测验（Embedded Quiz）

### 测验 1：《Rust 效应系统（Effect System）与其语言边界的分析论证》是一份归档文件。归档文件在知识体系中有什么作用？（理解层）

**题目**: 《Rust 效应系统（Effect System）与其语言边界的分析论证》是一份归档文件。归档文件在知识体系中有什么作用？

<details>
<summary>✅ 答案与解析</summary>

保留历史版本的内容，便于追溯概念演变、对比新旧表述，同时避免活跃学习路径被过时信息干扰。
</details>

---

### 测验 2：阅读归档文件时应该注意什么？（理解层）

**题目**: 阅读归档文件时应该注意什么？

<details>
<summary>✅ 答案与解析</summary>

注意文件顶部的归档说明和最后更新日期，理解其历史上下文，不要将其中的过时信息当作当前最佳实践。
</details>

---

### 测验 3：归档文件与活跃概念文件的主要区别是什么？（理解层）

**题目**: 归档文件与活跃概念文件的主要区别是什么？

<details>
<summary>✅ 答案与解析</summary>

归档文件不再维护更新，反映的是历史状态；活跃概念文件持续迭代，包含最新的语言特性和最佳实践。
</details>
