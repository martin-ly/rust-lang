> **Summary**:
>
> Rust Effect System Comprehensive Analysis. Core Rust concept.
>
# Rust 效应系统（Effect System）与其语言边界的全面分析论证
>
> **EN**: Rust Effect System Comprehensive Analysis
> **文档性质**：形式化分析论证 | **对齐标准**：PLDI、POPL、ICFP、OOPSLA 国际顶会学术传统
> **核心问题**：Rust 的类型系统是否构成效应系统？其边界在哪里？与代数效应、能力系统、所有权系统的本质差异为何？
> **表征方式**：思维导图 · 多维矩阵 · 定理推理判定树 · 边界语义空间决策树 · 结构化论证表格
>
> **来源**: [Rust RFCs](https://github.com/rust-lang/rfcs) · [Rust Blog](https://blog.rust-lang.org/)
---

## 目录

- [Rust 效应系统（Effect System）与其语言边界的全面分析论证](#rust-效应系统effect-system与其语言边界的全面分析论证)
  - [目录](#目录)
  - [一、术语澄清与概念谱系](#一术语澄清与概念谱系)
    - [1.1 效应系统的学术定义](#11-效应系统的学术定义)
    - [1.2 资源所有权系统的独立范畴](#12-资源所有权系统的独立范畴)
    - [1.3 对象能力模型（Object Capability Model）](#13-对象能力模型object-capability-model)
  - [二、表征一：概念谱系思维导图](#二表征一概念谱系思维导图)
  - [三、Rust 的"准效应系统"：五种控制流效应](#三rust-的准效应系统五种控制流效应)
    - [3.1 效应的枚举与分类](#31-效应的枚举与分类)
    - [3.2 Carried vs. Uncarried Effects 的边界](#32-carried-vs-uncarried-effects-的边界)
  - [四、表征二：跨语言效应系统多维矩阵](#四表征二跨语言效应系统多维矩阵)
    - [4.1 矩阵解读：Rust 的能力轮廓](#41-矩阵解读rust-的能力轮廓)
  - [五、Rust 的内存安全效应：所有权与借用](#五rust-的内存安全效应所有权与借用)
    - [5.1 所有权作为内存效应管理器](#51-所有权作为内存效应管理器)
    - [5.2 所有权系统与效应系统的本质差异](#52-所有权系统与效应系统的本质差异)
    - [5.3 基本所有权纪律的形式化描述](#53-基本所有权纪律的形式化描述)
  - [六、控制流效应的边界：Rust 的设计约束](#六控制流效应的边界rust-的设计约束)
    - [6.1 三种核心控制流效应](#61-三种核心控制流效应)
    - [6.2 零成本抽象约束下的效应边界](#62-零成本抽象约束下的效应边界)
    - [6.3 可挂起计算的边界选择](#63-可挂起计算的边界选择)
  - [七、表征三：决策定理推理判定树图](#七表征三决策定理推理判定树图)
    - [7.1 定理一：零成本抽象与通用效应处理器的不相容性](#71-定理一零成本抽象与通用效应处理器的不相容性)
    - [7.2 定理二：Uncarried Effects 的类型系统不可组合性](#72-定理二uncarried-effects-的类型系统不可组合性)
    - [7.3 定理三：所有权纪律与效应追踪的不可通约性](#73-定理三所有权纪律与效应追踪的不可通约性)
  - [八、表征四：边界语义空间决策树图](#八表征四边界语义空间决策树图)
    - [8.1 语义空间的三维定位](#81-语义空间的三维定位)
  - [九、Keyword Generics Initiative：跨越边界的尝试](#九keyword-generics-initiative跨越边界的尝试)
    - [9.1 效应泛型的提出](#91-效应泛型的提出)
    - [9.2 效应子句语法提案](#92-效应子句语法提案)
    - [9.3 效应泛型的局限与边界](#93-效应泛型的局限与边界)
  - [十、unsafe 边界的特殊地位：能力逃逸通道](#十unsafe-边界的特殊地位能力逃逸通道)
    - [10.1 unsafe 作为元效应](#101-unsafe-作为元效应)
    - [10.2 unsafe 的模块化封装与形式化验证](#102-unsafe-的模块化封装与形式化验证)
  - [十一、跨语言边界深度对比](#十一跨语言边界深度对比)
    - [11.1 效应系统的四种学术范式](#111-效应系统的四种学术范式)
    - [11.2 Koka 与 Rust 的根本分野](#112-koka-与-rust-的根本分野)
    - [11.3 Haskell 效应库生态的启示](#113-haskell-效应库生态的启示)
  - [十二、结论：Rust 效应系统的三重边界](#十二结论rust-效应系统的三重边界)
    - [12.1 边界一：内存效应 vs. 控制流效应的分裂](#121-边界一内存效应-vs-控制流效应的分裂)
    - [12.2 边界二：Carried vs. Uncarried 的类型系统断层](#122-边界二carried-vs-uncarried-的类型系统断层)
    - [12.3 边界三：零成本抽象 vs. 通用效应表达的不相容](#123-边界三零成本抽象-vs-通用效应表达的不相容)
    - [12.4 工程哲学总结](#124-工程哲学总结)
  - [十三、参考文献索引](#十三参考文献索引)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：《Rust 效应系统（Effect System）与其语言边界的全面分析论证》是一份归档文件。归档文件在知识体系中有什么作用？（理解层）](#测验-1rust-效应系统effect-system与其语言边界的全面分析论证是一份归档文件归档文件在知识体系中有什么作用理解层)
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

## 二、表征一：概念谱系思维导图

![Rust 效应系统概念谱系思维导图](sandbox:///mnt/agents/output/rust_effect_mindmap.png)

**图1：Rust 效应系统概念谱系思维导图** — 展示 Rust 语言中效应类型系统、资源所有权系统、对象能力模型三大范式的层级结构，以及 Carried/Uncarried 效应、借用检查器、能力令牌等关键概念的从属关系。底部标注三重核心边界。

---

## 三、Rust 的"准效应系统"：五种控制流效应

### 3.1 效应的枚举与分类

根据 Rust 语言设计博客的权威梳理，Rust 当前存在五种效应citeweb_search:1#2：

| 效应 | 语法形式 | 类型系统表现 | 完成度 | 分类 |
|------|----------|--------------|--------|------|
| `async` | `async fn`, `async {}` | **Carried**：desugar 为 `impl Future` | 稳定 | 控制流效应 |
| `unsafe` | `unsafe fn`, `unsafe {}` | **Uncarried**：仅向编译器传递信息，无对应类型 | 稳定 | 能力/权限效应 |
| `const` | `const fn` | **Uncarried**：编译期求值约束，无运行时类型 | 部分稳定（trait 支持尚不稳定） | 阶段效应 |
| `try` | `?` 运算符，`try {}`（不稳定） | **Carried**：与 `Result` 类型强关联 | 部分稳定 | 控制流效应 |
| `generators` | `|| { yield }`（不稳定） | **Carried**：desugar 为状态机 | 完全不稳定 | 控制流效应 |

### 3.2 Carried vs. Uncarried Effects 的边界

这是 Rust 效应系统的**第一条核心边界**：

> **Carried effects** 在类型系统中有具体 lowering 目标（如 `async fn` → `impl Future<Output = T>`）。**Uncarried effects** 仅作为编译器内部信息传递，不进入类型系统的可组合层citeweb_search:1#2。

此边界导致 Rust 的效应**不可在类型层面进行高阶抽象组合**。例如，`const` 和 `unsafe` 无法像 `async` 那样通过 trait bound 进行泛化编程。

---

## 四、表征二：跨语言效应系统多维矩阵

![跨语言效应系统能力成熟度多维矩阵](sandbox:///mnt/agents/output/rust_effect_multidim_matrix.png)

**图2：跨语言效应系统能力成熟度多维矩阵** — 在十个关键维度上对比 Rust、Haskell、Koka、Eff、OCaml 5、Scala 3、Swift 和 C++。Rust 在"零成本抽象"和"内存安全(所有权)"维度获得满分，但在"用户可定义效应"、"效应处理器"、"运行时Continuation捕获"维度得分极低，直观展示其设计取舍。

### 4.1 矩阵解读：Rust 的能力轮廓

从矩阵可见 Rust 的**能力轮廓（Capability Profile）**呈现极端不对称：

| 维度类别 | Rust 表现 | 设计意图 |
|---------|----------|---------|
| **静态保证类** | 效应静态追踪(8)、内存安全(10)、并发安全(9) | 编译期消除一切运行时开销 |
| **抽象表达类** | 用户可定义效应(2)、效应处理器(1)、行多态(2) | 拒绝开放效应扩展，防止运行时负担 |
| **运行时机制类** | 零成本抽象(10)、运行时Continuation捕获(0) | 明确排除 continuation 捕获机制 |

---

## 五、Rust 的内存安全效应：所有权与借用

### 5.1 所有权作为内存效应管理器

Rust 语言核心贡献者 boats 明确指出：

> "Rust has an excellent system for managing effects related to mutation and memory: this is what ownership and borrowing is all about, and it beautifully guarantees soundness even in the presence of concurrent mutation."citeweb_search:1#13

所有权系统管理的是**内存效应（memory effects）**：

- **突变（mutation）**
- **别名（aliasing）**
- **生命周期（lifetime）**
- **并发访问（concurrent access）**

### 5.2 所有权系统与效应系统的本质差异

| 维度 | 代数效应系统（Koka / Eff） | Rust 所有权系统 |
|------|---------------------------|-----------------|
| **追踪目标** | 可观察计算效应（IO、状态、异常、非确定性） | 资源生命周期与别名拓扑 |
| **抽象机制** | 效应处理器（effect handlers），高阶组合 | 借用检查器（borrow checker），局部推理 |
| **可扩展性** | 用户可定义新效应 | 用户无法定义新所有权规则（仅通过 `unsafe` 绕过） |
| **组合方式** | 效应行多态（row polymorphism） | 生命周期参数化（lifetime parametrization） |
| **运行时表现** | 通常需要运行时支持（continuation 捕获/恢复） | 零成本抽象，纯编译期消除 |

### 5.3 基本所有权纪律的形式化描述

根据 RustBelt 论文（Jung et al., POPL 2018）citeweb_search:1#3：

> "The basic ownership discipline enforced by Rust's type system is a simple one: If ownership of an object (of type T) is shared between multiple aliases ('shared references' of type `&T`), then none of them can be used to directly mutate it."

此纪律消除了 use-after-free、data races、iterator invalidation 等错误类，但对依赖别名可变状态的数据结构过于严格。因此标准库广泛使用 `unsafe` 操作扩展表达能力，形成**安全边界内的模块化松弛**。

---

## 六、控制流效应的边界：Rust 的设计约束

### 6.1 三种核心控制流效应

boats 将 Rust 中的控制流效应归纳为三类citeweb_search:1#13：

1. **Fallibility（可失败性）**：代码段无法完成并求值到预期结果 → `Result<T, E>`
2. **Multiplicity（多重性）**：代码段被求值多次 → `Iterator` / 循环
3. **Asynchrony（异步性）**：代码段在无法立即进展时让出控制流 → `Future`

### 6.2 零成本抽象约束下的效应边界

Rust 对更强效应设施的排斥有**充分理由**：

> "The primary cause is Rust's commitment to 'zero-cost' abstractions, which must be highly optimizable, be local in their performance impact, and give a high degree of control to the programmer. None of the elements of stronger effect facilities in widespread use (unwinding, greenthreads, internal iteration, boxed callbacks, etc) were able to meet this constraint."citeweb_search:1#13

这意味着 Rust 的效应系统边界由**性能契约**严格划定：

- 不允许运行时 continuation 捕获（如代数效应处理器通常所需）
- 不允许隐式分配（如 green threads 或 boxed closures）
- 效应传播必须是局部可优化的（如 `?` 运算符和 `async/await` 的语法糖）

### 6.3 可挂起计算的边界选择

Abubalay 的分析揭示了 Rust 与典型代数效应语言在**计算边界**上的根本差异citeweb_search:1#9：

> "Typical languages with effects treat the whole chain of stack frames between handler and operation as a single computation to be suspended and resumed all at once... Rust instead treats individual function bodies and blocks as distinct computations to be handled individually."

这导致 Rust 的 `async` 效应：**函数体是效应边界的最小单元**，而非跨函数的调用链。`?` 运算符因此表现为一种"no-op handler"，立即重新执行效应以跨计算单元传播，而非在运行时捕获 continuation。

---

## 七、表征三：决策定理推理判定树图

![决策定理推理判定树](sandbox:///mnt/agents/output/rust_effect_theorem_tree.png)

**图3：决策定理推理判定树** — 形式化展示三个不可能性定理的判定逻辑。每个定理从前提假设出发，通过二元判定节点（菱形）推导结论。定理一判定运行时 continuation 捕获与零成本抽象的冲突；定理二判定 uncarried effects 的类型不可组合性；定理三判定空间安全与行为安全的正交性。

### 7.1 定理一：零成本抽象与通用效应处理器的不相容性

**命题**：在 Rust 的零成本抽象约束下，通用代数效应处理器（general-purpose algebraic effect handlers）不可实现。

**论证**：

1. 通用效应处理器需要**捕获并恢复 continuation**，这要求运行时保存调用栈片段（stack fragments）或堆分配闭包。
2. Rust 的零成本抽象要求：抽象不引入超出手写汇编的额外运行时开销（Sutter 的 "pay only for what you use" 原则）。
3. continuation 捕获的最低成本是**栈切换或堆分配**，这与 Rust 的局部性能控制契约冲突。
4. 因此，Rust 只能实现**静态可消除的效应**（如 `async` → 状态机 lowering，`try` → `Result` 传播），而无法实现动态 handlers。

### 7.2 定理二：Uncarried Effects 的类型系统不可组合性

**命题**：`const` 与 `unsafe` 作为 uncarried effects，无法在 Rust 类型系统中进行高阶泛化。

**论证**：

1. Carried effects（`async`, `try`）有对应的类型构造器（`Future`, `Result`），因此可通过 trait bound 抽象（`T: Future`, `T: Try`）。
2. Uncarried effects 无类型构造器，仅作为函数修饰符存在。
3. Rust 的类型系统基于参数化多态（parametric polymorphism），要求抽象变量具有**kind * 或更高 kind**。
4. 由于 `const`/`unsafe` 不对应类型，无法参数化，导致**效应泛型（effect generics）** 需引入新的类型系统层级（如 `#[maybe(async)]` 的语法实验citeweb_search:1#2）。

### 7.3 定理三：所有权纪律与效应追踪的不可通约性

**命题**：Rust 的所有权系统与标准效应系统在数学结构上不可归约（irreducible）。

**论证**：

1. 效应系统的语义通常基于**可观察性（observability）**：一个效应是计算与外部环境的交互（Plotkin & Power 的代数效应语义）。
2. Rust 的所有权纪律基于**资源拓扑（resource topology）**：关注的是内存位置的可访问性图（accessibility graph），而非计算与环境的交互。
3. 虽然数据竞争可视为一种"并发效应"，但 Rust 通过**别名限制**而非**效应追踪**消除它。
4. 因此，所有权系统是**空间安全（spatial safety）**机制，效应系统是**行为安全（behavioral safety）**机制，二者属于正交维度。

---

## 八、表征四：边界语义空间决策树图

![边界语义空间决策树](sandbox:///mnt/agents/output/rust_effect_boundary_semantic_tree.png)

**图4：边界语义空间决策树** — 从语言设计决策点出发，沿三个正交维度（效应携带性、运行时策略、安全语义）展开语义空间。每个维度分为两个互斥分支，最终收敛到 Rust 的语义空间定位：编译期消除 × 别名拓扑 × 有限 Carried 效应。底部标注 Koka/Eff、Haskell、C++ 的对比定位。

### 8.1 语义空间的三维定位

Rust 在效应语义空间中的坐标可形式化为三元组：

```
Rust ⟹ (编译期消除, 别名拓扑约束, 有限Carried效应闭包)
```

对比语言的坐标：

| 语言 | 运行时策略 | 安全语义 | 效应携带性 |
|------|-----------|---------|-----------|
| **Koka / Eff** | 运行时 continuation 捕获 | 行为安全（代数效应） | 开放用户定义效应 |
| **Haskell** | 惰性求值 + Monad 抽象 | 行为安全（IO Monad） | Monad 类型构造器 |
| **Scala 3** | 托管运行时（JVM） | 混合（能力捕获 + 效应） | 显式能力标注 |
| **Rust** | **编译期消除** | **空间安全（所有权）** | **有限内置效应** |
| **C++** | 无类型抽象 | 无静态安全保证 | 无效应系统 |

---

## 九、Keyword Generics Initiative：跨越边界的尝试

### 9.1 效应泛型的提出

Rust 语言团队通过 Keyword Generics Initiative 正式提出效应泛型（Effect Generics）方案citeweb_search:3#7，试图解决效应不匹配（effect mismatch）导致的 API 重复问题：

> "When we introduce a new keyword for something which used to be a trait, we not only gain new functionality - we also lose the ability to be generic over that keyword. This proposal seeks to change that by introducing keyword generics: the ability to be generic over specific keywords."citeweb_search:3#13

### 9.2 效应子句语法提案

社区提案尝试使用 `effect` 子句实现操作泛型citeweb_search:3#4：

```rust
fn read_to_string(path: &str) -> io::Result<String>
effect
       async, const
{
    // 根据调用上下文推断 async 或 const
    if async || !async {
        let mut file = File::open("foo.txt")?;
        file.read_to_string(&mut string)?;
    } else {
        string = include_str!(path).to_string();
    }
    Ok(string)
}
```

### 9.3 效应泛型的局限与边界

即使效应泛型实现，仍存在不可跨越的边界：

1. **`unsafe` 被排除**：Rust 核心团队明确结论 "semantically `unsafe` in Rust is not an effect"citeweb_search:3#7。`unsafe` 是元效应（meta-effect），其语义是解除保证而非追踪效应，因此 "maybe-unsafe" 在逻辑上无意义。

2. **仅覆盖内置关键字**：当前提案范围仅限于 `const` 和 `async`citeweb_search:3#13，不开放用户自定义效应。

3. **无运行时 handlers**：效应泛型不改变底层 lowering 策略，仍通过编译期状态机/Result传播实现，不涉及 continuation 捕获。

---

## 十、unsafe 边界的特殊地位：能力逃逸通道

### 10.1 unsafe 作为元效应

`unsafe` 在 Rust 中扮演独特角色：它不是追踪某种计算效应，而是**解除类型系统的保证**。这使其更接近**对象能力模型**中的特权操作：

> "Capability-safe code should additionally have no ambient authority... an object should only be able to access pre-existing capabilities if it receives them from another object."citeweb_search:1#0

`unsafe` 块可视为一种**显式能力声明**：程序员在此区域内获得了绕过借用检查器的能力，但必须自行维护不变量。

### 10.2 unsafe 的模块化封装与形式化验证

RustBelt 形式化验证了 `unsafe` 的标准库使用模式citeweb_search:1#3：

> "These libraries extend the expressive power of Rust's type system by loosening its ownership discipline on aliased mutable state in a modular, controlled fashion... Even though a shared reference of type `&T` may not be used to directly mutate the contents of the reference, it may nonetheless be used to indirectly mutate them by passing it to one of the observably 'safe' (but internally unsafe) methods."

最新研究进一步通过 SafeFFI 系统优化 unsafe 与 safe 代码边界的运行时检查citeweb_search:3#12：

> "SafeFFI achieves superior performance compared to state-of-the-art systems, reducing sanitizer checks by up to 98%, while maintaining correctness and flagging all spatial and temporal memory safety violations."

同时，Rust Foundation 的 verify-rust-std 挑战使用 Kani 等模型检查器对标准库 unsafe API 进行形式化验证citeweb_search:3#1，截至 2025 年已覆盖 18 个任务并持续增长。

---

## 十一、跨语言边界深度对比

### 11.1 效应系统的四种学术范式

| 语言/系统 | 效应模型 | 所有权/能力 | 运行时成本 | 用户可扩展性 | 与 Rust 的边界关系 |
|-----------|----------|-------------|------------|--------------|-------------------|
| **Haskell** | Monad / Monad Transformer | 无（GC 管理） | 高（ thunk 求值 + 运行时栈） | 高（自定义 Monad） | Rust 拒绝 Monad 作为默认抽象，因其非零成本 |
| **Koka / Eff** | 代数效应 + 处理器 | 无 | 中（continuation 捕获） | 极高（用户定义效应 + 处理器） | Rust 的 `async` 可视为受限代数效应，但无通用处理器 |
| **Scala 3** | Capture Checking（能力捕获） | 能力系统（capability-based） | 低（编译期擦除） | 中（通过 `using` 子句） | 与 Rust 的 Send/Sync trait bounds 概念接近，但 Scala 3 是显式能力传递 |
| **Swift** | 结构化并发 + 异步函数 | ARC（引用计数） | 低 | 低（内置效应） | 与 Rust async 最相似，但 Swift 有隐式 executor 切换 |
| **OCaml 5** | 动态代数效应 | GC | 中 | 中 | 效应不出现在类型签名，运行时可能未处理错误 |
| **Rust** | 语法糖 + 类型 lowering | 所有权 + 借用 + unsafe 边界 | 零成本 | 低（仅语言内置效应） | **本文分析对象** |

### 11.2 Koka 与 Rust 的根本分野

Koka 的设计哲学与 Rust 形成鲜明对照citeweb_search:3#14：

> "Rust spent most of its innovation tokens on ownership, Koka spends it on effects."

Koka 的代数效应允许**库代码实现 async 系统**（仅需数百行代码，无需编译器修改），而 Rust 的 `async/await` 是编译器内置语法糖。这体现了两种截然不同的工程哲学：

- **Koka**：以效应为首要抽象，牺牲部分运行时可控性换取表达能力
- **Rust**：以性能可控性为首要约束，将效应限制为编译期可消除结构

### 11.3 Haskell 效应库生态的启示

Heftia 等 Haskell 效应系统库展示了代数效应的完整能力矩阵citeweb_search:3#10：

| 特性 | Heftia | Rust 现状 |
|------|--------|----------|
| 高阶效应 | ✅ | ❌ |
| 限定 Continuation | Multi-shot | 无 |
| 静态效应系统 | ✅ | 部分（仅内置） |
| 纯 Monad 表示 | ✅ | N/A |
| 动态效应重写 | ✅ | ❌ |

Rust 在效应表达能力上与 Haskell 生态存在代际差距，但这正是 Rust **零成本承诺**的直接后果。

---

## 十二、结论：Rust 效应系统的三重边界

### 12.1 边界一：内存效应 vs. 控制流效应的分裂

Rust 的所有权系统卓越地管理**内存效应**，但控制流效应（async/try/iterators）通过独立的语法糖和类型 lowering 管理，二者无统一抽象框架。

### 12.2 边界二：Carried vs. Uncarried 的类型系统断层

`async` 和 `try` 可进入类型系统，`const`、`unsafe` 和 `generators` 不能，导致效应的**可组合性边界**泾渭分明。效应泛型（effect generics）是 Rust 语言团队正在探索的跨越此边界的方案citeweb_search:1#2，但 `unsafe` 被明确排除citeweb_search:3#7。

### 12.3 边界三：零成本抽象 vs. 通用效应表达的不相容

Rust 拒绝运行时 continuation 捕获和隐式分配，这从根本上排除了通用代数效应处理器。Rust 的效应系统因此是**静态可消除效应的闭包**，而非开放的用户可扩展框架。

### 12.4 工程哲学总结

Rust 的效应系统边界不是技术债务，而是**有意识的工程哲学选择**：

> "Rust experimented with all of these concepts at some point in its history, it wasn't out of ignorance that they were excluded."citeweb_search:1#13

Rust 在**表达能力**与**性能可控性**之间选择了后者，通过将效应限制为编译期可消除的语法结构，维持了系统编程语言的核心承诺。这一边界使 Rust 区别于 Koka、Eff、Haskell 等以效应为首要抽象的语言，也区别于 Scala 3 等尝试在托管运行时中融合能力系统的语言。

---

## 十三、参考文献索引

| 引用 | 来源 | 权威性 |
|------|------|--------|
| EPFL 博士论文 | 形式化安全语言分类框架 | S（学术机构） |
| boats 博客 | "The problem of effects in Rust" | 高（Rust 语言核心贡献者） |
| Yoshua Wuyts 博客 | "Extending Rust's Effect System" | 高（Rust 异步生态核心维护者） |
| Abubalay 博客 | "A universal lowering strategy for control effects in Rust" | 中（独立 PL 研究） |
| Jung et al., POPL 2018 | RustBelt: Securing the Foundations of the Rust Programming Language | S（顶级会议论文） |
| Plotkin & Power, 2003 | Algebraic Operations and Generic Effects | S（代数效应奠基论文） |
| Lucassen & Gifford, 1988 | Polymorphic Effect Systems | S（效应系统奠基论文） |
| Leijen, 2014 | Koka: Programming with Row Polymorphic Effect Types | S（行多态效应类型） |
| Keyword Generics Initiative | Rust 官方语言设计文档 | S（Rust 官方） |
| SafeFFI (arXiv 2025) | 优化 unsafe/safe 边界检查 | S（学术论文） |
| verify-rust-std | Rust Foundation 形式化验证项目 | S（官方基金会） |
| Heftia (GitHub) | Haskell 代数效应库对比矩阵 | A（开源项目） |
| GFX::Monk Koka 分析 | Koka 效应系统实践评估 | B（技术博客） |

---

*文档生成时间：2026-06-02*
*对齐标准：POPL / PLDI / ICFP / OOPSLA / 学术 arXiv 2025-2026 / Rust 官方 Initiative*
*论证方法：形式化定义 → 边界枚举 → 跨语言对比 → 定理论证 → 工程哲学总结*
*表征方式：思维导图 · 多维矩阵热力图 · 定理推理判定树 · 边界语义空间决策树*

## 嵌入式测验（Embedded Quiz）

### 测验 1：《Rust 效应系统（Effect System）与其语言边界的全面分析论证》是一份归档文件。归档文件在知识体系中有什么作用？（理解层）

**题目**: 《Rust 效应系统（Effect System）与其语言边界的全面分析论证》是一份归档文件。归档文件在知识体系中有什么作用？

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
