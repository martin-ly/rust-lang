# 全局概念索引（Concept Index）

> **Bloom 层级**: 应用
> **定位**：本文件是 `concept/` 知识体系的**倒排索引**，从概念名称快速定位到定义文件、交叉引用位置、Bloom 认知层级和语义链接关系。
> **方法论对齐**: Wikipedia Infobox Pattern · Semantic Link Network · Knowledge Graph Indexing

---

## 📑 目录

- [全局概念索引（Concept Index）](#全局概念索引concept-index)
  - [📑 目录](#-目录)
  - [一、索引使用说明 \[来源: 倒排索引方法论参照信息检索标准 — Manning, Raghavan \& Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论\]](#一索引使用说明-来源-倒排索引方法论参照信息检索标准--manning-raghavan--schütze-introduction-to-information-retrieval-cambridge-2008-语义链接网络参照-knowledge-graph-构建方法论)
    - [1.1 概念类型标记 \[来源: 概念分类参照语义网络理论 — Collins \& Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承\]](#11-概念类型标记-来源-概念分类参照语义网络理论--collins--quillian-1969-层次语义网络模型-概念的层级组织与属性继承)
    - [1.2 语义链接标记 \[来源: 语义链接类型参照知识图谱关系本体 — W3C RDF/OWL 标准; 实体间关系的语义标注方法论\]](#12-语义链接标记-来源-语义链接类型参照知识图谱关系本体--w3c-rdfowl-标准-实体间关系的语义标注方法论)
  - [二、核心概念索引（🔷） \[来源: 概念定义基于 Rust Reference / RFCs / 学术论文; 索引结构参照 Wikipedia Infobox Pattern 的信息浓缩设计\]](#二核心概念索引-来源-概念定义基于-rust-reference--rfcs--学术论文-索引结构参照-wikipedia-infobox-pattern-的信息浓缩设计)
    - [A \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#a-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [B \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#b-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [C \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#c-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [D \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#d-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [E \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#e-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [F \[来源: 概念定义基于 Rust Reference / TRPL / 学术论文\]](#f-来源-概念定义基于-rust-reference--trpl--学术论文)
    - [G](#g)
    - [H](#h)
    - [I](#i)
    - [K](#k)
    - [L](#l)
    - [M](#m)
    - [N](#n)
    - [O](#o)
    - [P](#p)
    - [R](#r)
    - [S](#s)
    - [T](#t)
    - [U](#u)
    - [V](#v)
    - [Z](#z)
  - [三、交叉概念一致性审计（🔶） \[来源: 交叉一致性检查方法论参照概念图 (Concept Map) 理论 — Novak \& Cañas, *The Theory Underlying Concept Maps* (2008); 知识网络的连通性验证\]](#三交叉概念一致性审计-来源-交叉一致性检查方法论参照概念图-concept-map-理论--novak--cañas-the-theory-underlying-concept-maps-2008-知识网络的连通性验证)
    - [3.1 Pin（出现在 4+ 个文件中） \[来源: 跨文件概念一致性检查参照 RFC 2349 — Pin / 2018; concept/03\_advanced/02\_async.md 等 4+ 文件中的 Pin 定义一致性验证\]](#31-pin出现在-4-个文件中-来源-跨文件概念一致性检查参照-rfc-2349--pin--2018-concept03_advanced02_asyncmd-等-4-文件中的-pin-定义一致性验证)
    - [3.2 Send / Sync（出现在 3+ 个文件中）](#32-send--sync出现在-3-个文件中)
    - [3.3 Unsafe（出现在 3+ 个文件中）](#33-unsafe出现在-3-个文件中)
    - [3.4 生命周期（出现在 4+ 个文件中）](#34-生命周期出现在-4-个文件中)
  - [四、引用概念速查（🔹） \[来源: 速查表设计参照认知心理学中的组块化 (Chunking) 原则 — Miller (1956); 信息压缩与快速检索\]](#四引用概念速查-来源-速查表设计参照认知心理学中的组块化-chunking-原则--miller-1956-信息压缩与快速检索)
  - [五、按 Bloom 层级排序 \[来源: Bloom, B.S. et al. — *Taxonomy of Educational Objectives: The Classification of Educational Goals*. Handbook I: Cognitive Domain. Longman, 1956 (revised 2001); 认知层级作为知识结构组织的主轴\]](#五按-bloom-层级排序-来源-bloom-bs-et-al--taxonomy-of-educational-objectives-the-classification-of-educational-goals-handbook-i-cognitive-domain-longman-1956-revised-2001-认知层级作为知识结构组织的主轴)
    - [记忆（Remember）→ 理解（Understand）](#记忆remember-理解understand)
    - [应用（Apply）→ 分析（Analyze）](#应用apply-分析analyze)
    - [评价（Evaluate）→ 创造（Create）](#评价evaluate-创造create)
  - [六、来源与可信度](#六来源与可信度)
  - [七、Wave 11 新增概念索引](#七wave-11-新增概念索引)
    - [7.1 Wave 11 等价表达速查](#71-wave-11-等价表达速查)
  - [八、Wave 6 新增概念索引](#八wave-6-新增概念索引)
    - [7.1 反例 → 概念 速查索引](#71-反例--概念-速查索引)
  - [九、交叉概念单一来源规范（Single Source of Truth）](#九交叉概念单一来源规范single-source-of-truth)
    - [9.1 Pin（自引用安全）](#91-pin自引用安全)
    - [9.2 Send / Sync（并发安全标记）](#92-send--sync并发安全标记)
    - [9.3 Unsafe Rust（安全边界逃逸）](#93-unsafe-rust安全边界逃逸)
    - [9.4 Lifetimes（生命周期 / 区域类型）](#94-lifetimes生命周期--区域类型)
    - [9.5 维护规范](#95-维护规范)
  - [十、语义表达力全景梳理（Phase F）](#十语义表达力全景梳理phase-f)
  - [十一、Phase 7 五维升华新增概念索引](#十一phase-7-五维升华新增概念索引)
    - [11.1 可判定性谱系（Decidability Spectrum）](#111-可判定性谱系decidability-spectrum)
    - [11.2 表达力多视角（Expressiveness Multiview）](#112-表达力多视角expressiveness-multiview)
    - [11.3 惯用法谱系（Idioms Spectrum）](#113-惯用法谱系idioms-spectrum)
    - [11.4 执行模型同构性（Execution Model Isomorphism）](#114-执行模型同构性execution-model-isomorphism)
    - [11.5 系统设计原则（System Design Principles）](#115-系统设计原则system-design-principles)
    - [11.6 四层全局关系图谱](#116-四层全局关系图谱)
  - [八、TODO](#八todo)

## 一、索引使用说明 [来源: 倒排索引方法论参照信息检索标准 — Manning, Raghavan & Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论]

### 1.1 概念类型标记 [来源: 概念分类参照语义网络理论 — Collins & Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承]

| 标记 | 含义 | 示例 |
|:---|:---|:---|
| 🔷 **核心概念** | 有独立文件深入定义的概念 | 所有权、生命周期、Trait |
| 🔶 **交叉概念** | 在多个文件中重复出现、需一致性维护的概念 | Pin、Send、unsafe |
| 🔹 **引用概念** | 在其他文件中被引用但未独立定义的概念 | RAII、Zero-cost Abstraction |

### 1.2 语义链接标记 [来源: 语义链接类型参照知识图谱关系本体 — W3C RDF/OWL 标准; 实体间关系的语义标注方法论]

| 链接类型 | 符号 | 含义 |
|:---|:---|:---|
| 前置依赖 | `←` | 理解本概念必须先掌握的概念 |
| 后置蕴含 | `→` | 掌握本概念后可学习的概念 |
| 互斥/对立 | `⊘` | 与本概念互斥或形成对照的概念 |
| 形式化对应 | `≡` | 在形式化理论中的精确对应 |
| 反例关联 | `⚡` | 本概念的典型反例或失效条件 |

---

## 二、核心概念索引（🔷） [来源: 概念定义基于 Rust Reference / RFCs / 学术论文; 索引结构参照 Wikipedia Infobox Pattern 的信息浓缩设计]

### A [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **ADT (Algebraic Data Type)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 类型论 | 理解 | ← 类型系统基础 → 模式匹配 |
| **AFIT (Async Fn In Trait)** | [L3: 异步](../03_advanced/02_async.md) | L2 Trait、L7 演进 | 分析 | ← Trait + async → RPITIT |
| **Alias-XOR-Mutation (AXM)** | [L1: 借用](../01_foundation/02_borrowing.md) | L3 并发、L4 分离逻辑 | 理解 | ← 所有权 → 并发安全 |
| **Arc** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L3 并发、L1 所有权 | 应用 | ← Rc + Send/Sync → 跨线程共享 |
| **Async/Await** | [L3: 异步](../03_advanced/02_async.md) | L2 泛型、L3 Pin、L4 形式化 | 分析 | ← Future + Pin → 运行时 |
| **Atomic Memory Ordering** | [L3: 并发](../03_advanced/01_concurrency.md) | L1 借用、L4 内存模型 | 评价 | ← Send/Sync → 无锁数据结构 |

### B [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Borrowing (&/&mut)** | [L1: 借用](../01_foundation/02_borrowing.md) | L1 所有权、L3 并发、L4 分离逻辑 | 理解 | ← 所有权 → 生命周期 ≡ 分数权限 |
| **Box** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 所有权、L4 线性逻辑 | 应用 | ← 所有权 → 智能指针 |
| **Builder Pattern** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L2 Trait、L1 类型系统 | 应用 | ← 所有权 + 方法链 → API 设计 |

### C [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Cell / RefCell** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 借用、L3 并发 | 分析 | ← 内部可变性 → 运行时借用检查 |
| **Const Generics** | [L2: 泛型](../02_intermediate/02_generics.md) | L4 类型论、L7 演进 | 分析 | ← 泛型 → 类型级编程 |
| **Copy Trait** | [L1: 所有权](../01_foundation/01_ownership.md) | L2 Trait、L4 线性逻辑 | 理解 | ⊘ Move ≡ 线性逻辑 weakening |
| **Concurrency** | [L3: 并发](../03_advanced/01_concurrency.md) | L1 借用、L2 Send/Sync、L4 CSL | 分析 | ← 借用 + Send/Sync → 异步 |
| **CSP (Communicating Sequential Processes)** | [L5: Rust vs Go](../05_comparative/02_rust_vs_go.md) | L3 并发、L5 范式矩阵 | 评价 | ⊘ 所有权并发 |

### D [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Decision Tree (定理推理)** | [L0: 方法论](../00_meta/methodology.md) | 所有文件 | — | 规范所有推理链的呈现方式 |
| **Drop Trait** | [L1: 所有权](../01_foundation/01_ownership.md) | L2 Trait、L4 线性逻辑 | 理解 | ← 所有权 → RAII ≡ 资源消耗 |
| **dyn Trait** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 类型论 | 分析 | ⊘ impl Trait → 动态分发 |

### E [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Edition Mechanism** | [L7: 语言演进](../07_future/03_evolution.md) | 所有层 | 评价 | ← RFC 流程 → 向后兼容演进 |
| **Elision Rules** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L2 泛型、L4 区域类型 | 应用 | ← 生命周期标注 → 简化书写 |
| **enum (Sum Type)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 错误处理、L4 代数类型 | 理解 | ≡ 和类型 / 余积 (A + B) |
| **Error Handling (Result/Option)** | [L2: 错误处理](../02_intermediate/04_error_handling.md) | L1 类型系统、L3 异步 | 应用 | ← Option/Result → ? 运算符 |

### F [来源: 概念定义基于 Rust Reference / TRPL / 学术论文]

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **FFI (Foreign Function Interface)** | [L3: Unsafe](../03_advanced/03_unsafe.md) | L1 所有权、L5 Rust vs C++ | 评价 | ← unsafe → 外部代码互操作 |
| **Formal Methods (形式化方法)** | [L7: 形式化方法](../07_future/02_formal_methods.md) | L4 RustBelt、L6 工具链 | 创造 | ← RustBelt → 工业验证 |
| **Fractional Permissions** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L1 借用、L3 并发 | 评价 | ≡ 借用规则的形式化根基 |
| **Future** | [L3: 异步](../03_advanced/02_async.md) | L2 Trait、L3 Pin | 分析 | ← Trait + 状态机 → async/await |

### G

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **GATs (Generic Associated Types)** | [L2: 泛型](../02_intermediate/02_generics.md) | L2 Trait、L4 类型论 | 评价 | ← 关联类型 + 泛型 → HKT |
| **Generics** | [L2: 泛型](../02_intermediate/02_generics.md) | L1 类型系统、L4 类型论 | 应用 | ← 类型系统 → 单态化 |

### H

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **HRTB (Higher-Ranked Trait Bounds)** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L2 Trait、L4 类型论 | 评价 | ← 生命周期 + 泛型 ≡ ∀<'a> |
| **HM Type Inference** | [L4: 类型论](../04_formal/02_type_theory.md) | L1 类型系统、L2 泛型 | 分析 | → 类型自动推导 |

### I

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Impl Trait** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 类型论 | 分析 | ← Trait → 抽象返回类型 |
| **Interior Mutability** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 借用、L4 分离逻辑 | 分析 | ← Cell/RefCell → 运行时检查 |
| **Iris (Logic)** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L3 并发、L4 分离逻辑 | 评价 | → RustBelt 验证框架 |

### K

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Kani (Verifier)** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L7 形式化方法 | 应用 | ← 模型检测 → unsafe 验证 |

### L

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Lifetimes ('a)** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L2 泛型、L3 异步、L4 区域类型 | 理解 | ← 借用 → Send/Sync ≡ 区域约束 |
| **Linear Logic** | [L4: 线性逻辑](../04_formal/01_linear_logic.md) | L1 所有权、L5 Rust vs C++ | 评价 | ≡ 所有权的形式化根基 |
| **Liskov Substitution** | [L2: Trait](../02_intermediate/01_traits.md) | L4 子类型 | 理解 | → Trait 对象安全 |

### M

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Macros** | [L3: 宏](../03_advanced/04_macros.md) | L1 类型系统、L4 元编程 | 分析 | ← 语法扩展 → DSL |
| **MaybeUninit** | [L3: Unsafe](../03_advanced/03_unsafe.md) | L1 所有权、L4 内存模型 | 评价 | ← unsafe → 延迟初始化 |
| **Memory Model** | [L3: Unsafe](../03_advanced/03_unsafe.md) | L4 RustBelt、L5 对比 | 分析 | → Stacked/Tree Borrows |
| **Memory Safety** | [L1: 所有权](../01_foundation/01_ownership.md) | 所有层 | 理解 | ← 所有权 + 借用 + 生命周期 |
| **Monomorphization** | [L2: 泛型](../02_intermediate/02_generics.md) | L4 类型论 | 应用 | ← 泛型 → 零成本抽象 |
| **Move Semantics** | [L1: 所有权](../01_foundation/01_ownership.md) | L4 线性逻辑 | 理解 | ← 所有权 → 借用 ≡ 资源消耗 |
| **Mutex / RwLock** | [L3: 并发](../03_advanced/01_concurrency.md) | L2 Send/Sync、L4 分离逻辑 | 应用 | ← Send/Sync → 互斥访问 |

### N

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Newtype Pattern** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L1 类型系统、L2 Trait | 应用 | ← 零大小类型 → 类型安全 |
| **NLL (Non-Lexical Lifetimes)** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L4 区域类型 | 分析 | ← 词法作用域 → 控制流敏感 |

### O

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Option / Result** | [L2: 错误处理](../02_intermediate/04_error_handling.md) | L1 类型系统、L3 异步 | 应用 | ≡ Maybe Monad → ? 运算符 |
| **Orphan Rule** | [L2: Trait](../02_intermediate/01_traits.md) | L4 类型论 | 分析 | ← Trait 一致性 → 封装 |
| **Ownership** | [L1: 所有权](../01_foundation/01_ownership.md) | 所有层 | 理解 | ≡ 线性资源 ⊗ → 借用 |

### P

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Paradigm Matrix** | [L5: 范式矩阵](../05_comparative/03_paradigm_matrix.md) | L1-L4 | 评价 | ← 所有基础概念 → 语言选型 |
| **Pattern Matching** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 错误处理 | 应用 | ← enum → 穷尽性检查 |
| **Pin** | [L3: 异步](../03_advanced/02_async.md) | L1 借用、L2 内存管理、L4 形式化 | 分析 | ← 自引用 → Future 安全 |
| **Proc Macros** | [L3: 宏](../03_advanced/04_macros.md) | L1 类型系统 | 分析 | ← 编译器插件 → 派生宏 |

### R

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **RAII** | [L1: 所有权](../01_foundation/01_ownership.md) | L2 内存管理、L6 设计模式 | 理解 | ← Drop → 资源自动管理 |
| **Rc / RefCell** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 借用、L4 内存安全 | 分析 | ← 内部可变性 → 循环引用 |
| **Region Types** | [L4: 所有权形式化](../04_formal/03_ownership_formal.md) | L1 生命周期 | 评价 | ≡ 生命周期 |
| **repr** | [L3: Unsafe](../03_advanced/03_unsafe.md) | L5 Rust vs C++ | 应用 | ← FFI → 内存布局控制 |
| **Representational Space (表征空间)** | [L0: 语义空间](semantic_space.md) | 所有层 | 评价 | ← 所有概念 → 能/不能表达边界 |
| **RPITIT (Return Position Impl Trait In Trait)** | [L3: 异步](../03_advanced/02_async.md) | L2 Trait、L7 演进 | 评价 | ← AFIT → 关联返回类型 |
| **RustBelt** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L3 Unsafe、L7 形式化方法 | 评价 | ← Iris → Rust 安全验证 |

### S

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Send / Sync** | [L3: 并发](../03_advanced/01_concurrency.md) | L1 所有权、L2 Trait、L4 CSL | 分析 | ← 所有权 + 借用 → 并发安全 |
| **Separation Logic** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L1 借用、L3 并发 | 评价 | ≡ 借用规则 + 并发安全 |
| **Specialization** | [L2: Trait](../02_intermediate/01_traits.md) | L4 类型论、L7 演进 | 评价 | ← 泛型 → 特化实现 |
| **Stacked Borrows / Tree Borrows** | [L4: RustBelt](../04_formal/04_rustbelt.md) | L3 Unsafe、L4 形式化 | 评价 | → Unsafe 代码别名规则 |
| **struct (Product Type)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L4 代数类型 | 理解 | ≡ 积类型 / 记录 (A × B) |
| **Subtyping / Variance** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L4 类型论 | 分析 | ← 生命周期 → 类型安全 |
| **Supertrait** | [L2: Trait](../02_intermediate/01_traits.md) | L4 子类型 | 理解 | ← Trait 继承 → 组合约束 |

### T

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Trait** | [L2: Trait](../02_intermediate/01_traits.md) | L1 类型系统、L3 并发、L4 类型论 | 应用 | ← 类型系统 → 泛型约束 |
| **Trait Bounds** | [L2: Trait](../02_intermediate/01_traits.md) | L2 泛型、L4 约束求解 | 应用 | ← Trait + 泛型 → where 子句 |
| **Trait Objects (dyn)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 存在类型 | 分析 | ⊘ 泛型 → 动态分发 |
| **Typestate Pattern** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L1 所有权、L2 泛型 | 分析 | ← 所有权 → 编译期状态机 |
| **Core Crates** | [L6: 核心库谱系](../06_ecosystem/03_core_crates.md) | L1-L5 全部 | 应用 | ← 概念 → 工程选型 |
| **serde** | [L6: 核心库谱系](../06_ecosystem/03_core_crates.md) | L2 Trait、L1 类型系统 | 应用 | ← derive → 序列化 |
| **tokio** | [L6: 核心库谱系](../06_ecosystem/03_core_crates.md) | L3 async、L1 Send/Sync | 应用 | ← 运行时 → 异步生态 |
| **axum** | [L6: 核心库谱系](../06_ecosystem/03_core_crates.md) | L2 Trait、L3 async | 应用 | ← Handler → Web 后端 |
| **clap** | [L6: 核心库谱系](../06_ecosystem/03_core_crates.md) | L2 Trait、L1 类型系统 | 应用 | ← Parser → CLI |
| **Application Domains** | [L6: 应用主题](../06_ecosystem/04_application_domains.md) | L1-L5、L6 Crates | 评价 | ← 概念+crate → 工程落地 |
| **Web Backend** | [L6: 应用主题](../06_ecosystem/04_application_domains.md) | L3 async、L2 Trait | 应用 | ← axum+tokio → 微服务 |
| **Embedded Rust** | [L6: 应用主题](../06_ecosystem/04_application_domains.md) | L3 unsafe、L1 no_std | 应用 | ← embassy → 裸机 |
| **Blockchain** | [L6: 应用主题](../06_ecosystem/04_application_domains.md) | L1 类型安全、L3 unsafe | 应用 | ← solana → 智能合约 |
| **Game Engine** | [L6: 应用主题](../06_ecosystem/04_application_domains.md) | L3 unsafe、L2 泛型 | 应用 | ← bevy → ECS |
| **Type System** | [L1: 类型系统](../01_foundation/04_type_system.md) | 所有层 | 理解 | → 所有类型相关概念 |

### U

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Unsafe Rust** | [L3: Unsafe](../03_advanced/03_unsafe.md) | L1 所有权、L4 RustBelt、L5 对比 | 评价 | ⚡ 所有 safe 定理的边界 |
| **Unsafe Escape Hatch** | [L0: 语义空间](semantic_space.md) | L3 Unsafe、L5 对比 | 分析 | ⊘ safe 封闭性 → 局部逃逸 |
| **Unpin** | [L3: 异步](../03_advanced/02_async.md) | L3 Pin | 分析 | ⊘ Pin → 默认可移动 |

### V

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Variance** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L4 类型论 | 分析 | ← 子类型 → 生命周期安全 |

### Z

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Zero-cost Abstraction** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L2 泛型、L5 对比 | 评价 | ← 单态化 → 运行时零开销 |
| **Zero-cost Safety** | [L0: 语义空间](semantic_space.md) | L1-L4 | 评价 | ← 编译期检查 → 运行时零开销安全 |

---

## 三、交叉概念一致性审计（🔶） [来源: 交叉一致性检查方法论参照概念图 (Concept Map) 理论 — Novak & Cañas, *The Theory Underlying Concept Maps* (2008); 知识网络的连通性验证]

以下概念在**多个文件中重复出现**，需要确保定义一致：

### 3.1 Pin（出现在 4+ 个文件中） [来源: 跨文件概念一致性检查参照 RFC 2349 — Pin / 2018; concept/03_advanced/02_async.md 等 4+ 文件中的 Pin 定义一致性验证]

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: 异步](../03_advanced/02_async.md) | Pin 的核心定义：自引用安全 | ✅ 主定义 |
| [L1: 借用](../01_foundation/02_borrowing.md) | Pin 与借用规则的交互 | ⚠️ 需链接到主定义 |
| [L2: 内存管理](../02_intermediate/03_memory_management.md) | Pin 在堆内存中的使用 | ⚠️ 需链接到主定义 |
| [L4: 形式化](../04_formal/03_ownership_formal.md) | Pin 的形式化语义 | ✅ 已添加 🔍 待补充标记，链接到 L3 §8 |

**一致性要求**: 所有文件中对 Pin 的定义必须以 L3 为准，差异处需显式标注。

### 3.2 Send / Sync（出现在 3+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: 并发](../03_advanced/01_concurrency.md) | Send/Sync 的完整定义与规则 | ✅ 主定义 |
| [L2: Trait](../02_intermediate/01_traits.md) | Send/Sync 作为 Auto Trait 的特性 | ✅ 已链接 |
| [L4: RustBelt](../04_formal/04_rustbelt.md) | Send/Sync 的并发分离逻辑语义 | ✅ 已显式映射 |

### 3.3 Unsafe（出现在 3+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: Unsafe](../03_advanced/03_unsafe.md) | Unsafe 的完整定义与安全契约 | ✅ 主定义 |
| [L1: 所有权](../01_foundation/01_ownership.md) | Unsafe 突破所有权 | ✅ 已标注边界条件 |
| [L5: Rust vs C++](../05_comparative/01_rust_vs_cpp.md) | Unsafe 在对比语境中的意义 | ✅ 已对齐 |
| [L4: RustBelt](../04_formal/04_rustbelt.md) | Unsafe 在形式化中的范围 | ✅ 一致: unsafe 在证明范围外 |

### 3.4 生命周期（出现在 4+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L1: 生命周期](../01_foundation/03_lifetimes.md) | 核心定义、标注、Elision | ✅ 主定义 |
| [L2: 泛型](../02_intermediate/02_generics.md) | 生命周期作为泛型参数 | ⚠️ 需链接 |
| [L3: 异步](../03_advanced/02_async.md) | 生命周期在 Future 中的传播 | ⚠️ 需链接 |
| [L4: 形式化](../04_formal/03_ownership_formal.md) | 区域类型的形式化对应 | ✅ 已显式映射 |

---

## 四、引用概念速查（🔹） [来源: 速查表设计参照认知心理学中的组块化 (Chunking) 原则 — Miller (1956); 信息压缩与快速检索]

| 概念 | 首次出现文件 | 相关核心概念 | 简要说明 |
|:---|:---|:---|:---|
| **RAII** | L1 所有权 | Drop、所有权 | 资源获取即初始化 |
| **Zero-cost Abstraction** | L6 设计模式 | 单态化、泛型 | 抽象无运行时开销 |
| **Fearless Concurrency** | L3 并发 | Send/Sync、所有权 | 编译期保证并发安全 |
| **Typestate** | L6 设计模式 | 所有权、泛型 | 编译期状态机验证 |
| **Vtable** | L1 类型系统 | dyn Trait、动态分发 | 虚表实现多态 |
| **Hygienic Macros** | L3 宏 | 作用域、命名空间 | 宏变量不污染外部 |
| **Soundness** | L4 RustBelt | 类型安全、形式化 | 类型系统无 false negative |
| **Completeness** | L4 类型论 | HM 推断、停机问题 | 类型系统对正确程序可推导 |
| **Coherence** | L2 Trait | Orphan Rule | 类型系统无矛盾实现 |

---

## 五、按 Bloom 层级排序 [来源: Bloom, B.S. et al. — *Taxonomy of Educational Objectives: The Classification of Educational Goals*. Handbook I: Cognitive Domain. Longman, 1956 (revised 2001); 认知层级作为知识结构组织的主轴]

### 记忆（Remember）→ 理解（Understand）

| 概念 | 文件 | 层级 |
|:---|:---|:---|
| 所有权、Move/Copy/Drop | L1 | 记忆 → 理解 |
| 借用 &/&mut | L1 | 记忆 → 理解 |
| 生命周期标注 | L1 | 记忆 → 理解 |
| ADT (enum/struct) | L1 | 记忆 → 理解 |
| Option/Result | L2 | 理解 |
| RAII | L1/L6 | 理解 |

### 应用（Apply）→ 分析（Analyze）

| 概念 | 文件 | 层级 |
|:---|:---|:---|
| Trait / Trait Bounds | L2 | 应用 |
| 泛型 / 单态化 | L2 | 应用 |
| 错误处理 (? 运算符) | L2 | 应用 |
| Send/Sync | L3 | 分析 |
| Pin / async | L3 | 分析 |
| NLL / Elision | L1 | 分析 |
| 内部可变性 | L2 | 分析 |
| 内存模型 / unsafe | L3 | 分析 |

### 评价（Evaluate）→ 创造（Create）

| 概念 | 文件 | 层级 |
|:---|:---|:---|
| 线性逻辑 / 类型论 | L4 | 评价 |
| RustBelt / 分离逻辑 | L4 | 评价 |
| 并发安全定理 | L3/L4 | 评价 |
| Rust vs C++/Go | L5 | 评价 → 创造 |
| 范式矩阵 | L5 | 评价 |
| 形式化方法工业化 | L7 | 创造 |
| AI × Rust | L7 | 创造 |
| 语言演进设计 | L7 | 创造 |

---

## 六、来源与可信度

| 索引设计决策 | 来源 | 可信度 |
|:---|:---|:---|
| Bloom 层级映射 | Anderson & Krathwohl 2001 | ✅ |
| 语义链接类型设计 | Zhuge 2010 · Semantic Link Network | ✅ |
| 交叉概念审计方法 | Torchiano et al. 2018 · KB Consistency | ✅ |
| 概念分类（核心/交叉/引用） | — | 💡 原创 |

---

## 七、Wave 11 新增概念索引

以下概念为 Wave 11（表征空间元分析）中**新增或强化**的元概念：

| 新增概念 | 出现文件 | 说明 | 类型 |
|:---|:---|:---|:---|
| **表征空间 (Representational Space)** | L0 元层 | 从能表达/不能表达/等价表达视角的 Rust 元分析 | 🔷 元结构 |
| **语义封闭性 (Semantic Closure)** | L0 元层 | Safe Rust 作为封闭形式系统的公理与定理 | 🔷 元结构 |
| **表达力三维分类** | L0 元层 | 能且高效 / 能但痛苦 / 不能排除 | 🔷 元结构 |
| **等价表达谱系** | L0 元层 | 继承→Trait、异常→Result、虚函数→enum/dyn 等 | 🔶 交叉 |
| **机制组合代数** | L0 元层 | Own/Borrow/Lifetime/Trait/Generic 的合法/非法组合 | 🔷 元结构 |
| **跨语言表征空间对比** | L0 元层 | Rust vs C++/Haskell/Go/Java 五维矩阵 | 🔶 交叉 |
| **未来特性对表征空间的扩展** | L0 元层 | const trait、effects、specialization 等 | 🔶 交叉 |

### 7.1 Wave 11 等价表达速查

| 原概念 | Rust 等价表达 | 语义等价性 | 性能等价性 | 扩展性等价性 |
|:---|:---|:---|:---|:---|
| 继承 | Trait + 组合 | ✅ 观察等价 | ✅ 更优（静态分发）| ⚠️ 不等价（Orphan Rule）|
| 异常 | Result<T, E> | ✅ 观察等价 | ⚠️ 不等价（返回值 vs 异常表）| ✅ 更清晰 |
| 虚函数 | enum + match / dyn Trait | ✅ 观察等价 | ✅ 可控（静态/动态）| ⚠️ enum 封闭 / dyn 开放 |
| GC | 所有权 + Rc/Arc/Weak | ⚠️ 回收时机不等价 | ⚠️ 成本不等价 | ⚠️ 循环引用需手动处理 |
| 模板元编程 | const generics + 宏 | ⚠️ 能力不等价 | ✅ 等价（编译期）| ⚠️ 宏无类型信息 |
| 绿色线程 | async/await + OS 线程 | ⚠️ 调度不等价 | ✅ 相近 | ⚠️ 阻塞语义不同 |

---

## 八、Wave 6 新增概念索引

以下概念为 Wave 6 全量深度重构中**新增或强化**的元概念与结构化元素：

| 新增概念 | 出现文件数 | 说明 | 类型 |
|:---|:---|:---|:---|
| **定理一致性矩阵** | 27 | 每文件的 ⟹ 推理链表格 | 🔷 元结构 |
| **反命题决策树** | 27 | Mermaid 图：命题→反例→修正 | 🔷 元结构 |
| **认知路径 (6步递进)** | 27 | 从直觉到形式化的学习阶梯 | 🔷 元结构 |
| **边界极限测试** | 16 | 编译验证/反例代码块 | 🔶 交叉 |
| **章节过渡段落** | 27 | 章间逻辑衔接 | 🔹 引用 |
| **层次一致性标注** | 20+ | "此处为 X 文件 §Y 的精确对应" | 🔶 交叉 |

### 7.1 反例 → 概念 速查索引

| 反例/边界条件 | 目标概念 | 出现文件 |
|:---|:---|:---|
| `mem::forget` 跳过析构 | RAII / 所有权 | L1 所有权, L5 Rust vs C++ |
| `Rc<RefCell<T>>` 循环引用 | 所有权唯一性 | L1 所有权, L2 内存管理, L4 形式化 |
| `unsafe impl Send/Sync` | Send/Sync 安全契约 | L3 并发, L4 RustBelt |
| `Pin` + 自引用 | 生命周期 / 借用 | L3 异步, L1 借用 |
| `dyn Trait` 胖指针 | 零成本抽象 | L2 泛型, L1 类型系统 |
| 编译期栈深度溢出 | 宏展开限制 | L3 宏 |
| FFI ABI 不匹配 | Unsafe 边界 | L3 Unsafe, L5 对比 |

---

## 九、交叉概念单一来源规范（Single Source of Truth）

以下概念在多个文件中重复出现，本索引正式声明其**主定义文件**和**一致性规范**，确保全知识体系定义无冲突。

### 9.1 Pin（自引用安全）

| 项目 | 规范 |
|:---|:---|
| **主定义文件** | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) §5–§8 |
| **核心语义** | `Pin<P<T>>` 保证 `T` 的内存地址不变（location stability），当 `T: !Unpin` 时禁止安全移动 |
| **允许的差异** | 其他文件可引用主定义，但不得引入与主定义冲突的语义；可补充特定语境下的用法示例（如 L2 内存管理的堆 Pin、L1 借用的自引用） |
| **一致性检查** | 所有文件对 `Pin` 的描述必须以 "地址不变性" 为核心，不得以 "引用计数" 或 "线程安全" 作为首要定义 |

### 9.2 Send / Sync（并发安全标记）

| 项目 | 规范 |
|:---|:---|
| **主定义文件** | [`../03_advanced/01_concurrency.md`](../03_advanced/01_concurrency.md) §3–§4 |
| **核心语义** | `Send`: 类型可安全转移所有权到另一线程；`Sync`: 类型可安全被多线程共享引用（`&T`） |
| **允许的差异** | 其他文件可从形式化角度补充（如 L4 RustBelt 的 CSL 语义），但不得与 "转移/共享" 核心定义冲突 |
| **一致性检查** | 禁止将 `Send` 描述为 "线程安全" 的笼统概念；必须区分 `Send`（转移）与 `Sync`（共享） |

### 9.3 Unsafe Rust（安全边界逃逸）

| 项目 | 规范 |
|:---|:---|
| **主定义文件** | [`../03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) §1–§3 |
| **核心语义** | `unsafe` 是程序员向编译器承诺"我已手动验证以下 5 种超能力的安全性"：解引用裸指针、调用 unsafe 函数、访问 union 字段、实现 unsafe trait、访问 `static mut` |
| **允许的差异** | L1/L5 文件可从对比角度描述 unsafe（如 "unsafe 突破所有权"），但必须明确标注这是"简化表述"，完整定义见 L3 |
| **一致性检查** | 所有文件必须明确：`unsafe` 块不改变 borrow checker 规则，只是额外解锁 5 种操作；类型检查、生命周期检查在 unsafe 内仍然有效 |

### 9.4 Lifetimes（生命周期 / 区域类型）

| 项目 | 规范 |
|:---|:---|
| **主定义文件** | [`../01_foundation/03_lifetimes.md`](../01_foundation/03_lifetimes.md) §1–§4 |
| **核心语义** | 生命周期是引用的**有效范围标注**，编译器通过区域约束求解验证 "引用不悬垂"；`'static` 是最大（最长久）生命周期 |
| **允许的差异** | L2/L3/L4 文件可从泛型参数（L2）、async 捕获（L3）、区域类型形式化（L4）角度扩展，但不得与 "有效范围" 核心定义冲突 |
| **一致性检查** | 禁止将生命周期描述为 "运行时存在的东西" 或 "引用计数"；必须强调生命周期是**编译期静态分析**的抽象 |

### 9.5 维护规范

1. **新增交叉概念**: 若某概念在 ≥3 个文件中出现且定义存在差异风险，应纳入本 SSO 列表
2. **修订流程**: 修改主定义文件中的交叉概念定义时，必须同时检查所有引用该概念的文件，更新一致性标注
3. **自动化检查**: 未来通过机器可解析格式（JSON/YAML）自动检测术语定义冲突

---

---

## 十、语义表达力全景梳理（Phase F）

> **[`semantic_expressiveness.md`](./semantic_expressiveness.md)** —— 2026-05-13 新建

横向七维表达力光谱，正交于 L0-L7 纵向层级：

| 维度 | 核心问题 | 形式化对应 | Bloom |
|:---|:---|:---|:---:|
| D1 计算 | 编译期 vs 运行时计算边界 | 常量求值可判定性 | 分析 |
| D2 类型 | System Fω 子集 + 依赖类型子集 | 类型论 / 参数性 | 分析→评价 |
| D3 控制流 | 结构化 / Result / async / gen | 状态机 / Continuation | 分析 |
| D4 内存 | 所有权 + 借用 + 内部可变性 | 线性逻辑 / 分离逻辑 | 分析→评价 |
| D5 并发 | Send/Sync + 数据并行 + 异步 | 并发分离逻辑 (CSL) | 分析→评价 |
| D6 抽象 | Trait + 泛型 + 宏 + FFI | 参数性 / 卫生宏 | 评价 |
| D7 安全 | safe / unsafe / UB / 形式化验证 | RustBelt / Miri / Kani | 评价→创造 |

对比语言：Rust · C++ · Go · Haskell。每维度末尾附 L0-L7 双向映射表（66 个跨文件链接）。

---

## 十一、Phase 7 五维升华新增概念索引

> Phase 7 于 2026-05-21 完成，新增 9 个文件，覆盖「可判定性—表达力—惯用法—执行模型—系统设计」五维主线 + 四层全局关系图谱。

### 11.1 可判定性谱系（Decidability Spectrum）

| 概念 | 文件 | Bloom | 核心判定问题 | 可判定性 |
|:---|:---|:---:|:---|:---:|
| 编译期可判定性谱系 | `00_meta/decidability_spectrum.md` | 分析→评价 | 全链路判定边界 | — |
| L0 词法/语法判定 | 同上 | 分析 | Token→AST | ✅ |
| L1 名称解析判定 | 同上 | 分析 | Path 唯一解析 | ✅ |
| L2 类型推断判定 | 同上 | 分析 | 局部 HM 子集 | ✅ |
| L2 Trait 求解判定 | 同上 | 分析 | 受限可满足性 | ⚠️ |
| L3 借用检查判定 | 同上 | 分析 | NLL/Polonius | ✅ |
| L4 CTFE 有界判定 | 同上 | 评价 | 步数/栈深上限 | ⚠️ |
| L5 死锁不可判定 | 同上 | 评价 | Rice 定理 | ❌ |

### 11.2 表达力多视角（Expressiveness Multiview）

| 概念 | 文件 | Bloom | 理论视角 | 形式化对应 |
|:---|:---|:---:|:---|:---|
| Curry-Howard 对应 | `00_meta/expressiveness_multiview.md` | 分析→评价 | 类型语义 | 直觉主义逻辑 |
| CPS/async 等价性 | 同上 | 评价 | 控制语义 | λ 演算 + 续体 |
| π 演算 channel 移动 | 同上 | 分析 | 并发语义 | 线性 π 演算 |
| 参数性 Theorems for Free | 同上 | 评价 | 抽象语义 | Reynolds 1983 |
| 信息流控制 IFC | 同上 | 评价 | 安全语义 | Denning 1976 |

### 11.3 惯用法谱系（Idioms Spectrum）

| 概念 | 文件 | Bloom | 层级 | 效率 |
|:---|:---|:---:|:---|:---:|
| 七层惯用法谱系 | `06_ecosystem/03_idioms_spectrum.md` | 应用→分析 | L0-L6 | 零成本 |
| Typestate 模式 | 同上 | 应用 | L1 类型级 | 零成本 |
| Tower Service 组合 | 同上 | 分析 | L6 架构级 | 低开销 |
| ECS Archetype | 同上 | 分析 | L6 架构级 | 零成本 |
| 反惯用法判定树 | 同上 | 评价 | — | — |

### 11.4 执行模型同构性（Execution Model Isomorphism）

| 概念 | 文件 | Bloom | 执行模型 | 与 Go 同构度 |
|:---|:---|:---:|:---|:---:|
| 七类执行模型矩阵 | `05_comparative/05_execution_model_isomorphism.md` | 分析→评价 | 同步/异步/并行/CSP/Actor/内存/事件 | — |
| async 与 goroutine 不同构 | 同上 | 评价 | 异步 vs 有栈协程 | 不同构 |
| Rust-C++ 内存模型同构 | 同上 | 分析 | 原子序 Ordering | 同构 |
| 三重等价性 | 同上 | 评价 | async/CPS/状态机 | 等价 |

### 11.5 系统设计原则（System Design Principles）

| 概念 | 文件 | Bloom | 国际权威对应 | 设计维度 |
|:---|:---|:---:|:---|:---|
| Capability-Based Security | `06_ecosystem/05_system_design_principles.md` | 评价→创造 | Dennis & Van Horn 1966 | 内存安全 |
| Session Types 编码 | 同上 | 评价 | Honda 1993, Wadler 2012 | 并发安全 |
| 零成本抽象 Stroustrup | 同上 | 评价 | Stroustrup 1994 | 性能 |
| Error Kernel 模式 | 同上 | 创造 | Armstrong 2003 | 容错 |
| 帕累托前沿决策 | 同上 | 创造 | — | 权衡 |

### 11.6 四层全局关系图谱

| 图谱 | 文件 | Bloom | 关系粒度 | 思维表征 |
|:---|:---|:---:|:---|:---|
| 跨层依赖拓扑 | `00_meta/inter_layer_topology.md` | 元 | 层间 ⟹/←/≡/⊘ | Mermaid + 矩阵 |
| 层内模型映射 | `00_meta/intra_layer_model_map.md` | 元 | 模型间 ≡/⟹ | Mermaid + 矩阵 |
| 定理推理森林 | `00_meta/theorem_inference_forest.md` | 元 | 公理→定理→推论 | 层级树 + Mermaid |
| 边界扩展树 | `00_meta/boundary_extension_tree.md` | 元 | 安全边界扩展 | Mermaid + 风险矩阵 |

---

## 八、TODO

- [x] **高**: Wave 6 全量深度重构（27/27 文件）
- [x] **高**: 为所有文件添加定理一致性矩阵 + 反命题决策树 + 认知路径
- [x] **高**: 为所有 🔶 交叉概念建立"单一来源规范"（Single Source of Truth）声明 —— 已完成 §九
- [x] **高**: 在每个主定义文件中添加"其他文件中出现的链接" —— 已融入 SSO 声明与相关概念链接
- [x] **中**: 为每个概念补充"常见编译错误代码 → 概念"映射（如 E0382 → Move）
- [x] **中**: 建立"反例 → 概念"索引（如 Rc 循环引用 → 所有权边界）
- [x] **中**: 边界极限测试代码的 `cargo check` 编译验证 —— ✅ 232/232 通过 100%（`scripts/code_block_compiler.py`）
- [x] **低**: 导出为机器可解析格式（JSON/YAML）供自动一致性检查 —— 已完成 `concept_index.json`
- [x] **高**: Wave 11 表征空间元分析（semantic_space.md）
- [x] **低**: 与 `inter_layer_map.md` 的层间映射同步更新 —— ✅ 已完成
- [x] **高**: Phase 7 五维主线升华（9 个新文件 + 四层全局关系图谱）— ✅ 2026-05-21 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.2
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-21
**状态**: ✅ Phase 7 五维升华完成
