# 全局概念索引（Concept Index）

> **定位**：本文件是 `concept/` 知识体系的**倒排索引**，从概念名称快速定位到定义文件、交叉引用位置、Bloom 认知层级和语义链接关系。
> **方法论对齐**: Wikipedia Infobox Pattern · Semantic Link Network · Knowledge Graph Indexing

---

## 一、索引使用说明

### 1.1 概念类型标记

| 标记 | 含义 | 示例 |
|:---|:---|:---|
| 🔷 **核心概念** | 有独立文件深入定义的概念 | 所有权、生命周期、Trait |
| 🔶 **交叉概念** | 在多个文件中重复出现、需一致性维护的概念 | Pin、Send、unsafe |
| 🔹 **引用概念** | 在其他文件中被引用但未独立定义的概念 | RAII、Zero-cost Abstraction |

### 1.2 语义链接标记

| 链接类型 | 符号 | 含义 |
|:---|:---|:---|
| 前置依赖 | `←` | 理解本概念必须先掌握的概念 |
| 后置蕴含 | `→` | 掌握本概念后可学习的概念 |
| 互斥/对立 | `⊘` | 与本概念互斥或形成对照的概念 |
| 形式化对应 | `≡` | 在形式化理论中的精确对应 |
| 反例关联 | `⚡` | 本概念的典型反例或失效条件 |

---

## 二、核心概念索引（🔷）

### A

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **ADT (Algebraic Data Type)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 类型论 | 理解 | ← 类型系统基础 → 模式匹配 |
| **AFIT (Async Fn In Trait)** | [L3: 异步](../03_advanced/02_async.md) | L2 Trait、L7 演进 | 分析 | ← Trait + async → RPITIT |
| **Alias-XOR-Mutation (AXM)** | [L1: 借用](../01_foundation/02_borrowing.md) | L3 并发、L4 分离逻辑 | 理解 | ← 所有权 → 并发安全 |
| **Arc** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L3 并发、L1 所有权 | 应用 | ← Rc + Send/Sync → 跨线程共享 |
| **Async/Await** | [L3: 异步](../03_advanced/02_async.md) | L2 泛型、L3 Pin、L4 形式化 | 分析 | ← Future + Pin → 运行时 |
| **Atomic Memory Ordering** | [L3: 并发](../03_advanced/01_concurrency.md) | L1 借用、L4 内存模型 | 评价 | ← Send/Sync → 无锁数据结构 |

### B

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Borrowing (&/&mut)** | [L1: 借用](../01_foundation/02_borrowing.md) | L1 所有权、L3 并发、L4 分离逻辑 | 理解 | ← 所有权 → 生命周期 ≡ 分数权限 |
| **Box** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 所有权、L4 线性逻辑 | 应用 | ← 所有权 → 智能指针 |
| **Builder Pattern** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L2 Trait、L1 类型系统 | 应用 | ← 所有权 + 方法链 → API 设计 |

### C

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Cell / RefCell** | [L2: 内存管理](../02_intermediate/03_memory_management.md) | L1 借用、L3 并发 | 分析 | ← 内部可变性 → 运行时借用检查 |
| **Const Generics** | [L2: 泛型](../02_intermediate/02_generics.md) | L4 类型论、L7 演进 | 分析 | ← 泛型 → 类型级编程 |
| **Copy Trait** | [L1: 所有权](../01_foundation/01_ownership.md) | L2 Trait、L4 线性逻辑 | 理解 | ⊘ Move ≡ 线性逻辑 weakening |
| **Concurrency** | [L3: 并发](../03_advanced/01_concurrency.md) | L1 借用、L2 Send/Sync、L4 CSL | 分析 | ← 借用 + Send/Sync → 异步 |
| **CSP (Communicating Sequential Processes)** | [L5: Rust vs Go](../05_comparative/02_rust_vs_go.md) | L3 并发、L5 范式矩阵 | 评价 | ⊘ 所有权并发 |

### D

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Decision Tree (定理推理)** | [L0: 方法论](../00_meta/methodology.md) | 所有文件 | — | 规范所有推理链的呈现方式 |
| **Drop Trait** | [L1: 所有权](../01_foundation/01_ownership.md) | L2 Trait、L4 线性逻辑 | 理解 | ← 所有权 → RAII ≡ 资源消耗 |
| **dyn Trait** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 Trait、L4 类型论 | 分析 | ⊘ impl Trait → 动态分发 |

### E

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Edition Mechanism** | [L7: 语言演进](../07_future/03_evolution.md) | 所有层 | 评价 | ← RFC 流程 → 向后兼容演进 |
| **Elision Rules** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L2 泛型、L4 区域类型 | 应用 | ← 生命周期标注 → 简化书写 |
| **enum (Sum Type)** | [L1: 类型系统](../01_foundation/04_type_system.md) | L2 错误处理、L4 代数类型 | 理解 | ≡ 和类型 / 余积 (A + B) |
| **Error Handling (Result/Option)** | [L2: 错误处理](../02_intermediate/04_error_handling.md) | L1 类型系统、L3 异步 | 应用 | ← Option/Result → ? 运算符 |

### F

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
| **Unpin** | [L3: 异步](../03_advanced/02_async.md) | L3 Pin | 分析 | ⊘ Pin → 默认可移动 |

### V

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Variance** | [L1: 生命周期](../01_foundation/03_lifetimes.md) | L4 类型论 | 分析 | ← 子类型 → 生命周期安全 |

### Z

| 概念 | 主文件 | 交叉引用 | Bloom 层级 | 语义链接 |
|:---|:---|:---|:---|:---|
| **Zero-cost Abstraction** | [L6: 设计模式](../06_ecosystem/02_patterns.md) | L2 泛型、L5 对比 | 评价 | ← 单态化 → 运行时零开销 |

---

## 三、交叉概念一致性审计（🔶）

以下概念在**多个文件中重复出现**，需要确保定义一致：

### 3.1 Pin（出现在 4+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: 异步](../03_advanced/02_async.md) | Pin 的核心定义：自引用安全 | ✅ 主定义 |
| [L1: 借用](../01_foundation/02_borrowing.md) | Pin 与借用规则的交互 | ⚠️ 需链接到主定义 |
| [L2: 内存管理](../02_intermediate/03_memory_management.md) | Pin 在堆内存中的使用 | ⚠️ 需链接到主定义 |
| [L4: 形式化](../04_formal/03_ownership_formal.md) | Pin 的形式化语义 | 🔍 待补充精确对应 |

**一致性要求**: 所有文件中对 Pin 的定义必须以 L3 为准，差异处需显式标注。

### 3.2 Send / Sync（出现在 3+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: 并发](../03_advanced/01_concurrency.md) | Send/Sync 的完整定义与规则 | ✅ 主定义 |
| [L2: Trait](../02_intermediate/01_traits.md) | Send/Sync 作为 Auto Trait 的特性 | ⚠️ 需链接到主定义 |
| [L4: RustBelt](../04_formal/04_rustbelt.md) | Send/Sync 的并发分离逻辑语义 | ⚠️ 需显式映射 |

### 3.3 Unsafe（出现在 3+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L3: Unsafe](../03_advanced/03_unsafe.md) | Unsafe 的完整定义与安全契约 | ✅ 主定义 |
| [L1: 所有权](../01_foundation/01_ownership.md) | Unsafe 突破所有权 | ⚠️ 需标注为"边界条件" |
| [L5: Rust vs C++](../05_comparative/01_rust_vs_cpp.md) | Unsafe 在对比语境中的意义 | ⚠️ 需与 L3 定义对齐 |
| [L4: RustBelt](../04_formal/04_rustbelt.md) | Unsafe 在形式化中的范围 | ✅ 一致: unsafe 在证明范围外 |

### 3.4 生命周期（出现在 4+ 个文件中）

| 文件 | 定义侧重点 | 一致性检查 |
|:---|:---|:---|
| [L1: 生命周期](../01_foundation/03_lifetimes.md) | 核心定义、标注、Elision | ✅ 主定义 |
| [L2: 泛型](../02_intermediate/02_generics.md) | 生命周期作为泛型参数 | ⚠️ 需链接 |
| [L3: 异步](../03_advanced/02_async.md) | 生命周期在 Future 中的传播 | ⚠️ 需链接 |
| [L4: 形式化](../04_formal/03_ownership_formal.md) | 区域类型的形式化对应 | ✅ 已显式映射 |

---

## 四、引用概念速查（🔹）

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

## 五、按 Bloom 层级排序

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

## 七、TODO

- [ ] **高**: 为所有 🔶 交叉概念建立"单一来源规范"（Single Source of Truth）声明
- [ ] **高**: 在每个主定义文件中添加"其他文件中出现的链接"
- [ ] **中**: 为每个概念补充"常见编译错误代码 → 概念"映射（如 E0382 → Move）
- [ ] **中**: 建立"反例 → 概念"索引（如 Rc 循环引用 → 所有权边界）
- [ ] **低**: 导出为机器可解析格式（JSON/YAML）供自动一致性检查
- [ ] **低**: 与 `inter_layer_map.md` 的层间映射同步更新
