# KG 语义关系实例化（equivalentTo / instanceOf / appliesTo）

**日期**: 2026-07-16  **模式**: 已写回 kg_data_v3.json  
**equivalentTo**: 3 条  **instanceOf**: 18 条  **appliesTo**: 14 条  
**改动总数**: 35（跳过实体缺失 6）

## 谓词分布前后对比

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:relatedTo | 6758 | 6746 | -12 |
| ex:dependsOn | 854 | 854 | +0 |
| ex:entails | 768 | 768 | +0 |
| ex:instanceOf | 0 | 18 | +18 |
| ex:appliesTo | 0 | 14 | +14 |
| ex:refines | 12 | 12 | +0 |
| ex:counterExample | 5 | 5 | +0 |
| ex:mutexWith | 5 | 5 | +0 |
| ex:equivalentTo | 0 | 3 | +3 |

## 逐边明细与依据

| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |
|:---|:---|:---|:---|:---|:---|
| E3-same-concept-xlayer | added new edge | ex:PanicAndAbort | ex:equivalentTo | ex:Panic | 02_intermediate/03_error_handling/03_panic.md:9 Summary“Rust panic 的规范语义”，前置依赖指向 03_panic_and_abort.md；后者定位“系统讲解 Rust panic 机制”——同一 panic 概念的 L1/L2 两页 |
| E3-same-concept-xlayer | added new edge | ex:BorrowSanitizerRuntimeTreeBorrowsViolationDetection | ex:equivalentTo | ex:BorrowSanitizerBSanDynamicAliasingRuleVerificationForRust | 04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md 与 07_future/02_preview_features/24_borrow_sanitizer.md 均为 BorrowSanitizer/BSan 权威页（MCP 958；LLVM 插桩动态别名检测），跨 L4/L7 双页 |
| E3-same-concept-xlayer | retyped relatedTo | ex:RustBelt | ex:equivalentTo | ex:RustBelt_02separation | 两实体 prefLabel 均为 RustBelt；00_meta/02_sources/02_rustbelt_predicate_map.md 定位“将 RustBelt（Jung et al., POPL 2018）的核心形式化谓词映射到 L1-L3 工程概念”，04_formal/02_separation_logic/01_rustbelt.md Summary“RustBelt: a formal model of Rust's ownership and borrowing in Iris separation logic” |
| I1-category-listed | added new edge | ex:MiriRustUndefinedBehaviorDetector | ex:instanceOf | ex:VerificationToolchain | 04_formal/04_model_checking/01_verification_toolchain.md:6 Summary“The Rust formal verification toolchain: Miri, Kani, Creusot, Verus, Prusti, and RustBelt.” |
| I1-category-listed | added new edge | ex:KaniRustBoundedModelChecker | ex:instanceOf | ex:VerificationToolchain | 01_verification_toolchain.md:6 Summary 将 Kani 列为验证工具链成员 |
| I1-category-listed | retyped relatedTo | ex:AutoVerusAndVerusAutomatedVerificationEcosystem | ex:instanceOf | ex:VerificationToolchain | 01_verification_toolchain.md:6 Summary 将 Verus 列为验证工具链成员 |
| I1-category-listed | added new edge | ex:RustBelt_02separation | ex:instanceOf | ex:VerificationToolchain | 01_verification_toolchain.md:6 Summary 将 RustBelt 列为验证工具链成员 |
| I3-self-evident-kind | retyped relatedTo | ex:ProceduralMacros | ex:instanceOf | ex:Macros | 01_foundation/09_macros_basics/01_attributes_and_macros.md:4 关键术语“宏 (Macro) · 声明宏 (Declarative Macro) · 过程宏 (Procedural Macro)”；03_advanced/03_proc_macros/02_proc_macro.md:170“三种宏（Macro）的编译期执行模型相同”——过程宏是宏的一种 |
| I3-self-evident-kind | retyped relatedTo | ex:DerivableTraits | ex:instanceOf | ex:Traits | 02_intermediate/00_traits/06_derive_traits.md:7 Summary“标准库中可通过 #[derive(...)] 自动实现的 trait 参考”——可派生 trait 是 trait 的一个子范畴 |
| I3-self-evident-kind | added parallel edge | ex:PanicAndAbort | ex:instanceOf | ex:ErrorHandling | 01_foundation/08_error_handling/03_panic_and_abort.md 标题“Panic 与 Abort：不可恢复错误的处理机制”——panic/abort 是错误处理机制的一种（不可恢复分支） |
| I3-self-evident-kind | added new edge | ex:Panic | ex:instanceOf | ex:ErrorHandling | 02_intermediate/03_error_handling/03_panic.md:30“Panic 是 Rust 提供的机制，用于阻止函数正常返回，以响应通常不可恢复的错误条件” |
| I2-category-section | added new edge | ex:CowAndBorrowed | ex:instanceOf | ex:SmartPointers | 02_intermediate/02_memory_management/04_smart_pointers.md:620“下层概念: Pin · Cow”——Cow 被智能指针权威页收录为下层概念（写时克隆智能指针） |
| I2-category-section | added new edge | ex:PinAndUnpin | ex:instanceOf | ex:SmartPointers | 04_smart_pointers.md:620“下层概念: Pin · Cow”；:19 后置概念含 Pin——Pin 被智能指针权威页收录为下层概念 |
| I2-category-section | retyped relatedTo | ex:CustomAllocators | ex:instanceOf | ex:MemoryManagement | 02_intermediate/02_memory_management/01_memory_management.md:101 设 §5.7“自定义 Allocator（#[global_allocator]）”章节——自定义分配器是内存管理机制的实例 |
| I3-self-evident-kind | added parallel edge | ex:LockingPrimitives | ex:instanceOf | ex:Concurrency | 03_advanced/00_concurrency/07_lock_free.md:11“深入探讨 Rust 中的无锁编程”（位于 00_concurrency 章节）；01_concurrency.md:181-182 将锁/原子操作列为并发同步手段——无锁原语是并发技术的一种 |
| I1-category-listed | retyped relatedTo | ex:NewtypeAndWrapperTypes | ex:instanceOf | ex:DesignPatterns | 06_ecosystem/03_design_patterns/01_patterns.md:66“\| Newtype \| 结构型 \| 类型区分 + 约束 \| struct Wrapper(T) \|”——Newtype 被设计模式权威页列为结构型模式 |
| I3-self-evident-kind | added new edge | ex:EventDrivenArchitecture | ex:instanceOf | ex:DesignPatterns | 06_ecosystem/03_design_patterns/06_event_driven_architecture.md:16“Rust 实现事件驱动架构的核心模式”（位于 03_design_patterns 章节） |
| I3-self-evident-kind | added new edge | ex:CqrsEventSourcing | ex:instanceOf | ex:DesignPatterns | 06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md:15“设计高可靠分布式系统的数据持久化模式”（位于 03_design_patterns 章节） |
| I2-category-section | added new edge | ex:ClosureTypes | ex:instanceOf | ex:Closures | 01_foundation/00_start/03_closure_basics.md:2 关键术语“闭包 (Closure) · Fn · FnMut · FnOnce”；:7 Summary 将 Fn/FnMut/FnOnce（闭包类型）作为闭包概念的组成 |
| I3-self-evident-kind | added new edge | ex:ConstantEvaluation | ex:instanceOf | ex:CompileTimeExecution | 07_future/02_preview_features/32_compile_time_execution.md:1 标题“编译期执行与常量求值”——常量求值（const eval）是编译期执行的实例 |
| I2-category-section | added new edge | ex:TypeErasure | ex:instanceOf | ex:DispatchMechanisms | 02_intermediate/00_traits/02_dispatch_mechanisms.md:8 Summary 覆盖“动态分发、trait objects、vtables”；04_formal/05_rustc_internals/15_generics_compiler_behavior.md:4 将“静态分发与动态分发、类型擦除”并列为泛型编译行为——类型擦除是动态分发机制的实现 |
| A1-page-application | added parallel edge | ex:MiriRustUndefinedBehaviorDetector | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 04_formal/04_model_checking/08_miri.md:9 Summary“Miri is Rust's official MIR interpreter for detecting undefined behavior in unsafe and safe Rust code” |
| A1-page-application | added new edge | ex:KaniRustBoundedModelChecker | ex:appliesTo | ex:FormalMethods_04modelcheck | 04_formal/04_model_checking/09_kani.md:9 Summary“Kani is an AWS-developed bounded model checker for Rust. It verifies properties over all possible inputs and execution paths within bounds”——应用于模型检查领域 |
| A1-page-application | added parallel edge | ex:SerdePatterns | ex:appliesTo | ex:Traits | 02_intermediate/00_traits/03_serde_patterns.md:4“Serde 序列化模式：Rust 的类型驱动数据转换”（位于 00_traits 章节；关键术语 Serialize/Deserialize trait）——serde 是 trait 机制的应用 |
| A1-page-application | retyped relatedTo | ex:RustBelt_02separation | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 04_formal/02_separation_logic/01_rustbelt.md:23 后置/相关链接 Unsafe Rust；:35“扩展层次一致性标注至 L3 Unsafe”；来源标题“RustBelt: Securing the Foundations of the Rust Programming Language”——RustBelt 应用于 unsafe 抽象可靠性 |
| A2-prereq-domain | retyped relatedTo | ex:TreeBorrowsDeepDive | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md:10 受众“Unsafe Rust、形式化方法…开发者”；:15 前置依赖 Unsafe Rust——Tree Borrows 别名模型应用于 unsafe 代码合法性判定 |
| A2-prereq-domain | retyped relatedTo | ex:BehaviorConsideredUndefined | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 04_formal/01_ownership_logic/06_behavior_considered_undefined.md:14 前置依赖 Unsafe Rust；Summary“Rust Reference 明确列出的未定义行为（UB）清单…核心安全契约边界”——UB 清单应用于 unsafe 契约边界 |
| A2-prereq-domain | retyped relatedTo | ex:BorrowSanitizerRuntimeTreeBorrowsViolationDetection | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md 前置依赖 Unsafe Rust · Miri；Summary“基于 LLVM 插桩的动态分析工具，用于检测 Rust 别名模型…违规”——应用于 unsafe 别名违规检测 |
| A2-prereq-domain | added new edge | ex:ApplicationBinaryInterface | ex:appliesTo | ex:ForeignFunctionInterfaceFFI | 04_formal/05_rustc_internals/05_application_binary_interface.md:15 前置依赖 Linkage · FFI Advanced；来源 Rust Reference extern functions/external blocks——ABI 规则应用于 FFI 边界 |
| A1-page-application | added new edge | ex:MemoryModel | ex:appliesTo | ex:Concurrency | 03_advanced/02_unsafe/06_memory_model.md:11“其并发内存序维度见 Atomics and Memory Ordering”；:33“将 Rust 内存模型与原子操作…链接”——内存模型应用于并发语义 |
| A1-page-application | retyped relatedTo | ex:PinAndUnpin | ex:appliesTo | ex:AsyncProgramming | 03_advanced/01_async/08_pin_unpin.md:6 Summary“their interaction with futures and generators”；:16“探讨 Pin 与 Future、Generator 的交互，以及 async/await 的状态机实现”——Pin 应用于 async 状态机 |
| A1-page-application | added parallel edge | ex:GenericsCompilerBehavior | ex:appliesTo | ex:Generics | 04_formal/05_rustc_internals/15_generics_compiler_behavior.md:4 Summary“Rust 泛型（Generics）代码的编译行为：单态化、静态分发与动态分发、类型擦除…”——应用于泛型编译 |
| A1-page-application | added new edge | ex:TypeInference | ex:appliesTo | ex:TypeSystem | 04_formal/00_type_theory/03_type_inference.md:15“Rust 对 HM 的扩展（trait 约束、泛型（Generics）、生命周期（Lifetimes））”——类型推断算法应用于 Rust 类型系统 |
| A1-page-application | added parallel edge | ex:TheTraitSolverInRustc | ex:appliesTo | ex:Traits | 04_formal/05_rustc_internals/03_trait_solver_in_rustc.md:2 关键术语“Trait Solver · Selection · Fulfillment · Evaluation · Obligation”——trait 求解器应用于 trait 约束求解 |
| A1-page-application | retyped relatedTo | ex:DispatchMechanisms | ex:appliesTo | ex:Traits | 02_intermediate/00_traits/02_dispatch_mechanisms.md:8 Summary“Static and dynamic dispatch in Rust: monomorphization, trait objects, vtables, object safety”（位于 00_traits 章节）——分发机制应用于 trait 使用 |

## 跳过（实体缺失）

- `ex:LifetimesAdvanced` -[ex:equivalentTo]-> `ex:Lifetimes_00traits`：端点实体不存在
- `ex:AutoVerusAndVerusAutomatedVerificationEcosystem` -[ex:equivalentTo]-> `ex:AutoVerusVerus`：端点实体不存在
- `ex:SafetyTagsForUnsafeCode` -[ex:equivalentTo]-> `ex:SafetyTagsForUnsafeCode_03previewfea`：端点实体不存在
- `ex:SafetyTagsPreview` -[ex:equivalentTo]-> `ex:SafetyTagsForUnsafeCode_03previewfea`：端点实体不存在
- `ex:BorrowSanitizerBSanDynamicAliasingRuleVerificationForRust` -[ex:equivalentTo]-> `ex:BorrowSanitizerPreview`：端点实体不存在
- `ex:GameDevelopment_11domainappl` -[ex:equivalentTo]-> `ex:GameDevelopment_11domainappl_1`：端点实体不存在

## 范畴节点缺口清单（按约束未新建实体）

| 缺失节点 | 原计划边 | 说明/替代 |
|:---|:---|:---|

## 备注

- equivalentTo 在 schema 中声明为 Symmetric+Transitive+Reflexive，按 `type_kg_core_edges.py` 惯例只落单向边。
- Unsafe（L3 01_unsafe）与 L4 tree_borrows / behavior_considered_undefined **不**建 equivalentTo：后两者是别名模型/UB 清单等独立概念，已改用 appliesTo 指向 ex:SafeAndEffectiveUnsafeRust。

## 机器可读

- JSON: `reports/KG_SEMANTIC_EDGE_TYPING_2026-07-16.json`
