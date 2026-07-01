# Rust 知识体系全景导航（Navigation Hub）
>
> **EN**: Navigation
> **Summary**: Navigation hub and learning-path index for the concept map.
> **受众**: [初学者]
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定位**: 本文件是 `concept/` 知识体系的**统一入口**，提供按层级、按主题、按背景的多维导航路径。
> **适用对象**: 任何希望系统掌握 Rust 语义空间的读者。
> **Bloom 层级**: 应用
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
> **来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/)
---

## 〇、质量状态速览

| 指标 | 数值 | 状态 |
|:---|:---|:---:|
| 核心概念文件 | 58 | ✅ |
| 总文件数 | **81** | ✅ |
| 总行数 | ~75,000 | ✅ |
| 来源标注 | ~1,350 | ✅ |
| Mermaid 图表 | **332（20 种类型）** | ✅ |
| 代码块编译 | 226/226 通过 | ✅ |
| 死链接 | 0 | ✅ |
| 概念一致性 | 0 错误 / 0 警告 | ✅ |
| A/S/P 标记覆盖 | 58/58（100%） | ✅ |
| 判定树覆盖 | 8 棵（L1-L4） | ✅ |
| FTA 覆盖 | 5 棵（五大顶事件） | ✅ |

---

## 一、按层级导航（L0-L7）

### L0 元信息层 — 方法论与索引

| 文件 | 核心内容 | Mermaid 图表 |
|:---|:---|:---:|
| [knowledge_mindmap](knowledge_mindmap.md) | 全局认知入口：L0-L7 放射图 + 五维主线 | 2 |
| [methodology](methodology.md) | 思维表征规范：17 种类型定义与使用场景 | 5 |
| [learning_guide](learning_guide.md) | 学习路径：按背景（C++/Java/Haskell/新手）定制 | 1 |
| [sources](sources.md) | 权威来源清单：五级来源体系（规范→社区） | 3 |
| [inter_layer_map](inter_layer_map.md) | 跨层依赖图：L1-L4 定理传递链 | 2 |
| [inter_layer_topology](inter_layer_topology.md) | 跨层拓扑：认知路径 + 反命题树 | 3 |
| [intra_layer_model_map](intra_layer_model_map.md) | 层内映射：模型间关系 + 决策树 | 5 |
| [theorem_inference_forest](theorem_inference_forest.md) | 定理森林：L1-L4 六棵定理树 | 3 |
| [boundary_extension_tree](boundary_extension_tree.md) | 边界扩展树：安全边界五层扩展 + 风险矩阵 | 3 |
| [semantic_space](semantic_space.md) | 表征空间：能/不能表达 + 等价表达选择 | 5 |
| [semantic_expressiveness](semantic_expressiveness.md) | 表达力七维光谱：控制/数据/类型/并发/内存/抽象/安全 | 2 |
| [decidability_spectrum](decidability_spectrum.md) | 可判定性谱系：9 层判定边界 + Rice 定理 | 6 |
| [expressiveness_multiview](expressiveness_multiview.md) | 表达力七视角：类型/控制/内存/并发/抽象/安全/模块 | 7 |
| [cognitive_dimension_matrix](cognitive_dimension_matrix.md) | 双维认知矩阵：Krathwohl × Bloom 全局映射 | 1 |
| [asp_marking_guide](asp_marking_guide.md) | A/S/P 三维标记规范：认知自动化边界 | 2 |
| [concept_definition_decision_forest](concept_definition_decision_forest.md) | 概念判定森林：8 棵判定树（定义→前提→规则→判定） | 10 |
| [fault_tree_analysis_collection](fault_tree_analysis_collection.md) | 失效分析树集：5 棵标准 FTA（IEC 61025） | 5 |
| [quality_dashboard_v2](quality_dashboard_v2.md) | 思维表征覆盖率仪表板：332 图表 / 20 种类型 | 1 |
| [problem_graph](problem_graph.md) | 问题图谱：六大系统级问题分解树（全局→概念→方法） | 6 |
| [competency_graph](competency_graph.md) | 能力图谱：六维雷达 + Dreyfus 映射 + 自评工具 | 3 |
| [kg_ontology](kg_ontology.md) | 知识图谱本体：8 实体类型 + 8 关系类型 + RDF/OWL 格式 | 2 |
| [rustbelt_predicate_map](rustbelt_predicate_map.md) | RustBelt 谓词映射：own/shr/生命周期令牌 L4→L1 可视化 | 4 |
| [paradigm_transition_matrix](paradigm_transition_matrix.md) | 范式转换矩阵：C++/Java/Go/Python → Rust 模式映射 | 3 |
| [audit_checklist](audit_checklist.md) | 质量门禁：跨文件一致性检查清单 | 1 |

### L1 基础概念层 — 所有权、借用、生命周期、类型系统

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_ownership](../01_foundation/01_ownership.md) | 所有权唯一性、Move/Copy/Drop、RAII | 7 |
| [02_borrowing](../01_foundation/02_borrowing.md) | &T/&mut T、AXM 规则、Reborrow、内部可变性 | 6 |
| [03_lifetimes](../01_foundation/03_lifetimes.md) | 生命周期标注、Elision、NLL、HRTB、Variance | 5 |
| [04_type_system](../01_foundation/04_type_system.md) | ADT、Trait 对象、模式匹配、类型推断 | 8 |

> **认知路径**: L1 是 Rust 的"地基"——不理解所有权和借用，后续所有内容都无法建立正确直觉。建议从 ownership 开始，依次阅读 borrowing → lifetimes → type_system。

### L2 进阶概念层 — Trait、泛型、内存管理、错误处理

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_traits](../02_intermediate/01_traits.md) | Trait 定义、Bounds、Orphan Rule、GATs、Auto Traits | 5 |
| [02_generics](../02_intermediate/02_generics.md) | 单态化、Const Generics、HRTB | 6 |
| [03_memory_management](../02_intermediate/03_memory_management.md) | Box/Rc/Arc、RefCell/Mutex、Pin | 5 |
| [04_error_handling](../02_intermediate/04_error_handling.md) | Result/Option、? 运算符、错误传播 | 8 |

> **关键交叉点**: Trait Bounds 是 Trait 与泛型的结合部——理解这一点是掌握 Rust 零成本抽象的关键。

### L3 高级概念层 — 并发、异步、Unsafe、宏

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_concurrency](../03_advanced/01_concurrency.md) | Send/Sync、fearless concurrency、Atomics、Channel | 15 |
| [02_async](../03_advanced/02_async.md) | Future/Poll、async/await、Pin、AFIT、状态机 | 9 |
| [03_unsafe](../03_advanced/03_unsafe.md) | 裸指针、FFI、Union、Safety Contracts、Miri | 10 |
| [04_macros](../03_advanced/04_macros.md) | macro_rules!、过程宏、DSL | 8 |

> **核心洞察**: 并发和异步都是所有权系统在不同执行模型下的应用——线程是抢占式并行，Future 是协作式串行。

### L4 形式化理论层 — 线性逻辑、类型论、所有权形式化、RustBelt

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_linear_logic](../04_formal/01_linear_logic.md) | Girard 线性逻辑、仿射逻辑、Rust 映射 | 5 |
| [02_type_theory](../04_formal/02_type_theory.md) | HM 推断、System F、代数类型、子类型 | 5 |
| [03_ownership_formal](../04_formal/03_ownership_formal.md) | COR、区域类型、分离逻辑、Polonius | 5 |
| [04_rustbelt](../04_formal/04_rustbelt.md) | Iris 分离逻辑、并发安全证明、Unsafe 边界 | 5 |
| [05_verification_toolchain](../04_formal/05_verification_toolchain.md) | Kani/Verus/Creusot 选型、ROI 分析、分层验证 | 4 |

> **关键洞察**: L4 不是 L3 的"更高级版本"，而是 L1-L3 的"数学根基"——形式化证明向下保证上层概念的安全性。

### L5 对比分析层 — Rust vs C++/Go、范式矩阵、安全边界

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_rust_vs_cpp](../05_comparative/01_rust_vs_cpp.md) | 所有权 vs 智能指针、编译期 vs 运行时、形式系统 vs 机制工程 | 13 |
| [02_rust_vs_go](../05_comparative/02_rust_vs_go.md) | 所有权并发 vs CSP、确定性 vs 工程性 | 6 |
| [03_paradigm_matrix](../05_comparative/03_paradigm_matrix.md) | 多语言类型系统谱系、内存模型对比 | 8 |
| [04_safety_boundaries](../05_comparative/04_safety_boundaries.md) | 安全保证边界、反事实推理、失效条件 | 7 |
| [05_execution_model_isomorphism](../05_comparative/05_execution_model_isomorphism.md) | 七类执行模型矩阵、Rust↔Go 对比 | 5 |

> **综合功能**: L5 将 L1-L4 的知识转化为工程决策能力——为技术选型提供形式化论据。

### L6 生态工程层 — 工具链、设计模式、核心库、应用主题

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_toolchain](../06_ecosystem/01_toolchain.md) | Cargo、Clippy、Miri、交叉编译 | 9 |
| [02_patterns](../06_ecosystem/02_patterns.md) | Typestate、Builder、RAII、Newtype | 5 |
| [03_core_crates](../06_ecosystem/03_core_crates.md) | Tokio、Serde、SQLx、Axum 生态基石 | 6 |
| [03_idioms_spectrum](../06_ecosystem/03_idioms_spectrum.md) | L0-L6 七层惯用法 + 反惯用法判定树 | 5 |
| [04_application_domains](../06_ecosystem/04_application_domains.md) | Web、系统、嵌入式、区块链应用场景 | 6 |
| [05_formal_ecosystem_tower](../06_ecosystem/05_formal_ecosystem_tower.md) | 形式化分层塔：Tokio→Tower→Axum→Kani | 2 |
| [05_system_design_principles](../06_ecosystem/05_system_design_principles.md) | 七项原则 + 国际权威对齐 | 6 |
| [06_blockchain](../06_ecosystem/06_blockchain.md) | Solana/Polkadot、Move vs Rust、Kani 验证 | 3 |
| [07_game_ecs](../06_ecosystem/07_game_ecs.md) | ECS 架构、Bevy、Archetype | 7 |
| [08_wasi](../06_ecosystem/08_wasi.md) | WASI 四层架构、能力安全、wit-bindgen | 2 |
| [09_cargo_script](../06_ecosystem/09_cargo_script.md) | Cargo script 执行流程、决策树 | 2 |
| [10_public_private_deps](../06_ecosystem/10_public_private_deps.md) | 依赖泄漏/隔离、[RFC 3516](https://rust-lang.github.io/rfcs//3516-public-private-dependencies.html)、决策流程 | 2 |

> **出口层**: L6 是知识体系的"工程化落地"——将理论转化为可维护、可扩展的代码库。

### L7 前沿趋势层 — AI、形式化方法、语言演进

| 文件 | 核心内容 | 关键图表 |
|:---|:---|:---|
| [01_ai_integration](../07_future/01_ai_integration.md) | AI 生成-验证闭环、确定性容器、三层闭环 | 6 |
| [02_formal_methods](../07_future/02_formal_methods.md) | Creusot/Verus/Kani 工业化、TLA+ | 9 |
| [03_evolution](../07_future/03_evolution.md) | RFC 流程、Edition 机制、2015→2024 完整变更 | 6 |
| [04_effects_system](../07_future/04_effects_system.md) | Effect System 概念预研、AsyncFn、跨语言对比 | 4 |
| [05_rust_version_tracking](../07_future/05_rust_version_tracking.md) | 1.79→1.97+ 形式模型演进跟踪 | 3 |

> **反向驱动**: L7 的独特特征是"反馈"——AI 需求约束 Unsafe 精确性，形式化工具化推动 L4 扩展，语言演进扩展 L2 泛型系统。

---

## 二、按背景导航

### 完全新手（无系统编程经验）

```text
L1: ownership → borrowing → lifetimes → type_system
L2: traits → generics → memory_management → error_handling
L3: concurrency → async
```
**Checkpoint**: 完成 L1 后应能回答：为什么 `let s2 = s1; println!("{}", s1);` 编译失败？

### C/C++ 开发者

```text
L1: ownership（对比 unique_ptr） + L5: rust_vs_cpp
L3: unsafe（对比 C 指针安全）
L5: rust_vs_cpp（本体论差异系统对比）
```
**加速技巧**: `Box<T>` ≈ `unique_ptr<T>`，`Rc<T>` ≈ `shared_ptr<T>`（无循环回收），`&mut T` ≈ `T*`（编译器保证无别名）

### Java/Go 开发者

```text
L1: ownership（核心问题：没有 GC 如何管理内存？）
L2: traits（对比 Java Interface/Go Interface）
L3: concurrency（对比 goroutine/channel）
L5: rust_vs_go
```
**关键心智转换**: GC 对象生命周期 → 所有权系统管理生命周期

### Haskell/ML 开发者

```text
L2: traits + generics（利用类型论基础）
L4: linear_logic + type_theory（形式化视角）
L5: paradigm_matrix（Rust 在设计空间中的位置）
```
**加速技巧**: Trait ≈ Type Class，Lifetime ≈ Region Type，`?` ≈ Monad 的 `>>=`

---

## 三、按主题速查
>

| 你想了解 | 首选文件 | 次选 |
|:---|:---|:---|
| 为什么 Rust 安全？ | L1 ownership + L4 RustBelt | L5 safety_boundaries |
| async/await 原理 | L3 async | L7 effects_system |
| 并发编程 | L3 concurrency | L5 rust_vs_go |
| 泛型与 Trait | L2 traits + generics | L4 type_theory |
| Unsafe 边界 | L3 unsafe | L4 ownership_formal |
| 形式化验证 | L4 verification_toolchain | L7 formal_methods |
| 生态系统选型 | L6 core_crates + formal_ecosystem_tower | L6 patterns |
| 语言演进方向 | L7 evolution | L7 version_tracking |
| 可判定性边界 | L0 decidability_spectrum | L4 linear_logic |
| 表达力对比 | L0 expressiveness_multiview | L5 paradigm_matrix |

---

## 四、质量报告

- [质量基线报告 v1.9](../../reports/QUALITY_BASELINE_v1_9.md)
- [概念审计报告](../../reports/concept_audit_report.md)
- [概念一致性报告](../../reports/concept_consistency_report.md)
- [代码块编译报告](../../reports/code_block_compile_report.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 与知识体系 v2.0 同步
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Standard Library](https://doc.rust-lang.org/std/)
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)

## 认知路径

> **认知路径**: 本文件作为 Rust 分层知识体系的 **Rust 知识体系全景导航（Navigation Hub）** 元层导航节点，连接概念定义、学习路径与质量评估框架。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Navigation 结构化定义 ⟹ 学习者认知锚点可建立 | 本文件定义了元层结构 | 支持上层概念定位 | 高 |

> **过渡**: 利用本文件的导航结构，读者可以从当前位置快速跃迁到任意概念层级，实现非线性学习。
> **过渡**: Rust 知识体系全景导航（Navigation Hub） 的维护需要与概念内容同步更新，确保元数据与实际知识体系的一致性。
> **过渡**: 将 Rust 知识体系全景导航（Navigation Hub） 作为学习起点或复习锚点，有助于建立全局视野，避免陷入局部细节而忽视整体架构。

### 反命题与边界

> **反命题**: "元层文档可以替代具体概念学习" —— 错误。Rust 知识体系全景导航（Navigation Hub） 提供的是导航与评估框架，不能替代对核心概念（L1-L5）的深入理解与实践。
> **内容分级**: [综述级]

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文档《Rust 知识体系全景导航（Navigation Hub）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）

**题目**: 本文档《Rust 知识体系全景导航（Navigation Hub）》在 Rust 知识体系中属于哪一层级的元数据？

<details>
<summary>✅ 答案与解析</summary>

属于 00_meta 元数据层，为整个知识体系提供导航、评估、审计和结构化的支持框架，辅助学习者定位和理解核心概念。
</details>

---

### 测验 2：《Rust 知识体系全景导航（Navigation Hub）》的主要用途是什么？（理解层）

**题目**: 《Rust 知识体系全景导航（Navigation Hub）》的主要用途是什么？

<details>
<summary>✅ 答案与解析</summary>

作为知识体系的支撑文档，提供学习路径导航、概念关系映射、质量评估标准或审计检查清单，帮助学习者和维护者高效使用知识库。
</details>

---

### 测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）

**题目**: 元数据层文档能否替代 L1-L7 的核心概念学习？

<details>
<summary>✅ 答案与解析</summary>

不能。元数据层提供导航和评估框架，但不能替代对核心概念（所有权、类型系统、并发等）的深入理解与实践。
</details>
