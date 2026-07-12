# KG 范畴/领域节点补建（第二轮语义边实例化）

**日期**: 2026-07-12  **模式**: 已写回 kg_data_v3.json
**新建节点**: 17（跳过已存在 0）
**新建边**: 14（instanceOf 11 + appliesTo 3；跳过实体缺失 0）
**前序**: `reports/KG_SEMANTIC_EDGE_TYPING_2026_07_12.md`（第一轮；本报告解决其“范畴节点缺口清单”全部 9 项）

## 新建节点明细

| @id | @type | ex:path | layer | domain | bloom |
|:---|:---|:---|:---:|:---:|:---:|
| `ex:Vec` | ex:Primitive | `01_foundation/05_collections/01_collections.md` | L1 | language_core | L1-L2 |
| `ex:HashMap` | ex:Primitive | `01_foundation/05_collections/01_collections.md` | L1 | language_core | L1-L2 |
| `ex:AsyncRuntime` | ex:Concept | `03_advanced/01_async/04_future_and_executor_mechanisms.md` | L3 | async | L3-L4 |
| `ex:Tokio` | ex:Concept | `03_advanced/01_async/06_async_boundary_panorama.md` | L3 | async | L3-L4 |
| `ex:AutoTrait` | ex:Concept | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | L3 | concurrency | L3-L4 |
| `ex:Send` | ex:Primitive | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | L3 | concurrency | L3-L4 |
| `ex:Sync` | ex:Primitive | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | L3 | concurrency | L3-L4 |
| `ex:Box` | ex:Primitive | `02_intermediate/02_memory_management/04_smart_pointers.md` | L2 | ownership_memory | L2-L3 |
| `ex:Rc` | ex:Primitive | `02_intermediate/02_memory_management/04_smart_pointers.md` | L2 | ownership_memory | L2-L3 |
| `ex:Arc` | ex:Primitive | `02_intermediate/02_memory_management/04_smart_pointers.md` | L2 | ownership_memory | L2-L3 |
| `ex:AlgebraicDataType` | ex:Concept | `04_formal/00_type_theory/01_type_theory.md` | L4 | formal_methods | L4-L5 |
| `ex:Result` | ex:Primitive | `01_foundation/08_error_handling/01_error_handling_basics.md` | L1 | language_core | L1-L2 |
| `ex:Option` | ex:Primitive | `01_foundation/07_modules_and_items/05_enumerations.md` | L1 | language_core | L1-L2 |
| `ex:Serialization` | ex:Concept | `02_intermediate/00_traits/03_serde_patterns.md` | L2 | type_system | L2-L4 |
| `ex:ModelChecking` | ex:Concept | `04_formal/04_model_checking/09_kani.md` | L4 | formal_methods | L4-L5 |
| `ex:FormalVerificationFramework` | ex:Concept | `06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md` | L6 | ecosystem_security | L5-L6 |
| `ex:UnsafeAbstractionSoundness` | ex:Concept | `04_formal/02_separation_logic/01_rustbelt.md` | L4 | formal_methods | L4-L5 |

## 谓词分布前后对比

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:relatedTo | 4913 | 4913 | +0 |
| ex:dependsOn | 729 | 729 | +0 |
| ex:entails | 695 | 695 | +0 |
| ex:instanceOf | 0 | 11 | +11 |
| ex:appliesTo | 0 | 3 | +3 |

## 逐边明细与依据

| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |
|:---|:---|:---|:---|:---|:---|
| I1-category-listed | added new edge | ex:Vec | ex:instanceOf | ex:Collections | 01_foundation/05_collections/01_collections.md:5 关键术语“集合 (Collection) · 向量 (Vec)”；:10 Summary“The standard collections (Vec, VecDeque, HashMap, BTreeMap, sets)”——Vec 被集合权威页列为标准集合 |
| I1-category-listed | added new edge | ex:HashMap | ex:instanceOf | ex:Collections | 01_foundation/05_collections/01_collections.md:5 关键术语“集合 (Collection) · … · 哈希映射 (HashMap)”；:10 Summary 将 HashMap 列为标准集合；:41 设“1.3 HashMap vs BTreeMap”章节 |
| I3-self-evident-kind | added new edge | ex:Tokio | ex:instanceOf | ex:AsyncRuntime | 03_advanced/01_async/06_async_boundary_panorama.md:283“work-stealing 运行时（Tokio 多线程、async-std）”——Tokio 被明确归类为异步运行时；:9“Rust 版本: 1.97.0+ (Edition 2024) · Tokio 1.x” |
| I3-self-evident-kind | added new edge | ex:Send | ex:instanceOf | ex:AutoTrait | 03_advanced/00_concurrency/02_send_sync_auto_traits.md:3 标题“Send 与 Sync：Auto Trait 的并发安全契约”；:5 Summary“Send and Sync are auto traits that encode Rust's concurrency safety contract: `T: Send` …” |
| I3-self-evident-kind | added new edge | ex:Sync | ex:instanceOf | ex:AutoTrait | 03_advanced/00_concurrency/02_send_sync_auto_traits.md:3 标题“Send 与 Sync：Auto Trait 的并发安全契约”；:5 Summary“…and `T: Sync` is equivalent to `&T: Send`”——Sync 自述为 auto trait |
| I1-category-listed | added new edge | ex:Box | ex:instanceOf | ex:SmartPointers | 02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:37 设“1.2 Box：独占堆分配”章节——Box 被智能指针权威页列为成员 |
| I1-category-listed | added new edge | ex:Rc | ex:instanceOf | ex:SmartPointers | 02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:38 设“1.3 Rc 与 Arc：引用计数共享”章节 |
| I1-category-listed | added new edge | ex:Arc | ex:instanceOf | ex:SmartPointers | 02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:38 设“1.3 Rc 与 Arc：引用计数共享”章节 |
| I1-category-listed | added new edge | ex:Result | ex:instanceOf | ex:AlgebraicDataType | 04_formal/00_type_theory/01_type_theory.md:504“\| `Option<T>` / `Result<T, E>` \| C1: 递归类型 + ADT \|”；:121“代数数据类型（ADT）的积与余积语义是类型论的标准结论”（Pierce TAPL Ch.11）——Result 被类型论权威页归类为 ADT |
| I1-category-listed | added new edge | ex:Option | ex:instanceOf | ex:AlgebraicDataType | 04_formal/00_type_theory/01_type_theory.md:504“\| `Option<T>` / `Result<T, E>` \| C1: 递归类型 + ADT \|”；01_foundation/07_modules_and_items/05_enumerations.md:15 后置概念“Algebraic Data Types”——Option 被归类为 ADT |
| I2-category-section | added new edge | ex:VerificationToolchain | ex:instanceOf | ex:FormalVerificationFramework | 06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md:89“L4 验证扩展层 — 功能正确性证明 — Kani · Verus · Creusot”；:101 分层塔将验证工具链成员（Kani/Verus/Creusot）纳入形式化生态框架——验证工具链是形式化验证框架的组成部分 |
| A1-page-application | added new edge | ex:SerdePatterns | ex:appliesTo | ex:Serialization | 02_intermediate/00_traits/03_serde_patterns.md:2 关键术语“序列化 (Serialization) · 反序列化 (Deserialization) · serde”；:4 标题“Serde 序列化模式：Rust 的类型驱动数据转换”——serde 模式应用于序列化领域 |
| A1-page-application | added new edge | ex:KaniRustBoundedModelChecker | ex:appliesTo | ex:ModelChecking | 04_formal/04_model_checking/09_kani.md:9 Summary“Kani is an AWS-developed bounded model checker for Rust”；:60“Kani 是 AWS 开发并开源的 Rust 有界模型检查器（Bounded Model Checker）”——Kani 应用于模型检查领域 |
| A1-page-application | added new edge | ex:RustBelt_02separation | ex:appliesTo | ex:UnsafeAbstractionSoundness | 04_formal/02_separation_logic/01_rustbelt.md:118“[RustBelt: POPL 2018] … It provides a proof technique for verifying that unsafe code respects safe Rust's abstraction boundaries”——RustBelt 应用于 unsafe 抽象可靠性（soundness）证明 |

## 第一轮缺口清单 → 本轮解决对照

| 第一轮缺口 | 本轮解决 |
|:---|:---|
| ① ex:Vec / ex:HashMap → ex:Collections | 新建 2 实例节点 + 2 条 instanceOf |
| ② ex:Tokio → ex:AsyncRuntime | 新建范畴 ex:AsyncRuntime + 实例 ex:Tokio + 1 条 instanceOf |
| ③ ex:Send / ex:Sync → ex:AutoTrait | 新建范畴 ex:AutoTrait + 2 实例节点 + 2 条 instanceOf |
| ④ ex:Box / ex:Rc / ex:Arc → ex:SmartPointers | 新建 3 实例节点 + 3 条 instanceOf |
| ⑤ ex:Result / ex:Option → ex:AlgebraicDataType | 新建范畴 ex:AlgebraicDataType + 2 实例节点 + 2 条 instanceOf |
| ⑥ ex:Serialization（serde appliesTo 目标） | 新建领域节点 + ex:SerdePatterns appliesTo ex:Serialization |
| ⑦ ex:ModelChecking（kani appliesTo 目标） | 新建领域节点 + ex:KaniRustBoundedModelChecker appliesTo ex:ModelChecking |
| ⑧ ex:FormalVerificationFramework | 新建范畴节点 + ex:VerificationToolchain instanceOf ex:FormalVerificationFramework |
| ⑨ ex:UnsafeAbstractionSoundness（rustbelt appliesTo 目标） | 新建领域节点 + ex:RustBelt_02separation appliesTo ex:UnsafeAbstractionSoundness |

## 备注

- 节点结构严格对齐现有实体（K1 必填字段 + K7 layer/domain + ex:bloomLevel）；`ex:path` 均指向已确认存在的 concept/ 权威页（范畴节点允许与其实例共享权威页路径，与既有 E1 同路径双节点惯例一致）。
- `ex:layer`/`ex:domain` 按 `concept/00_meta/taxonomy.yaml` 前缀规则取值，可用 `scripts/add_kg_layer_domain.py` 复核。
- 边结构与第一轮 `scripts/type_kg_semantic_edges.py` 完全一致（`ex:evidence` 行号级引文 + `ex:rule` + `ex:reviewed`）。

## 机器可读

- JSON: `reports/KG_CATEGORY_NODES_2026-07-12.json`
