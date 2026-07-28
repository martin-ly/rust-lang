> **内容分级**: [综述级]

# PLAN_Semantic_Space_Wave.md 语义空间波浪计划 · 缺口分析与后续任务

**EN**: Semantic Space Wave Plan — Gap Analysis and Follow-up Tasks
**Summary**: 分析归档文件 `archive/01_governance/02_project_plans/PLAN_Semantic_Space_Wave.md` 的 Wave 11 目标，将其映射到当前 `concept/` 权威页，识别与国际权威内容的对称差，并输出可持续补充计划。

> **生成**: 2026-07-29
> **分析对象**: `archive/01_governance/02_project_plans/PLAN_Semantic_Space_Wave.md`（归档日期 2026-06-02）
> **当前基线**: 23 阻断质量门 + 5 语义观察门全部通过（2026-07-29）

---

## 1. Wave 11 核心目标回顾

PLAN 提出从元语言层面回答 5 个问题：

1. Rust 的表征空间（类型 + 所有权 + Trait + 宏 + unsafe + async 的设计空间）。
2. 安全 Rust 的语义封闭性（safe 子集是否封闭世界，unsafe 如何打破）。
3. 能表达 vs 不能表达的边界（哪些可高效表达、哪些痛苦、哪些被刻意排除）。
4. 等价表达的语义保持（同一概念多种 Rust 表达方式的等价性）。
5. 机制组合的语义空间（所有权×生命周期×Trait×泛型×宏×async×unsafe 的合法/非法组合）。

交付物：1 个顶层文件 `00_meta/semantic_space.md` + 增强 4 个现有文件 + 权威来源对齐。

---

## 2. 当前项目映射（已覆盖部分）

| PLAN 章节 | 目标内容 | 当前 `concept/` 权威页 | 覆盖状态 |
|:---|:---|:---|:---:|
| §1 表征空间定义 | 类型/所有权/Trait/生命周期/宏/unsafe/async 的表征能力 | `concept/00_meta/00_framework/semantic_space.md` | ✅ 完整 |
| §2 语义封闭性 | safe 封闭世界、unsafe 逃逸舱口 | `semantic_space.md` §2 · `03_advanced/02_unsafe/01_unsafe.md` · `04_formal/01_ownership_logic/01_linear_logic.md` | ✅ 完整 |
| §3 表达边界 | sweet spot / 痛苦表达 / 不能表达 | `semantic_space.md` §3 · `05_comparative/00_paradigms/05_language_semantic_model_matrix.md` | ✅ 完整 |
| §4 等价表达语义保持 | enum vs dyn Trait、Result vs 异常、GC vs 所有权等 | `semantic_space.md` §4 · `04_formal/11_computational_models/05_equivalence_of_computational_models.md` · `02_intermediate/00_traits/02_dispatch_mechanisms.md` | ✅ 完整 |
| §5 机制组合代数 | Own/Borrow/Lifetime/Trait/Generic 组合规则 | `semantic_space.md` §5 · `04_formal/00_type_theory/12_pattern_composition_algebra.md` · `04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md` | ✅ 完整 |
| §6 跨语言对比 | Rust vs C++/Haskell/Go/Java | `05_comparative/00_paradigms/01_paradigm_matrix.md` · `02_execution_model_isomorphism.md` · `05_language_semantic_model_matrix.md` | ✅ 完整 |
| §7 认知路径 | 6 步理解表征空间 | `semantic_space.md` §7 · `00_meta/04_navigation/07_learning_guide.md` | ✅ 完整 |
| 权威来源 | Felleisen / Leffler / RFC 230 / Rustonomicon / Herlihy & Shavit / Wadler | `semantic_space.md` · `00_meta/02_sources/05_international_authority_index.md` | ⚠️ 部分分散 |

### 2.1 已创建的延伸主题文件夹

当前 `concept/04_formal/` 已建立与 PLAN 对应的系统语义、算法语义、架构语义、计算模型等主题目录：

- `04_formal/08_algorithm_semantics/` — 算法语义（Hoare 逻辑、精化演算、迭代器正确性、算法等价）
- `04_formal/09_system_semantics/` — 系统语义（Actor、π 演算、组件、分布式、反应式、系统工程标准）
- `04_formal/10_architecture_semantics/` — 架构语义（软件架构形式化、模式语义、架构精化、约束）
- `04_formal/11_computational_models/` — 计算模型（计算语义框架、可计算性、形式语言与自动机、数学函数、等价性）
- `04_formal/12_concurrency_models/` — 并发模型（并发模型、表达力、并行/并发/异步/分布式语义）

这些目录在 2026-07-28 语义对齐 sprint 中已通过企业架构、系统工程、语义工程、AI 系统架构的国际权威内容进行了增强。

---

## 3. 对称差与缺口

### 3.1 已完全对齐的维度

- **表征空间总论**、**语义封闭性**、**表达边界**、**等价表达**、**机制组合**、**跨语言对比**、**认知路径**：均已在 `semantic_space.md` 及关联权威页中实现。
- **并发/并行/异步/分布式语义**：`04_formal/12_concurrency_models/` 与 `03_advanced/00_concurrency/`、`03_advanced/01_async/` 形成 L3-L4-L5 纵向覆盖。
- **系统语义**：`04_formal/09_system_semantics/` 覆盖 Actor、π 演算、组件、分布式、反应式、系统工程标准。
- **架构语义**：`04_formal/10_architecture_semantics/` 与 `06_ecosystem/14_enterprise_architecture/` 形成软件架构到企业架构的连续谱。

### 3.2 仍存在的缺口（按优先级排序）

| 优先级 | 缺口 | 说明 | 建议补全位置 |
|---:|---|---|---|
| P1 | **Felleisen 表达力理论** 缺少独立权威页 | 当前仅作为引用分散在 `semantic_space.md` 与 `paradigm_matrix.md`，未形成可独立检索的概念页 | 新建 `concept/04_formal/00_type_theory/13_expressive_power.md` |
| P2 | **观察等价性（Observational Equivalence）** 缺少独立权威页 | 在 `04_formal/11_computational_models/05_equivalence_of_computational_models.md` 与多个对比页中提及，但无系统定义 | 新建 `concept/04_formal/03_operational_semantics/06_observational_equivalence.md` 或并入 `05_equivalence_of_computational_models.md` |
| P3 | **Wadler / Theorems for Free / 参数性（Parametricity）** 缺少独立权威页 | 参数性是理解 Rust trait/泛型语义等价的关键；当前只在 `01_type_theory.md` 等页中零星出现 | 新建 `concept/04_formal/00_type_theory/09_parametricity_and_theorems_for_free.md` |
| P4 | **算法语义 ↔ 系统语义 ↔ 架构语义 的跨层映射索引** | 三个目录各自完整，但缺少一张统一的“语义分层映射表”说明算法→系统→架构的精化关系 | 增强 `concept/00_meta/00_framework/semantic_space.md` 或新建 `concept/00_meta/00_framework/semantic_layer_alignment_index.md` |
| P5 | **Green Threads / RFC 230 历史决策** 的语义影响 | 已有 `03_advanced/01_async/01_async.md` 与 `05_comparative/00_paradigms/02_execution_model_isomorphism.md` 提及，但未作为独立历史语义事件页 | 可选：在 `07_future/02_preview_features/` 或 `05_comparative/00_paradigms/` 增加历史注解页 |
| P6 | **Herlihy & Shavit 并发算法表达力** 的 Rust 投影 | `04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md` 已涉及，但缺少与 wait-free/lock-free 层次的具体映射 | 增强 `02_expressiveness_of_concurrent_models.md` |

---

## 4. 与国际权威内容的对称差

| 国际权威来源 | 当前状态 | 缺口 |
|---|---|---|
| Felleisen 1989 "On the Expressive Power of Programming Languages" | 被引用，未形成独立页 | P1 |
| Plotkin 1981 "Structural Operational Semantics" | 已在 `04_formal/03_operational_semantics/` 覆盖 | ✅ |
| Winskel "The Formal Semantics of Programming Languages" | 未显式引用 | 可在 `03_operational_semantics.md` 或 `01_computational_semantics_framework.md` 补充 |
| Herlihy & Shavit "The Art of Multiprocessor Programming" | 未显式引用 | P6 |
| Wadler 1989 "Theorems for Free!" | 未显式引用 | P3 |
| Milner π-calculus / Actor model | `04_formal/09_system_semantics/` 已覆盖 | ✅ |
| ISO/IEC/IEEE 42010 / 15288 / 12207 / 25010 | `06_ecosystem/14_enterprise_architecture/` 与 `04_formal/09_system_semantics/06_systems_engineering_standards.md` 已覆盖 | ✅ |
| NIST AI RMF / ISO 42001 / Anthropic RSP | `07_future/04_research_and_experimental/08-10` 已覆盖 | ✅ |

---

## 5. 后续可持续补充计划

### 5.1 短期（本轮可完成）

1. **P1**: 新建 `concept/04_formal/00_type_theory/13_expressive_power.md`
   - 内容：Felleisen 局部/全局变换标准、语法糖 vs 真正表达力、Rust 案例（? 运算符、Result vs 异常、Trait vs 继承）。
   - 必须包含：≥1 个 Mermaid 图、≥3 个反命题、≥1 个可编译 Rust 示例。
2. **P2**: 在 `concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md` 中新增“观察等价性”小节，或独立成页。
3. **P3**: 新建 `concept/04_formal/00_type_theory/09_parametricity_and_theorems_for_free.md`
   - 内容：参数性、自由定理、Rust 泛型/trait 的语义推论（如 `fn id<T>(x: T) -> T` 的行为约束）。

### 5.2 中期（下一轮 sprint）

1. **P4**: 创建 `concept/00_meta/00_framework/semantic_layer_alignment_index.md`
   - 一张表映射：算法语义 → 系统语义 → 架构语义 → 企业架构，说明每层精化关系与 Rust 工程映射。
2. **P5**: 增强 `04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md` 的 Herlihy & Shavit wait-free/lock-free/obstruction-free 层次，并映射到 Rust `crossbeam`、`parking_lot`、`tokio` 的实现选择。
3. **P6**: 在 `00_meta/02_sources/05_international_authority_index.md` 中补充 Winskel、Herlihy & Shavit、Wadler 的权威链接。

### 5.3 长期（季度维护）

1. 每季度复跑 `scripts/check_version_semantic_injection.py --strict` 与 `python scripts/check_cross_domain_coverage.py --strict`，确保新 Rust 版本与交叉语义域持续覆盖。
2. 每半年对 `semantic_space.md` 进行一次“对称差复核”，对照最新 PL 研究（POPL/PLDI/OOPSLA）补充表达边界案例。

---

## 6. 验收标准

- P1–P3 完成后，`python scripts/run_quality_gates.sh` 仍须 23+5 全通过。
- 新建页须满足 AGENTS.md §4.2 元数据模板、EN 标题、Summary、Bloom 层级、权威来源。
- 新建页须通过 `scripts/check_concept_authority_coverage.py --strict`（任一权威来源 100%）。
- KG 刷新：新增页后须按 AGENTS.md §7 运行 `generate_kg_index.py` → `generate_kg_v3.py` → `apply_kg_semantic_predicates.py --all-batches --apply` → `fallback_kg_generic_to_related.py --apply` → `compress_kg_relatedto.py --apply`。

---

## 7. 结论

- Wave 11 的核心交付物 `semantic_space.md` 与 5 个形式化语义主题目录已经建成并通过质量门。
- **剩余缺口集中在 3 个独立概念页**（Felleisen 表达力、观察等价性、Wadler 参数性）和 1 张跨层映射索引。
- 按 P1–P6 计划补齐后，PLAN_Semantic_Space_Wave.md 的语义空间目标可视为 100% 实现。

---

*由 Kimi Code CLI 根据 `archive/01_governance/02_project_plans/PLAN_Semantic_Space_Wave.md` 与当前 `concept/` 文件映射分析生成。*
