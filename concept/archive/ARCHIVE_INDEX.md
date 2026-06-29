> **Summary**:
>
> Archive Index. Core Rust concept.
>
# concept/archive/ 统一归档索引
>
> **EN**: Archive Index
> **受众**: [维护者]
> **内容分级**: [综述级]
> **最后更新**: 2026-06-08
> **状态**: 活跃维护
>
> **来源**: [Rust RFCs](https://github.com/rust-lang/rfcs) · [Rust Blog](https://blog.rust-lang.org/)
> **前置概念**: N/A
> **后置概念**: N/A
---

## 一、归档政策

1. **什么内容会进入本目录**
   - 已从活跃层级目录迁移出去的**重复内容**（与主文件重叠 >85%）
   - 被重构替代的旧版**层级索引**（`00.md`–`07.md`）
   - 已完成或已过时的**历史规划文件**
   - 过长、发散、不再符合当前文件层级规范的长文原稿

2. **活跃目录中不得保留的归档标记**
   - 活跃目录（`00_meta/`–`07_future/`）中不应存在标记为"已归档"的文件
   - 所有归档文件必须物理上位于 `concept/archive/`，以确保目录扫描、索引生成和死链检查的结果可预测

3. **归档不删除**
   - 本目录所有文件保留历史追溯价值，不执行物理删除
   - 如确需删除（敏感信息、法律风险），须经维护者评审并记录理由

---

## 二、归档文件分类清单

### 2.1 原根目录级索引（`concept/*.md`）

这些文件是概念体系早期的单层/根目录索引。随着 `00_meta/`–`07_future/` 子目录体系建立，它们的内容已被对应层级的 `README.md` 完全覆盖。

| 原文件 | 新归档名 | 行数 | 去向/替代 |
| :--- | :--- | :---: | :--- |
| `00.md` | `00_meta_layer_index_legacy.md` | 145 | `concept/00_meta/README.md` |
| `01.md` | `01.md` | 2,136 | `concept/05_comparative/01_rust_vs_cpp.md` |
| `02.md` | — | — | 原文件为 0 字节占位符，已直接删除 |
| `03.md` | `03_advanced_layer_index_legacy.md` | 145 | `concept/03_advanced/README.md` |
| `04.md` | `04_formal_layer_index_legacy.md` | 169 | `concept/04_formal/README.md` |
| `05.md` | `05_comparative_layer_index_legacy.md` | 168 | `concept/05_comparative/README.md` |
| `06.md` | `06_ecosystem_layer_index_legacy.md` | 147 | `concept/06_ecosystem/README.md` |
| `07.md` | `07_future_layer_index_legacy.md` | 202 | `concept/07_future/README.md` |

### 2.2 活跃层级中的重复/被替代文件

这些文件在活跃目录中仍保留编号，但内容已声明"已归档"（与主文件重叠 >85%）。Phase 3 瘦身将其物理迁移至 `archive/` 以释放编号并消除索引歧义。

| 原文件 | 新归档名 | 行数 | 主文件/整合去向 | 归档日期 |
| :--- | :--- | :---: | :--- | :--- |
| `01_foundation/19_numerics.md` | `01_foundation_19_numerics_archived.md` | ~95 | `01_foundation/10_numerics.md` | 2026-06-08 |
| `02_intermediate/22_iterator_patterns.md` | `02_intermediate_22_iterator_patterns_archived.md` | ~105 | `02_intermediate/15_iterator_patterns.md` | 2026-06-08 |
| `04_formal/07_separation_logic.md` | `04_formal_07_separation_logic_archived.md` | ~105 | `04_formal/11_separation_logic.md` | 2026-05-25 → 2026-06-08 |
| `04_formal/09_operational_semantics.md` | `04_formal_09_operational_semantics_archived.md` | ~105 | `04_formal/17_operational_semantics.md` | 2026-05-25 → 2026-06-08 |
| `05_comparative/16_rust_vs_ruby.md` | `05_comparative_16_rust_vs_ruby_archived.md` | ~100 | `05_comparative/08_rust_vs_ruby.md` | 2026-06-08 |
| `06_ecosystem/33_idioms_spectrum.md` | `06_ecosystem_33_idioms_spectrum_archived.md` | ~108 | `06_ecosystem/03_idioms_spectrum.md` | 2026-06-08 |
| `06_ecosystem/34_formal_ecosystem_tower.md` | `06_ecosystem_34_formal_ecosystem_tower_archived.md` | ~108 | `06_ecosystem/05_formal_ecosystem_tower.md` | 2026-06-08 |
| `03_advanced/02_async_programming.md` | `03_advanced_02_async_programming_archived.md` | ~30 | `03_advanced/02_async.md` + `02_async_patterns.md` | 2026-06-08 |
| `03_advanced/03_unsafe_rust.md` | `03_advanced_03_unsafe_rust_archived.md` | ~45 | `03_advanced/03_unsafe.md` | 2026-06-08 |
| `03_advanced/05_macros.md` | `03_advanced_05_macros_archived.md` | ~45 | `03_advanced/04_macros.md` + `07_proc_macro.md` | 2026-06-08 |
| `03_advanced/08_zero_cost_abstractions.md` | `03_advanced_08_zero_cost_abstractions_archived.md` | ~45 | `01_foundation/06_zero_cost_abstractions.md` | 2026-06-08 |
| `03_advanced/13_async_patterns.md` | `03_advanced_13_async_patterns_archived.md` | ~45 | `03_advanced/02_async_patterns.md` | 2026-06-08 |
| `01_foundation/03_lifetimes_original.md` | `01_foundation_03_lifetimes_original.md` | ~2,300 | `01_foundation/03_lifetimes.md`（精简重构版） | 2026-05-30 |
| `01_foundation/11_numeric_types_deprecated.md` | `01_foundation_11_numeric_types_deprecated.md` | ~400 | `01_foundation/11_numeric_types.md` | 2026-05-30 |
| `03_advanced/02_async_original.md` | `03_advanced_02_async_original.md` | ~3,600 | `03_advanced/02_async.md`（精简重构版） | 2026-05-30 |
| `06_ecosystem/26_game_development_deprecated.md` | `06_ecosystem_26_game_development_deprecated.md` | ~340 | 内容已分散至 `06_ecosystem/35_*`、`06_ecosystem/36_*` 等相关生态文件 | 2026-05-30 |
| `07_future/23_rust_edition_guide_deprecated.md` | `07_future_23_rust_edition_guide_deprecated.md` | ~300 | `07_future/05_rust_version_tracking.md` | 2026-05-30 |

### 2.3 Rust Effect System 根目录级长文

这些文件最初位于 `concept/` 根目录，是对 Rust Effect System 的百科全书级分析。内容已被结构化整合进 `07_future/04_effects_system.md`。

| 原文件 | 新归档名 | 行数 | 整合去向 |
| :--- | :--- | :---: | :--- |
| `rust_effect_system_encyclopedia.md` | `rust_effect_system_encyclopedia.md` | 1,848 | `concept/07_future/04_effects_system.md` v1.3+ |
| `rust_effect_system_comprehensive_analysis.md` | `rust_effect_system_comprehensive_analysis.md` | 416 | `concept/07_future/04_effects_system.md` v1.3+ |
| `rust_effect_system_deepened_broadened_analysis.md` | `rust_effect_system_deepened_broadened_analysis.md` | 596 | `concept/07_future/04_effects_system.md` v1.3+ |
| `rust_effect_system_boundary_analysis.md` | `rust_effect_system_boundary_analysis.md` | 282 | `concept/07_future/04_effects_system.md` v1.3+ |
| `Rust vs C++：形式系统模型 vs 机制工程模型 —— 核心论点索引.md` | 同名 | 145,926 | 结构化版本见 `05_comparative/01_rust_vs_cpp.md` |

### 2.4 历史规划文件

| 原文件 | 新归档名 | 行数 | 说明 |
| :--- | :--- | :---: | :--- |
| `concept/PLAN.md` | `PLAN_concept_knowledge_system_v2.md` | 618 | 2026-05-12 创建，Phase 19 已完成，规划内容已落地 |
| `concept/PLAN_Semantic_Space_Wave.md` | `PLAN_semantic_space_wave_11.md` | ~460 | Wave 11 语义空间梳理计划，产出已分散至 `00_meta/semantic_space.md` 等文件 |
| `concept/SUMMARY.md` | `SUMMARY_mdbook_legacy.md` | 269 | 旧版 mdBook 风格总目录，结构已过时，未被 mdBook 流程使用 |

---

## 三、跨文件引用维护

### 已修复的活跃引用

- `concept/README.md` 中 "详见 PLAN.md" → 指向 `archive/PLAN_concept_knowledge_system_v2.md`
- `concept/00_meta/inter_layer_topology.md` 中 PLAN.md 链接 → 指向 `archive/PLAN_concept_knowledge_system_v2.md`
- `concept/06_ecosystem/05_formal_ecosystem_tower.md` 变更日志中的 stray `$entry` 字符已清除

### 不需要修复的引用

- 归档文件内部之间的相互引用（Reference）（例如 `SUMMARY_mdbook_legacy.md` 中的 `00.md`、`PLAN.md` 链接）保留原样，因为它们描述的是归档时的原始目录结构
- 活跃文件中对 "原 01.md"、"旧 SUMMARY.md" 等名词性提及（非超链接）保留原样，作为历史说明

---

## 四、统计

| 类别 | 数量 |
| :--- | :--- |
| 根级索引归档/删除 | 8（6 归档 + 1 原 01.md 归档 + 1 0 字节占位符 02.md 删除） |
| 活跃层级重复文件迁移 | 12 |
| Effect System 长文归档 | 5 |
| 其他历史长文归档 | 5（3 原始长文 + 4 规划/目录文件） |
| **总计** | **~27 个历史文件已归集** |

---

> **维护提示**: 本索引应随每次归档操作同步更新。新增归档文件时，请补充到对应分类表格中，并更新"最后更新"日期。

## 嵌入式测验（Embedded Quiz）

### 测验 1：《concept/archive/ 统一归档索引》在本知识体系中扮演什么角色？（理解层）

**题目**: 《concept/archive/ 统一归档索引》在本知识体系中扮演什么角色？

<details>
<summary>✅ 答案与解析</summary>

作为导航和索引文档，帮助学习者快速定位内容、理解知识结构关系，是进入各层内容的入口和路线图。
</details>

---

### 测验 2：使用本索引文件时，最有效的学习策略是什么？（理解层）

**题目**: 使用本索引文件时，最有效的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先浏览整体结构建立全局视野，然后根据自身水平选择对应层级，遇到模糊概念时利用交叉引用（Reference）跳转复习。
</details>

---

### 测验 3：索引文档能否替代具体概念文件的学习？（理解层）

**题目**: 索引文档能否替代具体概念文件的学习？

<details>
<summary>✅ 答案与解析</summary>

不能。索引提供的是结构框架和导航，深入理解需要通过阅读具体概念文件、完成测验和实践练习来实现。
</details>
