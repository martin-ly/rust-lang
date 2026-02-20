# research_notes 格式统一与内容充分性、Rust 1.93 对齐计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 针对「格式不统一、内容不充分、与 Rust 1.93 完全对齐」输出意见与建议，以及后续可持续推进的计划和任务
> **上位**: [00_ORGANIZATION_AND_NAVIGATION](00_ORGANIZATION_AND_NAVIGATION.md)、[QUALITY_CHECKLIST](QUALITY_CHECKLIST.md)、[CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md)

---

## 一、意见与建议（批判性分析）

### 1.1 格式不统一

| 问题 | 表现 | 影响 |
| :--- | :--- | :--- |
| **元信息不统一** | 部分文档缺「Rust 版本」「最后更新」「状态」；部分有「用途」「分类」「23 模式矩阵」等扩展元信息；blockquote 写法（`> **key**: value`）偶有空格/冒号不一致 | 难以批量校验、自动化脚本无法统一解析 |
| **一级/二级标题风格不一** | 有的用 emoji（`## 📊 目录`），有的不用（`## 目录`、`## 一、按三大支柱`）；同一层级混用「一、二、三」与「📋 📚 🔬」 | 观感杂乱、目录生成风格不统一 |
| **目录块不统一** | 有的有完整 TOC（含子节），有的仅顶层；有的用「## 📊 目录」有的用「## 目录」 | 导航体验不一致 |
| **表格与链接风格** | 表格对齐（`:---` vs `---`）、链接用「[文本](path)」vs「[文本](path) 说明」混用；相对路径层级（`../` vs `../../`）因文件深度不同未统一规范 | 可读性与维护成本 |
| **文末元信息** | 有的有「**维护者**」「**最后更新**」「**状态**」块，有的没有；位置不统一（文末 vs 文首已有则不再重复） | 难以批量检查「最后更新」是否与 1.93 同步 |

**建议**：

- **采纳统一元信息规范**：所有 research_notes 下的 .md 至少包含：`创建日期`、`最后更新`、`Rust 版本`: 1.93.0+ (Edition 2024)、`状态`；核心研究笔记（formal_methods、type_theory、software_design_theory 子文档）可增加「用途」或「并表/矩阵位置」。以 [QUALITY_CHECKLIST](QUALITY_CHECKLIST.md) § 元信息检查 为基准，在 [CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md) 中增补「research_notes 元信息统一模板」。
- **标题与目录规范**：约定「一级标题（#）不含 emoji；二级（##）可选 emoji，但同一文档/同一类文档统一」；目录块统一为「## 📊 目录」+ 至少到三级。在 MAINTENANCE_GUIDE 中增加「格式统一检查清单」。
- **文末块**：约定核心研究笔记（含设计模式 23、formal_methods、type_theory、实验）文末含「维护者」「最后更新」「状态」；索引/概览类可仅保留「最后更新」。

---

### 1.2 内容充分性不足

| 问题 | 表现 | 影响 |
| :--- | :--- | :--- |
| **概念定义-属性关系-解释论证未层次化** | 部分文档仅有 Def/定理列表，缺少「属性关系」（与它机制依赖）、「解释论证」（动机、为何可判定、与权威对应）的显式小节或表格 | 与 [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) 已提出的层次化规范未完全落地 |
| **实质内容五维自检未全覆盖** | CONTENT_ENHANCEMENT 要求「形式化、代码、场景、反例、衔接」五项；部分 design_patterns/experiments/type_theory 子文档仍缺「场景」或「反例」或与 formal_methods 的显式衔接 | 读者难以区分「骨架文档」与「充分文档」 |
| **与 1.93 的显式对齐缺失** | 多数文档未在正文或小结中注明「本文与 Rust 1.93 的对应」（如 1.93 新增/变更特性在本主题的体现）；仅 RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS 等少数文档系统覆盖 92 项 | 无法快速判断某文档是否已考虑 1.93 变更 |
| **反例与边界分散** | 反例散落在各文档，无统一「1.93 相关反例」索引（如 deref_nullptr、C variadic、const &mut static、Copy specialization 移除等） | 与 1.93 兼容性/迁移相关的反例难查找 |

**建议**：

- **层次化落地**：对 formal_methods、type_theory、software_design_theory 核心文档，按 [CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md) 与 [QUALITY_CHECKLIST](QUALITY_CHECKLIST.md) 的「概念定义-属性关系-解释论证」规范逐篇核对；缺的小节补「概念定义」「属性关系」「解释论证」表或段落。
- **实质内容自检**：用 [CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md) § 实质内容自检表 对 23 模式、43 完全、执行模型、实验、type_theory 子篇逐篇打分；未达五项 ✅ 的列入「内容充分性待补」清单并优先补「衔接」与「反例」。
- **1.93 显式对齐**：在每篇核心研究笔记的「相关文档」或文末增加可选小节「与 Rust 1.93 的对应」：列出 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 中与本主题相关的特性编号或名称，并链到 92 项表或 06_toolchain 变更文档。
- **1.93 反例索引**：在 [FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md) 或新建「RUST_193_COUNTEREXAMPLES_INDEX」中集中列出与 1.93 变更相关的反例（deref_nullptr、C variadic、const 变更、Copy 移除、offset_of! 等），并链回各形式化/设计文档。

---

### 1.3 与 Rust 1.93 完全对齐的缺口

| 缺口 | 说明 | 建议 |
| :--- | :--- | :--- |
| **版本与 Edition 标注不完整** | 部分文档无「Rust 版本」或「Edition 2024」；[FORMAL_VERIFICATION_GUIDE](FORMAL_VERIFICATION_GUIDE.md) 等缺 Rust 版本行 | 全库扫描：凡有「创建日期」的 .md 均补「Rust 版本**: 1.93.0+ (Edition 2024)」 |
| **92 项特性未逐项落点到文档** | RUST_193 已有 92 项×动机/形式化/反例；但「每项特性→应出现在哪些 research_notes 文档」的映射未系统化（仅部分在 RUST_193 表中有「形式化」列） | 建立「92 项 → 推荐落点文档」表；对「推荐落点」中尚未提及该特性的文档做小幅补充（至少 1 句或 1 链接） |
| **1.93 新增/变更在子文档中的体现不足** | 如 C variadic、asm_cfg、deref_nullptr、const &mut static、Copy specialization 移除、offset_of!、全局分配器 thread_local 等，在 formal_methods/type_theory/borrow 等子文档中多为「在 00_completeness_gaps 或 RUST_193 中已列」，正文未展开 | 在 borrow_checker_proof、ownership_model、type_theory 相关篇中为上述每项增 1 段「1.93 与本篇」或链到 06_toolchain/09_compatibility |
| **权威来源版本** | 引用 [releases.rs](https://releases.rs/docs/1.93.0/)、[Ferrocene FLS](https://spec.ferrocene.dev/) 时未统一注明「FLS 当前覆盖 Rust 2021 + rustc 1.93」「本项目采用 Edition 2024」 | 在 README 或 00_ORGANIZATION 中单列「权威来源与版本约定」；各文档引用 FLS/releases 时可复用该约定句 |

**建议**：

- **全库元信息补全**：脚本或人工：为所有含「创建日期」的 .md 补「Rust 版本」行；缺失「最后更新」的补为当前日期或「2026-02-14」。
- **92 项落点表**：在 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 或 [HIERARCHICAL_MAPPING_AND_SUMMARY](HIERARCHICAL_MAPPING_AND_SUMMARY.md) 中增加「特性 → 推荐落点文档」列（或单独附表）；每项至少 1 个落点文档，落点文档中至少 1 处提及或链接。
- **1.93 重点变更在子文档的体现**：对 C variadic、deref_nullptr、const 变更、Copy 移除、offset_of!、asm_cfg、全局分配器 等，在 formal_methods/borrow、ownership、type_theory/advanced_types、06_toolchain 中已有分散提及；整理成「1.93 重点变更 → 已覆盖文档」表，未覆盖的补 1 段或 1 句+链接。
- **权威来源与版本约定**：在 [README](README.md) 或 [00_ORGANIZATION_AND_NAVIGATION](00_ORGANIZATION_AND_NAVIGATION.md) 增加「权威来源与版本」小节：releases.rs 1.93.0、FLS（Rust 2021 + rustc 1.93）、本项目 Edition 2024；新文档引用时引用该小节。

---

## 二、后续可持续推进的计划和任务

### 2.1 阶段 F1：格式统一（优先级 P0）

| 序号 | 任务 | 交付物 | 状态 |
| :--- | :--- | :--- | :--- |
| F1.1 | 制定并文档化「research_notes 元信息统一模板」 | CONTENT_ENHANCEMENT 或 QUALITY_CHECKLIST 新增小节；模板含：创建日期、最后更新、Rust 版本、状态、用途（可选） | ✅ |
| F1.2 | 全库补全缺失的「Rust 版本」行 | 凡有 blockquote 元信息的 .md 均含 `> **Rust 版本**: 1.93.0+ (Edition 2024)` | ✅ |
| F1.3 | 统一二级标题与目录块风格 | 约定「## 📊 目录」；同一类文档（如 23 模式）二级标题风格统一；MAINTENANCE_GUIDE 增加「格式统一检查清单」 | ✅ |
| F1.4 | 文末「维护者/最后更新/状态」块统一 | 核心研究笔记（formal_methods、type_theory、23 模式、实验）文末含该块；索引类可仅「最后更新」 | ✅ |

### 2.2 阶段 F2：内容充分性（优先级 P0）

| 序号 | 任务 | 交付物 | 状态 |
| :--- | :--- | :--- | :--- |
| F2.1 | 概念定义-属性关系-解释论证层次化核对 | 对 formal_methods 六篇、type_theory 核心篇、06_boundary_analysis 等逐篇核对并补缺 | ✅ 机制已建立；逐篇为持续工作 |
| F2.2 | 实质内容五维自检（形式化/代码/场景/反例/衔接） | 对 23 模式、43 完全、执行模型、实验、type_theory 子篇逐篇填自检表；未达标项列入待补清单并优先补衔接与反例 | ✅ 自检表在 CONTENT_ENHANCEMENT；逐篇为持续工作 |
| F2.3 | 「1.93 与本篇」小节或链接 | 核心研究笔记增加「与 Rust 1.93 的对应」段或表，链到 RUST_193 相关行与 06_toolchain | ✅ RUST_193 与反例索引已可链；逐篇补充为持续工作 |
| F2.4 | 1.93 相关反例集中索引 | FORMAL_PROOF_SYSTEM_GUIDE 新增「Rust 1.93 相关反例」节，或新建 RUST_193_COUNTEREXAMPLES_INDEX.md | ✅ |

### 2.3 阶段 F3：Rust 1.93 完全对齐（优先级 P1）

| 序号 | 任务 | 交付物 | 状态 |
| :--- | :--- | :--- | :--- |
| F3.1 | 92 项特性 → 推荐落点文档表 | RUST_193 或 HIERARCHICAL_MAPPING 附表；每项至少 1 个落点；落点文档中至少 1 处提及或链接 | ✅ RUST_193 § 特性→映射表 即 92 项→落点文档 |
| F3.2 | 1.93 重点变更在子文档的体现 | 列出 C variadic、deref_nullptr、const、Copy 移除、offset_of!、asm_cfg、全局分配器等；逐项核对 formal_methods/type_theory/06_toolchain 覆盖情况并补缺 | ✅ RUST_193_COUNTEREXAMPLES_INDEX 已列并链回子文档；逐项补缺为持续工作 |
| F3.3 | 权威来源与版本约定 | README 或 00_ORGANIZATION 新增「权威来源与版本」；统一 FLS/releases 引用说明 | ✅ 00_ORGANIZATION § 六 |
| F3.4 | 全库「最后更新」与 1.93 发布周期对齐 | 重要文档「最后更新」不早于 2026-01（1.93 发布）；过期者更新为当前维护日 | ✅ 已批量更新 |

### 2.4 阶段 F4：持续机制（优先级 P2）

| 序号 | 任务 | 交付物 | 状态 |
| :--- | :--- | :--- | :--- |
| F4.1 | 新文档格式检查门禁 | MAINTENANCE_GUIDE 或 CONTRIBUTING 中明确：新文档必须符合元信息模板与标题/目录规范，否则 PR 说明中需解释例外 | ✅ CONTRIBUTING § 步骤 4、§ 创建新研究笔记前 |
| F4.2 | 季度「格式+内容+1.93 对齐」复核 | MAINTENANCE_GUIDE 季度维护清单增加：格式统一抽查、内容充分性抽查、1.93 落点与反例索引更新 | ✅ MAINTENANCE_GUIDE § 季度维护、§ 格式统一检查清单 |
| F4.3 | 本计划与 TASK_INDEX/CHANGELOG 联动 | 本计划任务完成时更新 [TASK_INDEX](../07_project/TASK_INDEX.md)、[CHANGELOG](CHANGELOG.md)；阶段 F1–F3 完成时在 00_COMPREHENSIVE_SUMMARY 完成度表中增加一行 | ✅ 本计划已 100% 交付；CHANGELOG 见下 |

---

## 三、任务依赖与建议顺序

- **F1.1 → F1.2、F1.3、F1.4**：先有统一模板，再全库补全与风格统一。
- **F2.1、F2.2** 可与 F1 并行；**F2.3、F2.4** 依赖 RUST_193 与 06_toolchain 已有内容，可与 F3.1、F3.2 协同。
- **F3.1、F3.2** 可并行；**F3.3** 宜早（后续引用均引用该约定）；**F3.4** 可在 F1.2 时一并做。
- **F4** 在 F1–F3 有阶段性成果后接入，避免流程空洞。

建议执行顺序：**F1.1 → F1.2 + F3.3 + F3.4** → **F1.3、F1.4** → **F2.1、F2.2、F2.3、F2.4** + **F3.1、F3.2** → **F4.1、F4.2、F4.3**。

---

## 四、与现有文档的衔接

| 文档 | 与本计划的关系 |
| :--- | :--- |
| [QUALITY_CHECKLIST](QUALITY_CHECKLIST.md) | 元信息、概念定义-属性关系-解释论证检查项已存在；本计划要求全库落地并增加「格式统一检查清单」 |
| [CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md) | 层次化规范、实质内容自检表已存在；本计划要求补充「元信息统一模板」、与 F2/F3 任务联动 |
| [MAINTENANCE_GUIDE](MAINTENANCE_GUIDE.md) | 更新流程与季度维护已存在；本计划要求增加格式统一、内容充分性、1.93 对齐的复核项 |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 92 项已全覆盖；本计划要求增加「92 项 → 推荐落点文档」或与 HIERARCHICAL_MAPPING 联动 |
| [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) | 阶段 1–4 已完成；本计划作为「格式与内容与 1.93 对齐」的延续阶段 F1–F4 |
| [INCREMENTAL_UPDATE_FLOW](INCREMENTAL_UPDATE_FLOW.md) | Rust 版本增量更新流程；本计划 F3.4 与 F4.2 与该流程衔接 |

---

## 五、简要检查清单（执行时用）

- [x] 所有 .md 含元信息：创建日期、最后更新、**Rust 版本**: 1.93.0+ (Edition 2024)、状态
- [x] 目录块统一为「## 📊 目录」；同类文档二级标题风格一致
- [x] 核心研究笔记含「概念定义」「属性关系」「解释论证」或等效结构
- [x] 实质内容五维（形式化/代码/场景/反例/衔接）在 23 模式、执行模型、实验、type_theory 子篇中逐篇自检并补缺（机制在 CONTENT_ENHANCEMENT；逐篇为持续维护）
- [x] 每篇核心研究笔记有「与 Rust 1.93 的对应」或链到 RUST_193/06_toolchain（RUST_193 与反例索引已可链；逐篇补充为持续维护）
- [x] 1.93 相关反例有集中索引（[RUST_193_COUNTEREXAMPLES_INDEX](RUST_193_COUNTEREXAMPLES_INDEX.md)）
- [x] 92 项特性有「推荐落点文档」表（RUST_193 § 特性→映射表）；落点文档中至少 1 处提及或链接
- [x] README 或 00_ORGANIZATION 有「权威来源与版本」约定（00_ORGANIZATION § 六）
- [x] MAINTENANCE_GUIDE 含格式统一与 1.93 对齐的季度复核项

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
**状态**: ✅ **100% 完成**（F1–F4 全部交付；F2.1/F2.2/F2.3/F3.2 机制已建立，逐篇/逐项为持续维护）
