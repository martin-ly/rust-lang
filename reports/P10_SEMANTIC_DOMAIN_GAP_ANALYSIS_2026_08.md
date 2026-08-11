# P10 语义领域盘点与对称差分析报告

**EN**: P10 Semantic Domain Inventory and Symmetric-Difference Gap Analysis Report
**Summary**: Systematic inventory of `concept/` pages across 14 semantic domains, comparison against international authority sources, and a prioritized gap list for P10 no_std/embedded, idioms/patterns/architecture, formal methods, and RAG production.

> **日期**: 2026-08-11
> **Rust 版本**: 1.97.1+ (Edition 2024)
> **Bloom 层级**: L0
> **范围**: `concept/**/*.md`（824 页，排除 00_meta/stub/quiz/SUMMARY/sources）
> **工具**: `scripts/semantic_domain_inventory.py`
> **前置输入**:
>
> - `reports/PLAN_P10_Semantic_Domain_International_Alignment_2026_08_04.md`
> - `concept/00_meta/02_sources/06_external_authority_topic_index.md`
> - `concept/00_meta/02_sources/04_topic_authority_alignment_map.md`
> - `concept/00_meta/02_sources/05_international_authority_index.md`

---

## 1. 执行摘要

本轮 P10-1 对 `concept/` 全部 **824** 个 Markdown 页面进行了语义领域自动分类、元数据抽取、国际权威来源扫描和预期主题覆盖对比。

- **语义领域**: 14 个（所有权/借用/生命周期、类型系统、Trait、泛型、宏、并发/异步、Unsafe/FFI、嵌入式/no_std、错误处理、性能/零成本抽象、形式方法、生态/工具链、企业架构、元数据/导航/RAG）。
- **国际权威来源类别**: 8 类（官方文档、形式化/验证工具、嵌入式/安全关键、工业生态库、设计模式/性能/惯用法、学术论文、标准/企业架构、社区博客/演讲）。
- **预期主题清单**: 49 项（P10 优先级缺口 + 核心域基线）。
- **总体覆盖**: 46/49 = **93.9%**。
- **剩余缺口**: **3** 项，全部集中在 **RAG 生产化工件**（`tools/kg_rag/`），不属于 `concept/` 页面范畴。
- **思维表征健康度**: 13/14 个领域预期覆盖率达到 100%；多数领域 mindmap 覆盖率 ≥ 90%，反例节覆盖率 ≥ 70%。
- **代码块新鲜度**: `scripts/check_concept_code_blocks.py --strict --sample 0` 通过，candidate 3050/3050 pass，compile_fail 1156/1156 ok，无标注腐烂。

> **核心结论**: 与 P10 计划相比，`concept/` 层面的 P10-2（no_std/嵌入式）、P10-3（惯用法/模式/架构）、P10-4（计算语义模型）目标页已经存在，部分为待填充内容的骨架页；真正的剩余缺口在 **P10-5 RAG 生产化** 的工具/数据侧（golden query set、embedding 微调流水线、reranker/hybrid search）。

---

## 2. 语义领域 - 国际权威来源矩阵

下表由 `scripts/semantic_domain_inventory.py` 根据 2026-08-11 快照自动生成，完整矩阵见 [`concept/00_meta/05_ai_semantic_engineering/04_semantic_domain_alignment_matrix.md`](../../concept/00_meta/05_ai_semantic_engineering/04_semantic_domain_alignment_matrix.md)。

| 语义领域 | 页数 | mindmap% | 代码块% | 反例% | 决策树% | 对齐来源类别数 | 预期覆盖% | 主要来源类别 |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| 所有权 / 借用 / 生命周期 | 8 | 100% | 100% | 75% | 50% | 6 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 社区博客 / 演讲, 工业生态库, 设计模式 / 性能 / 惯用法 |
| 类型系统 | 36 | 100% | 97% | 53% | 56% | 8 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 设计模式 / 性能 / 惯用法, 工业生态库, 标准 / 企业架构, 嵌入式 / 安全关键, 社区博客 / 演讲 |
| Trait 系统 | 9 | 100% | 100% | 56% | 44% | 7 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 嵌入式 / 安全关键, 标准 / 企业架构, 社区博客 / 演讲 |
| 泛型 | 4 | 100% | 100% | 100% | 25% | 5 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 设计模式 / 性能 / 惯用法 |
| 宏与元编程 | 19 | 95% | 89% | 58% | 32% | 7 | 100.0% | 官方文档, 学术论文, 工业生态库, 社区博客 / 演讲, 形式化 / 验证工具, 设计模式 / 性能 / 惯用法, 标准 / 企业架构 |
| 并发 / 异步 / 并行 | 30 | 100% | 100% | 57% | 33% | 8 | 100.0% | 官方文档, 工业生态库, 学术论文, 形式化 / 验证工具, 设计模式 / 性能 / 惯用法, 嵌入式 / 安全关键, 标准 / 企业架构, 社区博客 / 演讲 |
| Unsafe / FFI / 底层 | 30 | 97% | 93% | 87% | 33% | 8 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 嵌入式 / 安全关键, 标准 / 企业架构, 设计模式 / 性能 / 惯用法, 社区博客 / 演讲 |
| 嵌入式 / no_std / 裸机 | 58 | 97% | 97% | 84% | 59% | 8 | 100.0% | 嵌入式 / 安全关键, 官方文档, 学术论文, 工业生态库, 标准 / 企业架构, 形式化 / 验证工具, 设计模式 / 性能 / 惯用法, 社区博客 / 演讲 |
| 错误处理 | 8 | 100% | 100% | 62% | 38% | 5 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 设计模式 / 性能 / 惯用法 |
| 性能 / 零成本抽象 | 28 | 96% | 96% | 82% | 82% | 7 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 设计模式 / 性能 / 惯用法, 标准 / 企业架构, 社区博客 / 演讲 |
| 形式方法 / 计算语义模型 | 145 | 94% | 90% | 72% | 31% | 8 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 标准 / 企业架构, 社区博客 / 演讲, 嵌入式 / 安全关键, 设计模式 / 性能 / 惯用法 |
| 生态 / 工具链 / 惯用法 | 212 | 96% | 89% | 76% | 48% | 8 | 100.0% | 官方文档, 学术论文, 形式化 / 验证工具, 工业生态库, 设计模式 / 性能 / 惯用法, 标准 / 企业架构, 社区博客 / 演讲, 嵌入式 / 安全关键 |
| 企业架构 / 标准 | 18 | 89% | 78% | 83% | 61% | 8 | 100.0% | 官方文档, 工业生态库, 学术论文, 标准 / 企业架构, 形式化 / 验证工具, 设计模式 / 性能 / 惯用法, 社区博客 / 演讲, 嵌入式 / 安全关键 |
| 元数据 / 导航 / RAG | 219 | 58% | 59% | 35% | 35% | 8 | 0.0% | 官方文档, 形式化 / 验证工具, 工业生态库, 学术论文, 嵌入式 / 安全关键, 标准 / 企业架构, 社区博客 / 演讲, 设计模式 / 性能 / 惯用法 |

> **矩阵完成度**: 矩阵覆盖 824/824 = **100%** `concept/` 内容页，每个领域至少对齐 2 个国际权威来源类别，满足 P10-1 完成标准。

---

## 3. 分领域盘点详情

对每个领域列出：**已有权威页**（代表性文件）、**缺失主题**、**陈旧引用/术语漂移风险**、**行动项**。

### 3.1 所有权 / 借用 / 生命周期

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` · `02_borrowing.md` · `03_lifetimes.md` · `04_lifetimes_advanced.md` · `05_move_semantics.md` |
| 缺失主题 | 无显著概念缺口；NLL/Polonius 已有 `03_advanced/02_unsafe/03_nll_and_polonius.md` |
| 陈旧引用 | `reference/lifetimes.html` 旧锚点已在本轮审计前修复；当前使用 `lifetime-elision.html` |
| 术语漂移风险 | `object safety` → `dyn compatibility` 已在前序轮次修复；需持续监控 `move semantics` 与 Rust Reference 的 `moved value` 表述一致性 |
| 行动项 | P2：季度复核旧锚点残留 |

### 3.2 类型系统

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/01_foundation/02_type_system/01_type_system.md` · `02_never_type.md` · `03_numerics.md` · `04_coercion_and_casting.md` · `02_intermediate/04_types_and_conversions/` 全系列 |
| 缺失主题 | 类型布局（type layout）由 `04_formal/05_rustc_internals/08_type_layout.md` 覆盖；f16/f128 预览在 `07_future/02_preview_features/35_f16_f128_preview.md` |
| 陈旧引用 | `04_coercion_and_casting.md` 需确认是否已对齐 Edition 2024 的 `dyn` 强制规则 |
| 术语漂移风险 | `unsized type` / `dynamically sized type (DST)` 在不同来源中命名差异；项目内已统一为 `DST` |
| 行动项 | P2：Edition 2024 类型强制/子类型变化复核 |

### 3.3 Trait 系统

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/02_intermediate/00_traits/01_traits.md` · `02_dispatch_mechanisms.md` · `04_advanced_traits.md` · `07_generic_associated_types.md` · `08_negative_impls.md` |
| 缺失主题 | 无 P0 缺口；特殊类型与 trait 细节见 `04_formal/05_rustc_internals/07_special_types_and_traits.md` |
| 陈旧引用 | RFC 255 object safety 链接有效；需跟踪 `dyn compatibility` 术语在官方文档中的最终落地 |
| 术语漂移风险 | `object safety` → `dyn compatibility` 已修复；`impl Trait` 在 return position / type alias 的精确捕获（precise capturing）需随 1.98 更新 |
| 行动项 | P2：1.98.0 stable 发布后复核 `RPITIT` / `TAIT` / precise capturing 术语 |

### 3.4 泛型

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/02_intermediate/01_generics/01_generics.md` · `02_const_generics.md` · `03_type_level_programming.md` · `05_const_generics_and_trait_objects.md` |
| 缺失主题 | 无显著缺口；泛型与 trait object 交叉覆盖完整 |
| 陈旧引用 | const generics 依赖 `min_const_generics` / `adt_const_params` 等 feature 名称需随 stable 更新 |
| 术语漂移风险 | `generic associated types (GATs)` 在 std docs 中已稳定使用，无需漂移修正 |
| 行动项 | P3：1.98.0 后清理仍标记为 nightly 的 const generics 示例 |

### 3.5 宏与元编程

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/01_foundation/09_macros_basics/01_attributes_and_macros.md` · `02_intermediate/06_macros_and_metaprogramming/` 全系列 · `03_advanced/03_proc_macros/` 全系列 |
| 缺失主题 | 宏卫生（hygiene）已有 `09_macro_hygiene.md`；条件编译已有 `11_conditional_compilation.md` |
| 陈旧引用 | `proc_macro` API 文档链接基本有效；`syn`/`quote` 版本号需随 crate 更新 |
| 术语漂移风险 | `declarative macros` / `macro_rules!` 命名统一；`procedural macros` 下 derive/attribute/function-like 分类统一 |
| 行动项 | P2：复核 `03_advanced/03_proc_macros/08_syn_quote_reference.md` 中 `syn` 2.x API 链接 |

### 3.6 并发 / 异步 / 并行

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/03_advanced/00_concurrency/` 全系列 · `03_advanced/01_async/` 全系列 |
| 缺失主题 | 无 P0 缺口；Send/Sync 边界、async+unsafe、Pin projection 等交叉域均已覆盖 |
| 陈旧引用 | Async Book 中 `pin.html` 旧链接已不存在；`03_advanced/01_async/08_pin_unpin.md` 已改用 `std::pin` 模块页 |
| 术语漂移风险 | `Pin` / `Unpin` / `pin projection` 官方文档结构变化较大；需持续对齐 `std::pin` 模块页 |
| 行动项 | P2：持续跟踪 `std::pin` 锚点变化 |

### 3.7 Unsafe / FFI / 底层

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/03_advanced/02_unsafe/` 全系列 · `03_advanced/04_ffi/` 全系列 · `03_advanced/05_inline_assembly/` · `03_advanced/06_low_level_patterns/` |
| 缺失主题 | 无 P0 缺口；unsafe extern blocks (Edition 2024) 已有 `03_advanced/04_ffi/05_unsafe_extern_blocks.md` |
| 陈旧引用 | 裸 `crates.io/` 链接已在本轮审计前修复 |
| 术语漂移风险 | `unsafe op in unsafe fn` (RFC 2585) 已落地；`unsafe attributes` / `unsafe extern` (Edition 2024) 需稳定后更新为正式表述 |
| 行动项 | P2：复核 unsafe 页中工业生态库链接的精确目标页 |

### 3.8 嵌入式 / no_std / 裸机

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/06_ecosystem/05_systems_and_embedded/` 全系列（58 页），覆盖 Embassy、RTIC、probe-rs、linker script、no_std allocators、Rust for Linux 等 |
| 缺失主题 | P10-2 规划的 5 个细化主题页（52-56）均已存在，但 `56_rust_for_linux_kernel_module_basics.md` 内容深度待补 |
| 陈旧引用 | Embedded Rust Book / Embedonomicon 链接需随 `docs.rust-embedded.org` 结构调整；`cortex-m` / `riscv-rt` 版本链接需随生态更新 |
| 术语漂移风险 | `critical-section` crate 的 API 在 1.x 后发生变化；`embedded-hal` 1.0 迁移已完成覆盖 |
| 行动项 | P1：补全 `56_rust_for_linux_kernel_module_basics.md` 的 Rust for Linux 内核模块代码示例；P2：扩展 `crates/c13_embedded` 到 ≥3 目标板 |

### 3.9 错误处理

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/01_foundation/08_error_handling/` 全系列 · `02_intermediate/03_error_handling/` 全系列 |
| 缺失主题 | 无显著缺口；`?` operator、anyhow/thiserror、exception safety 均已覆盖 |
| 陈旧引用 | TRPL Ch09 链接有效；`std::error::Error` 源链 API 随 1.81 的 `Error::source` 无变化 |
| 术语漂移风险 | `try` trait / `try` blocks 仍为 nightly；稳定后需更新 `?` operator 页 |
| 行动项 | P3：`try` blocks / `try` trait stable 后更新对应权威页 |

### 3.10 性能 / 零成本抽象

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/01_foundation/00_start/02_zero_cost_abstractions.md` · `06_ecosystem/10_performance/` · `03_advanced/06_low_level_patterns/` |
| 缺失主题 | 无 P0 缺口；SIMD、cache-friendly、custom allocators、zero-copy parsing 均已覆盖 |
| 陈旧引用 | Rust Performance Book 链接有效；LLVM 后端链接需随版本更新 |
| 术语漂移风险 | `zero-cost abstractions` 定义在不同来源中一致；`inline(always)` / `inline(never)` 行为与 Reference 对齐 |
| 行动项 | P2：随 1.98.0 更新 `portable_simd` / `std::simd` 稳定状态 |

### 3.11 形式方法 / 计算语义模型

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/04_formal/` 全系列（145 页），覆盖类型论、线性逻辑、分离逻辑、操作语义、模型检测、rustc internals、并发语义、算法语义、系统语义、架构语义、计算语义模型等 |
| 缺失主题 | P10-4 规划的 6 个目标页（12-17）均已存在：`12_linear_logic_and_ownership.md` · `13_session_types_and_rust_channels.md` · `14_effect_handlers_and_rust_limited_effects.md` · `15_refinement_types_and_flux.md` · `16_rustbelt_ownership_logic.md` · `17_aeneas_verification_pipeline.md` |
| 陈旧引用 | `doi.org` 与 `dl.acm.org` 链接对自动化请求常返回 403/404，浏览器通常可访问；建议补充 arXiv 或作者个人页镜像 |
| 术语漂移风险 | `behavior considered undefined` 官方列表随 Rust 版本微调；`Tree Borrows` vs `Stacked Borrows` 默认切换已记录 |
| 行动项 | P1：复核 `04_formal/11_computational_models/12-17` 内容深度，确保每页含 Rust 代码映射与反例；P2：为学术 DOI 链接补充可公开访问的 PDF/arXiv 镜像 |

### 3.12 生态 / 工具链 / 惯用法

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/06_ecosystem/` 全系列（toolchain、cargo、core crates、design patterns、web/networking、data/distributed、security、testing、performance、domain applications、networking、algorithm patterns）以及 `concept/05_comparative/05_idioms_patterns_architecture/` |
| 缺失主题 | P10-3 规划的惯用法/算法/设计模式/架构页骨架已齐，但 `05_comparative/05_idioms_patterns_architecture/` 下 7 个文件为骨架或内容极简 |
| 陈旧引用 | Cargo 1.97/1.98 特性页链接有效； crates 文档版本号需随上游更新 |
| 术语漂移风险 | `public/private dependencies` / `resolver v3` 已稳定；`cargo script` 在 1.79+ 稳定 |
| 行动项 | P1：填充 `05_idioms_patterns_architecture/01_idioms/05_typestate.md` 等 7 个骨架页；P2：更新 Cargo 1.98 特性页 |

### 3.13 企业架构 / 标准

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/06_ecosystem/14_enterprise_architecture/` 全系列（18 页） |
| 缺失主题 | 无 P0 缺口；TOGAF、ISO 42010、DDD、Clean/Hexagonal、微服务、可观测性、金融/IoT 场景均已覆盖 |
| 陈旧引用 | 外部标准组织链接（ISO/IEEE/OMG）可能因证书或访问策略被自动化工具判定为异常，浏览器可访问 |
| 术语漂移风险 | `zero trust` / `SRE` 术语与项目内定义一致；需跟踪 `AUTOSAR Adaptive` 对 Rust 的最新映射 |
| 行动项 | P2：复核 `16_rust_in_financial_services.md` 中前序 kb_auditor 报告的本地死链 |

### 3.14 元数据 / 导航 / RAG

| 维度 | 详情 |
|---|---|
| 已有权威页 | `concept/00_meta/` 全系列（framework、terminology、sources、audit、navigation、ai_semantic_engineering、knowledge_topology） |
| 缺失主题 | RAG 生产化工件：golden query set ≥200、embedding fine-tuning pipeline、reranker/hybrid search 尚未落地为 `tools/kg_rag/` 可运行脚本/数据集 |
| 陈旧引用 | 导航页中的跨层链接经 `kb_auditor.py` 检查无死链 |
| 术语漂移风险 | `RAG` / `embedding` / `reranker` 术语为项目自定义，与学术界一致 |
| 行动项 | P2：构建 `tools/kg_rag/golden_query_set_v1.json`；P2：实现 `tools/kg_rag/fine_tune_embedding.py`；P2：实现 `tools/kg_rag/hybrid_search.py` |

---

## 4. 对称差分析

### 4.1 缺口清单（外部权威来源有，但项目尚未完成对应工件）

| # | 缺口主题 | 所属领域 | 外部权威来源 | 建议目标路径 | 优先级 |
|---:|---|---|---|---|---|
| 1 | Golden query set ≥200 | 元数据 / 导航 / RAG | P10 RAG 评估计划 | `tools/kg_rag/golden_query_set_v1.json` | P2 |
| 2 | Embedding fine-tuning pipeline | 元数据 / 导航 / RAG | SentenceTransformers / LoRA 对比学习 | `tools/kg_rag/fine_tune_embedding.py` | P2 |
| 3 | Reranker / hybrid search | 元数据 / 导航 / RAG | BM25 + vector reranking 文献 | `tools/kg_rag/hybrid_search.py` | P2 |

> **说明**: 以上三项为 P10-5 定义的 RAG 生产化工件，属于 `tools/` 而非 `concept/`。`concept/` 侧已有 [`03_rag_evaluation_for_rust_kg.md`](../concept/00_meta/05_ai_semantic_engineering/03_rag_evaluation_for_rust_kg.md) 作为元页，因此不在概念层重复建立。

### 4.2 骨架页 / 待补内容提示

虽然路径已存在，但以下文件当前为空或内容极简，需在 P10 后续冲刺中补全为完整权威页：

- `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/05_typestate.md`
- `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/06_raii_cleanup.md`
- `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/07_builder.md`
- `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/08_defer.md`
- `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/04_actor.md`
- `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/05_plugin_system.md`
- `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/06_event_bus.md`

### 4.3 盈余 / 项目独有页（`concept/` 有，但国际权威来源未直接镜像）

以下页面属于项目为中文学习者、L0-L7 认知架构和知识图谱治理而设立的“脚手架”，AGENTS.md 允许保留为 `meta_navigation` 或 L5-L7 专题页：

- `concept/00_meta/00_framework/bloom_taxonomy.md` — Bloom 分类法与 L0-L7 映射
- `concept/00_meta/00_framework/knowledge_mindmap.md` — 全局知识思维导图
- `concept/00_meta/04_navigation/03_concept_index.md` — 全局概念索引
- `concept/00_meta/02_sources/06_external_authority_topic_index.md` — 外部权威来源主题索引
- `concept/05_comparative/00_paradigms/01_paradigm_matrix.md` — 多语言范式对比矩阵
- `concept/07_future/02_preview_features/01_effects_system.md` — Effects System 概念预研

### 4.4 术语漂移与链接健康

前序 P9 已完成以下漂移修复，本轮审计复测确认已修复：

- **object safety → dyn compatibility**: `concept/02_intermediate/00_traits/01_traits.md` 已更新判定矩阵。
- **Pin RFC 引用**: 2592 → 2349，`concept/03_advanced/01_async/08_pin_unpin.md` 已修复。
- **Lifetimes Reference 链接**: `reference/lifetimes.html` → `reference/lifetime-elision.html`，已在 `03_lifetimes.md` 修复。
- **Pin Rustonomicon 链接**: `nomicon/pin.html` → `std::pin` 模块页，`08_pin_unpin.md` 已修复。
- **Unsafe 页裸 crates.io 链接**: 已替换为具体 crate 页面或文档页。

本轮新增观察：

- 无新增术语漂移或官方文档死链（`kb_auditor.py --link-check` 0 死链）。
- `dl.acm.org` 与部分 `doi.org` 对自动化请求仍返回 403/404，浏览器可访问；建议持续补充 arXiv/作者页镜像。

建议 P10-7 继续每季度运行 `scripts/check_authority_freshness.py --strict` 以捕获新的漂移。

---

## 5. 与 P10-2 … P10-5 的衔接建议

| P10 任务 | 当前状态 | 关键动作 |
|---|---|---|
| **P10-2 no_std / 裸机 / 嵌入式 / 实时系统** | 概念页已齐 | 补全 `56_rust_for_linux_kernel_module_basics.md` 内容；扩展 `crates/c13_embedded` 到 ≥3 目标板并跑通 `cargo build --target` |
| **P10-3 惯用法 / 算法 / 设计模式 / 架构模式** | 目录与文件骨架已齐 | 填充 §4.2 列出的 7 个空骨架页；确保每页含定义、属性、关系、示例、反例、决策树、国际来源链接 |
| **P10-4 计算语义模型 / 形式方法** | 6 个目标页已存在 | 复核 `04_formal/11_computational_models/12-17` 内容深度，补充 Rust 代码映射与反例 |
| **P10-5 RAG 生产化** | 概念元页已存在，工具缺 | 构建 `tools/kg_rag/golden_query_set_v1.json` ≥200 条；实现 `fine_tune_embedding.py`；引入 BM25 + vector reranker |

---

## 6. 验证声明

本报告基于 `scripts/semantic_domain_inventory.py` 的自动生成结果，并与 `concept/00_meta/02_sources/06_external_authority_topic_index.md` 进行了交叉核对：

- 脚本扫描 `concept/**/*.md` 共 **824** 页。
- 缺口清单仅余 3 项 RAG 生产化工件；P10-2/3/4 的 `concept/` 目标页均已存在。
- 矩阵表直接复制自 `tmp/semantic_domain_matrix.md`（2026-08-11 快照）。
- 外部权威来源类别覆盖完整，无零引用类别（详见 `reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_08.md`）。
- 代码块新鲜度：`scripts/check_concept_code_blocks.py --strict --sample 0` 通过，candidate 3050/3050 pass，compile_fail 1156/1156 ok。
- 内容重叠检测未发现由本报告引入的新重复（详见 §7）。

---

## 7. 内容重叠检测

运行命令：

```bash
python scripts/detect_content_overlap.py
```

结果：

```text
扫描文件数: 1281
相似度阈值: 0.6
发现 2 对潜在重复文件
  [0.60] concept\04_formal\15_language_specification\01_rust_reference_and_normative_gap.md
          vs docs\12_research_notes\01_alignment_matrices\34_rust_reference_alignment.md
  [0.60] concept\04_formal\15_language_specification\01_rust_reference_and_normative_gap.md
          vs docs\12_research_notes\01_alignment_matrices\35_rust_reference_chapters_alignment.md
报告已保存: reports\CONTENT_OVERLAP_DETECTION_2026_08_11.md
```

- 上述 2 对为项目既有基线（`concept/` 权威页 vs `docs/12_research_notes` 研究笔记），相似度 0.60 处于阈值边界，属于合理的研究笔记引用关系。
- 本任务未新增 `concept/` 权威页正文，未引入新的重复对。

---

## 8. 附录：运行命令

```bash
# 生成本报告依赖的盘点数据
python scripts/semantic_domain_inventory.py

# 查看 JSON 盘点与矩阵 Markdown
cat tmp/semantic_domain_inventory.json
cat tmp/semantic_domain_matrix.md

# 代码块新鲜度验证
python scripts/check_concept_code_blocks.py --strict --sample 0
```

stdout 摘要：

```text
P10 Semantic Domain Inventory
  Total concept pages scanned: 824
  Expected topic coverage: 46/49 = 93.9%
  Gaps found: 3
```

---

## 9. 质量门状态

| 门 | 命令 | 结果 | 备注 |
|---|---|---|---|
| 死链检查 | `python scripts/kb_auditor.py --link-check` | ✅ 通过 | 死链 0，跨层问题 0 |
| 权威覆盖 | `python scripts/check_concept_authority_coverage.py --strict --include-crates` | ✅ 通过 | any=100% none=0 core_gaps=0 |
| 交叉域覆盖 | `python scripts/check_cross_domain_coverage.py --strict` | ✅ 通过 | 16/16 覆盖 |
| 权威新鲜度 | `python scripts/check_authority_freshness.py --strict` | ✅ 通过 | WARN 0，上游 stable 1.97.1 与库内一致 |
| 代码块新鲜度 | `python scripts/check_concept_code_blocks.py --strict --sample 0` | ✅ 通过 | candidate 3050/3050，compile_fail 1156/1156 ok |
| 内容重叠 | `python scripts/detect_content_overlap.py` | ✅ 基线 | 2 对既有基线，无新增重复 |
