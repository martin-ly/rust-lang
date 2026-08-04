# P10 语义领域与国际权威持续对齐计划

**EN**: P10 Plan: Semantic Domain Coverage and International Authority Alignment for the Rust Knowledge Base
**Summary**: Close remaining semantic gaps (no_std/embedded, idioms/algorithms/design patterns, formal computational models, AI RAG production) and maintain continuous alignment with the latest international Rust authoritative sources.

**日期**: 2026-08-04
**前置状态**: P9 已完成，`bash scripts/run_quality_gates.sh` 23 阻断门 + 5 观察门全绿；P9-2（Rust 1.98.0 stable 语义注入）保持 pending，将在 Rust 1.98.0 stable 发布后自动触发。

---

## 1. 目标

1. 对 `concept/` 全部语义领域进行系统性盘点，识别与国际化权威来源（The Rust Reference、The Rustonomicon、TRPL、RFCs、std docs、Rust Blog、Embedded Rust Book、Rust for Linux、Ferrous Systems、Rust Design Patterns、Rust API Guidelines、crates.io 生态文档、ACM/IEEE/PL 研究论文）的**对称差**。
2. 补齐 **no_std / 裸机 / 嵌入式 / 实时系统** 语义覆盖与硬件实测。
3. 建立 **Rust 惯用法、算法、设计模式、架构模式** 的权威语义页体系。
4. 深化 **计算语义模型 / 形式方法**（范畴论、模态逻辑、线性类型、会话类型、Effect 系统、精化类型、RustBelt/Aeneas/Flux/Verus）。
5. 将 **AI 语义检索（RAG）** 从基线推进到生产可用： golden query set、embedding 微调、评估指标 ≥ 0.5 recall@5。
6. 保持版本跟踪响应能力：Rust 1.98.0 stable 发布后自动执行语义注入。
7. 完成 P10 全部质量门验证。

---

## 2. 任务分解

### P10-1 语义领域全图盘点与对称差分析

- [ ] 运行 `scripts/semantic_domain_inventory.py`（新建/增强），扫描 `concept/` 全部内容页，按「所有权/借用/生命周期、类型系统、Trait、泛型、宏、并发/并行/异步、unsafe/FFI、嵌入式/no_std、错误处理、性能/零成本抽象、形式方法、生态/工具链、企业架构」等维度生成语义领域矩阵。
- [ ] 对每个领域，抽取权威国际化来源的目录结构/索引，生成**覆盖缺口表**（缺失主题、陈旧引用、术语漂移、对称差）。
- [ ] 输出：`reports/P10_SEMANTIC_DOMAIN_GAP_ANALYSIS_2026_08.md` + `concept/00_meta/05_ai_semantic_engineering/04_semantic_domain_alignment_matrix.md`。
- [ ] 完成标准：矩阵覆盖 ≥ 95% `concept/` 内容页，每个领域至少对齐 2 个国际权威来源，对称差清单经人工复核。

### P10-2 no_std / 裸机 / 嵌入式 / 实时系统语义加固

- [ ] 新增/增强权威页：
  - `concept/06_ecosystem/05_systems_and_embedded/52_no_std_allocators_and_panic_handlers.md`
  - `concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md`
  - `concept/06_ecosystem/05_systems_and_embedded/54_linker_scripts_and_memory_layout.md`
  - `concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md`
  - `concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md`
- [ ] 硬件实测：扩展 `crates/c13_embedded` 到至少 3 个目标板（新增 `thumbv7em-none-eabihf` 与 `riscv32imac-unknown-none-elf` 示例），`cargo build --target` 通过。
- [ ] 输出：`reports/P10_EMBEDDED_HARDWARE_COVERAGE_2026_08.md`。
- [ ] 完成标准：新增页数 ≥ 5，硬件目标 ≥ 3，全部示例在 CI 中通过 `cargo check`/`cargo build`。

### P10-3 Rust 惯用法、算法、设计模式、架构模式语义体系

- [ ] 新建 `concept/05_comparative/04_idioms_patterns_architecture/` 或同级目录（按 AGENTS §4.0 连续编号规则，由 `scripts/plan_renumber.py` 决定），包含：
  - Rust idioms（iterator chains、error propagation、? operator、Into/From/AsRef、Newtype、Typestate、RAII、defer/cleanup patterns）。
  - 算法：Rust 实现的经典数据结构（segment tree、Trie、union-find、graph algorithms、lock-free structures）及复杂度/安全性分析。
  - 设计模式：Strategy、Command、Visitor、State Machine、Builder、Adapter、Decorator 的 Rust 零成本表达。
  - 架构模式：Hexagonal/Clean Architecture、CQRS/ES、Microservices、Actor、Plugin System、Event Bus 在 Rust 中的实践与反例。
- [ ] 每页须包含：概念定义、属性、关系、正向/反向推理决策树、示例、反例、国际权威来源链接。
- [ ] 输出：`reports/P10_IDIOMS_PATTERNS_ARCHITECTURE_COVERAGE_2026_08.md`。
- [ ] 完成标准：新增权威页 ≥ 16，mindmap + 反例节覆盖率 100%，对应 quiz 注册表同步。

### P10-4 计算语义模型与形式方法深化

- [ ] 新增/增强：
  - `concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md`
  - `concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md`
  - `concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md`
  - `concept/04_formal/11_computational_models/15_refinement_types_and_flux.md`
  - `concept/04_formal/11_computational_models/16_rustbelt_ownership_logic.md`
  - `concept/04_formal/11_computational_models/17_aeneas_verification_pipeline.md`
- [ ] 对齐最新国际论文/工具文档（RustBelt POPL 2018、Aeneas ICFP 2022、Flux OOPSLA 2023、Verus）。
- [ ] 输出：`reports/P10_FORMAL_METHODS_ALIGNMENT_2026_08.md`。
- [ ] 完成标准：新增页数 ≥ 6，每个主题提供形式化定义、Rust 映射、工具链示例或反例。

### P10-5 AI 语义检索（RAG）生产化

- [ ] 构建 golden query set ≥ 200 条，覆盖 L0-L7、跨域、错误码、版本特性、no_std/embedded、形式方法。
- [ ] 实现 embedding 微调流水线：`tools/kg_rag/fine_tune_embedding.py`，在 Rust 概念语料上训练/微调（LoRA 或对比学习），目标 `concept_recall@5 ≥ 0.50`（P9 基线 0.167）。
- [ ] 引入 reranker / hybrid search（BM25 + vector）提升 source_recall@5。
- [ ] 输出：`reports/P10_RAG_PRODUCTION_EVALUATION_2026_08.md`。
- [ ] 完成标准：golden query set ≥ 200，concept_recall@5 ≥ 0.50，source_recall@5 ≥ 0.75，MRR/NDCG 显著提升，提供可复现评估脚本。

### P10-6 Rust 1.98.0 stable 发布响应（P9-2 自动触发）

- [ ] 发布当天：创建 `concept/07_future/00_version_tracking/rust_1_98_0.md`。
- [ ] 更新 `concept/07_future/01_rust_version_tracking.md`、SUMMARY、相关 Cargo 特性页。
- [ ] 运行 `scripts/check_version_semantic_injection.py --strict`，确保 1.98.0 特性 ↔ `concept/` 权威页双向链接 100%。
- [ ] 输出：`reports/P10_RUST_1_98_0_RELEASE_RESPONSE_2026_08.md`。
- [ ] 完成标准：1.98.0 语义注入覆盖率 100%，质量门仍全绿。

### P10-7 国际权威来源持续新鲜度与本体对齐

- [ ] 运行 `scripts/check_authority_freshness.py --strict`，生成 `reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_09.md`。
- [ ] 抽样 10 个核心 `concept/` 页，与 Reference/Nomicon/TRPL/最新 RFC 进行语义等价性复核。
- [ ] 修复术语漂移、死链、版本号不一致。
- [ ] 输出：`reports/P10_INTERNATIONAL_SOURCE_AUDIT_2026_08.md`。
- [ ] 完成标准：上游 stable/beta/nightly 变化与库内一致，无未解释死链，术语表同步更新。

### P10-8 质量门最终验证

- [ ] 运行 `bash scripts/run_quality_gates.sh`。
- [ ] 确保 23 阻断门 + 5 观察门全绿。
- [ ] 输出：`reports/P10_Semantic_Domain_Alignment_COMPLETION_2026_08_0X.md`。
- [ ] 完成标准：与 P9 基线相比无新增阻断/观察失败，新增内容不引入重复或死链。

---

## 3. 风险与依赖

| 风险 | 缓解措施 |
|---|---|
| Rust 1.98.0 stable 未在 P10 期间发布 | P10-6 保持 pending，发布后 24h 内触发 |
| 硬件目标板缺失 | 优先使用 QEMU/模拟目标 + `probe-rs` 本地验证 |
| RAG embedding 微调资源不足 | 默认使用轻量 SentenceTransformer + LoRA，可切换 API |
| 新增页过多导致重叠检测误报 | 每批新增后运行 `detect_content_overlap_v2.py` + `triage_overlap.py` |
| 形式方法页过于抽象 | 每页必须提供 Rust 代码映射与反例 |

---

## 4. 时间线与并行策略

建议并行启动子代理：

1. **子代理 A**（内容）：P10-1 + P10-7（语义盘点 + 国际来源审计）。
2. **子代理 B**（内容）：P10-2 no_std/嵌入式。
3. **子代理 C**（内容）：P10-3 惯用法/算法/模式/架构。
4. **子代理 D**（内容）：P10-4 形式方法/计算语义。
5. **子代理 E**（工具）：P10-5 RAG 生产化 + P10-6 1.98.0 发布监控/响应脚本。
6. **子代理 F**（质量）：P10-8 质量门守护，每完成一批内容即跑门。

---

## 5. 确认选项

请确认：

1. **全部推进**：并行启动 A–F 子代理，按上述计划推进到 100%。
2. **优先项推进**：先执行 P10-1（语义盘点）+ P10-2（no_std/嵌入式）+ P10-5（RAG），其余暂停。
3. **暂停规划**：暂不开始 P10，等待 Rust 1.98.0 发布后再启动。

> 默认推荐选项 1，与 P9 模式保持一致。
