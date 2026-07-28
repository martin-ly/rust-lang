# 语义对称差后续修复完善计划（确认执行版）

**EN**: Semantic Symmetric-Difference Follow-up Remediation Plan (Confirmed Execution)
**Summary**: 基于 2026-07-28 全面对称差批判性分析，经用户确认后进入执行阶段。本计划覆盖 P0–P3 四级任务与长期治理机制，目标 100% 完成。

> **Rust 版本**: 1.97.1 (Edition 2024)
> **生成时间**: 2026-07-28
> **确认事项**: 用户同意由 AI 决策任务范围、写入报告、立即执行 P0、对齐 Comprehensive Rust / Creusot / Flux / hax 等国际来源；**不同意将观察门强制转正为阻断门**（避免阻碍扩展）。
> **状态**: ✅ 已执行完成（2026-07-29）；23 阻断门 + 6 观察门全部通过；P2-6 阻塞待 Rust 1.98/1.99 发布；P3-4 用户跳过

---

## 一、执行摘要

| 维度 | 当前基线 | 目标 |
|---|---|---|
| 23 阻断质量门 | 全部通过 | 保持全部通过 |
| 6 语义观察门 | 全部通过 | 保持通过，不强制转正 |
| 国际权威来源索引 | 53 来源 100% 标题对齐 | 扩展至 60+ 来源 |
| S1 精确链接残差 | 31 处 | ≤5 处 |
| 验证工具生态 | 5 个深度覆盖 | ≥8 个深度覆盖 |
| 项目创新内容标记 | 无统一规范 | 建立 `project-specific` 标记规范 |
| `knowledge/` 导航 | 无 INDEX | 有 INDEX.md |

---

## 二、P0 — 立即修复（1-2 周内）

| # | 任务 | 目标文件 | 验收标准 | 状态 |
|---:|---|---|---|:---:|
| P0-1 | 将 Comprehensive Rust 纳入国际权威来源索引并建立章节映射 | `concept/00_meta/02_sources/05_international_authority_index.md`；`concept/00_meta/00_framework/comprehensive_rust_mapping.md` | 索引新增“国际课程”小节；映射表覆盖 Comprehensive Rust 主要章节 | ✅ 2026-07-28 |
| P0-2 | 修复 S1=31 残差中的概念页链接 | `concept/02_intermediate/00_traits/01_traits.md` 等 | 概念页 S1 降至 ≤10；全文 S1 ≤20 | ✅ 2026-07-28（S1: 31→1） |
| P0-3 | 补全 `knowledge/INDEX.md` 导航 | `knowledge/INDEX.md` | 列出所有 12 个文件并标注 canonical 链接 | ✅ 2026-07-28 |
| P0-4 | 在 L0 元信息中增加“项目创新 vs 官方规范”标记规范 | `concept/00_meta/00_framework/methodology.md` | 明确 A/S/P 外增加 `project-specific` 标记规则 | ✅ 2026-07-28 |
| P0-5 | 更新 Rust 1.98 preview 骨架内容 | `concept/07_future/00_version_tracking/rust_1_98_preview.md` | 覆盖截至 2026-07-28 已知的 1.98 候选特性或明确占位 | ✅ 2026-07-28 |

---

## 三、P1 — 短期补齐（2-6 周内）

| # | 任务 | 目标文件 | 验收标准 | 状态 |
|---:|---|---|---|:---:|
| P1-1 | 新增 Creusot 权威页 | `concept/04_formal/04_model_checking/11_creusot.md` | 覆盖 prophecy variables、Why3 后端、与 Prusti/Aeneas 对比 | ✅ 2026-07-28 |
| P1-2 | 新增 Flux 权威页 | `concept/04_formal/00_type_theory/14_flux.md` | 覆盖 liquid types、refinement signatures、限制 | ✅ 2026-07-28 |
| P1-3 | 扩展验证工具矩阵，新增 hax / crux-mir / VeriFast | `concept/04_formal/04_model_checking/04_modern_verification_tools.md` | 工具矩阵覆盖 ≥8 个主流验证工具（实际 14 个） | ✅ 2026-07-28 |
| P1-4 | 对齐 Rust Design Patterns | `concept/06_ecosystem/03_design_patterns/01_patterns.md` | 增加 §7 书映射（Idioms/Design Patterns/Anti-patterns/FP） | ✅ 2026-07-28 |
| P1-5 | 对齐 Rust Performance Book | `concept/06_ecosystem/10_performance/01_performance_optimization.md` | 增加 §7 国际权威来源对齐（19 章逐条映射） | ✅ 2026-07-28 |
| P1-6 | 修复剩余 S1 链接 | 全 `concept/` | S1 ≤ 5（实际 1） | ✅ 2026-07-28 |
| P1-7 | 建立 L1↔L4 全量术语对照表 | `concept/00_meta/04_navigation/04_inter_layer_map.md` §5.4 | 覆盖 5 组术语（Own/Borrow/Lifetime/UB/Variance） | ✅ 2026-07-28 |

---

## 四、P2 — 中期深化（1-3 个月）

| # | 任务 | 目标文件 | 验收标准 | 状态 |
|---:|---|---|---|:---:|
| P2-1 | 扩展国际来源索引：Little Book of Rust Books、Rust for Linux Kernel、Zero To Production In Rust | `concept/00_meta/02_sources/05_international_authority_index.md` | 新增 4-6 个权威来源 | ✅ 2026-07-28 |
| P2-2 | 评估 L4 中通用 CS 理论内容的层归属 | `concept/04_formal/00_type_theory/` 等 | 过度泛化内容改为 stub 或迁移 | ✅ 2026-07-28 |
| P2-3 | 建立 `docs/` / `content/` 与 `concept/` 的 canonical 边界巡逻 | `scripts/check_canonical_boundary.py`；`reports/CANONICAL_BOUNDARY_PATROL_*.md` | 每月输出重复风险报告；默认 threshold=0.60、跳过短页 | ✅ 2026-07-28 |
| P2-4 | 深化 Pin / async 语义精度 | `03_advanced/01_async/08_pin_unpin.md` | 与 std::pin 文档逐 API 对照；新增 §2.5 对照表 | ✅ 2026-07-28 |
| P2-5 | 深化 UB 清单与 Reference BCU 的逐条映射 | `04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | 11 条 UB 链接到 `r-undefined.*` 锚点；新增 §七 映射表 | ✅ 2026-07-28 |
| P2-6 | 补全 Rust 1.98/1.99 稳定特性权威页 | `concept/07_future/00_version_tracking/rust_1_98_stabilized.md`、`rust_1_99_preview.md` | 版本发布后 1 周内完成填充 | ⏸️ 阻塞：等待 Rust 1.98/1.99 正式发布 |

---

## 五、P3 — 长期治理（3-12 个月）

| # | 任务 | 目标文件/机制 | 验收标准 | 状态 |
|---:|---|---|---|:---:|
| P3-1 | 将 `authority_semantic_diff.py` 作为**观察门**挂载到 CI（不转正为阻断门） | `run_quality_gates.sh`、`quality_gates.yml` | 每次 PR 扫描核心页权威关键词并输出 warning；observe gate 计数更新为 6 | ✅ 2026-07-28 |
| P3-2 | 建立季度“国际来源语义抽样审计”机制 | `.kimi/templates/quarterly_international_source_audit.md` | 每季度抽样 5-8 个核心页与 Reference/Nomicon 对比 | ✅ 2026-07-29 |
| P3-3 | 观察门状态监控 | `reports/OBSERVE_GATE_BASELINE_2026_07_28.md` | 记录 5 个语义观察门基线，不强制转正 | ✅ 2026-07-29 |
| P3-4 | 建立非英文社区来源索引（可选） | `concept/00_meta/02_sources/05_international_authority_index.md` | 收录中文/日文/俄文高质量 Rust 资源 | ❌ 2026-07-28 用户确认跳过 |
| P3-5 | 自动化 patch release 响应流程 | `scripts/patch_release_response.py`；`docs/04_guides/17_patch_release_response_workflow.md`；AGENTS.md §7 | Rust 补丁版本发布后 48 小时内更新并跑全部门 | ✅ 2026-07-29 |

---

## 六、治理日历

| 频率 | 动作 | 工具/负责人 |
|---|---|---|
| 每次 PR | 跑 23 阻断门 + 6 观察门（含 authority_semantic_diff） | CI |
| 每月 | 检查上游版本 freshness；修复 S1 增长 | `check_authority_freshness.py`、`authority_link_precision.py` |
| 每月 | canonical 边界巡逻：输出重复风险报告 | `scripts/check_canonical_boundary.py` |
| 每季度 | 国际来源语义抽样审计；刷新 topic-authority map | 维护者 + `topic_authority_aligner.py` |
| 每次 Rust 新版本 | Patch release 响应；更新版本跟踪页 | 维护者 |

---

## 七、2026-07-28 执行验证结果

P0 与 P1 全部完成后实跑关键质量门：

| 检查项 | 命令 | 结果 |
|---|---|:---|
| 工作区编译 | `cargo check --workspace` | ✅ 通过 |
| 死链 / 跨层 | `python scripts/kb_auditor.py --link-check` | ✅ 死链 0 / 跨层 0 |
| 概念一致性 | `python scripts/concept_consistency_auditor.py --strict` | ✅ 0 错误 / 0 警告 |
| 语义健康 | `python scripts/semantic_health.py --strict` | ✅ 99.7 grade OK |
| 代码块编译 | `python scripts/check_concept_code_blocks.py --strict` | ✅ 300/300 pass, 892/892 compile_fail ok |
| 内容重叠 | `detect_content_overlap_v2.py \| triage_overlap.py` | ✅ MERGE=0 DOCS_INTERNAL=0 |
| 权威语义差分 | `python scripts/authority_semantic_diff.py --strict` | ✅ P0=0 P1=0 |
| 版本语义注入 | `python scripts/check_version_semantic_injection.py --strict` | ✅ 74/74 |
| 交叉域覆盖 | `python scripts/check_cross_domain_coverage.py --strict` | ✅ 16/16 |
| 示例编译 | `python scripts/check_examples_compile.py --strict` | ✅ 11 stdlib + 3 deps 通过 |
| 测验体系 | `python scripts/check_quiz_system.py --strict` | ✅ 0 失败 |
| 思维表征覆盖 | `python scripts/check_mindmap_coverage.py --strict` | ✅ 100% / 96.8% |
| 命名规范 | `python scripts/check_naming_convention.py --strict` | ✅ 0 ERROR |
| Stub 纯净度 | `python scripts/check_stub_purity.py --strict` | ✅ 0 伪 stub |
| KG 谓词精度 | `python scripts/check_kg_relation_precision.py --strict` | ✅ generic_ratio=0% |
| S1 精确链接 | `python scripts/authority_link_precision.py` | ✅ S1=1（剩余 1 处历史模糊链接） |

### P2/P3 本次推进验证（2026-07-28）

| 检查项 | 命令 | 结果 |
|---|---|:---|
| 死链 / 跨层 | `python scripts/kb_auditor.py --link-check` | ✅ 死链 0 / 跨层 0（P2-4/P2-5 新增锚点全部有效） |
| 权威语义差分 | `python scripts/authority_semantic_diff.py --strict` | ✅ P0=0 P1=0（P2-4/P2-5 关键词已覆盖） |
| 代码块编译 | `python scripts/check_concept_code_blocks.py --strict` | ✅ candidate 300/300 pass, compile_fail 892/892 ok |
| canonical 边界巡逻 | `python scripts/check_canonical_boundary.py --top 10` | ✅ 脚本可调；默认 threshold=0.60 输出 1190 对，多为 `docs/03_reference/quick_reference/` 与 `docs/12_research_notes/` 的合法摘要/研究笔记 |

### 2026-07-29 最终验证（命名规范修复与全门复跑）

修复 `docs/04_guides/patch_release_response_workflow.md` 命名违规 → `docs/04_guides/17_patch_release_response_workflow.md` 后复跑：

| 检查项 | 命令 | 结果 |
|---|---|---|
| 命名规范 | `python scripts/check_naming_convention.py --strict` | ✅ ERROR=0（仅保留 55 个历史 WARN） |
| 内容重叠 v2 | `detect_content_overlap_v2.py \| triage_overlap.py` | ✅ MERGE=0 DOCS_INTERNAL=0 |
| 示例编译 | `python scripts/check_examples_compile.py --strict` | ✅ 11 stdlib + 3 deps 通过，0 失败 |
| 工作区编译 | `cargo check --workspace` | ✅ 通过 |
| 工作区测试 | `cargo test --workspace --quiet` | ✅ 全部 crate 通过（含 doctests，无失败） |
| Clippy | `cargo clippy --workspace -- -D warnings` | ✅ 通过，无 warning |
| 安全审计 | `cargo audit --no-fetch` | ✅ 无漏洞 |
| 供应链审计 | `cargo vet --locked` | ✅ Vetting Succeeded（955 fully audited, 788 exempted） |
| mdbook 构建 | `mdbook build` | ✅ 通过（仅 search index 过大警告） |
| 死链 / 跨层 | `python scripts/kb_auditor.py --link-check` | ✅ 死链 0 / 跨层 0 |
| 语义健康 | `python scripts/semantic_health.py --strict` | ✅ 99.6 grade OK |
| 权威语义差分 | `python scripts/authority_semantic_diff.py --strict` | ✅ P0=0 P1=0 |
| 交叉域覆盖 | `python scripts/check_cross_domain_coverage.py --strict` | ✅ 16/16 = 100% |
| 拓扑质量 | `python scripts/check_topology_quality.py --strict` | ✅ T1–T6 全通过 |
| KG 形态 | `python scripts/check_kg_shapes.py --strict` | ✅ K1–K7 全 0 |
| 测验体系 | `python scripts/check_quiz_system.py --strict` | ✅ 0 失败，22/22 双向链接 |
| 思维表征覆盖 | `python scripts/check_mindmap_coverage.py --strict` | ✅ 100% / 96.8% |
| 版本语义注入 | `python scripts/check_version_semantic_injection.py --strict` | ✅ 74/74 = 100% |
| Stub 纯净度 | `python scripts/check_stub_purity.py --strict` | ✅ 0 伪 stub |
| KG 谓词精度 | `python scripts/check_kg_relation_precision.py --strict` | ✅ generic_ratio=0% |
| 权威覆盖 | `python scripts/check_concept_authority_coverage.py --strict --include-crates` | ✅ any=100% none=0 core_gaps=0 |
| 概念一致性 | `python scripts/concept_consistency_auditor.py --strict` | ✅ 0 错误 / 0 警告 |
| 代码块编译 | `python scripts/check_concept_code_blocks.py --strict` | ✅ candidate 300/300 pass, compile_fail 892/892 ok |
| 元数据一致性 | `python scripts/check_metadata_consistency.py --strict` | ✅ D1/D3/D4/D5/D6=0；D2=1（已白名单） |
| 权威页唯一性 | `python scripts/check_canonical_uniqueness.py --strict` | ✅ 0 真实重复（278 WARN 为合法相似） |
| 决策树 | `python scripts/check_decision_trees.py --strict` | ✅ PASS；Top30 覆盖率 100% |
| 双语标注 | `python scripts/add_bilingual_annotations.py --mode check-only` | ✅ 缺少 EN/Summary=0 |

---

## 八、验收总标准

- [x] P0 全部完成并通过 23 阻断质量门。
- [x] P1 全部完成，S1 ≤ 5，验证工具矩阵 ≥8 工具。
- [x] P2-1 ~ P2-5 已完成；P2-6 因 Rust 1.98/1.99 未发布而阻塞。
- [x] P3-1 已完成；P3-4 用户确认跳过；P3-2/P3-3/P3-5 已完成。
- [x] 新增/修改文件符合 AGENTS.md §4.2 元数据模板。
- [x] 所有代码块保持可编译（`check_concept_code_blocks.py --strict` pass：300/300 + 892/892 ok）。

---

> **维护说明**: 每完成一项任务，在本文件对应条目后追加 `✅ 完成日期 + commit/PR 引用`。
