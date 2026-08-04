# P10 质量门基线报告

**EN**: P10 Quality Gate Baseline Report
**Summary**: Baseline measurement of all 23 blocking + 5 observability quality gates at the start of P10-8 quality-gate guardian run.
**日期**: 2026-08-04
**执行命令**: `bash scripts/run_quality_gates.sh`
**执行方式**: 后台全量运行（任务 ID `bash-4npsxsq2`），结合关键门拆分实跑复核

---

## 1. 总体结论

| 类别 | 通过 | 失败 |
|---|---:|---:|
| 阻断门（23） | 18 | 5 |
| 观察门（5） | 5 | 0 |
| **合计** | **23** | **5** |

> 本次 P10-8 任务**不阻断**其他子代理推进，仅记录、报告并尝试自动修复本代理能力范围内的简单问题。

---

## 2. 阻断门明细

| # | 门 | 命令 | 结果 | 关键指标 |
|---:|---|---|---|---|
| 1 | Cargo Check | `cargo check --workspace` | ✅ 通过 | 全 workspace 通过 |
| 2 | Cargo Test | `cargo test --workspace --quiet` | ✅ 通过 | 全部 crate 测试通过 |
| 3 | Cargo Clippy | `cargo clippy --workspace -- -D warnings` | ✅ 通过 | 无 warning |
| 4 | Cargo Audit | `cargo audit --no-fetch` | ✅ 通过 | 无漏洞 |
| 5 | Cargo Vet | `cargo vet --locked` | ✅ 通过 | 通过 |
| 6 | mdbook Build | `mdbook build` | ✅ 通过 | 仅搜索索引大小警告 |
| 7 | KB Auditor | `python scripts/kb_auditor.py --link-check` | ❌ 失败 | 死链 **25** / 跨层问题 **25** |
| 8 | Content Overlap v1 | `python scripts/detect_content_overlap.py` | ✅ 通过 | 无 actionable |
| 9 | Bilingual Annotations | `python scripts/add_bilingual_annotations.py --mode check-only` | ✅ 通过 | 通过 |
| 10 | Mermaid Syntax | `mermaid` 语法检查 | ✅ 通过 | 无关键语法问题 |
| 11 | Topology Quality | `python scripts/check_topology_quality.py --strict` | ✅ 通过 | T1–T6 通过 |
| 12 | KG SHACL | `python scripts/check_kg_shapes.py --strict` | ✅ 通过 | K1–K7 全 0 |
| 13 | KG SHACL Real Engine | `python scripts/validate_kg_shacl.py --strict` | ✅ 通过 | conforms=True, violations=0 |
| 14 | Canonical Uniqueness | `python scripts/check_canonical_uniqueness.py --strict` | ❌ 失败 | **1 ERROR**：`cqrs_event_sourcing` 双权威页 |
| 15 | Concept Consistency | `python scripts/concept_consistency_auditor.py --strict` | ✅ 通过 | 无错误级发现 |
| 16 | Content Overlap v2 | `detect_content_overlap_v2.py + triage_overlap.py` | ✅ 通过 | MERGE=0, DOCS_INTERNAL=0 |
| 17 | Concept Authority Coverage | `python scripts/check_concept_authority_coverage.py --strict --include-crates` | ✅ 通过 | any=100%, 核心 L1-L4 无 P0 缺口 |
| 18 | Examples Compile | `python scripts/check_examples_compile.py --strict` | ✅ 通过 | 通过 |
| 19 | Naming Convention | `python scripts/check_naming_convention.py --strict` | ✅ 通过 | ERROR=0, WARN=0 |
| 20 | Quiz System | `python scripts/check_quiz_system.py --strict` | ❌ 失败 | registry=354页/1522块 vs actual=360页/1540块 |
| 21 | Metadata Consistency | `python scripts/check_metadata_consistency.py --strict` | ❌ 失败 | D5 稳定层 nightly 残留 **2** |
| 22 | Concept Code Blocks | `python scripts/check_concept_code_blocks.py --strict` | ❌ 失败 | rot=**8**（1 candidate fail + 5 unexpected_pass + 2 wrong_code） |
| 23 | Mindmap Coverage | `python scripts/check_mindmap_coverage.py --strict` | ✅ 通过 | mindmap 100%, 反例 97.6% |
| 24 | Semantic Health | `python scripts/semantic_health.py --strict` | ✅ 通过 | total=99.0 grade=OK |

## 3. 观察门明细

| # | 门 | 结果 | 关键指标 |
|---:|---|---|---|
| O1 | Stub Purity | ✅ 通过 | 伪 stub=0, 空壳页=0, 高重复=0 |
| O2 | Cross-Domain Coverage | ✅ 通过 | 16/16 = 100% |
| O3 | KG Relation Precision | ✅ 通过 | 核心 generic_ratio=0% |
| O4 | Decision Tree rustc Error Code | ✅ 通过 | 节点无歧义 |
| O5 | Version Semantic Injection | ✅ 通过 | 1.90-1.97 74/74=100%, 1.98 beta 39/39=100% |

---

## 4. 失败门详细诊断

### 4.1 KB Auditor Link Check

- **死链**: 25 个，全部位于 `concept/05_comparative/05_idioms_patterns_architecture/` 子目录，原因均为相对路径少了一层 `../`。
- **跨层问题**: 25 个，同样集中在新增的惯用法/模式/架构页，提示缺少向 L4 的向下引用。
- **docs/content/knowledge 死链**: 0

详见 `reports/kb_quality_dashboard.md` §死链检测。

### 4.2 Canonical Uniqueness

**1 ERROR**：双权威页声明

| 文件 A | 文件 B | 原因 |
|---|---|---|
| `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/02_cqrs_event_sourcing.md` | `concept/06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md` | 文件名词干相同 `cqrs_event_sourcing` |

需按 AGENTS.md §3.3 canonical 规则合并：保留一处权威页，另一处改为重定向 stub。

### 4.3 Quiz System

- **独立 quiz**: 23 个（注册表已登记）
- **嵌入式测验统计不符**: registry=354页/1522块，actual=360页/1540块
- 需更新 `concept/00_meta/quiz_registry.yaml` 中 `embedded_quizzes.pages` 与 `total_blocks`。

### 4.4 Metadata Consistency

- **D5 稳定层正文残留 nightly/preview/unstable**: 2 处
- 注：当前 `reports/METADATA_CONSISTENCY_BASELINE_2026-08-04.md` 与 `.json` 显示 D5=0，但脚本 `--strict` 实跑稳定复现 D5=2，报告文件待刷新。

### 4.5 Concept Code Blocks

| 文件 | 行 | 分类 | 状态 | 错误摘要 |
|---|---:|---|---|---|
| `concept/06_ecosystem/03_design_patterns/48_api_guidelines_idioms.md` | 486 | candidate | fail | `self` parameter is only allowed in associated functions |
| `concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md` | 420 | compile_fail | cf_unexpected_pass | 标注腐烂或编译器已修复 |
| `concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md` | 363 | compile_fail | cf_unexpected_pass | 标注腐烂或编译器已修复 |
| `concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md` | 421 | compile_fail | cf_wrong_code | 错误码不匹配 |
| `concept/04_formal/11_computational_models/16_rustbelt_ownership_logic.md` | 370 | compile_fail | cf_wrong_code | 错误码不匹配 |
| `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/06_raii_cleanup.md` | 105 | compile_fail | cf_unexpected_pass | 标注腐烂或编译器已修复 |
| `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/05_lock_free_data_structures.md` | 129 | compile_fail | cf_unexpected_pass | 标注腐烂或编译器已修复 |
| `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/05_plugin_system.md` | 129 | compile_fail | cf_unexpected_pass | 标注腐烂或编译器已修复 |

详见 `reports/P10_CODE_BLOCKS_DETAIL_2026_08_04.md`。

---

## 5. 与 P9 完成报告对比

P9 报告宣称 23 阻断 + 5 观察全部通过；P10 并行工作期间新增内容引入以下退化：

| 退化项 | P9 基线 | P10 基线 | 说明 |
|---|---:|---:|---|
| 死链 | 0 | 25 | 新增惯用法/模式/架构页路径错误 |
| 跨层问题 | 0 | 25 | 同上 |
| Canonical Uniqueness ERROR | 0 | 1 | 新增 CQRS/ES 页与既有页冲突 |
| Quiz System | 一致 | 不一致 | 新增 6 页/18 块嵌入式测验未同步注册表 |
| Metadata D5 | 0 | 2 | 新增页 nightly 残留 |
| Concept Code Blocks rot | 0 | 8 | 新增形式方法/惯用法页代码块标注问题 |

---

## 6. 修复建议汇总

| 问题类别 | 自动修复可行性 | 建议操作 |
|---|---|---|
| 死链（25） | ✅ 可自动 | 将 `concept/05_comparative/05_idioms_patterns_architecture/*/*/../*.md` 中的 `../../` 批量替换为 `../../../` |
| 代码块腐烂（8） | ⚠️ 部分可自动 | 调整 `compile_fail` 标注、补充上下文或改为 `ignore`；需逐块确认 |
| Quiz 注册表 | ✅ 可自动 | 更新 `embedded_quizzes.pages=360`, `total_blocks=1540` |
| Canonical 重复（CQRS） | ❌ 需内容决策 | 由 P10-3 子代理决定保留 `05_comparative` 还是 `06_ecosystem` 页，另一处改 stub |
| 跨层引用（25） | ❌ 需内容决策 | 由 P10-3 子代理补充 L4 向下引用 |
| Metadata D5（2） | ❌ 需定位 | 脚本未输出具体文件，需进一步排查或更新白名单 |

---

## 7. 后续动作

1. 立即自动修复死链与代码块腐烂。
2. 更新 quiz registry 数字。
3. 每小时重新运行关键检查（cargo check/test/clippy、mdbook build、kb_auditor、overlap v2、naming、code blocks），结果写入 `reports/P10_QUALITY_GATE_WATCH_2026_08_04.md`。
4. 将 canonical 重复、跨层引用、Metadata D5 等需内容决策的问题移交对应内容子代理跟进。
