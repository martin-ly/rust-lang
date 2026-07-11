# 根 examples/ 编译保护与 scripts/ 大扫除报告

> **日期**: 2026-07-12
> **任务**: P3-5（部分）根 examples/ 编译保护 + P3-6 scripts/ 大扫除
> **执行**: Kimi Code CLI subagent（未执行任何 git mutation；仓库存在外部 watcher 自动提交，本报告不涉及其提交行为）

---

## 任务 A — 根 examples/ 编译保护（P3-5 部分）

### A.1 14 个游离文件试编译结果

使用 `rustc 1.97.0 --edition 2024`（按是否有 `fn main` 选择 bin/lib）：

| 文件 | 直接编译 | 最终状态 |
| :--- | :---: | :--- |
| `advanced_usage_examples.rs` | ✅ | ✅ stdlib 直编 |
| `comprehensive_integration_example.rs` | ✅ | ✅ stdlib 直编 |
| `concurrent_data_structures.rs` | ✅ | ✅ stdlib 直编 |
| `module_complete_examples.rs` | ✅ | ✅ stdlib 直编 |
| `real_world_applications.rs` | ✅ | ✅ stdlib 直编 |
| `rust_194_array_windows_demo.rs` | ✅ | ✅ stdlib 直编 |
| `rust_194_control_flow_demo.rs` | ✅ | ✅ stdlib 直编 |
| `rust_194_lazy_lock_demo.rs` | ✅ | ✅ stdlib 直编 |
| `rust_194_lazylock_patterns.rs` | ✅ | ✅ stdlib 直编 |
| `comprehensive_web_server.rs` | ❌ 需 tokio | ✅ 经 examples_check crate |
| `microservice_template.rs` | ❌ 需 tokio/axum/async-trait | ✅ 经 examples_check crate（修复 1 个 E0382） |
| `rust_194_controlflow_patterns.rs` | ❌ 需 tokio | ✅ 经 examples_check crate（修复 4 个错误） |
| `cargo_script_demo.rs` | ❌ Cargo Script frontmatter | ⚠️ 豁免（需 `cargo +nightly -Zscript`） |
| `module_system_patterns.rs` | ❌ Cargo Script frontmatter | ⚠️ 豁免（需 `cargo +nightly -Zscript`） |

**编译保护方案**：新建 `examples/examples_check/` 轻量 bin crate（自带 `[workspace]` 表脱离根虚拟 workspace，
非 workspace 成员），以 3 个 `[[bin]]` 目标指向需依赖的示例文件，依赖 `tokio = "1" (full)` + `axum = "0.8"` +
`async-trait = "0.1"`，`Cargo.lock` 已生成并纳入跟踪，`cargo check --offline --locked` 通过。
未采用 `--extern` 方案：workspace 已构建的 tokio rlib 未启用 `rt-multi-thread` 特性，特征不匹配不可靠。

**发现并修复的真实腐烂**（5 处，均为示例代码 bug）：

- `rust_194_controlflow_patterns.rs`：3 处 `try_fold` 累加器误包 `ControlFlow::Continue(...)`（应为裸值，
  其中 `find_first_available` 需 `None::<&Connection>` 类型标注）；1 处 E0382（`failed` 移入结构体后
  又调用 `failed.len()`，提前计算 `actual`）。
- `microservice_template.rs`：1 处 E0382（`name` 移入 map 后又用于 println，调换顺序）。

### A.2 新脚本与质量门接入

- 新增 `scripts/check_examples_compile.py`：
  - 9 个 stdlib 示例 `rustc --edition 2024` 试编译；
  - 3 个依赖示例经 `examples/examples_check/` 执行 `cargo check --offline --locked`（锁漂移时回退重试）；
  - 2 个 Cargo Script 文件登记豁免清单（含原因）；
  - **登记制**：任何新增/删除的游离 `.rs` 未同步更新脚本内列表即视为失败，防止绕过；
  - 默认观察模式 exit 0，`--strict` 失败 exit 1。
- 接入 `scripts/run_quality_gates.sh` 为**第 19 门（观察门）**：门编号经 grep 确认现有为
  14 阻断 + 4 观察 = 18，新增后 14 阻断 + 5 观察 = 19；头部注释与通过语同步更新。
- `AGENTS.md` §5.1/§5.2 同步更新（19 项、第 19 门登记、观察门基线表新增 examples compile 行）。

### A.3 `examples/resolver_v3_practice/target/` gitignore 核查

- `.gitignore` 第 7 行 `**/target/` 已覆盖；`git ls-files` 验证该目录**未被 git 跟踪**（0 文件），
  `git check-ignore` 确认被忽略。无需任何移除操作。
- 新建的 `examples/examples_check/target/` 同样被 `**/target/` 覆盖，不会被提交。

### A.4 exercises 文档数字更正

- `exercises/README.md`：自述"30 道已上线"与实际严重不符。实测更正为：
  **42 道编号练习**（ownership 12 / type_system 8 / generics 5 / concurrency 6 / async 6 /
  error_handling 3 / macros 2）+ **8 道 Brown Ownership Inventories** + 10 道 Rustlings 风格 +
  7 道 Unsafe Rust + 5 个算法专题模块 + 3 个版本特性模块（rust_195/196/197）。
  注：前序审计文档（`.kimi/CRITICAL_SEMANTIC_AUDIT...`）称"22 Brown inventories"有误，
  实际 `brown_inventories/` 为 8 个 inventory 文件（12 个测试函数）。
  目录结构注释、各主题清单表（补 ex06–ex12 行）、版本号（1.1→1.2）同步更新。
- `exercises/rustlings_mapping.md`：映射范围 C01–C12 延伸到 **C01–C17**，新增 5 行映射：
  C13 嵌入式 / C14 语义网 / C15 验证工具（最近主题 22_clippy）/ C16 GUI / C17 Resolver V3
  （最近主题 10_modules）；版本 1.1→1.2。
- `examples/README.md`：补充 `module_system_patterns.rs`（原漏登，Cargo Script 格式）、
  `examples_check/` 目录说明与"编译保护（质量门）"一节；版本 1.2→1.3。

---

## 任务 B — scripts/ 大扫除（P3-6）

### B.1–B.2 一次性战役脚本归档

盘点 164 条目，确认 **97 个文件（96 脚本 + 1 配套数据文件）为已完成使命的一次性战役脚本**，
全部移入新建的 `scripts/archive/one_off_2026/`（含清单 README.md）：

- 原 `scripts/` 根目录 58 个：`fix_*`（26）、`add_*`（8）、`batch_*`（4）、`bulk_add_knowledge_module8`、
  `cleanup_*`（3）、`compact_blank_lines`、`deepen/enhance_summaries`、`final_bilingual_fix`、
  `generate_en_skeleton`、`improve_active_metadata`、`migrate_kg_v1_to_v2`、`rebuild_concept_headers`、
  `remove_status_toc_entries`、`replace_placeholder_generic`、`upgrade_cheatsheets`、
  `archive_deprecated_content`、`apply_*`（2）、`append_metadata_behavioral`、
  `temp_external_link_replacements.json` 等；
- 原 `scripts/maintenance/` 27 个：`bulk_*`（5）、`p1/p2_coverage_sprint`、`rust_197_release_day.py`、
  `fix_never_type`、`fix_async_drop_refs`、`fix_404_links`、`fix_archive_c_class_links`、
  `fix_archived_research_notes_links`、`fix_final_broken_links`、`fix_last_anchor_links`、
  `fix_remaining_anchors`、`fix_rod_readme_links`、`fix_coq_skeleton_links`、`fix_cargo_resolver`、
  `fix_unsafe_numbering`、`extend_unsafe_2024`、`add_cross_references`、`add_summary_entries`、
  `auto_add_structure`、`migrate_archive`、`archive_research_notes_candidates/peripheral` 等；
- 原 `scripts/fixes/` 12 个：`fix_p0/p1/p2_*`、`recover_*`、`append_*`、`fix_dangling_renames`、
  `fix_metadata_d3`、`fix_authority_url_placeholders`（`fixes/` 仅保留 3 个可复用的 `find_*` 诊断工具）。

**移动前引用核查**（全部通过）：对全部候选逐一 grep `run_quality_gates.sh`、`.github/workflows/`、
`scripts/git_hooks/`、其他脚本的 import/subprocess——**零阻断引用**。
命中的均为注释/docstring 或文档引用，已更新为归档路径：

- `docs/research_notes/10_authoritative_source_100_percent_roadmap.md`（8 处 p1/p2_coverage_sprint 活链）；
- `concept/00_meta/knowledge_topology/kg_ontology_v2.md`（migrate_kg_v1_to_v2）；
- `concept/00_meta/03_audit/template_deduplication_guide.md`（add_backward_*）；
- `docs/04_research/README.md`（fix_archived_research_notes_links）；
- `scripts/check_template_cliches.py` 与 `scripts/maintenance/archive_health_check.py` 的注释。
- `CHANGELOG.md` 为历史日志，保留原始路径不改动（归档 README 已注明）。

### B.3 `scripts/i18n/` 名实分离

4 个外链修复脚本移入**新建 `scripts/links/`**：`fix_external_links.py`、`fix_rfc_links.py`、
`fix_broken_links_batch.py`、`fix_common_broken_links.py`（无 CI/钩子/脚本引用）。
`scripts/i18n/` 现仅含 4 个 i18n 检查工具（check_concept_headers / check_external_links /
check_github_repos / check_terminology_consistency），名实相符。

### B.4 `scripts/README.md` 重写（v2.3 → v3.0）

- 新目录结构索引（`links/`、`archive/one_off_2026/`、`git_hooks/`）；
- 活跃脚本速查表按现状全量校正（移除已归档/已不存在的条目如 fix_anchor_links_v3、
  fix_broken_anchors_v4、fix_dead_links_v3 等，补充遗漏的 20+ 活跃脚本）；
- **本次会话新增脚本全部登记**：`check_examples_compile.py`（此前 `check_template_cliches`、
  `check_canonical_uniqueness`、`check_decision_trees`、`check_glossary_alignment`、
  `check_msrv_consistency` 已在表中，质量门编号更新为 13/14 阻断现状）；
- 归档边界说明更新（归档迁移脚本清单移除已归档项，新增"一次性战役脚本退役"流程）；
- `archive/one_off_2026/README.md` 新建：归档原因、引用核查记录、来源分布、97 项完整清单。

### B.5 验证

| 验证项 | 结果 |
| :--- | :--- |
| `bash -n scripts/run_quality_gates.sh` | ✅ 语法通过 |
| CI workflows grep 断裂引用 | ✅ 无（全部 97 个移动脚本名逐一 grep，零命中） |
| `check_template_cliches.py --strict` | ✅ exit 0 |
| `check_canonical_uniqueness.py --strict` | ✅ exit 0 |
| `check_decision_trees.py --strict` | ✅ exit 0 |
| `check_glossary_alignment.py --strict` | ✅ exit 0 |
| `check_msrv_consistency.py --strict` | ✅ exit 0 |
| `check_examples_compile.py --strict` | ✅ exit 0（9 stdlib + 3 deps 全通过） |
| `archive_health_check.py` py_compile | ✅ |
| `kb_auditor.py --link-check` | ⚠️ 死链 0；**跨层问题 1（既存，非本次引入）**：`concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md` 缺向 L2 向下引用（本任务未触碰该文件），kb_auditor exit 1 为既存状态 |

---

## 附注

1. **kb_auditor 既存问题**：上述 1 个跨层引用问题导致阻断门 7 当前 exit 1，建议主任务线后续处置
   （补充 L2 向下引用或加入豁免）。
2. **生成物副作用**：运行 kb_auditor 重新生成了 `concept_kb.json` 与
   `reports/kb_quality_dashboard.md`（内容重排，无语义变化），已被仓库 watcher 提交。
3. **未做 git commit**：本任务未执行任何 git mutation；观察到的 `update` 提交来自仓库外部
   watcher 进程（05:53–06:03 期间多次 `git add -A && git commit`），非本任务行为。
4. `examples/examples_check/Cargo.lock` 已跟踪，保证 CI/他机 `cargo check --offline --locked` 可复现。
