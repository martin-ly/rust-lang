# 脚本工具

> **项目**: Rust 系统化学习项目
> **维护者**: Rust 学习项目团队
> **最后更新**: 2026-07-12
> **状态**: ✅ 已完成（P3-6 大扫除）：97 个一次性战役脚本归档至 `archive/one_off_2026/`，`i18n/` 4 个外链修复脚本迁至 `links/`，`i18n/` 名实相符（仅保留 i18n 检查工具）。

---

## 目录结构

```text
scripts/
├── README.md                          # 本文件
│
├── archive/                           # 归档脚本（只读，不再维护）
│   ├── 2026/                          # 按年份分类的历史归档
│   │   ├── dead_link_audit/           # 5 月死链审计调试系列
│   │   ├── link_fix_iterations/       # 历史链接修复战役脚本
│   │   ├── compile_fail/              # compile_fail 验证旧版本
│   │   ├── knowledge_links/           # knowledge 模块链接旧脚本
│   │   ├── push_bump/                 # 批量推送/版本升级脚本
│   │   ├── one_off/                   # 早期一次性任务脚本
│   │   └── legacy_ps_batch/           # 过时 PowerShell / Batch 脚本
│   └── one_off_2026/                  # 2026-07-12 P3-6 大扫除归档的 97 个一次性战役脚本
│                                      # （fix_*/add_*/batch_*/bulk_*/coverage_sprint 等，含清单 README）
│
├── fixes/                             # 针对性问题诊断工具（find_*）
├── maintenance/                       # 项目结构维护工具（可重复运行）
├── links/                             # 外部链接批量修复工具（RFC/外链/断链批次）
├── utils/                             # 通用辅助工具
├── templates/                         # 文档模板（含 atlas_pages/ 人工策展页单一事实源）
├── i18n/                              # 国际化/双语检查工具（check_*）
└── git_hooks/                         # pre-commit 等 Git 钩子
```

---

## 活跃脚本速查

以下列出根目录下核心活跃脚本。完整清单可运行：

```bash
ls scripts/*.py scripts/*.sh scripts/*.ps1 scripts/*.bat
```

### 🔍 审计与检查

| 脚本 | 功能 |
|------|------|
| `audit_code_blocks.py` | 代码块标记审计 |
| `audit_concept_metadata.py` | `concept/` 元数据头审计 |
| `audit_crate_docs_boilerplate.py` | crate 文档样板完整性审计 |
| `audit_source_links.py` | 来源链接标注审计 |
| `audit_stable_apis.py` | 文档中稳定 API 标注审计 |
| `audit_remaining_source_placeholders.py` | 剩余来源占位符审计 |
| `c_class_directory_audit.py` | C 类文档目录审计 |
| `concept_audit.py` | 概念知识体系一致性检查 |
| `concept_consistency_auditor.py` | 跨文件概念定义一致性审计（质量门 14，阻断）：抽取 Send/Sync、所有权、借用、生命周期、内部可变性、Pin/Unpin、协变逆变、unsafe 定义并检测跨文件矛盾；`--strict` 发现 ERROR 级发现时 exit 1 |
| `cross_concept_diff.py` | 交叉概念 Diff |
| `docs_value_audit.py` | 文档价值分级审计 |
| `kb_auditor.py` | 知识库完整性检查（质量门 7，阻断） |
| `rust_version_tracker.py` | Rust 版本特性跟踪 |
| `version_fact_check.py` | 版本相关事实核查 |
| `lint_filenames.py` | 文件名 snake_case 命名检查 |
| `check_naming_convention.py` | 命名规范 lint（质量门 18，阻断；2026-07-14 R4 评估转正；AGENTS.md §4.0 N1–N6：序号格式/同号冲突/双前缀/变体后缀 stub 豁免/一级目录连续性/中文空格大小写；扫描 concept/knowledge/docs/content/crates/*/docs；默认 exit 0，`--strict` 时 ERROR>0 exit 1，WARN 不阻断） |
| `check_concept_numbering.py` | concept 文件编号检查 |
| `check_crates_docs_alignment.py` | crates 文档对齐检查 |
| `check_rust_feature_versioning.py` | Rust 特性版本标注检查 |
| `detect_content_overlap.py` | 三轨内容相似度去重检测（质量门 8，阻断） |
| `detect_content_overlap_v2.py` | 段落级重叠检测 v2（质量门 15，2026-07-12 转阻断：triage 可处理项 MERGE+DOCS_INTERNAL 基线 0） |
| `triage_overlap.py` | 重叠报告分诊（MERGE/DOCS_INTERNAL/SERIES/REVIEW；SERIES 白名单 = 正则 + `SERIES_PATH_RE` 路径族 + 显式 `SERIES_PAIRS` 人工复核登记） |
| `check_canonical_uniqueness.py` | `concept/` 权威页唯一性检查（质量门 13，阻断） |
| `check_quiz_system.py` | 测验体系一致性检查（质量门 19，阻断；2026-07-14 R4 评估转正）：quiz_registry.yaml 与实际文件一致性（题数/题型/难度分布/嵌入式统计）、独立 quiz 题型多样性 ≥3 种、难度标注率、quiz↔concept 双向链接率；默认 exit 0，`--strict` 检查 1-3 失败即 exit 1（回链缺失仅统计） |
| `check_template_cliches.py` | `concept/` 模板套话黑名单扫描；`--strict` 发现命中即 exit 1 |
| `audit_content_completeness.py` | `concept/` 内容完整性审计：TODO 类标记 / 空章节 / PLACEHOLDER_SECTION（占位引导语，观察指标默认 exit 0；`--strict` 存在即 exit 1） |
| `check_decision_trees.py` | 决策树机器可读层校验（`decision_trees.yaml` 结构/死端/概念覆盖）；结构错误 exit 1 |
| `check_glossary_alignment.py` | 术语表对齐检查（以 `terminology_glossary.md` 为权威）；`--strict` 有差异 exit 1 |
| `check_msrv_consistency.py` | MSRV 单一事实源检查（根 `Cargo.toml` rust-version=1.97.0）；`--strict` 不一致 exit 1 |
| `check_association_blocks.py` | `concept/` 关联区块存在性与命名合规检查 |
| `check_metadata_consistency.py` | 元数据 D1–D6 一致性检查（质量门 20，阻断；2026-07-14 转阻断） |
| `check_topology_quality.py` | atlas 拓扑质量 T1–T6（质量门 11，阻断） |
| `check_kg_shapes.py` | KG SHACL/形态校验（质量门 12，阻断） |
| `check_concept_authority_coverage.py` | concept 权威层国际化权威来源覆盖率（质量门 16，阻断；2026-07-14 R4 评估转正，`--strict --include-crates`）；`--include-crates` 附加 crates/*/docs 覆盖小节（非 stub 内容页口径 + **stub canonical 链接健康度**，默认观察 exit 0，`--strict` 时 crates 缺口>0 或 **stub canonical 死链>0** 亦阻断） |
| `semantic_health.py` | 综合语义健康分（质量门 23，阻断；2026-07-14 转阻断） |
| `check_mermaid_syntax.py` | Mermaid 语法检查（质量门 10，阻断） |
| `check_mindmap_coverage.py` | 内容页真 mindmap 图覆盖率与反例节存在率（质量门 22，阻断；2026-07-13 P4 挂入，2026-07-14 转阻断；`--strict` 低于基线 mindmap 10%/反例 40% 时 exit 1） |
| `auto_dedup_redirect.py` | 对高相似度非 `concept/` 文件生成指向 `concept/` 权威来源的重定向页 |
| `unify_association_headings.py` | 关联区块标题统一与核心页上层/下层概念补全（`--enrich-core`；默认 dry-run） |

### 🔗 链接检查

| 脚本 | 功能 |
|------|------|
| `check_links.py` | 本地 Markdown 链接有效性检查 |
| `check_dead_links.py` | 死链检查 |
| `mark_dead_links.py` | 死链标注 |
| `check_active_anchors.py` | 同文件锚点检查 |
| `check_all_concept_links_health.py` | concept 全量链接健康检查 |
| `check_authority_link_health.py` | 权威来源链接健康检查 |
| `check_github_links_health.py` | GitHub 链接健康检查 |
| `check_non_github_links_health.py` | 非 GitHub 外部链接健康检查 |
| `check_source_links_health_extended.py` | 来源链接健康检查（扩展版） |
| `links/fix_external_links.py` | 外部链接批量修复（2026-07-12 自 `i18n/` 迁入） |
| `links/fix_rfc_links.py` | RFC 链接修复（2026-07-12 自 `i18n/` 迁入） |
| `links/fix_broken_links_batch.py` | 断链批量修复（2026-07-12 自 `i18n/` 迁入） |
| `links/fix_common_broken_links.py` | 常见断链模式修复（2026-07-12 自 `i18n/` 迁入） |

### 🌐 i18n 与双语标注

| 脚本 | 功能 |
|------|------|
| `add_bilingual_annotations.py` | 术语双语标注（质量门 9，阻断） |
| `check_i18n_metadata.py` | i18n 元数据检查 |
| `check_knowledge_docs_i18n.py` | knowledge/docs i18n 检查 |
| `list_i18n_metadata.py` | i18n 元数据列表 |
| `multilingual_alignment.py` | 多语言对齐 |
| `i18n/check_concept_headers.py` | concept 文件头 i18n 检查 |
| `i18n/check_external_links.py` | 外链 i18n 检查 |
| `i18n/check_github_repos.py` | GitHub 仓库引用检查 |
| `i18n/check_terminology_consistency.py` | 术语一致性检查 |

### 📝 生成工具

| 脚本 | 功能 |
|------|------|
| `auto_toc_generator.py` | 自动生成目录 |
| `auto_link_concepts.py` | 自动添加概念交叉链接 |
| `auto_categorize_blocks.py` | 代码块自动分类 |
| `generate_crate_docs_boilerplate.py` | 批量生成 crate 文档样板 |
| `generate_summary.py` | 生成汇总 |
| `validate_summary.py` | 汇总校验 |
| `generate_version_features.py` | 生成版本特性表 |
| `generate_kg_index.py` / `generate_kg_v3.py` | 知识图谱索引 / KG v3 生成 |
| `generate_knowledge_topology_atlas.py` | 知识拓扑 atlas 生成（数据驱动页 01/02/06/07/08/10/README + 人工策展页 03/04/05/09 从 `templates/atlas_pages/` 原样拷贝；纪律：只重生成、不手改） |
| `extract_concept_topology.py` | 概念拓扑抽取 |
| `extract_runnable_quizzes.py` | 提取可运行测验 |
| `grade_concept.py` | 概念分级 |
| `kg_reasoning.py` / `type_kg_core_edges.py` / `topic_authority_aligner.py` | KG 推理 / 核心边标注 / 主题权威对齐 |
| `owl_consistency_check.py` | OWL 本体一致性检查 |
| `compute_slug.py` | slug 计算 |
| `concept_config.py` | concept 配置共享模块 |
| `build_search_index.py` | ⚠️ 已退役（2026-07-12）：无活跃消费者，搜索由 mdbook searchindex / tools/kg_rag 提供 |

### 🔧 清理与维护

| 脚本 | 功能 |
|------|------|
| `archive_file.py` | 通用归档迁移工具 |
| `bulk_rename.py` | 批量重命名仓库路径为 snake_case 并更新内部引用 |
| `quarterly_maintenance.py` | 季度维护编排 |
| `quarterly_sync.py` | 季度同步 |
| `quarterly_zombie_cleanup.py` | 季度僵尸内容清理 |
| `roded_governance.py` | RoDed 治理 |

### 🏗️ 构建与测试

| 脚本 | 功能 |
|------|------|
| `run_quality_gates.sh` | 本地一键运行全部 23 个质量门（23 阻断 + 0 观察） |
| `cargo_build_optimized.sh` / `.ps1` | 优化编译 |
| `cargo_update_check.sh` / `.ps1` | 依赖更新检查 |
| `run_miri.sh` / `.bat` | Miri 测试 |
| `exercise_check.sh` / `.ps1` | 练习题评测 |
| `code_block_compiler.py` | 代码块编译验证 |
| `verify_compile_fail_v3.py` | `compile_fail` 代码块验证 |
| `check_examples_compile.py` | 根 `examples/` 游离示例编译保护（质量门 17，阻断；2026-07-14 R4 评估转正并新增 CI job `examples-compile`）：9 个 stdlib 示例 rustc 直编 + 3 个依赖示例经 `examples/examples_check/` crate + 2 个 Cargo Script 豁免；未登记的新游离文件视为失败；`--strict` 失败 exit 1 |
| `check_concept_code_blocks.py` | concept/ 代码块批量编译实测（质量门 21，阻断；2026-07-13 重构为独立门，2026-07-14 转阻断）：提取全部 ```rust 块并分类（anno_ignore/compile_fail/should_panic/pseudo/nightly/nostd/dep_skip/dep_untested/dep/candidate）；compile_fail 块验证确实失败且与标注 E0xxx 一致（支持 editionNNNN fence）；std-only 候选 >300 时按文件分层抽样（默认 300，seed 固定）`rustc --edition 2024` 自动包 `fn main` 直编；`--with-deps` 用 `target/debug/deps` 的 rmeta 做 `--extern` 实测依赖块（多 feature 产物轮换重试，找不到依赖归“需依赖未测”）；分批 300 块防超时；结果写 `--json`/`--report`；`--strict` 时“应过但失败/标注腐烂”>0 → exit 1。基线：`reports/CONCEPT_CODE_BLOCKS_BASELINE_2026_07_13.md` |

### 📋 日常工具

| 脚本 | 功能 |
|------|------|
| `check_dependencies.sh` / `.bat` | 依赖检查 |
| `daily_checklist.sh` / `.ps1` | 每日检查清单 |
| `supply_chain_audit.py` | 供应链审计 |

### 🚀 Rust 版本发布相关

| 脚本 | 功能 |
|------|------|
| `rust_197_release_day.sh` | Rust 1.97.0 发布日执行脚本 |
| `rust_197_upstream_monitor.sh` | 上游发布动态监控 |
| `probe_rust_197_apis.rs` / `probe_rust_198_apis.rs` | 候选 API 可用性探测 |
| `check_authority_freshness.py` | 权威源新鲜度周期巡检（2026-07-13 P5 新增；**手动巡检工具，非 CI 质量门**——网络依赖门不适合 CI 阻断）：concept/ 权威源域名引用扫描 + 上游 stable 版本比对（releases.json/releases.rs，网络不可达优雅降级 exit 0）+ 1.98 preview beta→stable 迁移到期检查；默认观察 exit 0，`--strict` 可处置 WARN exit 1（网络降级除外），`--offline` 跳过网络检查 |

---

## 命名检查与批量重命名

### `lint_filenames.py`

检查新增/变更的文件名是否符合 `snake_case` / `number_prefix_snake_case` 规范。

```bash
# 默认：检查相对于 origin/main 的变更文件（PR/提交前使用）
python scripts/lint_filenames.py

# 检查所有已跟踪文件（治理审计使用）
python scripts/lint_filenames.py --all

# 对全部历史文件也返回非零退出码
python scripts/lint_filenames.py --all --strict

# 排除指定前缀
python scripts/lint_filenames.py --all --exclude archive/ --exclude reports/
```

### `bulk_rename.py`

将仓库路径批量重命名为 snake_case，并自动更新 tracked 文本文件中的内部引用。

```bash
# 单文件
python scripts/bulk_rename.py docs/LINK_CHECK_REPORT.md reports/01_link_check_report.md

# 多文件成对传入
python scripts/bulk_rename.py \
  scripts/cargo-build-optimized.sh scripts/cargo_build_optimized.sh \
  scripts/run-miri.sh scripts/run_miri.sh

# 配合计划文件批量执行
python scripts/bulk_rename.py $(awk '{print $1, $2}' target/tmp/rename_plan.txt)
```

**注意事项**：

1. 优先使用 `git mv`；对未跟踪文件退回到 `mv`。
2. 在大小写不敏感的文件系统（如 Windows）上，纯大小写重命名后会通过 `git checkout -- <new>` 重新物化文件，避免引用更新阶段找不到新路径。
3. 更新内部引用时默认跳过 `archive/`、`.kimi/`、`.venv/`、`target/`，保证只读/例外区域不被改写。
4. 仅扫描以下扩展名的文本文件：`.md`、`.json`、`.toml`、`.yaml`、`.yml`、`.py`、`.rs`、`.sh`、`.js`、`.hbs`。
5. 运行前建议先通过 `python scripts/lint_filenames.py --all` 生成清单并核对重命名计划。

### `plan_renumber.py` / `apply_renumber.py`（重编号框架，2026-07-12 新增）

目录内两位连续序号（`NN_`）重编号工程的两阶段工具链：

- `plan_renumber.py`：**只读**，生成 dry-run 映射表与计划报告，不移动任何文件。
  顺序优先级：`SUMMARY.md` 教学顺序 → 未收录文件字母序；README 最前；
  `rust_1_9x_*` / `00_meta/00_framework/` / `07_future/00_version_tracking/`
  无序号专题系列保持无序号；排除 `sources/`、`quiz*`、`knowledge_topology/` 等目录。
- `apply_renumber.py`：默认 **dry-run**；显式 `--apply` 才用 `os.rename`
  （两阶段临时名，处理链式/环状重命名）移动文件，并全库重写
  `.md/.py/.json/.yaml/.toml` 中的相对/绝对/仓库相对路径引用
  （按引用方文件移动前后位置双向重算），结构化同步 `concept_kb.json` 与
  `kg_data*.json`/`kg_index.json`，重生成 `SUMMARY.new.md`（写 `tmp/` 供 diff）。
  跳过 `book/ reports/ archive/ tmp/ vendor/ target/ .git/`。**不使用任何 git 命令**。

```bash
# 阶段 1：生成映射表与报告（只读）
python scripts/plan_renumber.py --root concept \
  --out tmp/renumber/mapping_concept.csv --report tmp/renumber/plan_report.md

# 阶段 2：dry-run 验证链接重写（默认）
python scripts/apply_renumber.py --mapping tmp/renumber/mapping_concept.csv --scope concept

# 阶段 2：实际执行（需人工 review 映射表与 SUMMARY.new.md 后）
python scripts/apply_renumber.py --mapping tmp/renumber/mapping_concept.csv --scope concept --apply
```

**注意事项**：

1. `--root`/`--scope` 参数化，`docs/`、`knowledge/`、`crates/` 可复用同一框架。
2. 所有读写使用 `newline=''`，保证 LF/CRLF 文件行尾不被翻转。
3. 执行前必须人工 review `tmp/renumber/plan_report.md` 的疑点清单与
   `tmp/renumber/apply_log.md` 的未解析引用清单。
4. 输出产物（`tmp/renumber/`）不应提交版本控制。

---

## 子目录说明

### `fixes/`

针对性问题诊断工具（保留可重复运行的 find 系列）：

- `find_cfg_gap.py` — 查找条件编译配置间隙
- `find_clippy_issue.py` — 定位 Clippy 警告问题
- `find_issue.py` — 通用问题定位

> 原 `fixes/` 下 12 个一次性修复战役脚本（fix_p0/p1/p2_*、recover_* 等）已于 2026-07-12 归档至 `archive/one_off_2026/`。

### `maintenance/`

项目结构维护工具（均为可重复运行的检查/建议类工具）：

- `analyze_doc_structure.py` — 分析文档结构
- `archive_health_check.py` — 归档健康检查
- `assess_research_notes.py` / `check_research_notes.py` — 研究笔记评估/检查
- `authority_coverage_dashboard.py` — 权威来源覆盖仪表盘
- `auto_fix_broken_links.py` — 自动断链修复（通用）
- `check_authoritative_source_gaps.py` / `suggest_authoritative_sources.py` — 权威来源缺口检查/建议
- `check_code_example_anchors.py` — 代码示例锚点检查
- `check_i18n_translation_gap.py` — i18n 翻译缺口检查
- `check_version_facts.py` — 版本事实检查
- `cleanup_unused_aliases.py` — 清理未使用的别名
- `extract_titles.py` — 标题抽取
- `final_authoritative_source_checklist.py` — 权威来源最终清单
- `find_orphan_concept_pages.py` — 孤立 concept 页查找
- `list_large_crates_docs.py` — 大型 crate 文档清单

> 原 `maintenance/` 下 26 个一次性战役脚本（bulk_add_*、p1/p2_coverage_sprint、fix_never_type、fix_async_drop_refs、rust_197_release_day.py 等）已于 2026-07-12 归档至 `archive/one_off_2026/`。

### `links/`

外部链接批量修复工具（2026-07-12 自 `i18n/` 迁入，名实分离）：

- `fix_external_links.py` — 外部链接批量修复
- `fix_rfc_links.py` — RFC 链接修复
- `fix_broken_links_batch.py` — 断链批量修复
- `fix_common_broken_links.py` — 常见断链模式修复

### `utils/`

通用辅助工具：

- `enhance_placeholder_files.py` — 归档迁移脚本：增强占位文件或将 PENDING_ITEMS 归档到 `docs/archive/small_files/`

### `i18n/`

国际化检查工具（check_* 系列，不含修复脚本）：

- `check_concept_headers.py` / `check_external_links.py` / `check_github_repos.py` / `check_terminology_consistency.py`

### `templates/`

docs/ crate 文档样板模板；`templates/atlas_pages/` 为知识拓扑 atlas 人工策展页（03/04/05/09）的单一事实源，由 `generate_knowledge_topology_atlas.py` 原样拷贝到 `concept/00_meta/knowledge_topology/`（LF 行尾）。修改这些页请改模板后重跑生成器。

---

## 归档说明

`scripts/archive/` 目录存放以下类型的历史脚本：

1. **迭代旧版本**：如 `fix_dead_links.py` / `v2` → `v3`（保留 v3，归档 v1/v2）
2. **一次性调试脚本**：如 `_debug_docs_links*.py`、`_analyze_*.py` 系列
3. **批量推送脚本**：如 `push_22.py` ~ `push_30.py`、`final_push.py` 等
4. **过时的平台脚本**：被 Python 跨平台脚本替代的 PowerShell/Batch 脚本
5. **一次性链接修复战役脚本**：`link_fix_iterations/` 下各轮次死链修复脚本
6. **一次性战役脚本（2026-07-12 P3-6 大扫除）**：`one_off_2026/` 下 97 个已完成使命的 fix_*/add_*/batch_*/bulk_*/coverage_sprint 脚本（移动前已确认无质量门/CI/pre-commit/其他脚本 import 引用；详见 `one_off_2026/README.md` 清单）

> ⚠️ 归档脚本不再维护，仅供参考或历史回溯。如需使用，请先检查活跃目录中是否有更新的替代版本。

---

## `archive/` 只读边界

1. **任何脚本不得向 `archive/` 写入新的活跃内容**。`archive/` 仅用于存放历史/归档资料，写入操作只能通过显式的**归档迁移脚本**完成。
2. 已标注为归档迁移脚本的工具包括：
   - `scripts/archive_file.py`
   - `scripts/quarterly_sync.py`
   - `scripts/roded_governance.py`
   - `scripts/utils/enhance_placeholder_files.py`
   - （历史，已归档至 `archive/one_off_2026/`：`archive_deprecated_content.py`、`migrate_archive.py`、`archive_research_notes_candidates.py`、`fix_archive_c_class_links.py`）
3. `bulk_rename.py` 在更新内部引用时会跳过 `archive/`、`.kimi/`、`.venv/`、`target/`，避免误改只读区域。
4. 如果发现普通脚本向 `archive/` 写入非归档内容，应改为写入 `tmp/` 或作为 bug 报告。

---

## 使用规范

### 添加新脚本

1. **命名规范**：
   - 使用 `snake_case`（脚本/源码文件名）
   - 名称应清晰描述功能
   - 添加适当的文件扩展名
2. **文档要求**：
   - 脚本头部添加注释说明功能
   - 复杂脚本添加使用示例
   - 更新此 README
3. **权限设置**：
   - Shell 脚本: `chmod +x script.sh`
   - Python 脚本: 添加 shebang `#!/usr/bin/env python3`

### 迭代开发

如需对现有脚本进行大幅迭代：

1. 将旧版本移入 `archive/2026/` 对应分类目录
2. 新版本保留在根目录，替换旧版本引用
3. 在 README 中更新说明

### 一次性战役脚本退役

使命完成的一次性脚本（针对特定批次数据硬编码路径/替换表）：

1. 确认无质量门 / CI workflow / pre-commit / 其他脚本 import 引用
2. 移入 `archive/one_off_2026/`（或按年份新建 `one_off_<year>/`），更新 `one_off_<year>/README.md` 清单
3. 更新活跃文档中对旧路径的引用（死链由质量门 7 拦截）
4. 在本 README 的归档说明中登记

---

## 已知例外

以下文件/目录因历史原因、平台约定或特殊用途保留原名称，不强制改为 snake_case：

| 类别 | 例外项 | 原因 |
|------|--------|------|
| 根级特殊文件 | `AGENTS.md`、`Cargo.lock`、`Cargo.toml`、`README.md`、`SUMMARY.md` | Agent/构建/mdbook 约定 |
| 配置目录 | `.cargo/`、`.github`、`.vscode/` | 工具/平台约定目录 |
| GitHub 模板 | `.github/ISSUE_TEMPLATE/` | GitHub  issue 模板目录名 |
| 日期风格报告 | `reports/`、各 `crates/*/reports/` | NAMING_CONVENTION 过渡期日期风格例外 |
| 归档目录 | `archive/`（含 `archive/2026/concept_archive/`，原 `concept/archive/` 已于 2026-07-12 迁入）、各 `*/archive/`（如 `crates/*/src/archive/`） | 只读历史归档 |
| Agent 工作区 | `.kimi/` 及其 `archive/` | Agent 会话与日期风格例外 |
| 虚拟环境 | `tools/kg_rag/.venv/` | 第三方依赖，不应提交 |
| 构建产物 | `target/`、`book/` | 生成目录 |
| 目录名 | `docs/15_rust_formal_engineering_system/`、`examples/resolver_v3_practice/{edge-bin,legacy-lib,modern-app}/`、`crates/c13_embedded/real-hardware-demos/`、`crates/c13_embedded/real-hardware-demos/{embassy-demo,rtic-demo}/` | 历史目录/示例项目目录，本次仅重命名文件 |
| 容器文件 | `crates/c06_async/deployment/docker/Dockerfile` | Dockerfile 标准命名 |

---

[返回项目主页](../README.md)

---

> **文档版本**: 3.0
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-12
> **状态**: ✅ P3-6 大扫除完成（97 脚本归档 one_off_2026/，links/ 目录建立，i18n/ 名实相符）
