# 脚本工具

> **项目**: Rust 系统化学习项目
> **维护者**: Rust 学习项目团队
> **最后更新**: 2026-07-04
> **状态**: 清理中（Phase 3 C4），文件名规范化与 archive/ 边界已确认

---

## 目录结构

```
scripts/
├── README.md                          # 本文件
│
├── archive/                           # 归档脚本（按年份分类，只读）
│   └── 2026/
│       ├── dead_link_audit/           # 5 月死链审计调试系列（一次性）
│       ├── link_fix_iterations/       # 历史链接修复战役脚本
│       ├── compile_fail/              # compile_fail 验证旧版本
│       ├── knowledge_links/           # knowledge 模块链接旧脚本
│       ├── push_bump/                 # 批量推送/版本升级脚本
│       ├── one_off/                   # 其他一次性任务脚本
│       └── legacy_ps_batch/           # 过时 PowerShell / Batch 脚本
│
├── fixes/                             # 针对性问题修复工具
├── maintenance/                       # 项目结构维护工具
├── utils/                             # 通用辅助工具
├── templates/                         # 文档模板
└── i18n/                              # 国际化/双语标注工具
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
| `concept_audit.py` | 概念知识体系一致性检查 |
| `concept_consistency_auditor.py` | 跨文档概念对齐检查 |
| `cross_concept_diff.py` | 交叉概念 Diff |
| `docs_value_audit.py` | 文档价值分级审计 |
| `kb_auditor.py` | 知识库完整性检查 |
| `rust_version_tracker.py` | Rust 版本特性跟踪 |
| `version_fact_check.py` | 版本相关事实核查 |
| `lint_filenames.py` | 文件名 snake_case 命名检查 |
| `detect_content_overlap.py` | 检测 `concept/`、`knowledge/`、`docs/` 三轨内容相似度，生成去重报告 |
| `auto_dedup_redirect.py` | 对高相似度非 `concept/` 文件自动生成指向 `concept/` 权威来源的重定向页 |

### 🔗 链接检查与修复

| 脚本 | 功能 |
|------|------|
| `check_links.py` | 本地 Markdown 链接有效性检查 |
| `check_active_anchors.py` | 同文件锚点检查 |
| `check_all_concept_links_health.py` | concept 全量链接健康检查 |
| `check_github_links_health.py` | GitHub 链接健康检查 |
| `check_non_github_links_health.py` | 非 GitHub 外部链接健康检查 |
| `check_source_links_health_extended.py` | 来源链接健康检查（扩展版） |
| `fix_anchor_links_v3.py` | emoji/特殊字符锚点修复 |
| `fix_broken_anchors_v4.py` | 不存在标题的锚点降级修复 |
| `fix_dead_links_v3.py` | 死链批量修复 |
| `fix_dot_anchor_links.py` | 点号锚点修复 |

### 🌐 i18n 与双语标注

| 脚本 | 功能 |
|------|------|
| `add_bilingual_annotations.py` | 术语双语标注 |
| `check_i18n_metadata.py` | i18n 元数据检查 |
| `fix_concept_en_titles.py` | 概念页英文标题规范化 |
| `fix_concept_i18n_metadata_v2.py` | 概念页 i18n 元数据修复 |
| `list_i18n_metadata.py` | i18n 元数据列表 |
| `multilingual_alignment.py` | 多语言对齐 |

### 📝 生成工具

| 脚本 | 功能 |
|------|------|
| `add_sources.py` | 批量添加来源标注 |
| `add_missing_sources.py` | 补充缺失来源 |
| `auto_toc_generator.py` | 自动生成目录 |
| `auto_link_concepts.py` | 自动添加概念交叉链接 |
| `build_search_index.py` | 构建搜索索引 |
| `generate_crate_docs_boilerplate.py` | 批量生成 crate 文档样板 |
| `generate_en_skeleton.py` | 生成英文骨架 |
| `generate_summary.py` | 生成汇总 |
| `generate_version_features.py` | 生成版本特性表 |
| `extract_runnable_quizzes.py` | 提取可运行测验 |

### 🔧 清理与维护

| 脚本 | 功能 |
|------|------|
| `archive_deprecated_content.py` | 归档过时内容 |
| `batch_archive_c_class.py` | 批量归档 C 类文档 |
| `bulk_rename.py` | 批量重命名仓库路径为 snake_case 并更新内部引用 |
| `cleanup_mechanical_citations.py` | 清理机械引用 |
| `cleanup_title_embedded_citations.py` | 清理标题内嵌引用 |
| `fix_code_blocks.py` | 代码块标记修复 |
| `fix_templated_chains.py` | 模板链修复 |
| `quarterly_maintenance.py` | 季度维护编排 |
| `quarterly_sync.py` | 季度同步 |
| `quarterly_zombie_cleanup.py` | 季度僵尸内容清理 |

### 🏗️ 构建与测试

| 脚本 | 功能 |
|------|------|
| `cargo_build_optimized.sh` / `.ps1` | 优化编译 |
| `cargo_update_check.sh` / `.ps1` | 依赖更新检查 |
| `run_miri.sh` / `.bat` | Miri 测试 |
| `exercise_check.sh` / `.ps1` | 练习题评测 |
| `code_block_compiler.py` | 代码块编译验证 |
| `verify_compile_fail_v3.py` | `compile_fail` 代码块验证 |

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
| `batch_version_refresh.py` | 批量版本号刷新 |

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
python scripts/bulk_rename.py docs/LINK_CHECK_REPORT.md docs/link_check_report.md

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

---

## 子目录说明

### `fixes/`

针对性问题排查工具，例如：

- `find_cfg_gap.py` — 查找条件编译配置间隙
- `find_clippy_issue.py` — 定位 Clippy 警告问题
- `find_issue.py` — 通用问题定位

### `maintenance/`

项目结构维护工具，例如：

- `analyze_doc_structure.py` — 分析文档结构
- `auto_add_structure.py` — 自动添加文档结构
- `add_cross_references.py` — 批量添加 concept ↔ knowledge 交叉引用
- `cleanup_unused_aliases.py` — 清理未使用的别名
- `fix_final_broken_links.py` — 死链修复（维护版）
- `migrate_archive.py` — 归档迁移脚本：将旧目录移入 `archive/`

### `utils/`

通用辅助工具，例如：

- `enhance_placeholder_files.py` — 归档迁移脚本：增强占位文件或将 PENDING_ITEMS 归档到 `docs/archive/small_files/`

### `i18n/`

国际化专用工具，例如：

- `fix_rfc_links.py` — RFC 链接修复（i18n 版）

### `templates/`

docs/ crate 文档样板模板。

---

## 归档说明

`scripts/archive/2026/` 目录存放以下类型的历史脚本：

1. **迭代旧版本**：如 `fix_dead_links.py` / `v2` → `v3`（保留 v3，归档 v1/v2）
2. **一次性调试脚本**：如 `_debug_docs_links*.py`、`_analyze_*.py` 系列
3. **批量推送脚本**：如 `push_22.py` ~ `push_30.py`、`final_push.py` 等
4. **过时的平台脚本**：被 Python 跨平台脚本替代的 PowerShell/Batch 脚本
5. **一次性链接修复战役脚本**：`link_fix_iterations/` 下各轮次死链修复脚本

> ⚠️ 归档脚本不再维护，仅供参考或历史回溯。如需使用，请先检查活跃目录中是否有更新的替代版本。

---

## `archive/` 只读边界

1. **任何脚本不得向 `archive/` 写入新的活跃内容**。`archive/` 仅用于存放历史/归档资料，写入操作只能通过显式的**归档迁移脚本**完成。
2. 已标注为归档迁移脚本的工具包括：
   - `scripts/archive_file.py`
   - `scripts/archive_deprecated_content.py`
   - `scripts/maintenance/archive_research_notes_candidates.py`
   - `scripts/maintenance/migrate_archive.py`
   - `scripts/maintenance/fix_archive_c_class_links.py`
   - `scripts/quarterly_sync.py`
   - `scripts/roded_governance.py`
   - `scripts/utils/enhance_placeholder_files.py`
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

---

## 已知例外

以下文件/目录因历史原因、平台约定或特殊用途保留原名称，不强制改为 snake_case：

| 类别 | 例外项 | 原因 |
|------|--------|------|
| 根级特殊文件 | `AGENTS.md`、`Cargo.lock`、`Cargo.toml`、`README.md`、`SUMMARY.md` | Agent/构建/mdbook 约定 |
| 配置目录 | `.cargo/`、`.github/`、`.vscode/` | 工具/平台约定目录 |
| GitHub 模板 | `.github/ISSUE_TEMPLATE/` | GitHub  issue 模板目录名 |
| 日期风格报告 | `reports/`、各 `crates/*/reports/` | NAMING_CONVENTION 过渡期日期风格例外 |
| 归档目录 | `archive/`、各 `*/archive/`（如 `concept/archive/`、`crates/*/src/archive/`） | 只读历史归档 |
| Agent 工作区 | `.kimi/` 及其 `archive/` | Agent 会话与日期风格例外 |
| 虚拟环境 | `tools/kg_rag/.venv/` | 第三方依赖，不应提交 |
| 构建产物 | `target/`、`book/` | 生成目录 |
| 目录名 | `docs/rust-formal-engineering-system/`、`examples/resolver_v3_practice/{edge-bin,legacy-lib,modern-app}/`、`crates/c13_embedded/real-hardware-demos/`、`crates/c13_embedded/real-hardware-demos/{embassy-demo,rtic-demo}/` | 历史目录/示例项目目录，本次仅重命名文件 |
| 容器文件 | `crates/c06_async/deployment/docker/Dockerfile` | Dockerfile 标准命名 |

---

[返回项目主页](../README.md)

---

> **文档版本**: 2.2
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-07-04
> **状态**: 清理中（文件名规范化已完成，archive/ 边界已确认）
