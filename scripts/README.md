# 脚本工具

> **项目**: Rust系统化学习项目
> **维护者**: Rust学习项目团队
> **最后更新**: 2026-06-02

---

## 目录结构

```
scripts/
├── README.md                          # 本文件
│
├── 【根目录：活跃脚本】                # 当前维护的核心工具
│
├── archive/                           # 归档脚本（按年份分类）
│   └── 2026/
│       ├── dead_link_audit/           # 5月死链审计调试系列（一次性）
│       ├── link_fix_iterations/       # 链接修复迭代旧版本
│       ├── compile_fail/              # compile_fail 验证旧版本
│       ├── knowledge_links/           # knowledge 模块链接旧脚本
│       ├── push_bump/                 # 批量推送/版本升级脚本
│       ├── one_off/                   # 其他一次性任务脚本
│       └── legacy_ps_batch/           # 过时 PowerShell / Batch 脚本
│
├── fixes/                             # 针对性问题修复工具
├── maintenance/                       # 项目结构维护工具
└── utils/                             # 通用辅助工具
```

---

## 活跃脚本（根目录）

### 🔍 审计与检查

| 脚本 | 功能 | 说明 |
|------|------|------|
| `audit_code_blocks.py` | 代码块标记审计 | 为不完整片段添加 `ignore` 标记 |
| `audit_stable_apis.py` | 稳定 API 审计 | 检查文档中 API 稳定性标注 |
| `concept_audit.py` | 概念知识体系审计 | 概念一致性自动化检查 |
| `concept_consistency_auditor.py` | 概念一致性审计 | 跨文档概念对齐检查 |
| `kb_auditor.py` | 知识库审计 | 知识库完整性检查 |
| `cross_concept_diff.py` | 交叉概念 Diff | 对比不同文档中的概念描述 |
| `rust_version_tracker.py` | Rust 版本跟踪 | 监控 Rust 版本特性更新 |
| `version_fact_check.py` | 版本事实核查 | 验证版本相关陈述的准确性 |

### 🔗 链接检查与修复

| 脚本 | 功能 | 说明 |
|------|------|------|
| `check_links.py` | 链接有效性检查 | 跨平台链接检查（Python） |
| `fix_anchor_links_v3.py` | 锚点链接修复 | 批量修复 Markdown 损坏锚点（v3 最新版） |
| `fix_broken_anchors_v4.py` | 损坏锚点降级修复 | 将指向不存在标题的锚点降级为纯文本 |
| `check_active_anchors.py` | 活跃内容锚点检查 | 检查 concept/knowledge/book 中的同文件锚点 |
| `fix_code_blocks.py` | 代码块修复 | 修复不完整代码块标记 |
| `fix_compile_failures.py` | 编译失败修复 | 批量修复编译失败的代码块标记 |
| `fix_readme_navigation.py` | README 导航修复 | 修复 README 目录导航 |

### 📝 生成工具

| 脚本 | 功能 | 说明 |
|------|------|------|
| `add_sources.py` | 批量添加来源标注 | 为文档添加权威来源引用 |
| `auto_toc_generator.py` | 自动生成目录 | 基于目录结构生成 SUMMARY.md |
| `auto_categorize_blocks.py` | 代码块自动分类 | 为编译失败代码块建议正确标记 |
| `build_search_index.py` | 构建搜索索引 | 基于 concept_kb.json 构建索引 |
| `generate_summary.py` | 生成汇总 | 自动生成文档汇总 |
| `generate_version_features.py` | 生成版本特性表 | 按 Rust 版本整理特性 |
| `code_block_compiler.py` | 代码块编译验证 | 提取并测试 Markdown 中的 Rust 代码 |

### 🔧 清理与维护

| 脚本 | 功能 | 说明 |
|------|------|------|
| `archive_deprecated_content.py` | 归档过时内容 | 清理不再维护的文档到 archive |
| `cleanup_mechanical_citations.py` | 清理机械引用 | 移除冗余的机械式引用标记 |
| `cleanup_title_embedded_citations.py` | 清理标题内嵌引用 | 清理嵌入标题的引用 |

### 🏗️ 构建与测试

| 脚本 | 功能 | 说明 |
|------|------|------|
| `cargo-build-optimized.sh` / `.ps1` | 优化编译 | Cargo 编译优化（Linux/macOS / Windows） |
| `cargo-update-check.sh` / `.ps1` | 依赖更新检查 | 检查并报告依赖更新 |
| `run-miri.sh` / `.bat` | Miri 测试 | 运行 Miri 检测未定义行为 |
| `exercise-check.sh` / `.ps1` | 练习题评测 | Rust 练习题自动化评测 |
| `verify_compile_fail_v3.py` | compile_fail 验证 | 验证 `compile_fail` 代码块确实编译失败 |

### 📋 日常工具

| 脚本 | 功能 | 说明 |
|------|------|------|
| `check_dependencies.sh` / `.bat` | 依赖检查 | 检查项目依赖完整性 |
| `daily_checklist.sh` / `.ps1` | 每日检查清单 | 日常维护任务清单 |

---

## 子目录说明

### `fixes/`

针对性问题排查工具：

- `find_cfg_gap.py` — 查找条件编译配置间隙
- `find_clippy_issue.py` — 定位 Clippy 警告问题
- `find_issue.py` — 通用问题定位

### `maintenance/`

项目结构维护工具：

- `analyze_doc_structure.py` — 分析文档结构
- `auto_add_structure.py` — 自动添加文档结构
- `add_cross_references.py` — 批量添加 concept ↔ knowledge 交叉引用
- `cleanup_unused_aliases.py` — 清理未使用的别名

### `utils/`

通用辅助工具：

- `enhance_placeholder_files.py` — 增强占位文件内容

---

## 归档说明

`archive/2026/` 目录存放以下类型的历史脚本：

1. **迭代旧版本**：如 `fix_anchor_links.py` → `v2` → `v3`（保留 v3，归档 v1/v2）
2. **一次性调试脚本**：如 `_debug_docs_links*.py`、`_analyze_*.py` 系列
3. **批量推送脚本**：如 `push_22.py` ~ `push_30.py`、`final_push.py` 等
4. **过时的平台脚本**：被 Python 跨平台脚本替代的 PowerShell/Batch 脚本

> ⚠️ 归档脚本不再维护，仅供参考或历史回溯。如需使用，请先检查活跃目录中是否有更新的替代版本。

---

## 使用规范

### 添加新脚本

1. **命名规范**：
   - 使用 `snake_case` 或 `kebab-case`
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

[返回项目主页](../README.md)

---

> **文档版本**: 2.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-06-02
> **状态**: ✅ 脚本全面清理归档完成
