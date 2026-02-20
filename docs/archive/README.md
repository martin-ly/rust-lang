# 归档文件说明

> **创建日期**: 2025-11-15
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已归档
> **归档原因**: 清理与主题子主题不相关的文件，保持项目结构清晰
> **用途**: 过程性报告、历史版本文档；历史可查、主目录简洁
> **判定目标**: 历史可查、主目录简洁
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.8

---

## 📋 归档目录结构

```text
docs/archive/
├── README.md                    # 本说明文件
├── root_completion_reports/     # 根目录完成度/状态类报告（2026-01-27 全面归档）⭐
├── legacy_root_archive/         # 原根目录 archive/ 迁入（2026-01-27 全面归档）⭐ NEW
├── spell_check/                 # 拼写检查相关文件
├── status/                      # 项目状态报告
├── updates/                     # 更新报告
├── reports/                     # 各种总结和报告
└── temp/                        # 临时文件和个人文件
```

---

## 📁 各目录说明

### root_completion_reports/ - 根目录完成度与状态报告（2026-01-27）

与**项目主题（Rust 学习资源）**无直接关系的完成度、推进、周报类文件，已统一归档到此目录，便于根目录只保留核心文档与配置。

**归档范围**：原位于仓库根目录的、以完成度/状态/周报等为主题的 `.md` 报告，例如：

- `FINAL_*`、`PUSH_TO_100_*`、`PROGRESS_*`、`PROJECT_*_COMPLETE*`
- `WEEK1_*`、`WEEK2_*`、`ULTIMATE_*`、`TASK_PROGRESS_*`
- `TEST_COVERAGE_*`、`TEST_CASES_*`、`FUZZ_TESTING_*`
- `MODULE_FEATURES_*`、`RESEARCH_TASKS_*`、`COMPLETION_*`、`ACHIEVEMENT_*` 等

**保留在根目录的文档**：`README.md`、`README.en.md`、`PROJECT_STRUCTURE.md`、`MIGRATION_GUIDE_1.91.1_TO_1.92.0.md`。

**说明**：归档副本位于 `docs/archive/root_completion_reports/`。**2026-01-27 全面归档**：根目录中与主题无关的完成度/推进/周报类 .md 已全部复制到本目录并从根目录删除；`docs/research_notes/` 中的完成度类报告（`COMPLETION_SUMMARY_2025_12_25.md`、`COMPREHENSIVE_PROGRESS_REPORT_2025_12_25.md`、`FINAL_COMPLETION_STATUS_2025_12_25.md`、`ULTIMATE_COMPLETION_REPORT_2025_12_25.md`）已一并迁入本目录。完成度与 100% 认定以 [FINAL_PUSH_COMPLETE_SUMMARY_2026_01_27.md](root_completion_reports/FINAL_PUSH_COMPLETE_SUMMARY_2026_01_27.md) 为准。

---

### legacy_root_archive/ - 原根目录 archive/（2026-01-27 全面归档）

原位于仓库根目录的 `archive/` 文件夹（含 `reports/2025-12-25/` 等完成度/任务/状态类报告）已整体迁入本目录，根目录不再保留 `archive/`。

---

### spell_check/ - 拼写检查相关文件

包含所有拼写检查配置和完成报告：

- `SPELL_CHECK_FINAL_COMPLETION.md` - 拼写检查最终完成报告
- `SPELL_CHECK_CONFIGURATION.md` - 拼写检查配置说明
- `SPELL_CHECK_SUPPLEMENT_REPORT.md` - 拼写检查补充报告
- `SPELL_CHECK_SETUP_SUMMARY.md` - 拼写检查设置总结

### status/ - 项目状态报告

包含项目状态和质量报告：

- `PROJECT_STATUS_2025_10_20.md` - 项目状态报告
- `PROJECT_QUALITY_REPORT_2025_10_25.md` - 项目质量报告

### updates/ - 更新报告

包含各种更新和完成报告：

- `ALL_FILES_UPDATE_COMPLETE_2025_11_15.md` - 所有文件更新完成报告
- `FINAL_UPDATE_SUMMARY_2025_11_15.md` - 最终更新总结
- `RESEARCH_NOTES_UPDATE_SUMMARY_2025_11_15.md` - 研究笔记更新总结
- `THREE_FOLDERS_UPDATE_COMPLETE_2025_11_15.md` - 三个文件夹更新完成
- `THREE_FOLDERS_UPDATE_SUMMARY_2025_11_15.md` - 三个文件夹更新总结
- `FORMAL_SYSTEM_UPDATE_2025_11_15.md` - 形式化系统更新
- `RESEARCH_NOTES_UPDATE_2025_11_15.md` - 研究笔记更新
- `QUICK_REFERENCE_UPDATE_2025_11_15.md` - 快速参考更新
- `DOCUMENTATION_UPDATE_COMPLETE_2025_11_15.md` - 文档更新完成

### reports/ - 各种总结和报告

包含文档标准化、修复报告等：

- `CRATES_DOCUMENTATION_CONSOLIDATION_SUMMARY_2025_11_15.md` - Crates 文档整合总结
- `CRATES_DOCUMENTATION_FINAL_REPORT_2025_11_15.md` - Crates 文档最终报告
- `CRATES_DOCUMENTATION_REVIEW_2025_11_15.md` - Crates 文档审查报告
- `CRATES_DOCUMENTATION_STANDARD_2025_11_15.md` - Crates 文档标准规范
- `DUPLICATE_TOC_FIX_REPORT_2025_11_15.md` - 重复目录修复报告
- `CARGO_WORKSPACE_PROFILE_GUIDE.md` - Cargo 工作空间配置文件指南
- `RUST_1.91_FEATURES_COMPREHENSIVE.md` - Rust 1.91 特性综合说明

### temp/ - 临时文件和个人文件

包含临时文件、个人索引等：

- `MY_PERSONAL_INDEX.md` - 个人索引文件
- `QUICK_START_KNOWLEDGE_SYSTEM.md` - 快速启动知识系统
- `REFERENCE_VALIDITY_MODEL_ALIGNMENT.md` - 引用有效性模型对齐
- `rust_logic_view.md` - Rust 逻辑视图
- `QUICK_REFERENCE.md` - 快速参考（根目录版本）
- `QUICK_FIX_README.md` - 快速修复说明
- `QUICK_START_SPELL_CHECK.md` - 快速启动拼写检查
- `swap/` - 临时交换目录（如果存在）

---

## 🎯 归档原则

### 归档的文件类型

1. **临时报告文件** - 各种更新、完成、总结报告
2. **状态文件** - 项目状态、质量报告
3. **配置说明** - 工具配置和使用说明
4. **个人文件** - 个人索引和临时笔记
5. **重复文件** - 与核心文档重复的内容

### 保留的核心文件

以下文件保留在主目录中，因为它们是项目核心内容：

- `docs/README.md` - 主文档索引
- `docs/quick_reference/` - 快速参考目录
- `docs/research_notes/` - 研究笔记目录
- `docs/rust-formal-engineering-system/` - 形式化工程系统
- `docs/toolchain/` - 工具链文档
- `crates/` - 所有学习模块
- `README.md` - 项目主 README

---

## 📊 归档统计

- **归档文件总数**: 约 30+ 个文件（不含 root_completion_reports）+ root_completion_reports 内约 87 个
- **归档目录数**: 6 个分类目录（含 root_completion_reports）
- **归档日期**: 2025-11-15；root_completion_reports 于 2026-01-27 新增

---

## 🔍 查找归档文件

如果需要查找归档的文件，可以：

1. 查看本 README 了解文件分类
2. 使用文件搜索工具在 `docs/archive/` 目录中搜索
3. 查看各子目录的 README（如果有）

---

## ⚠️ 注意事项

1. **不要删除归档文件** - 这些文件可能包含有用的历史信息
2. **定期清理** - 如果归档文件过多，可以考虑进一步整理
3. **更新链接** - 如果有外部链接指向归档文件，需要更新

---

**最后更新**: 2026-01-27
