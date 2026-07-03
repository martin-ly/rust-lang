> **归档说明**: 本文档为历史归档文件，内容可能已过时。最新信息请参考对应活跃文档。

# 📦 文档归档索引

> **分级**: [C]
本索引记录所有归档文档的原位置、归档原因和归档日期。

## 归档目录结构
>
> **[来源: Rust Official Docs]**

```text
archive/docs/
├── 06_toolchain/                # 历史工具链文档
├── 2026_03_reorganization/      # 2026 年 3 月重组历史文档
├── 2026_05_historical_docs/     # 2026 年 5 月历史文档
├── c_class_audit_2026_06_08/    # 2026-06-08 C 类审计产物
├── content/                     # 原 content/ 专题历史文档
├── deprecated/                  # Coq/Aeneas 形式化计划（已废弃）
├── duplicate_content_2026_06_08/# 重复内容审计备份
├── reports/                     # 历史报告
├── rust-ownership-chinese/      # 中文所有权资料（已整合）
├── temp/                        # 临时文件
└── version_reports/             # Rust 版本验证报告
```

## 归档清单
>
> **[来源: Rust Official Docs]**

### 1. deprecated_20260318/ (73 文件)
>
> **[来源: Rust Official Docs]**

| 原文件 | 归档原因 | 归档日期 |
|--------|---------|----------|
| 00_rust_2024_edition_learning_impact.md | 内容已整合到 06_toolchain | 2026-03-18 |
| EDITION_2024_COMPREHENSIVE_GUIDE.md | 内容已整合到 06_toolchain | 2026-03-18 |
| RUST_194_MIGRATION_GUIDE.md | 内容已整合到 05_guides | 2026-03-18 |
| ... | ... | ... |

**说明**: 此目录包含 2026年3月重组过程中识别出的过时文档。这些文档的内容已被整合到新的目录结构中。

### 2. deprecated/ (5 文件)

| 原文件 | 归档原因 | 状态 |
|--------|---------|------|
| AENEAS_INTEGRATION_PLAN.md | 形式化验证计划，待评估 | 评估中 |
| COQ_ISABELLE_PROOF_SCAFFOLDING.md | 证明脚手架，待评估 | 评估中 |
| COQ_OF_RUST_INTEGRATION_PLAN.md | Coq 集成计划，待评估 | 评估中 |
| coq_skeleton/README.md | Coq 骨架项目 | 评估中 |
| README.md | 过时说明 | 已归档 |

**说明**: 此目录包含形式化验证相关的计划文档。需要评估是否有价值保留或完全删除。

### 3. temp/ (8 文件)

| 原文件 | 归档原因 | 建议操作 |
|--------|---------|----------|
| QUICK_REFERENCE.md | 临时参考，内容已迁移 | 可删除 |
| QUICK_START_KNOWLEDGE_SYSTEM.md | 临时启动指南 | 可删除 |
| ... | ... | ... |

**说明**: 临时文件，确认内容已迁移后可安全删除。

### 4. rust-ownership-chinese/ (40+ 文件)

| 原文件 | 归档原因 | 说明 |
|--------|---------|------|
| rust_ownership_semantics_complete_analysis.md | 中文所有权分析 | 已整合到 rust-ownership-decidability |
| 扩展主题：async-await形式语义补充.md | 中文扩展内容 | 已整合 |
| ... | ... | ... |

**说明**: 中文所有权文档已完成整合；原 `docs/rust-ownership-decidability/` 整体迁移至 `archive/rust-ownership-decidability/`。

## 如何恢复归档文档

如需恢复某个归档文档：

1. 在此索引中找到文档位置
2. 从归档目录复制回原位置或新位置
3. 更新相关链接和索引
4. 在本索引中标注"已恢复"

## 定期清理计划

- **每季度**: 评估 deprecated/ 目录内容
- **每半年**: 清理 temp/ 目录
- **每年**: 审查所有归档内容，考虑永久删除

---

**最后更新**: 2026-03-19
