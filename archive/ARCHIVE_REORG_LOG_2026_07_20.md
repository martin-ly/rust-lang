# Archive 重组迁移记录

- 重组日期: 2026-07-20
- 重组方案: 方案 A（双轨主题化）
- 执行阶段: 阶段 0–5（阶段 6 验证收尾同步进行）
- 生成时间: 2026-07-20T22:42:19.489501

## 统计摘要

- 重命名/移动 (R): 0
- 修改 (M): 3
- 新增 (??): 0
- 删除 (D): 0

## 阶段执行摘要

| 阶段 | 主要动作 | 状态 |
|------|----------|------|
| 0 | 备份当前结构、生成重叠扫描、冻结 archive | 完成 |
| 1 | 小目录归并：cargo_package_management、research_notes、2026/H1/Q2、content、reports | 完成 |
| 2 | 中等目录与镜像去重：2026/concept_archive、crates_reports、docs/ 全家、deprecated/temp 合并 | 完成 |
| 3 | 研究笔记与形式化资料：research_notes_2026_06_25 拆分 | 完成 |
| 4 | 超大独立集合：rust_ownership_decidability、backup_from_docs 移至 09_special_collections，创建 stub 入口 | 完成 |
| 5 | 索引重构：README、THEMATIC_INDEX、RELATIONSHIP_MAP 重写 | 完成 |

## 新建 Stub 文件

- `archive/05_formal_methods/01_ownership_decidability_collection/README.md`
- `archive/08_quality_audits/07_backup_from_docs_entry/README.md`
- `archive/06_ecosystem/08_crate_case_studies/README.md`

## 删除/合并的重复目录与文件

- `archive/docs/content/` — 与 `archive/content/` 合并，重复文件删除
- `archive/docs/deprecated/` — 与 `archive/08_quality_audits/deprecated/` 合并到 `05_formal_methods/04_coq_aeneas_deprecated/`
- `archive/docs/temp/` — 与 `archive/08_quality_audits/temp/` 合并到 `08_quality_audits/05_temp_quick_reference/`
- `archive/2026/` 空目录移除
- `archive/docs/` 空目录移除
- `archive/reports/` 空目录移除

## 超大独立集合迁移

- `archive/rust-ownership-decidability/` → `archive/09_special_collections/rust_ownership_decidability/`
- `archive/backup_from_docs/` → `archive/09_special_collections/backup_from_docs/`

## 新增/更新工具脚本

- `scripts/apply_archive_reorg.py` — 读取 CSV 映射执行 `git mv` 迁移
- `scripts/verify_archive_reorg.py` — 验证迁移后目录结构、死链、stub 合规、文件数量守恒

## 附录：Git 重命名/移动清单（前 200 条）

```text
```

