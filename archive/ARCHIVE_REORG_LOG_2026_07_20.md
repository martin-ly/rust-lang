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
- `scripts/check_archive_integrity.py` — 修正 stub 检测逻辑，避免把普通 README 误判为 stub
- `tmp/fix_archive_dead_links.py` — 修复重组后活跃目录到 archive 的旧路径死链
- `tmp/fix_knowledge_stub_links.py` — 修复 knowledge/ 重定向 stub 的相对链接
- `tmp/fix_archive_internal_links.py` — 修复 archive/ 内部 Markdown 文件之间的断裂相对链接

## 阶段 6：清理、验证与收尾

### 死链修复

- 修复 `concept/` 中指向旧 archive 路径的 23 个死链（reports/2026_07、docs/content/academic 等）。
- 修复 `docs/` 和 `content/` 中指向旧 archive 路径的 201 个死链（docs/06_toolchain、docs/2026_03_reorganization、docs/2026_05_historical_docs、content/ecosystem/... 等）。
- 将 `docs/` / `content/` 中指向 `knowledge/` 目录的 9 个死链直接重定向到 `concept/` 权威页。
- 为 `concept/` 中指向缺失 `knowledge/` 文件目标的 13 个死链创建重定向 stub（12 个新文件），使 `knowledge/` 恢复导航入口。
- 修正上述 12 个 `knowledge/` stub 的相对链接，确保 stub 指向正确的权威页。

### 质量门验证（阶段 6 复测）

| 检查 | 结果 |
|------|------|
| `python scripts/kb_auditor.py --link-check` | ✅ 死链 0 / docs\|content\|knowledge 死链 0 |
| `python scripts/detect_content_overlap.py` | ✅ 通过（5 对 stub↔canonical 警告，exit 0） |
| `python scripts/check_naming_convention.py --strict` | ✅ ERROR=0 / WARN=54 |
| `python scripts/check_archive_integrity.py --strict` | ⚠️ 仍有 archive 内部历史链接断裂，详见备注 |

### 备注

- `check_archive_integrity.py` 的 stub 误报已修正：由 3038 条降至 14 条（均为历史文件中声明为 stub/archive redirect 但正文超长的真实条目）。
- archive 内部历史文件之间的交叉链接（~17K 条）断裂主要因目录主题化重组后相对路径变化；已通过 `tmp/fix_archive_internal_links.py` 尝试自动修复，剩余未解决项需人工复核。

## 附录：Git 重命名/移动清单（前 200 条）

```text
```
