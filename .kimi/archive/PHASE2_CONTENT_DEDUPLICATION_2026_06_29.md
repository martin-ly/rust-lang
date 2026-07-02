# 第二阶段执行清单：内容去重与命名规范

> **阶段**: 第二阶段（可持续改进计划 Phase 3）
> **目标**: 以 `concept/` 为唯一权威来源，合并/归档 concept/、knowledge/、docs/ 中的重复内容；分批清理不符合 snake_case 的文件名
> **来源**: `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`
> **开始日期**: 2026-06-29

---

## C1 内容重叠检测

- [x] 运行 `scripts/detect_content_overlap.py`，扫描 `concept/`、`knowledge/`、`docs/`。
- [x] 生成最新报告：`reports/CONTENT_OVERLAP_DETECTION_2026_06_29.md`
  - 扫描文件数：660
  - 相似度阈值：0.6
  - 潜在重复对：25
- [x] 复核相似度 ≥ 0.75 的文件对，对非 `concept/` 文件生成重定向（保留原文件路径，内容改为指向 `concept/` 权威来源的链接）。

### 高优先级重复对（相似度 ≥ 0.75）

| 相似度 | 建议动作 | 文件对 |
|:---|:---|:---|
| 1.00 | 合并到 `concept/`；`knowledge/` 改为重定向 | `concept/04_formal/36_tree_borrows_deep_dive.md` ↔ `knowledge/04_expert/miri/01_tree_borrows.md` |
| 0.75 | 合并到 `concept/`；`knowledge/` 改为摘要+链接 | `concept/06_ecosystem/45_compiler_internals.md` ↔ `knowledge/04_expert/01_compiler_internals.md` |
| 0.75 | 合并到 `concept/`；`knowledge/` 改为重定向 | `concept/07_future/19_rust_edition_preview.md` ↔ `knowledge/06_ecosystem/02_edition_2024.md` |
| 0.75 | 合并到 `concept/`；其余改为摘要/速查 | `concept/07_future/rust_1_96_stabilized.md` ↔ `knowledge/06_ecosystem/emerging/05_rust_1_96.md` ↔ `docs/06_toolchain/06_22_rust_1_96_features.md` |
| 0.75 | `docs/` 保留速查表，指向 concept/ 权威页 | `concept/07_future/rust_1_97_preview.md` ↔ `docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md` |
| 0.75 | 合并到 `concept/`；`docs/` 改为指南摘要 | `concept/07_future/13_unsafe_fields_preview.md` ↔ `docs/05_guides/05_unsafe_fields_preview.md` |
| 0.75 | 合并异步闭包内容到单一权威页 | `knowledge/03_advanced/async/02_async_closure.md` ↔ `knowledge/06_ecosystem/emerging/01_async_closures.md` ↔ `docs/03_guides/03_async_closures_deep_dive.md` |

### 中优先级重复对（0.60 ~ 0.74）

- [x] `concept/03_advanced/03_unsafe.md` / `knowledge/03_advanced/unsafe/04_unsafe_rust.md`
- [x] `concept/07_future/22_edition_guide.md` / `concept/07_future/23_rust_edition_guide.md` / `knowledge/06_ecosystem/02_edition_2024.md`
- [x] `concept/07_future/08_safety_tags_preview.md` / `docs/05_guides/05_safety_tags_guide.md`
- [x] `concept/07_future/19_rust_for_linux.md` / `docs/04_research/04_rust_for_linux.md`
- [x] Rust 1.95 相关：`knowledge/06_ecosystem/emerging/03_rust_1_95.md`、`04_rust_1_95_preview.md` / `docs/06_toolchain/06_14_rust_1_95_nightly_preview.md`

---

## C2 合并重复内容到 `concept/`

原则：

1. `concept/` 文件成为唯一权威来源。
2. 被合并的 `knowledge/` / `docs/` 文件保留文件名，内容改为：
   - 简短说明该主题已迁移到 `concept/xxx.md`
   - 提供 `> **权威来源**: [concept/xxx.md](...)` 链接
   - 删除重复正文
3. 若 `docs/` 文件是速查表/指南格式，可保留其格式但明确标注“本速查表对应 concept/ 权威页”。

任务列表：

- [x] 合并 Tree Borrows 内容（1.00 相似度）
  - `knowledge/04_expert/miri/01_tree_borrows.md` → `concept/04_formal/36_tree_borrows_deep_dive.md`
  - `docs/content/academic/10_tree_borrows_guide.md` → `concept/04_formal/36_tree_borrows_deep_dive.md`
- [x] 合并 Compiler Internals 内容
  - `knowledge/04_expert/01_compiler_internals.md` → `concept/06_ecosystem/45_compiler_internals.md`
- [x] 合并 Rust Edition 2024 内容
  - `knowledge/06_ecosystem/02_edition_2024.md` → `concept/07_future/19_rust_edition_preview.md`
- [x] 合并 Rust 1.96 稳定特性内容
  - `knowledge/06_ecosystem/emerging/05_rust_1_96.md` → `concept/07_future/rust_1_96_stabilized.md`
  - `docs/06_toolchain/06_22_rust_1_96_features.md` → `concept/07_future/rust_1_96_stabilized.md`
- [x] 合并 Unsafe Fields 内容
  - `docs/05_guides/05_unsafe_fields_preview.md` → `concept/07_future/13_unsafe_fields_preview.md`
- [x] 合并 Async Closures 内容
  - 权威页：`concept/03_advanced/24_async_closures.md`
  - `knowledge/03_advanced/async/02_async_closure.md` → 重定向页
  - `knowledge/06_ecosystem/emerging/01_async_closures.md` → 重定向页
  - `docs/03_guides/03_async_closures_deep_dive.md` → 重定向页
- [x] 处理 Rust 1.97 预览 + 速查表关系
  - `concept/07_future/rust_1_97_preview.md` 为权威页
  - `docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md` 保留速查表格式，添加权威来源链接
- [x] 处理 Unsafe Rust 相关内容
  - 权威页：`concept/03_advanced/03_unsafe.md`
  - `knowledge/03_advanced/unsafe/04_unsafe_rust.md` → 重定向页
  - `concept/03_advanced/12_unsafe_rust_patterns.md` 同步更新交叉引用
- [x] 处理 Rust for Linux 相关内容
  - 权威页：`concept/07_future/19_rust_for_linux.md`
  - `docs/04_research/04_rust_for_linux.md` → 重定向页
- [x] 处理 Rust 1.95 相关内容
  - 权威页：`docs/06_toolchain/06_14_rust_1_95_nightly_preview.md`
  - `knowledge/06_ecosystem/emerging/03_rust_1_95.md` → 重定向页
  - `knowledge/06_ecosystem/emerging/04_rust_1_95_preview.md` → 重定向页

---

## C3 分批重命名不符合规范的文件

依据 `NAMING_CONVENTION.md`：

- Markdown/脚本/目录名使用 `snake_case` 或 `number_prefix_snake_case`
- 禁止中文、空格、混合大小写（过渡期例外见下）

### 过渡期例外（暂不改动）

- `.kimi/` 中以日期风格命名的文件（如 `BCD_TRACK_STATUS_2026_06_28.md`）
- `.github/ISSUE_TEMPLATE/`（GitHub 强制模板目录名）
- 第三方虚拟环境（`tools/kg_rag/.venv/`）
- `reports/` 中日期风格文件
- `archive/` 下历史归档的中文/大写文件名

### 本次已处理

- [x] `concept/00_meta/` 大写文件名统一为 snake_case
  - `BILINGUAL_TEMPLATE.md` → `bilingual_template.md`
  - `LEARNING_MVP_PATH.md` → `learning_mvp_path.md`（合并根目录重复文件，统一入口）
  - `LEARNING_MVP_PATH_EN.md` → `concept/00_meta/learning_mvp_path_en.md`
  - `placeholders/placeholder-generic.md` → `placeholders/placeholder_generic.md`
- [x] `concept/sources/` 大写文件名统一为 snake_case
  - `RFC_INDEX.md` → `rfc_index.md`
  - `THEOREM_TIER_SPEC.md` → `theorem_tier_spec.md`
- [x] `.github/workflows/` 中 11 个 hyphen 文件名统一为 snake_case
  - `docs-preview.yml` → `docs_preview.yml`
  - `docs-quality.yml` → `docs_quality.yml`
  - `link-check.yml` → `link_check.yml`
  - `mdbook-pages.yml` → `mdbook_pages.yml`
  - `pr-checks.yml` → `pr_checks.yml`
  - `rust-version-tracker.yml` → `rust_version_tracker.yml`
  - `rust-version-tracking.yml` → `rust_version_tracking.yml`
  - `security-audit.yml` → `security_audit.yml`
  - `semver-checks.yml` → `semver_checks.yml`
  - `weekly-dependency-check.yml` → `weekly_dependency_check.yml`
  - `weekly-deps.yml` → `weekly_deps.yml`
- [x] `.cargo/audit-db..lock` 已删除（空文件，多余点号）
- [x] 新增 `scripts/bulk_rename.py` 批量重命名与引用更新工具
- [x] `scripts/lint_filenames.py` 调整：默认只检查新增/重命名文件（`--diff-filter=ACR`），避免内容-only 修改误报

### 待后续批次处理

- [ ] `docs/` 与 `knowledge/` 中历史上传的中文/大写文件名（建议按主题批次迁移或归档）
- [ ] `concept/archive/` 中历史规划文件大写名称

---

## C4 更新脚本与文档说明

- [x] `scripts/README.md` 已包含 `detect_content_overlap.py` / `auto_dedup_redirect.py` / `lint_filenames.py` 说明
- [ ] 在 `scripts/README.md` 中补充 `bulk_rename.py` 的使用说明
- [ ] 在 `ARCHIVE_POLICY.md` 中补充“内容去重后旧文件如何归档”的示例
- [ ] 更新 `CONTRIBUTING.md`，说明新增概念文件应以 `concept/` 为权威来源

---

## 验收标准

第二阶段完成时，仓库应满足：

1. 相似度 ≥ 0.75 的重复对全部处理完毕（合并、归档或明确引用关系）。
2. `concept/` 外不再存在大段复制自 `concept/` 的内容。
3. 新增/修改文件命名 100% 符合 `NAMING_CONVENTION.md`。
4. 所有迁移后的重定向文件链接可达，`kb_auditor.py` 死链为 0。

---

*本清单随执行进度更新，完成后进入第三阶段（国际化与可持续性）。*
