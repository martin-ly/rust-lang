# Rust 知识库重复内容合并计划

> **状态**: ✅ 已完成执行（2026-06-21）
> **执行方式**: 合并独特内容 → 删除重复文件 / 归档历史文件 / 替换为重定向；链接检查与修复已完成（31 处破损链接已修复）。

- **生成日期**: 2026-06-21
- **执行日期**: 2026-06-21
- **来源报告**: `reports/CONTENT_OVERLAP_DETECTION_2026_06_09.md`
- **处理范围**: 相似度 ≥ 0.9 的文件对
- **总对数**: 16 对（含 8 对 exact duplicates，相似度 1.00）

---

## 1. 执行原则与顺序

**canonical 选择规则**（按优先级）：

1. 轨道优先级：`concept/` > `knowledge/` > `docs/` > `content/`
2. 内容完整性：行数/字节数更大、示例更全、引用更规范
3. 新鲜度：`最后更新` 日期更新者优先
4. 当轨道优先级与内容完整性冲突时，以内容保留为首要目标，并在 Notes 中说明

**涉及多对的文件需集中处理**：

- `concept/03_advanced/03_unsafe.md` 出现在 5 对中：先合并 `docs/05_guides/05_unsafe_rust_guide.md` 的独特内容，再归档/删除其余 4 个重复文件。
- `concept/07_future/19_rust_for_linux.md` 出现在 3 对中：先合并 `docs/06_toolchain/06_rust_for_linux_tooling_guide.md` 的工具链细节，再将 `docs/03_guides/03_rust_for_linux_guide.md` 替换为重定向，最后归档 `docs/rust-ownership-decidability/extensions/rust-for-linux.md`。
- `concept/07_future/19_rust_edition_preview.md` 与 `knowledge/06_ecosystem/02_edition_2024.md`、`docs/05_guides/06_rust_2024_edition_migration_guide.md` 形成三角重复：以 `knowledge/06_ecosystem/02_edition_2024.md` 为 canonical，合并其余两者的独特内容后删除。

**action 说明**：

- `merge_and_delete`: 将非 canonical 文件中的独特内容并入 canonical 文件，然后删除重复文件。
- `replace_with_redirect`: 删除重复文件，原地留下仅含重定向说明的小文件。
- `archive`: 将重复文件移动到 `archive/deprecated/` 目录，保留历史痕迹。

---

## 2. 重复对合并表

| 相似度 | 文件 A | 文件 B | Keep | Action | Notes |
|:---|:---|:---|:---|:---|:---|
| 1.00 | `concept/03_advanced/13_inline_assembly.md` | `knowledge/03_advanced/unsafe/02_inline_asm.md` | `concept/03_advanced/13_inline_assembly.md` | `replace_with_redirect` | concept 版 764 行，含平台差异矩阵、s390x 向量寄存器、4 个嵌入式测验；knowledge 版 434 行，自标记为摘要索引并指向 concept。直接替换 knowledge 为重定向。 |
| 1.00 | `concept/07_future/rust_1_97_preview.md` | `knowledge/06_ecosystem/emerging/06_rust_1_97_preview.md` | `concept/07_future/rust_1_97_preview.md` | `replace_with_redirect` | concept 版 730 行，完整跟踪 nightly 1.98.0；knowledge 版仅 31 行，明确为 concept 摘要索引。 |
| 1.00 | `concept/03_advanced/03_unsafe.md` | `docs/05_guides/05_unsafe_rust_guide.md` | `concept/03_advanced/03_unsafe.md` | `merge_and_delete` | concept 版 3063 行，最权威完整；docs 版 1126 行，侧重工程实践与 Rustonomicon 逐章对标。需将 docs 版中 Rustonomicon 对标表、完整代码示例等独特内容并入 concept 后删除。 |
| 1.00 | `concept/03_advanced/03_unsafe.md` | `docs/research_notes/formal_methods/10_unsafe_concept_mindmap.md` | `concept/03_advanced/03_unsafe.md` | `archive` | docs 版已自标记为“归档级/历史研究材料”，内容被 concept 完全覆盖，且目录结构指向 knowledge/concept。直接归档。 |
| 1.00 | `concept/03_advanced/03_unsafe.md` | `docs/research_notes/formal_methods/10_unsafe_safety_proof_tree.md` | `concept/03_advanced/03_unsafe.md` | `archive` | 同上，docs 版为历史安全证明树，内容已被 concept 覆盖，自标记为历史研究材料。归档。 |
| 1.00 | `concept/03_advanced/03_unsafe.md` | `docs/rust-ownership-decidability/17-unsafe-rust/01-intro.md` | `concept/03_advanced/03_unsafe.md` | `archive` | docs 版顶部已有 `ARCHIVED` 横幅，声明与 concept 完全重复（相似度 1.00），归档日期 2026-06-09。归档。 |
| 1.00 | `concept/03_advanced/03_unsafe.md` | `docs/rust-ownership-decidability/extensions/unsafe-rust-patterns.md` | `concept/03_advanced/03_unsafe.md` | `archive` | docs 版顶部已有 `ARCHIVED` 横幅，声明内容被 concept/03_unsafe.md 与 concept/03_advanced/12_unsafe_rust_patterns.md 完全覆盖。归档。 |
| 1.00 | `concept/07_future/19_rust_for_linux.md` | `docs/rust-ownership-decidability/extensions/rust-for-linux.md` | `concept/07_future/19_rust_for_linux.md` | `archive` | docs 版顶部已有 `ARCHIVED` 横幅，声明与 concept 完全重复，归档日期 2026-06-09。concept 版更新（2026-06-20）、更完整。归档。 |
| 1.00 | `knowledge/04_expert/academic/01_coq_formalization_guide.md` | `docs/content/academic/10_coq_formalization_guide.md` | `knowledge/04_expert/academic/01_coq_formalization_guide.md` | `replace_with_redirect` | knowledge 版 661 行，更新（2026-05-19）、含完整 Coq/Iris 示例与 RustBelt 引用；docs 版 438 行，顶部已说明“内容已整合至知识轨道，最新内容请参阅 knowledge 版”。 |
| 0.90 | `concept/07_future/19_rust_edition_preview.md` | `knowledge/06_ecosystem/02_edition_2024.md` | `knowledge/06_ecosystem/02_edition_2024.md` | `merge_and_delete` | 轨道优先级倾向 concept，但 concept 版仅 143 行（预览 stub），而 knowledge 版 632 行、内容完整（含迁移步骤、`gen` 关键字、陷阱矩阵、权威来源标注）。以内容保留优先，将 concept 版独有的 5 个嵌入式测验与认知路径并入 knowledge 后删除 concept 版。 |
| 0.90 | `concept/07_future/19_rust_edition_preview.md` | `docs/05_guides/06_rust_2024_edition_migration_guide.md` | `docs/05_guides/06_rust_2024_edition_migration_guide.md` | `replace_with_redirect` | docs 版 613 行，聚焦迁移实操与边界测试；concept 版为短预览。因 pair 9 已将 concept 版删除，本对实际执行：将 docs 版中“决策树”“陷阱 1-5”等迁移专属内容并入 `knowledge/06_ecosystem/02_edition_2024.md` 后删除 docs 版（见 pair 14）。此处记为对 concept 的 redirect。 |
| 0.90 | `concept/07_future/19_rust_edition_preview.md` | `docs/rust-ownership-decidability/16-program-semantics/rust-194-features/05-edition-2024-semantics.md` | `concept/07_future/19_rust_edition_preview.md` | `archive` | docs 版 911 行，形式化语义，已自标记为历史研究材料并指向 concept/07_future/23_rust_edition_guide.md 与 knowledge/06_ecosystem/02_edition_2024.md。由于 concept 预览版（pair 9/10）也将被移除，最终 canonical 为 knowledge 版；docs 版直接归档。 |
| 0.90 | `concept/07_future/19_rust_for_linux.md` | `docs/03_guides/03_rust_for_linux_guide.md` | `concept/07_future/19_rust_for_linux.md` | `replace_with_redirect` | concept 版 809 行，更新（2026-06-20），含采用状态矩阵、边界测试；docs 版 330 行，自身指向 concept 获取完整论述。替换 docs 版为重定向。 |
| 0.90 | `concept/07_future/19_rust_for_linux.md` | `docs/06_toolchain/06_rust_for_linux_tooling_guide.md` | `concept/07_future/19_rust_for_linux.md` | `merge_and_delete` | docs 版 351 行，专注工具链需求、裸机目标、`panic_handler`、`alloc` 配置等独特内容。将这些内容并入 concept 版“技术细节/工具链”章节后删除 docs 版。 |
| 0.90 | `knowledge/06_ecosystem/02_edition_2024.md` | `docs/05_guides/06_rust_2024_edition_migration_guide.md` | `knowledge/06_ecosystem/02_edition_2024.md` | `merge_and_delete` | 以 knowledge 版为 Edition 2024 集群 canonical。将 docs 版的迁移前准备、分步迁移策略、六大核心变更详解、决策树、边界测试等实操内容并入 knowledge 后删除 docs 版。 |
| 0.90 | `knowledge/06_ecosystem/02_edition_2024.md` | `docs/rust-ownership-decidability/16-program-semantics/rust-194-features/05-edition-2024-semantics.md` | `knowledge/06_ecosystem/02_edition_2024.md` | `archive` | docs 版为形式化/历史材料，已自标记归档，直接归档即可。 |

---

## 3. 重定向文件模板

对于 `replace_with_redirect` 的文件，替换后的内容建议使用如下模板：

```markdown
> **内容已迁移**
>
> 本文档内容与以下 canonical 文件重复，已迁移至：
> [相对路径到 canonical 文件](../path/to/canonical.md)
>
> 迁移日期: 2026-06-21
> 原文件路径: `原文件路径`
```

---

## 4. 建议的合并执行顺序

1. **Unsafe 集群**（涉及 `concept/03_advanced/03_unsafe.md`）
   - 合并 `docs/05_guides/05_unsafe_rust_guide.md` → `concept/03_advanced/03_unsafe.md`
   - 归档其余 4 个 docs/research_notes/docs-rod 重复文件
   - 删除 `docs/05_guides/05_unsafe_rust_guide.md`

2. **Rust for Linux 集群**（涉及 `concept/07_future/19_rust_for_linux.md`）
   - 合并 `docs/06_toolchain/06_rust_for_linux_tooling_guide.md` → `concept/07_future/19_rust_for_linux.md`
   - 将 `docs/03_guides/03_rust_for_linux_guide.md` 替换为重定向
   - 归档 `docs/rust-ownership-decidability/extensions/rust-for-linux.md`

3. **Edition 2024 集群**（涉及 `knowledge/06_ecosystem/02_edition_2024.md`）
   - 合并 `concept/07_future/19_rust_edition_preview.md` 的独特测验 → `knowledge/06_ecosystem/02_edition_2024.md`
   - 合并 `docs/05_guides/06_rust_2024_edition_migration_guide.md` 的迁移实操内容 → `knowledge/06_ecosystem/02_edition_2024.md`
   - 归档 `docs/rust-ownership-decidability/16-program-semantics/rust-194-features/05-edition-2024-semantics.md`
   - 删除 `concept/07_future/19_rust_edition_preview.md` 与 `docs/05_guides/06_rust_2024_edition_migration_guide.md`

4. **Inline Assembly**
   - 将 `knowledge/03_advanced/unsafe/02_inline_asm.md` 替换为重定向

5. **Rust 1.97 Preview**
   - 将 `knowledge/06_ecosystem/emerging/06_rust_1_97_preview.md` 替换为重定向

6. **Coq 形式化验证**
   - 将 `docs/content/academic/10_coq_formalization_guide.md` 替换为重定向

---

## 5. 风险与注意事项

- `concept/03_advanced/03_unsafe.md` 是多个重复对的中心节点，合并前建议先备份。
- `concept/07_future/19_rust_edition_preview.md` 与更完整的 `concept/07_future/22_edition_guide.md`、`concept/07_future/23_rust_edition_guide.md` 不同，本计划仅处理其重复问题；如项目希望保留 concept 轨道，可考虑将 knowledge 版内容反向合并到 `concept/07_future/23_rust_edition_guide.md`。
- 所有 `archive` 操作建议先确认 `archive/deprecated/` 目录结构与命名规范，避免覆盖。
- 合并后需运行链接检查脚本，确保被删除/归档文件的内部引用已更新。
