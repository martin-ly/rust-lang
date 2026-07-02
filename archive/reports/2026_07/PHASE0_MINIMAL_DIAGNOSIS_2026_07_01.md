# Phase 0 最小诊断报告

> **诊断日期**: 2026-07-01
> **诊断范围**: 结构重复度、权威来源链接健康度、关键事实偏差
> **方法**: 复用现有审计脚本 + 针对性 grep 抽样
> **项目基线**: v3.0 / Rust 1.96.0 stable / Edition 2024

---

## 1. 关键数字总览

| 指标 | 数值 | 状态 |
|---|---|:---:|
| 总 Markdown 文件 | ~3,691 | — |
| 总 Rust 源文件 | ~1,699 | — |
| `concept/` 文件数 | 371 | — |
| 概念文件 EN 标题覆盖率 | 370/371 (99.7%) | ✅ |
| 概念文件 Summary 覆盖率 | 369/371 (99.5%) | ✅ |
| 概念文件权威来源覆盖率 | 358/371 (96.5%) | ⚠️ |
| 三轨内容潜在重复对（≥0.6） | 30 对 | ⚠️ |
| `docs/` 损坏链接 | 348 个 | 🔴 |
| `concept/` 死链 | 31 个 | 🟡 |
| 跨层引用缺失 | 39 个 | 🟡 |
| 关键事实偏差（`&const`、async closures nightly、Edition 1.82） | 0 个活跃文件 | ✅ |
| `kb_auditor.py` 仪表盘生成 | 崩溃 | 🔴 |

---

## 2. 结构重复度诊断

使用 `scripts/detect_content_overlap.py`（阈值 0.6）扫描 955 个文件，发现 **30 对潜在重复文件**。

### 2.1 高相似度重复（≥0.75）

| 相似度 | 文件 A | 文件 B | 主题 | 状态 |
|---|---|---|---|---|
| 1.00 | `concept/04_formal/36_tree_borrows_deep_dive.md` | `knowledge/04_expert/miri/01_tree_borrows.md` | Tree Borrows | ⚠️ 待去重 |
| 0.78 | `knowledge/06_ecosystem/emerging/05_rust_1_96.md` | `docs/06_toolchain/06_22_rust_1_96_features.md` | Rust 1.96 | ⚠️ 待去重 |
| 0.75 | `concept/06_ecosystem/45_compiler_internals.md` | `knowledge/04_expert/01_compiler_internals.md` | 编译器内部 | ⚠️ 待去重 |
| 0.75 | `concept/07_future/19_rust_edition_preview.md` | `knowledge/06_ecosystem/02_edition_2024.md` | Edition 2024 | ⚠️ 待去重 |
| 0.75 | `concept/07_future/rust_1_96_stabilized.md` | `knowledge/06_ecosystem/emerging/05_rust_1_96.md` | Rust 1.96 | ⚠️ 待去重 |
| 0.75 | `concept/00_meta/comprehensive_rust_mapping.md` | `docs/01_learning/01_google_rust_mapping.md` | Google Rust 映射 | ⚠️ 待去重 |
| 0.75 | `concept/04_formal/36_tree_borrows_deep_dive.md` | `docs/content/academic/10_tree_borrows_guide.md` | Tree Borrows | ⚠️ 待去重 |
| 0.75 | `concept/07_future/13_unsafe_fields_preview.md` | `docs/05_guides/05_unsafe_fields_preview.md` | Unsafe Fields | ⚠️ 待去重 |
| 0.75 | `knowledge/03_advanced/async/02_async_closure.md` | `docs/03_guides/03_async_closures_deep_dive.md` | Async Closures | ⚠️ 待去重 |
| 0.75 | `knowledge/06_ecosystem/emerging/01_async_closures.md` | `docs/03_guides/03_async_closures_deep_dive.md` | Async Closures | ⚠️ 待去重 |

### 2.2 重复主题分布

重复主要集中在以下主题：

- **版本特性**: Rust 1.95 / 1.96 / 1.97 / Edition 2024（最多）
- **形式化**: Tree Borrows、编译器内部
- **异步**: Async Closures
- **Unsafe**: Unsafe Fields、Unsafe Rust 模式
- **对比/映射**: Google Comprehensive Rust 映射

### 2.3 关键发现

1. 大部分高相似度重复是**版本特性文档按版本分散**导致的，与“版本中心制 → 特性中心制”的治理目标一致。
2. `knowledge/` 和 `docs/` 中多个文件与 `concept/` 权威源重复，符合去重策略中“以 `concept/` 为唯一权威源”的方向。
3. 未发现同名文件跨目录的重大冲突（除版本特性外）。

---

## 3. 权威来源链接健康度诊断

### 3.1 `docs/` 链接健康

使用 `scripts/check_links.py` 扫描 574 个 Markdown 文件：

| 类别 | 数量 |
|---|---|
| 总链接数 | 50,108 |
| 有效链接 | 23,444 |
| 损坏链接 | **348** |
| 外部链接 | 26,315 |
| 仅锚点链接 | 15,237 |
| 问题文件数 | **146** |

### 3.2 损坏链接类型分布

| 问题类型 | 数量 | 主要原因 |
|---|---|---|
| 锚点不存在 | 210 | Emoji 标题、Markdown 锚点生成不一致、重复标题 |
| 文件/路径不存在 | ~100+ | 目标文件迁移/删除后未更新链接 |
| 外部 404/超时 | ~30+ | 第三方站点变更 |

### 3.3 `concept/` 链接健康

使用 `scripts/check_all_concept_links_health.py` 扫描：

- 检查 1,247 个 concept/ 扩展权威链接
- **异常链接: 0**

使用 `scripts/check_source_links_health_extended.py` 扫描：

- **异常链接: 1**
  - `https://github.com/verus-lang/verusverus/guide/`（404，疑似 `verusverus` 拼写错误）

使用 `scripts/check_non_github_links_health.py` 扫描 2,703 个非 GitHub 外部链接：

- HTTP 200: 2,219
- 白名单: 482
- **疑似失效: 2**
  - `https://jeffreypalermo.com/blog/the-onion-architecture-part-3/`（429）
  - `https://www.eprosima.com/index.php/products-all/eprosima-fast-dds`（超时）

### 3.4 `kb_auditor.py` 死链检查

- 发现 **31 个死链**
- 发现 **39 个跨层引用问题**（主要是 L1 文件缺少向 L0 的向下引用）
- 仪表盘生成阶段崩溃：`TypeError: argument of type 'NoneType' is not iterable`

---

## 4. 关键事实偏差诊断

针对既有报告（`COMPREHENSIVE_AUTHORITATIVE_ALIGNMENT_DIFF_2026_06_23.md`）中提到的关键事实偏差进行复核：

| 偏差项 | 既有报告状态 | 当前复核结果 |
|---|---|---|
| `content/emerging/async_closures.md` 标 nightly-only | 🔴 高 | ✅ 已迁移为重定向文件，正确标注 1.85.0 stable |
| `knowledge/06_ecosystem/02_edition_2024.md` 版本号 1.82 | 🔴 高 | ✅ 已改为重定向文件，目标文件 `concept/07_future/19_rust_edition_preview.md` 标注 1.85.0+ stable |
| `gen` 关键字预留 vs gen blocks nightly 混淆 | 🔴 高 | ✅ 当前文件正确区分 |
| `&const` 应为 `&raw const` | 🔴 高 | ✅ 未在活跃文件中发现错误用法；仅发现合法 `&constraint` / `&const_async_config` |
| async closures / AsyncFn 时间线 | 🟡 中 | ✅ `concept/03_advanced/24_async_closures.md` 正确标注 1.85.0 stable；RTN 仍正确标注 nightly |
| async-std 维护模式 | 🟡 中 | ✅ 活跃文件中均标注 `[已归档]` / `[已归档 2025-03]` |
| wasm32-wasi 重命名 | 🟡 中 | ✅ 活跃文件中主要作为历史引用并提示重命名 |

### 4.1 结论

**关键事实偏差已在活跃文件中得到有效修正**。剩余工作主要是：

1. 清理 `archive/` 和旧报告中过时的表述（非活跃内容）；
2. 统一 boilerplate 顶部的生态状态提示（大量文件顶部仍有自动生成的 `async-std` / `wasm32-wasi` 提示）。

---

## 5. 概念文件元数据诊断

使用 `scripts/audit_concept_metadata.py` 扫描 `concept/` 371 个文件：

| 指标 | 数量 | 占比 |
|---|---:|---:|
| 有英文标题 (EN) | 370 | 99.7% |
| 英文标题为占位符 | 3 | 0.8% |
| 有英文摘要 (Summary) | 369 | 99.5% |
| 英文摘要为占位符 | 21 | 5.7% |
| 有权威来源链接 | 358 | 96.5% |

### 5.1 缺失权威来源的文件示例

- `concept/00_meta/bilingual_template.md`
- `concept/00_meta/concept_consistency_audit_checklist.md`
- `concept/00_meta/learning_mvp_path_en.md`
- `concept/00_meta/template_deduplication_guide.md`
- `concept/01_foundation/29_quiz_pl_foundations.md`
- `concept/07_future/19_rust_edition_preview.md`

### 5.2 英文标题占位符

- `concept/04_formal/31_miri.md`: `Miri`
- `concept/04_formal/32_kani.md`: `Kani`
- `concept/07_future/19_rust_edition_preview.md`: `Rust 2024 Edition (1.85.0+ stable)`

---

## 6. 治理机制诊断

### 6.1 计划文件状态

`.kimi/` 中存在约 16 个 `.md` 文件，部分已归档到 `.kimi/archive/`。根据 `SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`，应保留单一活跃执行清单。

### 6.2 脚本健康

| 脚本 | 状态 | 说明 |
|---|---|---|
| `detect_content_overlap.py` | ✅ 正常 | 输出重复对报告 |
| `check_links.py` | ✅ 正常 | 扫描 docs/ 链接 |
| `check_all_concept_links_health.py` | ✅ 正常 | concept/ 外部链接 0 异常 |
| `check_source_links_health_extended.py` | ✅ 正常 | 1 个拼写错误链接 |
| `check_non_github_links_health.py` | ✅ 正常 | 2 个疑似失效 |
| `kb_auditor.py` | 🔴 崩溃 | 仪表盘生成 `TypeError` |
| `audit_concept_metadata.py` | ✅ 正常 | 元数据扫描 |

### 6.3 关键发现

`kb_auditor.py` 的仪表盘生成函数存在 bug，需要修复以恢复质量仪表盘更新。

---

## 7. 风险分级与优先级建议

### 🔴 紧急（建议 1–2 周内处理）

1. **修复 `kb_auditor.py` 仪表盘生成 bug** — 质量仪表盘是项目门面，当前无法生成。
2. **处理 `docs/` 348 个损坏链接** — 大量锚点问题影响阅读体验；优先修复 `docs/02_reference/quick_reference/` 等高频访问路径。

### 🟡 高优先级（建议 2–4 周内处理）

1. **处理 `concept/` 31 个死链 + 39 个跨层引用缺失** — 权威来源链接完整性。
2. **推进内容去重** — 优先处理版本特性（1.95/1.96/1.97/Edition 2024）的“特性中心制”迁移。
3. **清理 boilerplate 顶部的 `async-std` / `wasm32-wasi` 提示** — 大量自动生成的提示造成噪音。

### 🟢 中优先级（建议 1–3 个月内处理）

1. **补齐 13 个 `concept/` 文件的权威来源链接**。
2. **替换/修复 3 个英文标题占位符**。
3. **归档 `.kimi/` 和 `reports/` 中过期计划/报告**。
4. **评估并修复 `docs/` 中第三方外部 404 链接**。

---

## 8. 后续行动建议

基于最小诊断先行方案，建议立即进入 **Phase 1 紧急止血**，聚焦：

1. 修复 `kb_auditor.py` bug；
2. 修复 `docs/` 高频路径的损坏链接（尤其是 quick_reference/ 和实践项目）；
3. 修复 `concept/` 死链和跨层引用缺失；
4. 修正 `verusverus` 拼写错误链接；
5. 清理 boilerplate 提示噪音。

完成后再根据实际效果决定是否扩大诊断范围。

---

*报告生成时间: 2026-07-01*
*生成工具: scripts/detect_content_overlap.py, scripts/check_links.py, scripts/check_all_concept_links_health.py, scripts/check_source_links_health_extended.py, scripts/check_non_github_links_health.py, scripts/kb_auditor.py, scripts/audit_concept_metadata.py*
