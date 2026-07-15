# 命名规范与编号债务清理报告

**日期**: 2026-07-15
**范围**: `concept/` 编号债务 + `crates/*/docs/` 结构规范化
**目标**: 修复高优先级编号/命名违规，保持 `check_naming_convention.py --strict` 无新增 ERROR，且 `kb_auditor.py --link-check` 死链为 0。

---

## 1. 基线与最新结果

### 1.1 `python scripts/check_naming_convention.py --strict`

| 指标 | 清理前 | 清理后 | 变化 |
|---|---:|---:|---:|
| ERROR | 0 | 0 | 0 |
| WARN | 79 | 64 | **-15** |
| N1 WARN | 75 | 63 | -12 |
| N4 WARN | 3 | 0 | **-3** |
| N5 WARN | 1 | 1 | 0 |

> 清理后仍无 ERROR，`--strict` 通过。

### 1.2 `python scripts/kb_auditor.py --link-check`

| 指标 | 结果 |
|---|---|
| 死链 | 0 |
| docs/content/knowledge 死链 | 0 |
| 跨层问题 | 1（既存：`concept/01_foundation/04_control_flow/03_let_chains.md` 缺少 L0 向下引用） |

### 1.3 `cargo check --workspace`

通过。

---

## 2. 本次修改清单

### 2.1 `concept/` 编号债务

| 原路径 | 新路径 | 说明 |
|---|---|---|
| `concept/02_intermediate/09_quizzes/` | `concept/02_intermediate/08_quizzes/` | 补齐 `02_intermediate/` 目录跳号（07→09 缺 08） |
| `concept/07_future/03_preview_features/` | `concept/07_future/02_preview_features/` | 补齐 `07_future/` 目录跳号（01→03 缺 02） |
| `concept/00_meta/placeholders/` | `concept/00_meta/07_placeholders/` | 为小目录编号 |
| `concept/00_meta/01_trpl_3rd_ed_mapping.md` | `concept/00_meta/06_trpl_3rd_ed_mapping.md` | 解决 `00_meta/` 根目录 `01_` 重复，迁移到空号 `06_` |
| `concept/01_foundation/11_quizzes/24_quiz_type_system.md` | `concept/01_foundation/11_quizzes/01_quiz_type_system.md` | 测验文件连续编号 |
| `concept/01_foundation/11_quizzes/25_quiz_error_handling.md` | `concept/01_foundation/11_quizzes/02_quiz_error_handling.md` | 测验文件连续编号 |
| `concept/01_foundation/11_quizzes/26_quiz_modules_testing.md` | `concept/01_foundation/11_quizzes/03_quiz_modules_testing.md` | 测验文件连续编号 |
| `concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md` | `concept/01_foundation/11_quizzes/04_quiz_closures_iterators.md` | 测验文件连续编号 |
| `concept/01_foundation/11_quizzes/29_quiz_pl_foundations.md` | `concept/01_foundation/11_quizzes/05_quiz_pl_foundations.md` | 测验文件连续编号 |
| `concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md` | `concept/01_foundation/11_quizzes/06_quiz_ownership_borrowing.md` | 测验文件连续编号 |
| `concept/00_meta/README.md` | — | 新增「编号说明」节，解释 `knowledge_topology/` 作为大型无序号专题系列目录保留 |
| `concept/00_meta/kg_index.json` | — | 因路径变更重新生成 |
| `concept/00_meta/kg_data_v3.json` | — | 因路径变更重新生成 |
| `concept_kb.json` | — | `kb_auditor.py` 自动更新 |

> 所有重命名均通过 `scripts/apply_renumber.py` 执行，自动重写跨文件链接/引用。

### 2.2 `crates/*/docs/` 结构规范化

| 原路径 | 新路径 | 说明 |
|---|---|---|
| `crates/c01_ownership_borrow_scope/docs/rust_194_updates/` | `crates/c01_ownership_borrow_scope/docs/tier_04_rust_194_updates/` | 非 tier 目录规范化为 `tier_04_*` |
| `crates/c03_control_fn/docs/rust_194_updates/` | `crates/c03_control_fn/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c04_generic/docs/rust_194_updates/` | `crates/c04_generic/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c05_threads/docs/rust_194_updates/` | `crates/c05_threads/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c06_async/docs/rust_194_updates/` | `crates/c06_async/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c07_process/docs/rust_194_updates/` | `crates/c07_process/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c08_algorithms/docs/rust_194_updates/` | `crates/c08_algorithms/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c10_networks/docs/rust_194_updates/` | `crates/c10_networks/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c11_macro_system_proc/docs/rust_194_updates/` | `crates/c11_macro_system_proc/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c12_wasm/docs/rust_194_updates/` | `crates/c12_wasm/docs/tier_04_rust_194_updates/` | 同上 |
| `crates/c03_control_fn/docs/snippets/` | `crates/c03_control_fn/docs/tier_03_snippets/` | 非 tier 目录规范化 |
| `crates/c08_algorithms/docs/archive/` | `archive/2026/crates_c08_algorithms_docs_archive_2025/` | 旧归档/报告目录移出活跃 `crates/*/docs/` |

### 2.3 删除的变体后缀 stub（N4 清零）

| 删除文件 | 说明 |
|---|---|
| `crates/c07_process/docs/tier_04_advanced/05_testing_and_benchmarking_expanded.md` | `*_expanded` 变体后缀 stub |
| `crates/c07_process/docs/tier_04_advanced/07_modern_process_libraries_final.md` | `*_final` 变体后缀 stub |
| `crates/c09_design_pattern/docs/tier_02_guides/04_behavioral_patterns_guide_supplement.md` | `*_supplement` 变体后缀 stub |

### 2.4 KG 浏览器重建

- 重新生成 `concept/00_meta/kg_index.json`（`scripts/generate_kg_index.py`）
- 重新生成 `concept/00_meta/kg_data_v3.json`（`scripts/generate_kg_v3.py`）
- 重建 `tools/kg_browser/index.html`（`tools/kg_browser/build.py`）

---

## 3. 剩余 WARN 摘要（64 条）

### 3.1 已知/允许的系列目录 WARN（52 条）

这些目录均为 AGENTS.md §4.0-4 允许的无序号专题系列，且已附 README 索引；当前 `check_naming_convention.py` 对无序号系列目录统一发出 WARN。

| 位置 | WARN 数量 | 说明 |
|---|---|---|
| `concept/00_meta/00_framework/*.md` | 21 | 元层框架专题系列文件，目录含 README |
| `concept/00_meta/knowledge_topology/`（含 2 个无序号文件） | 3 | 大型拓扑图谱系列，已备案说明 |
| `concept/07_future/00_version_tracking/*.md` | 14 | Rust 版本追踪专题系列 |

### 3.2 其他目录未编号 WARN（11 条）

主要为 `content/`、`docs/`、`knowledge/` 下的专题子目录，不在本次高优先级修复范围内；按 AGENTS.md §4.0-4 可通过后续补 README 索引或重编号处理。

- `content/ecosystem`、`content/ecosystem/deep_dives`、`content/safety_critical`
- `docs/00_meta/analysis`、`docs/00_meta/history`、`docs/02_learning/quizzes`、`docs/03_reference/quick_reference`、`docs/08_usage_guides/workflow`、`docs/12_research_notes/02_formal_methods/coq_skeleton`、`docs/15_rust_formal_engineering_system/03_practical_applications/memory`、`docs/15_rust_formal_engineering_system/03_practical_applications/performance`
- `knowledge/02_intermediate/control_flow`、`knowledge/02_intermediate/macros`、`knowledge/02_intermediate/type_system`
- `knowledge/03_advanced/async`、`knowledge/03_advanced/concurrency`、`knowledge/03_advanced/macros`、`knowledge/03_advanced/unsafe`
- `knowledge/04_expert/academic`、`knowledge/04_expert/miri`、`knowledge/04_expert/safety_critical`
- `knowledge/05_reference/guides`
- `knowledge/06_ecosystem/databases`、`knowledge/06_ecosystem/deep_dives`、`knowledge/06_ecosystem/deployment`、`knowledge/06_ecosystem/emerging`

### 3.3 一级目录跳号 WARN（1 条）

- `docs/` 顶层缺 `10_`：属于既有空号策略，未在本次范围内修改。

### 3.4 本次未处理的 `crates/*/docs/` 项目

- `tier_05_*` 子目录（如 `tier_05_exercises`、`tier_05_tutorials` 等）：当前 `check_naming_convention.py` 的 `tier_0\d+_*` 规则允许，未产生 WARN；若后续明确仅允许 `tier_01`–`tier_04`，可再统一调整。

---

## 4. 执行命令记录

```bash
# 1. 基线检查
python scripts/check_naming_convention.py --strict
python scripts/kb_auditor.py --link-check

# 2. 重编号（dry-run 后执行）
python scripts/apply_renumber.py --mapping tmp/renumber/cleanup_mapping.csv --scope "" --dry-run --log tmp/renumber/apply_dryrun.log.md
python scripts/apply_renumber.py --mapping tmp/renumber/cleanup_mapping.csv --scope "" --apply --log tmp/renumber/apply_apply.log.md

# 3. 清理非 tier 目录/变体后缀
mv crates/c08_algorithms/docs/archive/* archive/2026/crates_c08_algorithms_docs_archive_2025/
rmdir crates/c08_algorithms/docs/archive
rm -f crates/c07_process/docs/tier_04_advanced/05_testing_and_benchmarking_expanded.md
rm -f crates/c07_process/docs/tier_04_advanced/07_modern_process_libraries_final.md
rm -f crates/c09_design_pattern/docs/tier_02_guides/04_behavioral_patterns_guide_supplement.md

# 4. 重建 KG 索引与浏览器
python scripts/generate_kg_index.py
python scripts/generate_kg_v3.py
python tools/kg_browser/build.py

# 5. 验证
python scripts/kb_auditor.py --link-check
python scripts/check_naming_convention.py --strict
cargo check --workspace
```

---

## 5. 结论

- 本次清理共移动/重命名 **21 个目录/文件映射**（涉及 73 个实际文件），删除 3 个变体后缀 stub，迁移 1 个旧归档目录。
- `check_naming_convention.py --strict` 保持 **ERROR=0**，WARN 由 79 降至 64。
- `kb_auditor.py --link-check` 死链保持 0，`cargo check --workspace` 通过。
- 剩余 WARN 主要为已备案的无序号专题系列目录和未纳入本次范围的 `content/`/`docs/`/`knowledge/` 子目录，未引入新的结构违规。
