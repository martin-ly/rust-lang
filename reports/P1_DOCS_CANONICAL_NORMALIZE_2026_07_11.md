# P1 — docs/ 与 knowledge/ 非权威页 Canonical 规范化（接续完成）

**日期**: 2026-07-11
**Rust 版本**: 1.97.0+ (Edition 2024)
**作用域**: 仅 `docs/`、`knowledge/`。**未触碰** `concept/`、`archive/`、`book/`、`tmp/`（tmp 仅放临时脚本，已被 `.gitignore` 排除）、`crates/`。
**红线遵守**: 0 删除任何定理/引理/推论/证明/`Def x.y`/CVE/反例/形式化定义/代码示例/决策树/独特研究内容；未虚构 lint/错误码/版本号/属性语法。

---

## 1. 跳过集合（前置 agent 已处理，禁止重复改写）

`git status --short docs knowledge` 显示 **45** 个已 `M` 文件（25 个 `docs/02_reference/quick_reference/*`、13 个 `docs/research_notes/formal_methods/*`、6 个 `docs/research_notes/type_theory/*`、`docs/research_notes/software_design_theory/...` 等），全部加入跳过集合，本轮**未触碰**。

> 跳过集合快照：`tmp/skip_set.txt`（45 条；临时文件，未纳入版本控制）。

---

## 2. 候选识别

工具：`python scripts/detect_content_overlap_v2.py --budget 999999 --threshold 0.45`（产出 `reports/CONTENT_OVERLAP_V2_2026-07-11.{md,json}`）+ 全量盘点脚本（`tmp/inventory.py`、`tmp/list_naked.py`、`tmp/list_nomarker.py`，均为临时脚本）。

盘点结论（非跳过 docs/knowledge 共 618 文件）：

- 绝大多数已带 `权威来源`/canonical 标记（前置批次已规范化），并在文首 `权威来源` 指向对应 `concept/` 权威页（抽查 `05_threads_concurrency_usage_guide.md`、`05_type_system_usage_guide.md`、`05_async_programming_usage_guide.md` 等均已对齐，且含「权威来源对齐完成」状态）。
- **唯一未带任何 canonical 标记的实质性（>40 行、非 README/stub）文件仅 6 个**，即本轮唯一待处理集合：

| 文件 | 行数 | 性质 | 处置 |
|---|---:|---|---|
| `docs/05_guides/05_cfg_select_macro_guide.md` | 340 | `cfg_select!` 工程使用指南（独特） | 加 canonical 块 → `28_conditional_compilation.md` |
| `docs/06_toolchain/06_jump_tables_guide.md` | 237 | `-C jump-tables` 编译器选项专题（concept 无独立权威页） | 加「无 concept 权威页」定位块 + 1 条相关 concept 链接 |
| `docs/01_learning/learning_mvp_path.md` | 67 | TRPL→concept 逐章映射（本文件即映射权威页，concept 端为重定向 stub） | 加 canonical 定位块 |
| `docs/trpl_3rd_ed_diff.md` | 122 | TRPL 与 concept 对齐差异分析（独特比较） | 加定位块 + `⚠需专家复核`（正文历史链接保留） |
| `docs/00_master_index.md` | 43 | 项目总索引（纯导航，无概念复述） | 不改写（导航索引，无语义复述，强制加 canonical 块语义不当） |
| `docs/05_guides/README.md` | 48 | 目录索引（纯导航） | 不改写（同上） |

> 其余无标记文件均为 ≤40 行的 README/目录索引/微小 stub（`docs/01_learning/01_official_resources_mapping.md` 33 行、`docs/04_thinking/04_multi_dimensional_concept_matrix.md` 28 行、`06_toolchain/06_0*_rust_1_93_*.md` 13 行 stub 等），无通用概念复述，按红线保留原样。

---

## 3. 处理结果（量化）

| 指标 | 数值 |
|---|---:|
| 处理（编辑）文件总数 | **4** |
| 跳过（已 `M`）数 | **45** |
| 仅审视/故意保留的导航索引 | 2（`00_master_index.md`、`05_guides/README.md`） |
| 新增 canonical/定位块数 | **4**（3 个「concept 为权威」块 + 1 个「concept 无对应权威页」定位块含相关链接） |
| 压缩通用复述段数 | **0**（4 文件正文均为独特 guide/映射/差异分析/工具链专题，无与 concept 重复的通用概念复述段可压缩） |
| TOC 中英冗余括号去重数 | **0**（未改动任何 TOC；候选文件无 `标题（English）{#...-标题...}` 冗余需去重） |
| **净增行 / 净减行** | **+22 / −0**（`git diff --numstat`：5/0 + 5/0 + 7/0 + 5/0） |

### 3.1 0 删除实锤（定理/证明/反例/代码段被删计数 = 0）

自检方法：

```bash
git diff -- docs/05_guides/05_cfg_select_macro_guide.md \
            docs/01_learning/learning_mvp_path.md \
            docs/trpl_3rd_ed_diff.md \
            docs/06_toolchain/06_jump_tables_guide.md \
  | grep -E '^-' | grep -vE '^---'   # 输出为空
```

- 4 文件 `git diff --numstat` 删除列全为 `0`，合计 **0 删除**。
- 全部为「文首标题下追加块」的纯增量编辑（pattern a/§3.4），未触及正文任何段落、代码块、定理/证明/反例/决策树。
- 因此定理/证明/反例/代码段被删计数 = **0**（因整轮无任何删除）。

### 3.2 各文件 canonical 目标（相对路径按文件深度计算，均已 `test -e` 验证存在）

| 文件 | canonical/相关目标 | 存在 |
|---|---|---|
| `docs/05_guides/05_cfg_select_macro_guide.md` | `../../concept/03_advanced/03_proc_macros/28_conditional_compilation.md` | ✅ |
| `docs/01_learning/learning_mvp_path.md` | `../../concept/00_meta/trpl_3rd_ed_mapping.md`（重定向 stub，反向指向本文件）| ✅ |
| `docs/01_learning/learning_mvp_path.md` | `../../concept/00_meta/04_navigation/learning_mvp_path.md` | ✅ |
| `docs/trpl_3rd_ed_diff.md` | `../concept/00_meta/trpl_3rd_ed_mapping.md` + `01_learning/learning_mvp_path.md` | ✅ |
| `docs/06_toolchain/06_jump_tables_guide.md` | `../../concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md`（最近相关，非本专题权威页） | ✅ |

---

## 4. canonical 链接目标存在性抽查（≥10）

方法（`tmp/verify_links.py`）：抽取 `docs/`、`knowledge/` 文首（前 60 行）canonical 块中所有 `concept/*.md` 目标，去重后 `os.path.exists` 校验。

- 文首 canonical 块共解析出 **178** 个去重 `concept/` 目标：**171 存在 / 7 缺失**。
- 抽样 15 个：**14 OK / 1 缺失**（缺失项 `concept/01_foundation/00_pl_prerequisites.md` 为 `docs/trpl_3rd_ed_diff.md` **正文历史链接**，本轮编辑前即存在，非本轮引入）。

抽样明细（前 15）：

```
OK   concept/00_meta/00_framework/comprehensive_rust_mapping.md
OK   concept/00_meta/02_sources/international_authority_index.md
OK   concept/00_meta/04_navigation/learning_mvp_path.md
OK   concept/00_meta/04_navigation/quick_reference.md
OK   concept/00_meta/trpl_3rd_ed_mapping.md
MISS concept/01_foundation/00_pl_prerequisites.md   ← 历史遗留（见 §6）
OK   concept/01_foundation/00_start/00_start.md
OK   concept/01_foundation/00_start/06_zero_cost_abstractions.md
OK   concept/01_foundation/00_start/15_closure_basics.md
OK   concept/01_foundation/00_start/36_keywords.md
OK   concept/01_foundation/00_start/37_operators_and_symbols.md
OK   concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md
OK   concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md
OK   concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md
OK   concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md
```

**本轮新增的 4 个 concept 目标全部存在**（§3.2）；7 个缺失全部为历史遗留链接，引用方均非本轮新增（见 §6）。

---

## 5. kb_auditor 复核（第 7 门）

`python scripts/kb_auditor.py`（扫描 `concept/` 462 文件）：

| 项 | 数值 |
|---|---:|
| 死链 | **0** |
| 跨层问题 | **0** |
| 模板化 ⟹ | **0** |

> 本轮未改动 `concept/`（红线），故 concept 侧三项维持 0/0/0；新增 docs 链接均指向已存在 concept 页，未引入新死链。运行副作用：`reports/kb_quality_dashboard.md`、`concept_kb.json` 被审计器刷新（属正常再生成）。

---

## 6. `⚠需专家复核` 点清单（均非本轮引入，正文保留未改）

下列为盘点中发现的**历史遗留** concept 链接失效（随目录重构旧路径失效），按红线 #2 留原文并标记，建议纳入后续「链接治理」统一校正（不属于 P1 canonical 规范化范围，本轮不修复）：

1. `docs/trpl_3rd_ed_diff.md`（正文，已在文首 canonical 块内联标注 `⚠需专家复核`）：
   - `../concept/01_foundation/00_pl_prerequisites.md`（应为 `01_foundation/00_start/34_pl_prerequisites.md`）
   - `../concept/01_foundation/10_error_handling_basics.md`（应为 `01_foundation/08_error_handling/32_error_handling_basics.md`）
   - `../concept/02_intermediate/15_error_handling_deep_dive.md`（应为 `02_intermediate/03_error_handling/16_error_handling_deep_dive.md`）
   - `../concept/05_comparative/02_rust_vs_cpp.md`（应为 `05_comparative/01_systems_languages/01_rust_vs_cpp.md`）
   - `../concept/06_ecosystem/01_toolchain.md`（应为 `06_ecosystem/00_toolchain/01_toolchain.md`）
   - `../concept/00_meta/learning_mvp_path.md`（应为 `00_meta/04_navigation/learning_mvp_path.md`）
2. `knowledge/06_ecosystem/databases/README.md` → `concept/06_ecosystem/23_database_systems.md`（缺失）
3. `docs/research_notes/software_design_theory/07_crate_architectures/02_tower_architecture.md` → `concept/06_ecosystem/05_formal_ecosystem_tower.md`（缺失）
4. `docs/04_research/04_rust_for_linux.md` → `concept/07_future/19_rust_for_linux.md`（缺失）
5. `docs/research_notes/10_edition_guide_alignment.md` → `concept/07_future/22_edition_guide.md`（缺失）

> 上述 2–5 引用文件均不在本轮编辑集合内；仅列出供后续治理，本轮不改动。

---

## 7. 边界判断说明（宁可加块保全文，也不误删）

- `docs/06_toolchain/06_jump_tables_guide.md`：`-C jump-tables`/跳转表在 `concept/` 无独立权威页（grep `jump.table|跳转表|jump-tables` 仅 async/unsafe 页偶发提及），按 §3.4/约束 #4 保留全文，仅补一条最近相关 concept 链接（LLVM 后端与代码生成），不删除正文。
- `docs/01_learning/learning_mvp_path.md`：`concept/00_meta/trpl_3rd_ed_mapping.md` 是**反向指向本文件**的重定向 stub，故本文件即 TRPL→concept 映射的权威承载页（AGENTS.md §2.1 允许 docs 保留此类跨切索引）；canonical 块据此表述为「docs 侧映射权威页」，而非「从属于 concept」。
- `docs/00_master_index.md`、`docs/05_guides/README.md`：纯导航索引，无通用概念复述、无 concept 正文重复；对其强加「concept 为权威」块语义不当，故保留原样并在此说明。

---

## 8. 复现命令

```bash
git status --short docs knowledge                         # 跳过集合（45）
python scripts/detect_content_overlap_v2.py --budget 999999 --threshold 0.45
git diff --numstat -- docs/05_guides/05_cfg_select_macro_guide.md \
  docs/01_learning/learning_mvp_path.md docs/trpl_3rd_ed_diff.md \
  docs/06_toolchain/06_jump_tables_guide.md               # 5/0 5/0 7/0 5/0
python scripts/kb_auditor.py                              # 死链0/跨层0/模板化0
```

**结论**: 本轮在前置 45 文件之外，完成剩余 **6 个未规范化实质性文件**的处置（4 编辑 + 2 导航索引保留并说明），纯增量 **+22/−0**，**0 删除**任何独特深度/证明/反例/代码，kb_auditor 三项维持 **0/0/0**。
