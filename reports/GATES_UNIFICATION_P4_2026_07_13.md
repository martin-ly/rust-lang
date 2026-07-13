# P4 门具体系统一报告（Gates Unification P4）

> 日期：2026-07-13（执行 2026-07-14 早）｜ 依据：`.kimi/FOLLOW_UP_PLAN_P1_P5_2026_07_13.md`（P4）
> 范围：质量门 21 → 23（15 阻断 + 8 观察）、TOC 统一刷新、atlas quiz 排除、CRLF 归一。

## 1. 任务 1：两门挂入（21 → 23 门）

### 1.1 门禁 diff 摘要

| 文件 | 变更 |
|---|---|
| `scripts/run_quality_gates.sh` | 观察门段新增 `run_gate "Mindmap Coverage (observe)" python scripts/check_mindmap_coverage.py` 与 `run_gate "Quiz System (observe)" python scripts/check_quiz_system.py`（均默认观察模式，不加 --strict，附基线注释）；头部注释 6→8 观察门、补两门说明；结尾 `All 21 quality gates passed (15 blocking + 6 semantic observe)` → `All 23 ... (15 blocking + 8 semantic observe)`。`bash -n` 通过。 |
| `AGENTS.md` | §5 命令区「21 个质量门（15 阻断 + 6 语义观察）」→ 23/8；§5.1 标题 21→23 项、观察门 6→8，新增门 22（check_mindmap_coverage，--strict 基线 mindmap≥10%/反例≥40%，当前 11.4%/71.1%）与门 23（check_quiz_system，注册表/题型/难度/双向链接）条目；§5.2 基线表新增 mindmap coverage 与 quiz system 两行（均为 ⏳ 新增观察门 2026-07-13 P4）；§6 红线第 6 条「6 语义观察门」→ 8。 |
| `.github/workflows/quality_gates.yml` | 新增 `mindmap-coverage` 与 `quiz-system` 两个 observe job（`continue-on-error: true`，python 3.12）；summary `needs` 与 jobs map 各补 2 项（20→22 job 条目）；页脚 `All 21 quality gates completed (15 blocking + 6 semantic observe)` → 23/8。YAML 解析校验通过。 |
| `scripts/README.md` | `check_quiz_system.py` 登记为「质量门 23，观察（2026-07-13 P4 挂入，原 W3-a 独立观察检查器）」；`check_mindmap_coverage.py` 登记为「质量门 22，观察（原 W2-a 独立观察检查器）」；`run_quality_gates.sh` 行 21→23 门（15 阻断 + 8 观察）。 |

### 1.2 本地实跑（观察模式）

- `python scripts/check_mindmap_coverage.py` → **exit 0**；内容页 429：mindmap 49（11.4%）/ 反例 305（71.1%），均超 --strict 基线（10%/40%）。
- `python scripts/check_quiz_system.py` → **exit 0**；失败 0、观察警告 0：注册表 21 quiz 一致 / 题型均 ≥3 种 / 难度标注 309/309=100% / quiz→concept 21/21、concept→quiz 回链 21/21。
- 脚本门数自洽：22 个 `run_gate` 调用 + 1 个 overlap-v2 自定义阻断块 = **23 门**，与结尾计数一致。

## 2. 任务 2：TOC 统一刷新

- 机制判定：concept/ 页内目录为**手工维护的 `## 📑 目录` 区**（`scripts/auto_toc_generator.py` 仅面向 `docs/`，不适用）。
- 对 `reports/FIVE_ELEMENTS_BACKFILL_P1B_2026_07_13.md` 列出的 **39 页**逐页审计（脚本：`tmp/p4_toc_check.py`）：
  - **23 页** TOC 已含「📋 关键属性」「🔗 概念关系」条目（P1-b 回填时已同步）；
  - **3 页缺条目，已补**（仅 TOC 区追加 2 行，未动正文）：`01_foundation/03_values_and_references/01_reference_semantics.md`、`02_intermediate/03_error_handling/02_error_handling_deep_dive.md`、`03_advanced/01_async/03_async_patterns.md`；
  - **13 页本无 `## 📑 目录` 区**（全页无 TOC 机制，非 P1-b 引入的缺漏），不新建 TOC，登记如下：00_start/04_effects_and_purity、00_start/06_keywords、02_type_system/05_data_abstraction_spectrum、03_values_and_references/03_variable_model、07_modules_and_items/12_items、10_testing_basics/02_useful_development_tools、03_error_handling/04_exception_safety_rust_cpp、04_types_and_conversions/05_rtti_and_dynamic_typing、00_concurrency/04_cross_platform_concurrency、01_async/07_async_closures、02_unsafe/06_memory_model、02_unsafe/07_unsafe_reference、03_proc_macros/04_macro_debugging_and_diagnostics。
- 锚点修正：首次插入误用 `#关键属性`，经 mdbook 渲染实测（`book/03_advanced/01_async/03_async_patterns.html` 中 `id="-关键属性"`）确认为库内惯例 `#-关键属性`（emoji 剥离后空格→连字符），6 行已全部改正。

## 3. 任务 3：atlas quiz 排除

- `scripts/extract_concept_topology.py` `should_include()` 新增排除规则：文件名 stem 或任一目录段含 `quiz`（不区分大小写）即排除，附注释说明 quiz 页由 `check_quiz_system.py`（观察门 23）与 `concept/00_meta/quiz_registry.yaml` 独立管理。
- 覆盖范围：`NN_quizzes/` 目录 5 个（00_meta/05、01_foundation/11、02_intermediate/09、06_ecosystem/13、07_future/05）+ 散落 `*_quiz_*` 文件 + `04_navigation/15_quiz_registry.md`，共 22 个 quiz 相关 md 全部退出图谱。
- 重跑 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py`：`01_concept_definition_atlas.md` 中 quiz 条目 **21 → 0**（grep -ci quiz = 0）。
- 回归：`python scripts/check_topology_quality.py --strict` **exit 0**（T1=0/T2=0.749/T3 跳出 6/189 死端 0/T4=1.0/T5=0/T6=0）；`kb_auditor --link-check` 死链 **0**、exit 0。

## 4. 任务 4：CRLF 归一

- `concept/00_meta/knowledge_topology/kg_tlo_alignment.md` 实测 **已是 LF**（`grep -c $'\r'` = 0；`file` 报告无 CRLF 标记），疑由前序轮次 atlas 生成器统一落盘（`write_out()` 强制 LF）完成。**0 改动，仅验证**。
- `tmp/` 下 4 个历史备份副本未动（tmp 不入版本控制）。

## 5. 验证汇总

| 检查 | 命令 | 结果 |
|---|---|---|
| 脚本语法 | `bash -n scripts/run_quality_gates.sh` | 通过 |
| 门数自洽 | grep `run_gate` + overlap-v2 块 | 22 + 1 = **23**，与结尾计数一致 |
| 新门 1 | `check_mindmap_coverage.py`（观察） | exit 0（11.4% / 71.1%） |
| 新门 2 | `check_quiz_system.py`（观察） | exit 0（失败 0 / 警告 0） |
| 死链 | `python scripts/kb_auditor.py --link-check` | 死链 0、跨层 0，exit 0 |
| 拓扑（quiz 排除后） | `check_topology_quality.py --strict` | exit 0 |
| 构建 | `mdbook build` | exit 0（仅既有 search index 体积 WARN） |
| CI YAML | python yaml.safe_load | 通过；summary needs/jobs 各 22 条 |
| TOC 锚点 | mdbook 渲染 id 实测 | `#-关键属性` 与渲染一致 |

## 6. 遗留

1. 两门按 §5.2 转正规则进入观察期（连续 4 周或 10 次 CI 达标后可评估转阻断）；mindmap 门 --strict 当前即 exit 0，quiz 门 --strict 待评估。
2. 13 个无 TOC 页若后续引入目录区，需同步补「关键属性/概念关系」条目（可复用 `tmp/p4_toc_check.py`）。
3. `nightly_quality_report.yml` 未挂这两门（本任务范围外，如需同步见计划 P5）。
