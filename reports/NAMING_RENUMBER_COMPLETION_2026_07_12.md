# 命名重编号与规范 lint 落地完成报告（2026-07-12）

> 范围：AGENTS.md §4.0 全库重编号收尾统计 + 命名 lint（N1–N6）新建与质量门接入 + v2 去重 SERIES 白名单登记。
> 原则：所有数字均可从文件或命令复核（每条附复核方式）；无法从留存产物复核的数字显式标注，不编造。

---

## 1. 重编号全量统计（可复核）

数据源：`tmp/renumber/mapping_*.csv`、`tmp/renumber/plan_*.md`、`tmp/renumber/apply_log*.md`、`tmp/renumber/phase2_stats.json`。

| 范围 | 映射行 | 变更项 | 明细 | 复核方式 |
|---|---:|---:|---|---|
| `concept/` | 457 | **384 文件** | 扫描 457 个 .md，renumber 384、保持不变 73；README 保持原名 | `tmp/renumber/plan_report.md` 头部；`python -c "import csv;r=list(csv.DictReader(open('tmp/renumber/mapping_concept.csv')));print(sum(1 for x in r if x['old_path']!=x['new_path']))"` → 384 |
| `docs/` | **562** | 558 | 32 目录行 + 530 文件行；apply dry-run 通过 **517 文件移动 + 32 目录改名**；reason 分布：renumber 249 / relocate 166 / dir_rename 32 / prefix_cleanup 11 / unchanged 104 | `tmp/renumber/plan_docs.md` 头部；`mapping_docs.csv`；`phase2_stats.json`（dir_rows=32） |
| `knowledge/` | 139 | **7 文件** | 01_fundamentals 教学顺序环状换号（ownership→borrowing→lifetimes→iterators） | `tmp/renumber/plan_knowledge.md`；`mapping_knowledge.csv` |
| `crates/` | 561 | **245 项** | renumber 227 / relocate 9 / variant_merge_review 8 / prefix_cleanup 1；apply **已执行** 245 移动 | `tmp/renumber/plan_crates.md` 头部；`tmp/renumber/apply_log.md`（scope=crates，"文件移动: 245（已执行）"） |

### 链接重写（按留存日志口径）

| 阶段 | 日志 | 重写文件数 | 重写处数 | 状态 |
|---|---|---:|---:|---|
| docs | `tmp/renumber/apply_log_docs_dryrun.md` | 479 | 约 **9210** | dry-run 记录 |
| knowledge | `tmp/renumber/apply_log_knowledge_dryrun.md` | 10 | 约 **31** | dry-run 记录 |
| crates | `tmp/renumber/apply_log.md` | 98 | 约 **290** | 实执行 |
| **可复核合计** | — | 587 | **约 9531** | — |

> ⚠️ **口径说明**：concept 阶段的 apply 日志未留存（`apply_log.md` 被最后一次 crates apply 覆盖，其头部 scope=crates），concept 384 文件改名的链接重写数无法从留存产物复核。汇总的"约 2.4 万处"无法从 `tmp/renumber/` 现有文件重建，本报告仅确认上述 9531 处可复核下限；如需精确总数，须从 CI 记录或重新 dry-run 历史映射补证。

## 2. 质量终态（本轮实跑复核）

```
$ python scripts/kb_auditor.py        # 2026-07-12 实跑，exit 0
  文件数: 465   死链: 0   跨层问题: 0   模板化 ⟹: 0
```

- **死链终态 0、跨层 0**：✅ 本轮实跑复核（输出存档于 `reports/kb_quality_dashboard.md`）。
- **kb_auditor 跨层检查器修复**：`scripts/kb_auditor.py::check_inter_layer_consistency` 已改为"优先解析到真实文件并用目录结构判定层级（对文件重编号鲁棒）"，失败时回退路径片段推断——修复前对重编号后的 `32_unsafe_boundary_panorama.md` 误报 1 个跨层问题（见 `reports/EXAMPLES_CI_AND_SCRIPTS_CLEANUP_2026_07_12.md`），修复后 0。

## 3. 变体/冗余处置（可复核清单）

**4 个净删除**（viewNN 合并）：`crates/c07_process/docs/` 历史 `view01–05` 五个同质导航 stub 合并为单页 `24_formal_analysis_views.md`（文件内注明"由历史 view01–05 五个同质导航 stub 合并而来（2026-07-12 变体清理）"），净删除 4 个。复核：`ls crates/c07_process/docs/ | grep -c view` → 仅 `24_formal_analysis_views.md`。

**变体后缀 stub（N4 豁免态，3 个）**——均 ≤11 行且含"权威来源"blockquote，命名 lint 按 WARN 处理：

| 文件 | 行数 | 主干 |
|---|---:|---|
| `crates/c07_process/docs/tier_04_advanced/05_testing_and_benchmarking_expanded.md` | 11 | `04_testing_and_benchmarking.md` |
| `crates/c07_process/docs/tier_04_advanced/07_modern_process_libraries_final.md` | 11 | `06_modern_process_libraries.md` |
| `crates/c09_design_pattern/docs/tier_02_guides/04_behavioral_patterns_guide_supplement.md` | 11 | `03_behavioral_patterns_guide.md` |

**其余重编号波次 stub（机器可枚举）**：`concept/` 3 个（safety_tags_in_formal、game_development、rust_edition_guide）、`docs/` 双文件 stub 6 个（06_research 3 + 09_toolchain 2 + 08_guides safety_tags 1）、`knowledge/` 2 个（async_closure、rust_1_95_preview）、crates 根重复 stub 5 个（c05 message_passing + c07 09/10/11/19）。与 `.kimi/NAMING_AND_SEMANTIC_ALIGNMENT_PLAN_2026_07_12.md` N0-2（9 组冗余）+ crates 3 变体的"13 stub"口径一致；精确逐文件归属受"禁止 git"约束无法 diff 复核，以上清单为当前文件系统状态的可复核枚举。

## 4. AGENTS.md §4.0 新规则（已生效）

8 条：目录内两位连续序号（01 起，00 留导览）/ 一级目录连续不跳号 / 同目录禁同号（小目录重排、大目录可留空号须记录）/ 专题系列可无序号须 README 索引 / quizzes 归 `NN_quizzes/` / crates docs 仅 `tier_0N_*` + `NN_`（禁 viewNN、散名、变体后缀）/ 禁双前缀与异形前缀（日期后缀仅限豁免目录）/ 批量重命名统一走 `plan_renumber.py` + `apply_renumber.py`。

## 5. 新增命名 lint（质量门 20，观察）

`scripts/check_naming_convention.py`（重写）：扫描 concept/knowledge/docs/content/crates/*/docs（23 个根，1779 文件/256 目录），实现 N1–N6：

| 规则 | 级别 | 首跑结果 |
|---|---|---:|
| N1 序号格式 NN_ + snake_case slug（无序号系列文件/目录按 WARN） | ERROR/WARN | ERROR 0 / WARN 81 |
| N2 同目录同号冲突 | ERROR | 0（修复后；见下） |
| N3 双前缀/异形前缀 | ERROR | 0 |
| N4 变体后缀（stub 豁免降 WARN） | ERROR/WARN | WARN 3（均为已处置 stub，见 §3） |
| N5 一级目录连续不跳号 | WARN | 1（`docs/` 顶层缺 10_：原 `07_future` 空目录重编号后删除，按大目录留空号策略维持 WARN） |
| N6 中文/空格/混合大小写 | ERROR | 0 |

**首跑发现并已修复 1 个真实遗留 ERROR**：`docs/15_rust_formal_engineering_system/01_theoretical_foundations/` 下 `02_memory_safety` 与 `02_ownership_system` 同号（N2）。处置：`02_memory_safety` → `04_memory_safety`（同时补齐缺号 04，目录变为 01–06 连续），同步更新唯一入链 `crates/c05_threads/README.md:584`。修复后 lint ERROR=0。

默认 exit 0（观察）；`--strict` 时 ERROR>0 则 exit 1（已实测：修复前 --strict exit 1，修复后 exit 0）。

## 6. 质量门接入 diff 要点

- `scripts/run_quality_gates.sh`：新增 `Naming Convention (observe)` 观察门；头部注释与结尾汇总 19→20 门（14 阻断 + 6 观察）；v2 可处置基线 53→54（见 §7 说明）。
- `.github/workflows/quality_gates.yml`：新增 `naming-convention` job（observe，`continue-on-error: true`），加入 summary 的 `needs` 与 jobs 映射；PR 评论页脚 "18 gates (14+4)" → "20 gates (14+6)"（原页脚已过时，一并修正）。
- `.github/workflows/nightly_quality_report.yml`：新增 `naming` 观察门输出与 issue 摘要条目；注释 4→6 观察门；overlap_v2 WARN 阈值 53→54。
- `AGENTS.md`：§5 命令新增命名 lint、19→20 门；§5.1 门清单 19→20（观察 5→6，新增第 20 门）；§5.2 基线表新增 naming convention 行、overlap v2 行更新为复测值；§6 红线"5 语义观察门"→"6 语义观察门"。
- `scripts/README.md`：`check_naming_convention.py` 行更新为质量门 20 描述；`triage_overlap.py` 行补充 SERIES_PAIRS 显式登记说明。

## 7. v2 去重 SERIES 白名单登记（任务 3）

登记位置：`scripts/triage_overlap.py` 新增显式常量 `SERIES_PAIRS`（带复核证据注释，`is_series()` 优先于正则判定，按完整路径 + basename 双匹配容忍重编号）：

1. `crates/c10_networks/docs/07_rust_190_examples_collection.md` ↔ `08_rust_190_examples_part2.md`——人工复核：分章文件（Part1/Part2），实测正文相似度 12.7%，保留分章结构。
2. `crates/c02_type_system/readme_rust_189.md` ↔ `readme_rust_190.md`——人工复核：版本系列 README（1.89/1.90），57% 独特内容，保留。

**复跑验证**（`python scripts/detect_content_overlap_v2.py --budget 999999` + `python scripts/triage_overlap.py`，2026-07-12）：

- 两对确认归入 SERIES（`reports/OVERLAP_TRIAGE_2026-07-12.json`：SERIES=24）。
- ⚠️ **可处置项未下降，维持 54**（MERGE=5 + DOCS_INTERNAL=49；总命中 552，REVIEW=474）。原因：两对本就被 SERIES 正则（`rust_19\d`/`readme_rust_`/`examples_collection`/`_part\d`）覆盖，显式登记是**加固**（不再依赖文件名模式，容忍未来重编号），不改变计数。
- **基线勘误**：AGENTS.md §5.2 原记"MERGE=4+49=53"，实测 MERGE=5——其中 autoverus 对（`concept/04_formal/04_model_checking/07_autoverus.md` ↔ `concept/07_future/03_preview_features/33_autoverus_preview.md`）双向重复计数 2 条，去重后唯一对 4+49=53 与原口径一致。`run_quality_gates.sh` 与 nightly 的 WARN 阈值已按条目口径更新为 54，避免误报升级。

## 8. 复核命令汇总

```bash
python scripts/check_naming_convention.py            # ERROR=0 WARN=85, exit 0
python scripts/check_naming_convention.py --strict   # exit 0
python scripts/kb_auditor.py                         # 死链 0 / 跨层 0, exit 0
python scripts/triage_overlap.py                     # SERIES=24 MERGE=5 DOCS_INTERNAL=49
bash -n scripts/run_quality_gates.sh                 # 语法通过
```
