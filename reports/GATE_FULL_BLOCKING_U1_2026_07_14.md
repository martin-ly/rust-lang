# 质量门全阻断化（U1）报告

**日期**：2026-07-14
**背景**：用户指示将 4 个语义观察门（metadata consistency / concept code blocks / mindmap coverage / semantic health）全部转阻断，达成 **23 门全阻断（23 blocking + 0 semantic observe）**；观察门机制保留，当前 0 个在观察。

## 1. 转阻断前提：4 门 `--strict` 单独实跑（2026-07-14）

| 门 | 命令 | 实测指标 | exit |
|---|---|---|:---:|
| Metadata Consistency | `python scripts/check_metadata_consistency.py --strict` | D1–D6 全 0（D2/D5 白名单豁免登记不变） | 0 |
| Concept Code Blocks | `python scripts/check_concept_code_blocks.py --strict`（默认抽样） | rot=0：candidate 抽样 300 pass/0 fail；compile_fail 822 ok/0 标注腐烂 | 0 |
| Mindmap Coverage | `python scripts/check_mindmap_coverage.py --strict` | 内容页 430：mindmap 387（90.0%）/ 反例 363（84.4%），阈值 10%/40% | 0 |
| Semantic Health | `python scripts/semantic_health.py --strict` | 总分 99.6 grade OK（meta 100.0 / topo 98.4 / dedup 100.0 / kg 100.0） | 0 |

## 2. 改动文件

| 文件 | 改动 |
|---|---|
| `scripts/run_quality_gates.sh` | 4 个观察门移入阻断段并加 `--strict`（code blocks 用默认抽样保持时长可控）；头部注释改为 23 blocking + 0 observe；观察段保留注释说明（机制保留，当前 0 个观察门）；结尾输出改为 `23 blocking + 0 semantic observe` |
| `.github/workflows/quality_gates.yml` | metadata-consistency / semantic-health / concept-code-blocks / mindmap-coverage 4 个 job：去 `continue-on-error: true` 改 false、命令加 `--strict`、名称改 `(strict)`；summary jobs 映射名称同步；页脚改 `23 blocking + 0 semantic observe` |
| `.github/workflows/nightly_quality_report.yml` | 头部注释对齐 23 阻断 + 0 观察；metadata / semantic_health 从观察位移入阻断位并加 `--strict`；新增 code_blocks / mindmap 两个阻断输出（原 nightly 未挂载，对齐本地门集）；issue 触发条件与 job 汇总表同步纳入 4 门 |
| `AGENTS.md` | §5 命令注释；§5.1 标题与门表（23 阻断，门 20–23 转 `--strict` 阻断，观察门段改为「0，机制保留」说明）；§5.2 改为「观察门机制说明（当前 0 个在观察）」，基线表 4 行标 ✅ 已转阻断 2026-07-14 并更新复测指标；§6 红线 6 门数表述；最后更新行 |
| `scripts/README.md` | 门 20/21/22/23 条目「观察」改「阻断（2026-07-14 转阻断）」；`run_quality_gates.sh` 条目改 23 阻断 + 0 观察 |

## 3. 验证结果

- `bash -n scripts/run_quality_gates.sh`：OK。
- YAML `safe_load`：`quality_gates.yml` / `nightly_quality_report.yml` 均 OK。
- 4 门单独 `--strict` 实跑：全部 exit 0（见 §1）。
- `bash scripts/run_quality_gates.sh` 全量：**EXIT=0**，无 ❌ 行，结尾输出
  `✅ All 23 quality gates passed (23 blocking + 0 semantic observe).`
  23 个 `run_gate` 全部 passed（10 基础 + 8 strict 转正 + overlap v2 actionable=0 + 4 新转阻断）。

## 4. 备注

- 观察门转正机制（AGENTS.md §5.2）保留：新增观察门在 `run_quality_gates.sh` 观察段与 `quality_gates.yml` 以 `continue-on-error: true` + `(observe)` 后缀挂载，达标后按流程转阻断。
- code blocks 门 `--strict` 使用默认分层抽样（300/候选 + 全量 compile_fail），门内运行时长可控；`--with-deps` 依赖块实测仍不挂入门内（需先 `cargo build --workspace`）。
- 与并行代理的 concept/ 反例节回填无文件交集；本次改动仅触及门编排、CI workflow 与文档。
