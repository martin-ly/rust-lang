# 观察门转正与去重检测 v2 升级报告（P2-5 + P3-7）

**EN**: Gate Promotion & Dedup v2 Escalation Report
**Summary**: 评估去重 v2 转阻断可行性并升级为可处理项基线 WARN 判定；4 个语义观察门经本地 --strict 实跑验证后转为阻断门；nightly 补齐至 18 门；3 对疑似重复 workflow 完成判定与处置。

> **日期**: 2026-07-12  **范围**: `scripts/run_quality_gates.sh`、`scripts/check_concept_authority_coverage.py`、`.github/workflows/{nightly_quality_report,quality_gates,ci_optimized,rust_version_tracker,rust_version_tracking,version_tracking,weekly_dependency_check,weekly_deps}.yml`、`AGENTS.md` §5

---

## 1. 任务 A — 去重检测升级（P2-5）

### 1.1 v2 转阻断可行性评估

本地实跑（2026-07-12）：

```
python scripts/detect_content_overlap_v2.py
# scanned=1913 indexed=1417 candidates=536300 hits=592 (same_dir=580 cross_dir=12)
python scripts/triage_overlap.py
# total=592 MERGE=4 DOCS_INTERNAL=49 SERIES=22 REVIEW=517
```

| 指标 | 值 |
|---|:---:|
| v1（现阻断门 8）命中 | 1 对（漏检属实） |
| v2 命中 | 592 对 |
| **可处理项（MERGE+DOCS_INTERNAL）** | **53（4+49）> 0** |
| SERIES（版本系列白名单） | 22 |
| REVIEW（待人工复核） | 517 |

**结论：暂不转阻断。** 前序 P0-5 处置 54 对后仍有 53 个可处理项存量（MERGE 4 / DOCS_INTERNAL 49），若直接转阻断将立即红 CI。过渡方案已实施：

- `run_quality_gates.sh` 中 v2 观察门由“计数报告”升级为**可处理项基线 WARN 判定**：先跑 v2 再跑 `triage_overlap.py`，解析 `OVERLAP_TRIAGE_*.json` 的 MERGE+DOCS_INTERNAL：
  - `> 基线 53` ⇒ ⚠️ WARN 升级提示（新增重复，需先 triage 处置）；
  - `= 0` ⇒ 提示具备转阻断资格（届时改为 `--strict --budget 0`，可处理项>0 即 exit 1）；
  - 其余 ⇒ 维持观察，不置 FAILED。
- **基线记录**：2026-07-12，MERGE=4 + DOCS_INTERNAL=49 = **53**（总命中 592，indexed 1417）。

### 1.2 nightly_quality_report.yml 补齐（9 门 → 18 门）

原 nightly 仅跑 9 门（缺 mermaid 与全部语义观察门）。已补齐，与 `run_quality_gates.sh` / `quality_gates.yml` 对齐：

- 新增 mermaid 语法检查（阻断）。
- 新增 4 个已转正 strict 门：topology / kg_shapes / canonical_uniqueness / concept_consistency（失败触发 issue）。
- 新增 4 个观察门：metadata、overlap v2（含 triage 可处理项输出 `overlap_v2_actionable`，超基线记 `warn`）、semantic_health、authority_coverage（continue-on-error 语义，不触发 issue）。
- issue 触发条件与汇总表同步更新；artifact 上传路径补齐全部 `reports/*` 基线报告。

### 1.3 疑似重复 workflow 对判定

| 对 | 判定 | 处置 |
|---|---|---|
| `ci.yml` vs `ci_optimized.yml` | **真重复**。fmt/clippy/test/doc 在每次 PR 重复运行；ci_optimized 的 miri/bench 已由 `miri.yml`/`performance.yml` 专职覆盖。ci.yml 功能更全（9 jobs：命名规范/nightly-preview/quiz/供应链审计/coverage 等独有价值） | 保留 `ci.yml`；`ci_optimized.yml` 加 DEPRECATED 头注并停用 push/PR 触发（仅手动），其唯一独有价值（多 OS 测试矩阵）备注后续迁入 ci.yml |
| `rust_version_tracker.yml` vs `rust_version_tracking.yml` | **真重复**（同功能：检测最新 stable vs MSRV + 建 issue）。另发现第三方 `version_tracking.yml`（name 同为 "Rust Version Tracking"，周频，委托 `scripts/rust_version_tracker.py`）亦真重复 | 保留功能最全的 `rust_version_tracking.yml`（迁移计划报告/outputs/force_check/180 天留存），加权威头注；另两个加 DEPRECATED 头注并停用调度 |
| `weekly_dependency_check.yml` vs `weekly_deps.yml` | **功能不同，互补**：前者只读检测（outdated+audit 周报 + issue）；后者写操作（cargo update + 测试 + 自动 PR） | 均保留，两文件头注说明分工 |

---

## 2. 任务 B — 观察门转正机制（P3-7）

### 2.1 机制与基线表

已在 `AGENTS.md` §5.1 后新增 **§5.2 观察门转正机制**：连续 4 周（或连续 10 次 CI 运行）达标 → 评估转阻断；转正前提为本地 `--strict` 实跑 exit=0。基线状态表（2026-07-12，摘自 `reports/` 最新基线）：

| 门 | 基线指标 | --strict 实跑 | 状态 |
|---|---|:---:|---|
| topology quality | T1=1.1% / T2=83.3% pass / T3 死端=0 / T4=93.3% / T5=T6=0 | exit 0 | ✅ 已转阻断 |
| KG SHACL | K1–K6=0（K1b=55 仅扣分） | exit 0 | ✅ 已转阻断 |
| canonical uniqueness | 0 处违规 | exit 0 | ✅ 已转阻断 |
| concept consistency | 0 错误级发现 | exit 0 | ✅ 已转阻断 |
| metadata consistency | D1=0 / D2=1 / D3=0 / D5=17 / D6=13（flagged 30/483） | exit 1 | ⏳ 维持观察 |
| overlap v2 | 可处理项 53>0 | — | ⏳ 维持观察（见 §1.1） |
| semantic health | 总分 90.3 grade OK（去重分量 85.0） | exit 0 | ⏳ 维持观察（聚合门，待去重归零） |
| authority coverage | 内容页 any=99.5% / none=2 / 核心缺口=1 | exit 1 | ⏳ 维持观察 |

### 2.2 转正执行（4 门）

前提验证（本地实跑）：`check_topology_quality.py --strict`、`check_kg_shapes.py --strict`、`check_canonical_uniqueness.py --strict`、`concept_consistency_auditor.py --strict` 均 **exit=0**。已在以下两处同步转阻断：

- `scripts/run_quality_gates.sh`：4 门移入阻断段（`--strict`），头部注释记录转正依据；门总数更新为 **14 阻断 + 4 观察 = 18**。
- `.github/workflows/quality_gates.yml`：对应 4 个 job 改 `--strict` + `continue-on-error: false`，名称去 "(observe)"，PR 汇总文案同步。

未达标门维持观察：

- **metadata**（D2=1/D5=17，`--strict` exit=1）。
- **semantic_health**：当前 grade=OK 90.3 分（非任务前提假设的 WARN），但为聚合门且去重分量（85.0）受 overlap v2 可处理项 53 拖累，待去重归零后再评估；其 `--strict` 仅 grade=FAIL 才阻断。
- **authority_coverage**：任务前提为已达标，但 2026-07-12 实跑发现**较 07-11 基线退化**（any 100%→99.5%、none 0→2、核心 L1–L4 缺口 0→1，疑似当日新增内容页所致）。已为其脚本**新增 `--strict` 支持**（any<100% / none>0 / 核心缺口>0 即 exit 1），待恢复达标后可立即转正。
- **overlap v2**：见 §1.1。

## 3. 验证记录

| 项 | 结果 |
|---|---|
| `bash -n scripts/run_quality_gates.sh` | ✅ 语法通过 |
| 8 个改动 workflow `yaml.safe_load` | ✅ 全部通过 |
| 4 个转正门 `--strict` 实跑 | ✅ 全部 exit=0（按 run_quality_gates.sh 顺序整段复跑，FAILED=0） |
| 观察门（metadata/authority/semantic_health）实跑 | ✅ exit=0（观察模式不阻断） |
| v2 可处理项 WARN 块实跑 | ✅ actionable=53 = 基线 ⇒ “未超基线，维持观察”（>53 走 WARN 分支、=0 走转正提示分支，逻辑经 bash 条件验证） |
| `check_concept_authority_coverage.py --strict` | ✅ 新增后实跑 exit=1 并正确列出 3 项失败原因（符合“未达标不转正”判定） |

## 4. 改动文件清单

1. `scripts/run_quality_gates.sh` — 4 门转阻断；v2 升级为可处理项基线 WARN；头注与总数更新
2. `scripts/check_concept_authority_coverage.py` — 新增 `--strict`（阻断阈值：any=100%/none=0/核心缺口=0）
3. `.github/workflows/nightly_quality_report.yml` — 补齐至 18 门，issue 条件与产物路径同步
4. `.github/workflows/quality_gates.yml` — 4 个 job 转 `--strict` 阻断
5. `.github/workflows/ci_optimized.yml` — DEPRECATED 头注 + 停用自动触发
6. `.github/workflows/rust_version_tracker.yml` — DEPRECATED 头注 + 停用调度
7. `.github/workflows/version_tracking.yml` — DEPRECATED 头注 + 停用调度（评估时新发现的第三重复）
8. `.github/workflows/rust_version_tracking.yml` — 权威工作流头注
9. `.github/workflows/weekly_dependency_check.yml` / `weekly_deps.yml` — 分工头注
10. `AGENTS.md` — §5/§5.1 门数更新（14 阻断 + 4 观察），新增 §5.2 观察门转正机制，§6 红线 6 门数同步

## 5. 后续跟进项

- overlap v2：处置存量 53 个可处理项（MERGE 4 / DOCS_INTERNAL 49），归零后将门 16 改 `--strict --budget 0` 转阻断。
- authority coverage：核查当日新增内容页（none=2、核心缺口=1），补齐权威引用后转正。
- metadata：清理 D2=1（foundations_gap_closure_index）与 D5=17（稳定层 nightly 关键词）。
- ci_optimized.yml：多 OS 测试矩阵迁入 ci.yml 后删除该文件。
- 未做 git commit（按任务要求）。
