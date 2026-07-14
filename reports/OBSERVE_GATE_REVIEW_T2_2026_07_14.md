# 观察门转正再评估（T2 轮）

> **日期**: 2026-07-14
> **范围**: 4 个语义观察门（metadata consistency / concept code blocks / mindmap coverage / semantic health）
> **方式**: 逐一本地实跑 `--strict`（或等价严格模式）取当前数字；**只评估，不改门禁**（`scripts/run_quality_gates.sh` 未动）
> **转正规则**（AGENTS.md §5.2）：连续 4 周（或连续 10 次 CI 运行）达标且本地 `--strict` exit=0，经评估后转阻断
> **执行约束**: 未执行任何 git 命令

---

## 1. 实跑证据

### 1.1 metadata consistency（门 20）

```text
$ python scripts/check_metadata_consistency.py --strict   → exit 0
[P0-1] scanned=512 flagged_files=0
  D1=0  D2=0  D3=0  D4=0  D5=0  D6=0 （全 0）
报告: reports/METADATA_CONSISTENCY_BASELINE_2026-07-14.md
```

- D1–D6 **全 0**，`--strict` **exit 0**。
- 自 2026-07-12 归零以来连续达标（07-12、07-13、07-14 三次本地实跑同值；D2 豁免 2 项 / D5 豁免 29 项均已显式登记白名单）。

### 1.2 concept code blocks（门 21）

```text
$ python scripts/check_concept_code_blocks.py --sample 0 --with-deps \
    --json tmp/cb_t2.json --report reports/CONCEPT_CODE_BLOCKS_T2_RECHECK_2026_07_14.md
total=4994  tested=2867（candidate 1876 全过 / compile_fail 816 块 815 ok / dep 175 块 149 pass + 26 无 rmeta）
rot_total = 1（compile_fail_unexpected_pass）
脚本逻辑（line 821）: --strict 且 rot > 0 → exit 1  ⇒ 当前 --strict exit 1
```

- **rot 从基线 370 → 1**（2026-07-13 基线后并行轮次修复了缺上下文类 ~250 与其余腐烂块；本次全量复跑实测）。
- 唯一剩余腐烂块：`concept/06_ecosystem/01_cargo/20_cargo_manifest_targets.md:187`，`rust,compile_fail` 块（`harness = false` 测试目标缺 main，标注 E0601）在检查器直编 harness 下编译通过 → `cf_unexpected_pass`（标注与实测语义差异，属真腐烂 1 块）。
- `--strict` **exit 1**（rot=1>0，脚本 line 821 逻辑 + 当前 JSON 数据双重确认）。

### 1.3 mindmap coverage（门 22）

```text
$ python scripts/check_mindmap_coverage.py --strict   → exit 0
TOTAL 内容页 430：mindmap 170 (39.5%) / 反例存在 353 (82.1%)
基线阈值（--strict）: mindmap >= 10%, 反例 >= 40%
```

- M1（mindmap 覆盖率）= **39.5%**（基线阈值 10%，远超）；M2（反例节存在率）= **82.1%**（基线阈值 40%，远超）。
- `--strict` **exit 0**。分层看 03_advanced mindmap 仅 3.1%、07_future 仅 7.6%，但门阈值为全库聚合口径，不构成分层阻断条件。

### 1.4 semantic health（门 23）

```text
$ python scripts/semantic_health.py   → exit 0
[P4] total=99.6 grade=OK (meta=100.0 topo=98.4 dedup=100.0 kg=100.0)
报告: reports/SEMANTIC_HEALTH_2026-07-14.md
```

- 总分 **99.6 grade OK**，与 2026-07-13 同值；该门 `--strict` 仅在 grade=FAIL 时阻断，当前 exit 0。
- 聚合门：其数值由 metadata/topology/dedup/KG 四个子项合成，自身无独立新信号。

## 2. 转正结论表

| 观察门 | 当前指标 | `--strict` exit | 结论 | 理由 / 所需条件 |
|:---|:---|:---:|:---|:---|
| metadata consistency | D1–D6 全 0（scanned 512，flagged 0） | 0 | **维持观察**（已具备转正技术条件） | 指标与 exit 均满足转正前提；但 §5.2 要求连续 4 周或 10 次 CI 达标，自 07-12 归零起仅 ~3 次本地实跑、<1 周。**条件**：累计满 4 周/10 次 CI 达标后在下一轮评估转正 |
| concept code blocks | rot=1（基线 370 → 1；tested 2867） | **1** | **维持观察** | `--strict` 当前 exit 1，不满足"转正前提：本地实跑 --strict exit=0"。**条件**：① 清零 `20_cargo_manifest_targets.md:187` 的 `cf_unexpected_pass`（修正标注或改写为可在检查器 harness 下复现 E0601 的形态）；② rot=0 后连续达标再评估 |
| mindmap coverage | M1=39.5%（阈值 10%）/ M2=82.1%（阈值 40%） | 0 | **维持观察** | 数值远超阈值且 exit 0，技术条件满足；同样受 4 周/10 次 CI 连续达标要求约束（07-13 P4 才挂入 CI，仅 1 天）。**条件**：连续达标期满；另建议关注 03_advanced（3.1%）/07_future（7.6%）分层低位，作为内容改进项而非门禁条件 |
| semantic health | 99.6 grade OK（meta 100/topo 98.4/dedup 100/kg 100） | 0 | **维持观察** | 聚合门，无独立信号；随子门转正后自然具备转正基础。**条件**：4 周/10 次 CI 达标 + 建议待 concept code blocks 子项改善后再议 |

**本轮无门转阻断**。metadata consistency 与 mindmap coverage 已达"指标 + exit"技术条件，唯一缺口是连续达标时长；concept code blocks 是唯一硬性不达标项（rot=1 使 --strict exit 1）。

## 3. 关联说明

- 本评估与同日 S3 转正 4 门（authority coverage / quiz system / naming convention / examples compile）无重叠：该 4 门已在 `quality_gates.yml` 为阻断 job，本轮仅将其纳入 nightly workflow（见 `.github/workflows/nightly_quality_report.yml` 变更与 T2 任务汇报）。
- 复跑产物：`tmp/cb_t2.json`、`tmp/cb_t2_run.log`（tmp/ 不入版本控制）、`reports/CONCEPT_CODE_BLOCKS_T2_RECHECK_2026_07_14.md`、`reports/METADATA_CONSISTENCY_BASELINE_2026-07-14.md`、`reports/SEMANTIC_HEALTH_2026-07-14.md`、`reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-14.md`。
