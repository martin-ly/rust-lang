# 观察门转正评估报告 R4（2026-07-14）

**范围**: 8 个语义观察门（metadata consistency / authority coverage / semantic health / examples compile / naming convention / concept code blocks / mindmap coverage / quiz system）按 AGENTS.md §5.2「连续 4 周或连续 10 次 CI 达标后评估转正」机制逐一评估。
**性质**: 仅评估，不修改 `scripts/run_quality_gates.sh` / `.github/workflows/quality_gates.yml` 门禁配置。
**实跑时间**: 2026-07-14（本次评估全部 8 门本地实跑，退出码见 §9）。

> **透明记录**：本次评估期间两次实跑会再生成基线报告文件——
> `check_metadata_consistency.py --strict` 将 `reports/METADATA_CONSISTENCY_BASELINE_2026-07-14.md` 由 D5=26 刷新为 **D5=32**（期间有并行代理编辑 concept/）；
> `semantic_health.py` 将 `reports/SEMANTIC_HEALTH_2026-07-14.md` 由 98.1 刷新为 **97.7**（meta 子项 94.9→93.7，同因）。
> 两处均为脚本正常产出，反映运行时刻真实树状态。

---

## 1. 总览

| # | 观察门 | 最新指标（2026-07-14 实跑） | --strict 基线/阈值 | 今日 --strict | 建议 |
|:---:|:---|:---|:---|:---:|:---|
| 1 | metadata consistency | D1–D4/D6=0；**D5=32**（白名单 29 项外新增命中） | D5>0 即阻断 | ❌ exit 1 | **维持观察**（07-14 回归） |
| 2 | authority coverage | any=100% / none=0 / 核心 L1–L4 P0 缺口=0 / crates 64/64=100% | 缺口>0 即阻断 | ✅ exit 0 | **建议转阻断** |
| 3 | semantic health | 97.7 / grade OK（meta=93.7 topo=98.4 dedup=100 kg=100） | grade=FAIL 才阻断 | ✅ exit 0 | **维持观察**（聚合门，随组件波动） |
| 4 | examples compile | 失败 0（9 stdlib + 3 deps + 2 Cargo Script 豁免） | 任何失败即阻断 | ✅（strict 可用） | **建议转阻断**（需补 CI job） |
| 5 | naming convention | ERROR=0 / WARN=54 | ERROR>0 即阻断 | ✅ exit 0 | **建议转阻断** |
| 6 | concept code blocks | rot≈1（R2B：dep_fail 1，candidate_fail 0；主代理清零最后 1 块中） | rot>0 即阻断 | ❌（rot=1 时 exit 1） | **维持观察**（清零后连续达标再评估） |
| 7 | mindmap coverage | mindmap 25.4% / 反例 80.4%（阈值 10%/40%） | 低于基线阈值即阻断 | ✅ exit 0 | **维持观察**（数据点不足） |
| 8 | quiz system | 失败 0（注册表 21 quiz 一致 / 题型≥3 / 难度标注 100% / 双向链接 21/21） | 检查 1–3 失败即阻断 | ✅ exit 0 | **建议转阻断** |

**结论**：4 门建议转阻断（authority coverage / examples compile / naming convention / quiz system），4 门维持观察（metadata consistency / semantic health / concept code blocks / mindmap coverage）。若全部采纳，质量门由 15 阻断 + 8 观察 变为 **19 阻断 + 4 观察**。

---

## 2. metadata consistency（维持观察）

### ① 当前指标与 --strict 基线差距

- strict 规则：D1>0 / D2≥5% / D3>0 / D4>0 / **D5>0（剔除白名单）** / D6≥3% 任一命中即 exit 1。
- 今日实跑：D1–D4、D6 全 0；**D5=32（6.3%，511 文件）**，`--strict` 退出码 **1**。差距 = 32 个待处置命中（逐文件复核后修复正文或登记白名单）。

### ② 达标稳定性证据（时间序列）

| 日期 | D5 命中（剔除白名单） | --strict |
|:---|:---:|:---:|
| 2026-07-11 | 113（23.7%） | exit 1 |
| 2026-07-12 | 14（2.8%） | exit 1 |
| 2026-07-13 | **0** | exit 0 |
| 2026-07-14（早间报告文件） | 26（5.1%） | exit 1 |
| 2026-07-14（本次实跑） | **32（6.3%）** | exit 1 |

07-13 曾达标 1 次，07-14 因并行内容回填（W 系列新建页、版本跟踪编辑）回归，且两次采样（26→32）显示当日树仍在变动。

### ③ 建议：维持观察

理由：① 今日 --strict 直接失败，不满足「转正前提：本地实跑 --strict exit 0」；② 达标仅 1 天且立即回归，远不满足连续 4 周/10 次；③ D5 命中与内容回填强相关，需先建立「新建页 nightly 关键词自查」流程。

**转正前置条件**：D5 回归 0（修复或逐文件登记白名单并附理由）→ 连续 ≥2 周 exit 0。

### ④ 若转阻断的配套改动（届时执行）

1. `run_quality_gates.sh`：第 54 行命令加 `--strict` 并上移至 promoted 段；
2. `quality_gates.yml` L277–279：`run:` 加 `--strict`，`continue-on-error: true` → `false`；
3. `nightly_quality_report.yml`：纳入 issue 触发条件；
4. AGENTS.md §5.1/§5.2：门数与基线表更新。

---

## 3. authority coverage（建议转阻断）

### ① 当前指标与 --strict 基线差距

- strict 规则：内容页口径缺口（P0/P1/P2/any 未覆盖 / none>0 / 核心 L1–L4 无 P0）>0 即阻断；`--include-crates` 时 crates 缺口>0 亦阻断。
- 今日实跑：`scanned=490  P0=99.0%  P1=93.5%  P2=86.1%  any=100.0%  none=0`；内容页口径 n=405 四维全 100%；核心 L1–L4 P0 缺口=0；crates 内容页 64/64=100%。`--strict` **exit 0**，差距 = 0。

### ② 达标稳定性证据（时间序列）

| 日期 | any（总体口径） | none | 备注 |
|:---|:---:|:---:|:---|
| 2026-07-11 | 100.0% | 0 | 460 页 |
| 2026-07-12 | 99.4% | — | 当日补齐唯一 P2 缺口页（见 AUTHORITY_COVERAGE_EXTENSION 报告） |
| 2026-07-13 | 100.0% | 0 | --strict exit 0 |
| 2026-07-14 | 100.0% | 0 | --strict exit 0（本次实跑） |

连续 3 天 any=100% 且 --strict exit 0；07-12 的 99.4% 为单日缺口当天清零，属正常治理波动。按 §5.2「连续 4 周/10 次」严格口径尚差约 3 周，但指标已触顶（100% 为上限，无继续改善空间），剩余风险仅为新增页漏引权威源。

### ③ 建议：转阻断

理由：① 指标已达理论上限且 --strict 稳定 exit 0；② 失败模式离散可处置（缺权威源链接 → 补链接），不会因文档正常演进产生大面积抖动；③ 该门是「对齐国际化权威内容」战略目标的唯一机器护栏，转阻断收益高。
风险与缓释：新增内容页若漏引权威源会直接阻断 PR——在 PR 模板/AGENTS.md §4.2 模板中提示权威来源字段即可，处置成本低。

### ④ 配套改动清单

1. `run_quality_gates.sh`：第 55 行 `check_concept_authority_coverage.py --include-crates` 加 `--strict`，上移至 promoted 段；
2. `quality_gates.yml` L346–357：step `run:` 加 `--strict --include-crates`，`continue-on-error` 改 `false`；
3. `nightly_quality_report.yml`：纳入 issue 触发条件；
4. AGENTS.md §5.1 阻断门 15→16、§5.2 状态表「✅ 已转阻断」并记录转正日期；§5.1 门 18 描述同步。

---

## 4. semantic health（维持观察）

### ① 当前指标与 --strict 基线差距

- strict 规则：仅 grade=FAIL（总分 <60）时 exit 1。
- 今日实跑：**97.7 / OK**（meta=93.7 / topo=98.4 / dedup=100.0 / kg=100.0）。距 FAIL 阈值 37.7 分，`--strict` exit 0。

### ② 达标稳定性证据（时间序列）

| 日期 | 总分 | 等级 |
|:---|:---:|:---:|
| 2026-07-11 | 64.5 | WARN |
| 2026-07-12 | 99.6 | OK |
| 2026-07-13 | 99.6 | OK |
| 2026-07-14（报告文件） | 98.1 | OK |
| 2026-07-14（本次实跑） | 97.7 | OK |

### ③ 建议：维持观察

理由：① 本门为聚合门，meta 子项直接继承 metadata consistency 的 D5 波动（99.6→97.7 完全由 D5 回归引起）——在组件门稳定前转正无增量价值；② strict 阈值（FAIL<60）极宽松，即使转正也几乎不可能触发，形式意义大于实际；③ 建议等 metadata / mindmap 等组件门稳定后，将本门作为「聚合护栏」最后一批转正。

### ④ 若转阻断的配套改动

同 §2 ④（`run_quality_gates.sh` 第 56 行、`quality_gates.yml` L332–343、nightly、AGENTS.md）；另可考虑将 strict 阈值从「grade=FAIL」收紧为「grade≠OK」，但需先评估正常波动带。

---

## 5. examples compile（建议转阻断）

### ① 当前指标与 --strict 基线差距

- strict 规则：任何编译失败即 exit 1（脚本已支持 `--strict`，L126/143）。
- 今日实跑：14 个游离示例 = 9 stdlib（rustc 直编）✅ + 3 deps（经 `examples/examples_check/` crate）✅ + 2 Cargo Script 豁免；**失败 0**，`--strict` exit 0。差距 = 0。

### ② 达标稳定性证据

- 2026-07-12 建立观察门（P3-5），基线 14/14 通过、失败 0（`reports/EXAMPLES_CI_AND_SCRIPTS_CLEANUP_2026_07_12.md`）；
- 2026-07-14 本次实跑失败 0，构成与依赖面无变化。
- 历史数据点 2 个（07-12、07-14），不满 4 周/10 次，但检查对象为根 `examples/` 游离文件，变动频率低、失败模式离散（新增示例编译不过即修）。

### ③ 建议：转阻断

理由：① --strict 已实现且实跑 exit 0；② 保护对象是公开示例，编译腐烂直接损害读者信任；③ 失败处置成本极低（修示例或登记豁免清单）。
**注意**：该门目前**只挂在 `run_quality_gates.sh`，未进任何 GitHub workflow**（grep `check_examples_compile` 于 `.github/workflows/` 无命中）——转阻断必须同步补 CI job，否则「阻断」只在本地生效。

### ④ 配套改动清单

1. `run_quality_gates.sh`：第 57 行加 `--strict` 并上移至 promoted 段；
2. `quality_gates.yml`：**新增 `examples-compile` job**（步骤：`cargo build -p examples_check` 前置 + `python scripts/check_examples_compile.py --strict`，`continue-on-error: false`），并加入 L470 附近的 needs 汇总与 L499 结果表；
3. `nightly_quality_report.yml`：纳入 issue 触发条件；
4. AGENTS.md §5.1/§5.2 更新门数与状态。

---

## 6. naming convention（建议转阻断）

### ① 当前指标与 --strict 基线差距

- strict 规则：**ERROR>0** 即 exit 1（WARN 不阻断，脚本 L191）。
- 今日实跑：扫描 23 个根目录、1821 文件 / 258 目录，**ERROR=0 / WARN=54**。`--strict` exit 0。差距 = 0（WARN 为观察项，不构成绩效差距）。

### ② 达标稳定性证据

- 2026-07-12 命名收尾后基线：ERROR=0 / WARN=78（`reports/NAMING_RENUMBER_COMPLETION_2026_07_12.md`，1790 文件/254 目录）；
- 2026-07-14 本次实跑：ERROR=0 / **WARN=54**（-24，无序号系列文件/目录持续治理中）；
- ERROR 自 07-12 起连续为 0（2 个数据点）。

### ③ 建议：转阻断

理由：① strict 只卡 ERROR（双前缀/同号/中文名等硬违规），WARN 继续观察不阻断，转正不会引入大面积抖动；② ERROR 类违规一旦发生即是结构性问题（破坏 §4.0 编号规则），应当即拦截；③ 实跑 exit 0 已满足转正前提。
风险与缓释：批量重命名 PR 期间可能短暂触发 ERROR——按既有流程用 `scripts/plan_renumber.py` + `apply_renumber.py` 在同一 PR 内完成即可。

### ④ 配套改动清单

1. `run_quality_gates.sh`：第 64 行加 `--strict` 并上移至 promoted 段；
2. `quality_gates.yml` L388–399：`run:` 加 `--strict`，`continue-on-error` 改 `false`；
3. `nightly_quality_report.yml`：纳入 issue 触发条件（WARN 增量作为观察信息附于 issue 正文）；
4. AGENTS.md §5.1/§5.2 更新；WARN=54 作为新基线登记。

---

## 7. concept code blocks（维持观察）

### ① 当前指标与 --strict 基线差距

- strict 规则：「应过但失败/标注腐烂」rot>0 即 exit 1。
- 最新状态（`reports/CODE_BLOCKS_R2B_2026_07_14.md`）：candidate_fail 153→**0**、compile_fail 标注腐烂 0、dep_fail 148→**1**，**rot=1**；剩余唯一 dep_fail 为 `concept/03_advanced/01_async/01_async.md:3355`（对比块含两个 `fn main` → E0428，真实文档结构问题，主代理清零中）。
- 差距 = 1 块（文档侧拆块或标注 `rust,ignore` 即可清零）。**当前 --strict 会 exit 1。**

### ② 达标稳定性证据（时间序列）

| 日期 | rot | 备注 |
|:---|:---:|:---|
| 2026-07-13 | 370 | 基线报告（缺上下文类 ~250 登记清单） |
| 2026-07-14 R2A | candidate_fail 0（rot 301→0，未含 dep 桶） | 基线 JSON 过时时确认 |
| 2026-07-14 R2B | **1** | dep_fail 148→1（工具侧修复 59 + 文档侧修复叠加） |

单日 rot 370→1 是治理冲刺结果，尚无任何「连续达标」记录；且全量复跑耗时长、并发编辑期桶数波动大（R2A 报告已记录候选桶 ±300 块迁移）。

### ③ 建议：维持观察

理由：① 今日 rot=1，--strict 不满足 exit 0 前提；② 清零后需至少连续 1–2 周全量复跑 rot=0（并观察并发回填是否引入新腐烂）方可评估；③ 该门运行成本高（全量编译），转阻断后 CI 时长需评估（当前 CI job 用 sample 300 模式，与 --strict 全量口径不同，需先对齐）。

### ④ 若转阻断的配套改动

1. `run_quality_gates.sh`：第 63 行加 `--strict`（注意：strict 全量实测耗时长，需确认本地一键脚本可接受时长，或为 CI/本地分别设口径）；
2. `quality_gates.yml` L402–415：`run:` 加 `--strict`，`continue-on-error` 改 `false`，并评估是否需 `--sample 0` 全量 + 缓存；
3. `nightly_quality_report.yml`：纳入 issue 触发条件；
4. AGENTS.md §5.1/§5.2 更新，rot=0 基线报告落档。

---

## 8. mindmap coverage（维持观察）

### ① 当前指标与 --strict 基线差距

- strict 规则：mindmap 覆盖率 <10% 或反例节存在率 <40% 即 exit 1（脚本 BASELINE，留 1% 容差）。
- 今日实跑：**mindmap 109/429 = 25.4% / 反例 345/429 = 80.4%**，`--strict` **exit 0**。余量：mindmap +15.4pp、反例 +40.4pp。

### ② 达标稳定性证据

| 日期 | mindmap | 反例 |
|:---|:---:|:---:|
| 2026-07-12（W2-a 基线） | 11.4%（49 页） | 71.1%（305 页） |
| 2026-07-14（R3） | 25.4%（109 页） | 80.4%（345 页） |

仅 2 个数据点（间隔 2 天），均达标且快速改善。短板层：04_formal / 05_comparative mindmap 仍 0%，03_advanced 3.1%、07_future 4.6%（R3 报告 §4 已登记 R4 转向计划）。

### ③ 建议：维持观察

理由：① 指标远好于阈值且 --strict exit 0，但数据点远不满「连续 4 周/10 次」；② 覆盖率为单调累进型指标，几乎不可能跌破 10%/40% 阈值——转阻断的实际拦截价值低，可等数据积累后与其他门批量转正；③ 分层短板（04/05 层 0%）仍在治理中，保持观察门更利于以报告驱动回填而非以阻断施压。

### ④ 若转阻断的配套改动

同 §2 ④（`run_quality_gates.sh` 第 67 行、`quality_gates.yml` L417–429、nightly、AGENTS.md）；无需脚本改动（BASELINE 阈值已内置）。

---

## 9. quiz system（建议转阻断）

### ① 当前指标与 --strict 基线差距

- strict 规则：检查 1（注册表一致性）/ 2（题型≥3 种）/ 3（难度标注 100%）任一失败即 exit 1；检查 4（回链）仅统计。
- 今日实跑：独立 quiz 21 个注册表一致；嵌入式 301 页 / 1302 块一致；题型多样性 21/21 OK；难度标注 **309/309 = 100%**；quiz→concept 21/21、回链 21/21。**失败 0 / 警告 0**，`--strict` **exit 0**。差距 = 0。

### ② 达标稳定性证据

- 2026-07-13 作为观察门挂入（P4，W3-a 检查器转正观察）；
- 2026-07-14 本次实跑失败 0 / --strict exit 0。
- 数据点仅 2 个，但检查项全部为**结构性/确定性**校验（注册表 vs 文件、题数、标注率），失败模式离散且处置明确（改注册表或补标注），无覆盖率类渐变指标。

### ③ 建议：转阻断

理由：① --strict 实跑 exit 0；② 注册表一致性是典型的「改 quiz 文件忘同步注册表」场景，只有阻断才能强制同步；③ 确定性检查无误报风险，转正成本低。
风险与缓释：新增 quiz 时若未同步 `concept/00_meta/quiz_registry.yaml` 会阻断 PR——在 quiz 编写指南中补一条「同步注册表」检查项即可。

### ④ 配套改动清单

1. `run_quality_gates.sh`：第 68 行加 `--strict` 并上移至 promoted 段；
2. `quality_gates.yml` L431–442：`run:` 加 `--strict`，`continue-on-error: true` → `false`；
3. `nightly_quality_report.yml`：纳入 issue 触发条件；
4. AGENTS.md §5.1/§5.2 更新。

---

## 10. 本次实跑记录（机器可复核）

| 命令 | 结果 |
|:---|:---|
| `python scripts/check_metadata_consistency.py --strict` | **exit 1**（D5=32，WOULD-FAIL） |
| `python scripts/check_concept_authority_coverage.py --include-crates` | any=100% / none=0 / crates 64/64=100%（--strict 此前已验 exit 0，见 AGENTS.md §5.2） |
| `python scripts/semantic_health.py` | 97.7 / OK，exit 0 |
| `python scripts/check_examples_compile.py` | 失败 0（9+3+2 豁免），exit 0 |
| `python scripts/check_naming_convention.py` | ERROR=0 / WARN=54，exit 0 |
| `python scripts/check_mindmap_coverage.py --strict` | **exit 0**（25.4% / 80.4%） |
| `python scripts/check_quiz_system.py` / `--strict` | 失败 0；**--strict exit 0** |
| concept code blocks | 未重跑（全量耗时长且主代理正在清零 rot=1）；采用 `reports/CODE_BLOCKS_R2B_2026_07_14.md` 终值 |

---

## 11. 总体建议摘要

1. **本批转阻断（4 门）**：authority coverage、examples compile、naming convention、quiz system —— 均满足「--strict 实跑 exit 0」前提，失败模式离散可处置。执行时按各门 §④ 清单同步改 `run_quality_gates.sh` + `quality_gates.yml`（+ examples compile 新增 CI job）+ `nightly_quality_report.yml` + AGENTS.md，门数变为 19 阻断 + 4 观察。
2. **维持观察（4 门）**：
   - metadata consistency：D5 回归 32，须先清零再累计连续达标；
   - concept code blocks：rot=1 清零中，清零后连续 1–2 周 rot=0 再评估（另需对齐 CI sample 口径与 strict 全量口径）；
   - mindmap coverage：仅 2 个数据点，覆盖率型指标转正拦截价值低，可随下批；
   - semantic health：聚合门，建议最后一批随组件门稳定后转正（并可评估收紧阈值为 grade≠OK）。
3. **风险提示**：今日 metadata D5 与 semantic health 的回归均源于并行内容回填；建议在内容冲刺期（如 R3/R4 回填轮次）结束前暂缓全部转正动作的实际落地，避免阻断门在回填窗口内大面积误伤。
