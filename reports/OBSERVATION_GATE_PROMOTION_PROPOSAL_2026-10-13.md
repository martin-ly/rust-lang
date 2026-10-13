# 观察门 O1–O5 转正评估建议书（2026-10-13）

> 依据：AGENTS.md §5.2 转正规则原文——"任一语义观察门**连续 4 周（或连续 10 次 CI 运行）达标**，经评估后转为阻断门（在 `run_quality_gates.sh` 与 `quality_gates.yml` 中改为 `--strict` 且 `continue-on-error: false`）。转正前提：本地实跑 `--strict` 当前 exit=0。"
> 证据源：`reports/QUALITY_GATES_BASELINE_2026-10-13{,_b,_c}.txt`（三轮全量存档）、`reports/OBSERVE_GATE_BASELINE_2026_07_28.md`、`reports/OBSERVATION_GATES_BASELINE_2026-07-31.md`、`reports/P10_QUALITY_GATE_{BASELINE,WATCH}_2026_08_04.md`、各门日期化 JSON/MD 存档、git log、`.github/workflows/quality_gates.yml`。
> 只读分析，未修改任何既有文件；本报告为唯一新增文件。

## 0. 全局连续性事实（先于逐门判定）

- 观察门建立：2026-07-15（AGENTS.md §5.2："2026-07-15 起新增 O1/O2/O3/O4/O5 五个语义观察门"）。
- git log 月度提交数（`git log --since=2026-07-15` 统计）：2026-07 = 125，2026-08 = 55，**2026-09 = 0**，2026-10 = 18。最后一次 8 月提交为 2026-08-12 `183cc9270`，下一次提交为 10 月中旬；**08-12 → 10-12 约 9 周无任何提交**。
- `quality_gates.yml` 触发条件为 `push`/`pull_request`（main/master）：9 月无提交 ⇒ 该窗口内 CI 质量门大概率无运行记录，"连续 4 周/10 次 CI"链条在 08-12 处断裂。
- 本机无 `gh` CLI，远端 Actions 运行历史无法直接核验；连续性证据只能取自 reports/ 日期化存档与 git log。
- 当前链条：2026-10-12 复跑 + 2026-10-13 三轮全量存档（`_b`/`_c` 提交 `9bd680625`、`cbcc42a34` 明确记录"全量门复跑存档 b/c（23门全绿）"），共 4 次达标，尚不足 10 次/4 周。
- 转正前提"本地实跑 `--strict` 当前 exit=0"：最近一次五门 `--strict` 全 PASS 记录为 `OBSERVATION_GATES_BASELINE_2026-07-31.md`（"O1…✅ PASS / O2…✅ PASS / O3…✅ PASS / O4…✅ PASS / O5…✅ PASS"）；10-13 三轮存档按 `run_quality_gates.sh` 观察段以**无 `--strict`** 方式运行（如 `run: python scripts/check_stub_purity.py`），五门均 ✅。**各门转正前需在当前 HEAD 重跑一次 `--strict` 确认 exit=0**（本任务只读，未执行）。

---

## 1. O1 — Stub Purity（`scripts/check_stub_purity.py`）

**判定：继续观察（指标达标，连续性链条不足）。**

- 定义（§5.1 表 O1 行）："`docs/`/`knowledge/`/`content/`/`crates/*/docs/` 中声明为 stub/redirect 的文件是否保留通用概念完整正文"；转阻断条件原文："伪 stub=0 且空壳页=0"。
- 证据清单：
  - AGENTS.md §5.1 基线行："伪 stub 51 / 空壳页 0 / 高重复 0（`reports/STUB_PURITY_BASELINE_2026_07_15.md`）"——建门时伪 stub=51，未达标。
  - `OBSERVE_GATE_BASELINE_2026_07_28.md` O1 段："伪 stub（声明为 stub 但正文过长）：0 / 空壳页…：0 / 高重复正文…：0"（扫描页数 1029）——首次全 0。
  - `OBSERVATION_GATES_BASELINE_2026-07-31.md`："O1 | `python scripts/check_stub_purity.py --strict` | ✅ PASS | 伪 stub 0 / 空壳页 0 / 高重复正文 0"。
  - `P10_QUALITY_GATE_WATCH_2026_08_04.md`："全部 5 个观察门通过"。
  - 三轮存档（.txt/_b/_c 同值）："扫描页数：1035 / 伪 stub…：0 / 空壳页…：0 / 高重复正文…：0" + "✅ Stub Purity (observe) passed"。
- 达标判定：指标条件（伪 stub=0 且空壳页=0）自 2026-07-28 起持续满足；但达标记录仅 07-28、07-31、08-04、10-12、10-13×3，08-04→10-12 之间无任何运行记录，不构成连续 4 周或连续 10 次。
- 转正建议+风险：不建议本轮转正。缺的证据：08-12 后连续 ≥10 次 CI（或连续 4 周）达标记录；当前 HEAD 的 `--strict` 实跑 exit=0 确认。风险：伪 stub 属内容治理类指标，随批量回填易回弹（07-15 基线 51 即回填期产物），过早阻断会频繁卡 PR。

## 2. O2 — Cross-Domain Coverage（`scripts/check_cross_domain_coverage.py`）

**判定：继续观察（指标达标，连续性链条不足）。**

- 定义（§5.1 表 O2 行）："Rust 关键交叉/边界语义域（let chains、unsafe extern、async+unsafe、FFI+async、Send/Sync boundaries 等）是否有 `concept/` 非 stub 权威页"；转阻断条件原文："覆盖率达 100% 且连续 4 周/10 次 CI 稳定"。
- 证据清单：
  - `CROSS_DOMAIN_COVERAGE_BASELINE_2026_07_15.md`："总主题数：16 / 已覆盖：16 (100.0%) / 未覆盖：0"——建门即 100%。
  - `OBSERVE_GATE_BASELINE_2026_07_28.md` O2 段："总主题数：16 / 已覆盖：16 (100.0%) / 未覆盖：0"。
  - `OBSERVATION_GATES_BASELINE_2026-07-31.md`："O2 … --strict | ✅ PASS | 关键交叉/边界语义域 16/16 覆盖 = 100%"。
  - `P10_QUALITY_GATE_WATCH_2026_08_04.md`："全部 5 个观察门通过"。
  - 三轮存档（同值）："总主题数：16 / 已覆盖：16 (100.0%) / 未覆盖：0" + "✅ Cross-Domain Coverage (observe) passed"。
- 达标判定：100% 覆盖自 07-15 起从未回落（含 10-13 三轮）；但运行记录分布与 O1 相同（07-15/07-28/07-31/08-04/10-12/10-13×3），08-04→10-12 断链，连续 4 周/10 次 CI 条件不满足。
- 转正建议+风险：不建议本轮转正；五门中指标最稳（唯一建门即 100% 且主题清单固定），是下一轮转正的第一候选。缺的证据：一段不断档的 ≥10 次 CI 达标记录 + 当前 HEAD `--strict` exit=0。风险低：主题清单固定，退化概率小。

## 3. O3 — KG Relation Precision（`scripts/check_kg_relation_precision.py`）

**判定：继续观察，但为五门中连续性证据最强者；若远端 CI 历史核验通过，可提前转正。**

- 定义（§5.1 表 O3 行）："核心 50 实体的 KG 关系是否使用具体语义谓词（`dependsOn`/`entails`/`mutexWith`/`refines`/`equivalentTo`/`counterExample`）而非通用 `ex:RelationAnnotation`"；转阻断条件原文："核心 generic_ratio=0% 且连续 4 周/10 次 CI 稳定"。
- 证据清单（日期化 JSON 存档，15 次连续运行，`core_generic_ratio` 全 0.0）：
  - `KG_RELATION_PRECISION_2026-07-15.json`：`core_generic_ratio: 0.0`（core_relations 2389）；07-16、07-17、07-21、07-24、07-28、07-29、07-30、07-31、08-01、08-05、08-07、08-11 同值 0.0；`2026-10-12.json`、`2026-10-13.json` 同值 0.0。
  - 07-15 → 08-11 共 13 次运行、跨 27 天（≈4 周），该段本身满足"连续 4 周（或连续 10 次）达标"字面条件。
  - 三轮存档（.txt）："[KG relation precision] total_relations=10625 generic_ratio=0.00% / core_entities=50 core_relations=2799 core_generic_ratio=0.00% / core_lacking_semantic=0"；_c 轮 total_relations=10689/core_relations=2804，仍 0.00%。
  - `OBSERVATION_GATES_BASELINE_2026-07-31.md`："O3 … --strict | ✅ PASS | 核心 50 实体 generic_ratio=0.00%"。
- 达标判定：指标条件持续满足且运行次数最多；但 08-11 之后至 10-12 无运行记录，链条断裂——07-15→08-11 的 4 周链条成立却未被评估转正，之后链条重启，当前仅 4 次。
- 转正建议+风险：两条路径二选一：(a) 用 `gh run list` 核验 07-15→08-11 窗口远端 CI 全绿后按既有链条直接转正（尊重"连续 4 周达标"已成立的事实）；(b) 自 10-12 起重计，至 ~11-10 满 4 周/10 次后转正。风险：KG 刷新流水线（10-13 提交 `cbcc42a34` 记录 entities 720→721、relations 10689）持续新增关系，新边若默认走 generic 谓词会立即触发阻断；转正前建议确认刷新流水线对新谓词的默认策略。

## 4. O4 — Decision Tree rustc Error Code Coverage（`scripts/check_decision_trees.py`）

**判定：继续观察（指标达标但存在口径矛盾，连续性不足）。**

- 定义（§5.1 表 O4 行）："决策树 YAML 中 rustc error code 映射：节点级格式 `E\d{4}`、无节点歧义、Top 30 常见错误码覆盖率"；转阻断条件原文："节点歧义=0 且连续 4 周/10 次 CI 稳定"。
- 证据清单：
  - AGENTS.md §5.1 基线行："20 码节点级映射 / 0 节点歧义 / Top 30 覆盖率 18/30=60%"。
  - `OBSERVE_GATE_BASELINE_2026_07_28.md` O4 段："node_rustc_codes=32 unique=32 ambiguous=0 / top30_coverage=30/30 (100%)"。
  - `OBSERVATION_GATES_BASELINE_2026-07-31.md`："O4 … --strict | ✅ PASS | 节点歧义 0 / Top 30 error code 映射覆盖 18/30 = 60%"，且其"后续行动"称"距离 ≥80% 转正条件尚有 6 个码的缺口"——与 §5.1 表 O4 行转阻断条件（仅要求节点歧义=0）及 07-28 实测 30/30 相互矛盾。
  - 三轮存档（同值）："node_rustc_codes=38 unique=38 ambiguous=0 / top30_coverage=30/30 (100%)" + "✅ Decision Tree rustc Error Code Coverage (observe) passed"（trees=29 nodes=454）。
- 达标判定：转正条件"节点歧义=0"自 07-28 起持续满足（07-28/07-31/10-13×3 均 ambiguous=0）；Top30 覆盖率已 100%，高于任何口径阈值。但同样受 08-12→10-12 断链影响，连续性不足；且 07-31 报告与 §5.1/07-28 存档的 Top30 数值（18/30 vs 30/30）不一致，需先澄清口径。
- 转正建议+风险：不建议本轮转正。缺的证据：口径矛盾澄清（18/30 与 30/30 何者为当时实跑值）+ 连续 4 周/10 次记录 + 当前 HEAD `--strict` exit=0。风险：脚本存在 `SyntaxWarning: "\d" is an invalid escape sequence`（10-13 存档原文），Python 未来版本可能报错使门自身失效；转正前应先修脚本。

## 5. O5 — Version Semantic Injection（`scripts/check_version_semantic_injection.py`）

**判定：继续观察（指标达标，连续性链条不足）。**

- 定义（§5.1 表 O5 行）："Rust 1.90–1.97 稳定特性在版本跟踪页与 `concept/` 权威页之间的双向链接覆盖率"；转阻断条件原文："覆盖率 ≥80% 且连续 4 周/10 次 CI 稳定"。
- 证据清单：
  - `VERSION_SEMANTIC_INJECTION_BASELINE_2026_07_15.md`："版本范围：1.90 – 1.97（共 8 个稳定版本）/ 提取特性数：74 / 已映射：74 (100.0%) / 未映射：0"。
  - `OBSERVE_GATE_BASELINE_2026_07_28.md` O5 段："提取特性数：74 / 已映射：74 (100.0%) / 未映射：0"。
  - `OBSERVATION_GATES_BASELINE_2026-07-31.md`："O5 … --strict | ✅ PASS | 1.90–1.97 稳定特性双向链接覆盖 74/74 = 100%"。
  - 三轮存档（同值）："版本范围：1.90 – 1.99（共 10 个稳定版本）/ 提取特性数：142 / 已映射：142 (100.0%) / 未映射：0"，补丁页"双向链接完整：1 / 1" + "✅ Version Semantic Injection (observe) passed"。
- 达标判定：≥80% 条件自 07-15 起持续满足（100%）；检查范围已从 1.90–1.97/74 特性扩至 1.90–1.99/142 特性仍 100%，扩容未引起退化，是积极信号。连续性同 O1/O2：08-04→10-12 断链，不足 4 周/10 次。
- 转正建议+风险：不建议本轮转正。缺的证据：连续 ≥10 次 CI 达标记录 + 当前 HEAD `--strict` exit=0。风险：Rust 新版本（1.98/1.99 及后续）发布时特性清单自动扩容，新特性页若滞后创建会立即阻断 PR；转正时应保留"新版本发布后 7 天宽限"条款或确认 rust_version_tracker workflow 先于内容页生成。

---

## 6. 总体建议与 AGENTS.md 修改草案

**总体判定**：五门指标条件全部达标（10-13 三轮全绿），但"连续 4 周/10 次 CI 稳定"这一程序性前提对全部五门都不成立——08-12→10-12 九周无提交即无 CI 链条，当前链条仅 4 次（10-12 + 10-13×3）。按 §5.2 自 2026-07-15 起的强制纪律（"不得以任何口头或一次性指示绕过"），**本轮五门均建议继续观察**；O3 若经远端 CI 历史核验确认 07-15→08-11 链条，可提前转正；O2 指标最稳，为下一轮（约 2026-11-10 满 4 周/10 次后）第一转正候选。

**转正前置动作（适用于全部门）**：
1. 在当前 HEAD 实跑五门 `--strict` 各一次，确认 exit=0（§5.2 明文前提）。
2. 用 `gh run list --workflow=quality_gates.yml` 导出 CI 运行历史，补齐连续性台账（本机无 gh，无法代验）。
3. 修复 `check_decision_trees.py` 的 `\d` 转义 SyntaxWarning，避免门自身在未来 Python 版本失效。
4. 澄清 O4 的 Top30 口径矛盾（§5.1 基线 18/30 vs 07-28/10-13 实测 30/30 vs 07-31 报告 18/30）。

**AGENTS.md 门清单修改草案（供转正轮执行，本轮不改动）**：
- §5.1 标题与 §5.2 标题计数勘误：两处现文分别写"4 项语义观察"/"当前 4 个在观察"，正文实为 5 门（O1–O5），应统一为 5。
- 每门转正时：§5.1 观察门表删除对应行；阻断门清单追加该门（命令带 `--strict`）；`run_quality_gates.sh` 观察段对应 `run_gate` 行移入阻断段并加 `--strict`；`quality_gates.yml` 对应 job 的 `run:` 加 `--strict`、`continue-on-error: true` 改 `false`；§5.2 表追加一行转正记录（日期、依据报告、实跑 exit 码），格式沿用既有"✅ 已转阻断（日期，依据）"条目。
- 建议新增纪律条款：转正评估报告必须逐门引用日期化存档行（如本建议书），且连续性台账以 CI 运行记录为准、reports/ 存档为辅助证据。
