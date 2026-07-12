# crates/*/docs 权威覆盖全量推进报告（2026-07-12 第二轮）

> **EN**: Crates Docs Authority Coverage — Full Sweep (Round 2)
> **Summary**: Pushes crates/*/docs international-authority coverage from sampling baseline to full sweep: 64/64 = 100% of non-stub content pages covered, 10 files appended, 35 unique URLs curl-verified HTTP 200, and the coverage check is wired into `check_concept_authority_coverage.py --include-crates` (observe; `--strict`-capable).
>
> 前序：`reports/AUTHORITY_COVERAGE_EXTENSION_2026_07_12.md`（第一轮：抽样 51 非 stub 文件 100%，全量 12.2→20.8%）。

---

## 一、覆盖率前→后

| 口径 | 本轮前 | 本轮后 |
|---|---:|---:|
| 全量 576 文件（含 stub）有权威来源 | 120/576 = 20.8% | **129/576 = 22.4%** |
| 非 stub 内容页（分母 64） | 54/64 = 84.4% | **64/64 = 100.0%** ✅ |

- 全量 576 = stub/重定向 509 + 内容页 64 + 纯索引 README 2 + 代码清单豁免页 1（含嵌套子 crate `c11_macro_system_proc_macros/docs/` 3 文件，均为 stub）。
- 509 个 stub 按 AGENTS.md §2 为 canonical 重定向/占位页，不要求国际权威外链（任务书：stub 跳过）。
- 登记跳过（不计入内容页分母，逐文件理由）：
  - `crates/c15_verification_tools/docs/README.md`、`crates/c16_gui/docs/README.md`：纯索引 README（≤30 行且链接行占比 >60%；第一轮已覆盖）。
  - `crates/c03_control_fn/docs/snippets/README.md`：纯代码片段目录豁免页（AGENTS.md §4.0 豁免目录说明，无概念正文）。

## 二、加节文件（10 个，均为 Rust 1.94 版本专题系列索引）

`crates/{c01,c03,c04,c05,c06,c07,c08,c10,c11,c12}*/docs/rust_194_updates/README.md`（完整清单见 `tmp/crates_docs_authority_appended.json`）。

- 位置与格式与第一轮全库一致：文件末尾追加 `## 国际权威来源` 节（curl 实测声明 + 2 条链接，按 crate→链接集映射表，复用第一轮 19 crate 链接集）。
- 加节文案未使用 `check_template_cliches.py` 黑名单句式；链接标题按 crate 主题定制（macros/procedural-macros、rustwasm book、std::process/std::io 等）。

## 三、URL 验证统计

- 去重 URL **35 个**（25 个复用第一轮已验证集合，10 个本轮新增：`reference/macros.html`、`reference/procedural-macros.html`、`rustwasm.github.io/docs/book/`、`webassembly.org`、`w3.org/TR/rdf11-concepts/`、`docs.rs/oxigraph`、`book/`、`std/`、`book/ch11-00-testing.html`、`cargo/commands/cargo-test.html`）。
- 全部经 `curl -L` 并发复测（`xargs -P 8`，UA Mozilla）：**35/35 HTTP 200**（明细 `tmp/crates_authority_url_check.txt`）。
- 备注：URL 清单文件须为 LF 行尾（CRLF 会导致 curl 000，本轮已排障复测）。

## 四、门禁化（--include-crates 扩展）

| 文件 | 变更 |
|---|---|
| `scripts/check_concept_authority_coverage.py` | 新增 `CRATES_AUTH_RE`（P0/P1/P2 超集 + tokio.rs/rustwasm/rust-embedded/webassembly.org/w3.org/egui/kani/aeneas 等生态权威域）、`crates_classify()`（stub/quiz/index_readme/code_listing/content，口径与 `tmp/crates_docs_authority_full.py` 一致，幂等：先剥离已追加节再判纯索引）、`scan_crates_docs()`、`--include-crates` 参数；`--strict` 时 crates 内容页缺口>0 亦阻断 |
| `scripts/README.md` | 登记 `--include-crates` 扩展说明 |
| `scripts/run_quality_gates.sh` | 覆盖观察门改为 `--include-crates`（门数不变，报告附加小节）；修正头部过期注释 |
| `.github/workflows/quality_gates.yml` | authority-coverage 观察 job 同步加 `--include-crates`（仍 `continue-on-error: true`，门数不变） |
| `AGENTS.md` | §5.1 门 18 与 §5.2 authority coverage 行更新（crates 扩展基线 64/64=100%；--strict 实跑 exit 0） |

实跑：`--include-crates` exit 0（观察）；`--include-crates --strict` exit 0（concept any=100%/none=0/core_gap=0 且 crates 缺口=0）。

## 五、质量门验证（2026-07-12 实跑）

| 检查 | 结果 |
|---|---|
| `python scripts/kb_auditor.py` | 死链 **0**，跨层问题 0，exit 0 ✅ |
| `mdbook build` | 通过 ✅ |
| `python scripts/check_template_cliches.py` | OK 无命中，exit 0 ✅ |
| `python scripts/detect_content_overlap.py`（v1 阻断门 8） | 仍仅既有 1 对（migration_197 vs 21_rust_197_cheatsheet），exit 0 ✅ |
| `detect_content_overlap_v2.py --budget 999999` + `triage_overlap.py` | 命中 559→**573**（+14）；可处理项 **MERGE=0 + DOCS_INTERNAL=0 = 0**（阻断基线 0，通过 ✅）；新增 crates 对全部落入族 A `REVIEWED_PATH_RE`（crates/*/docs/\*\*），最高 0.846 < 0.85 MERGE 阈值，SERIES 129 / REVIEWED 444 / REVIEW 0 |
| `check_concept_authority_coverage.py --include-crates --strict` | exit **0** ✅ |

## 六、变更文件清单

- `crates/*/docs/`：10 个 `rust_194_updates/README.md` 追加「国际权威来源」节（仅本轮实际改动）。
- 门禁化 5 文件：`scripts/check_concept_authority_coverage.py`、`scripts/README.md`、`scripts/run_quality_gates.sh`、`.github/workflows/quality_gates.yml`、`AGENTS.md`。
- 工具/证据（tmp，不入版本控制）：`tmp/crates_docs_authority_full.py`（扫描+批量加节脚本，分类口径单一来源）、`tmp/crates_authority_urls.txt`、`tmp/crates_authority_url_check.txt`、`tmp/crates_docs_authority_appended.json`。
- 报告：`reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-12.{md,json}`（含 crates 小节，由脚本生成）、本文件。

---

*本轮产出：reports/CRATES_DOCS_AUTHORITY_FULL_COVERAGE_2026_07_12.md（本文件）*
