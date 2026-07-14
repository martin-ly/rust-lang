# crates docs stub canonical 链接健康度纳入质量门 W3

**EN**: Crates Docs Stub Canonical Link Health Promotion to Blocking Gate
**Summary**: 将 `crates/*/docs/` 中 stub 文件的 `concept/` canonical 链接存在性检查纳入既有质量门 16（`check_concept_authority_coverage.py --strict --include-crates`），确保未来新增 stub 必须含有效 canonical 链接。

> **日期**: 2026-07-14
> **关联**: AGENTS.md §5.2 门 16、`.github/workflows/quality_gates.yml` `concept-authority-coverage` job

---

## 1. 背景

- W2 已把 `crates/*/docs/` 内 **163 处失效 canonical 链接**全部修复。
- 这些链接多存在于由旧通用概念文档改造而成的 **stub/重定向页**中，原指向 `concept/` 权威页但目标路径已因编号调整、目录合并或文件名规范化而失效。
- 为防止未来新增 stub 再次出现死 canonical 链接，需要把 stub 链接健康度纳入既有阻断门。

## 2. 扩展内容

### 2.1 检查器扩展：`scripts/check_concept_authority_coverage.py`

在 `scan_crates_docs()` 中新增对 stub 文件 canonical 链接的本地存在性检查：

1. **提取链接**：正则 `\[([^\]]+)\]\(([^)]+)\)` 抽取所有 markdown 链接。
2. **过滤 canonical 链接**：
   - 本地相对链接且目标落在 `concept/` 目录下；
   - 或外部 `http/https` 链接命中 `CRATES_AUTH_RE`（生态权威域，用于统计，不参与本地存在性检查）。
3. **解析与存在性检查**：对本地 `concept/` 链接，按源文件相对路径解析为绝对路径，使用 `os.path.exists()` 验证；失效则计入 `dead_canonical`。
4. **报告**：在 `--include-crates` 报告末尾增加「crates stub canonical 链接健康度」小节；`dead_canonical=0` 显示 ✅，>0 列出前 30 处明细。
5. **阻断逻辑**：`--strict --include-crates` 下，若 `content` 页 gaps>0 **或** `dead_canonical>0` 则 `exit 1`。
6. **帮助文本**：更新 `--include-crates` 说明，反映 stub canonical 链接检查。

### 2.2 CI 同步

`.github/workflows/quality_gates.yml` 中 `concept-authority-coverage` job 已使用 `--strict --include-crates`，无需新增 job；仅将该 step 名称/注释更新为：

> Run concept international authority coverage (... +crates docs section incl. stub canonical link health)

### 2.3 文档同步

- `AGENTS.md` §5.2 authority coverage 基线行补充：**stub canonical 链接 dead=0**（2026-07-14 W2 修复 163 处失效链接后复测）。
- `scripts/README.md` 中 `check_concept_authority_coverage.py` 条目补充 stub canonical 链接健康度说明。

## 3. 验证结果

### 3.1 扩展检查器实跑

```bash
python scripts/check_concept_authority_coverage.py --strict --include-crates
```

输出（2026-07-14）：

```text
[crates-authority] total=576 content=64 covered=64 (100.0%) gaps=0 dead_canonical=0
[concept-authority] scanned=491  P0=99.0%  P1=93.3%  P2=85.9%  any=100.0%  none=0
[concept-authority] content-scope n=406  P0=100.0%  P1=99.8%  P2=99.8%  any=100.0%
[concept-authority] core L1-L4 gaps (no P0): 0
[concept-authority] report: reports\CONCEPT_AUTHORITY_COVERAGE_2026-07-14.md
[concept-authority] PASS (--strict): any=100% none=0 core_gaps=0
```

- ✅ exit 0
- ✅ 报告含 `dead_canonical = 0` 小节
- ✅ crates 内容页覆盖 64/64 = 100%

### 3.2 全量质量门

```bash
bash scripts/run_quality_gates.sh > tmp/gates_w3_2026_07_14.log 2>&1; echo "EXIT=$?"; tail -40 tmp/gates_w3_2026_07_14.log
```

输出（节选最后 40 行，2026-07-14）：

```text
EXIT=0
[result] candidate pass=300 fail=0 | compile_fail ok=866 unexpected_pass=0 wrong_code=0 | should_panic pass=0 fail=0 | dep pass=0 fail=0 untested=0 | timeout=0
✅ Concept Code Blocks (strict) passed

=== Mindmap Coverage (strict) ===
== 内容页思维表征覆盖率（W2-a 观察门，默认 exit 0）==
层                   内容页         mindmap            反例存在
01_foundation        49      49 (100.0%)      48 ( 98.0%)
02_intermediate      35      35 (100.0%)      35 (100.0%)
03_advanced          62      62 (100.0%)      60 ( 96.8%)
04_formal            54      54 (100.0%)      54 (100.0%)
05_comparative       19      19 (100.0%)      19 (100.0%)
06_ecosystem        121     121 (100.0%)     120 ( 99.2%)
07_future            64      64 (100.0%)      63 ( 98.4%)
-------------------------------------------------------
TOTAL               404     404 (100.0%)     399 ( 98.8%)
基线阈值（--strict）: mindmap >= 10%, 反例 >= 40%
✅ Mindmap Coverage (strict) passed

=== Semantic Health (strict) ===
[P4] semantic health total=99.6 grade=OK (meta=100.0 topo=98.4 dedup=100.0 kg=100.0)
[P4] report: reports/SEMANTIC_HEALTH_2026-07-14.md
✅ Semantic Health (strict) passed

=== Content Overlap v2 (blocking, actionable baseline=0) ===
...
[overlap-v2] actionable (MERGE+DOCS_INTERNAL) = 0 (baseline 0)
✅ overlap-v2 可处理项=0。

✅ All 23 quality gates passed (23 blocking + 0 semantic observe).
```

- ✅ EXIT=0
- ✅ 23 门全阻断通过

---

## 4. 结论

- `crates/*/docs/` stub canonical 链接健康度已成功纳入既有质量门 16，成为阻断条件之一。
- 当前基线：`dead_canonical=0`、`content gaps=0`、concept/ 内容页 any=100%、none=0、核心 L1-L4 无 P0 缺口=0。
- 未来新增 stub 若包含指向不存在的 `concept/` 文件链接，CI 与本地 `run_quality_gates.sh` 将阻断。

---

*由 `scripts/check_concept_authority_coverage.py` 扩展后生成*
