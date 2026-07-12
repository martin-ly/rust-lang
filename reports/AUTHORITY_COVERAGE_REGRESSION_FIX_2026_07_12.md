# 权威覆盖率退化定位与修复（2026-07-12）

**EN**: Concept Authority Coverage Regression — Root Cause & Fix
**Summary**: The 2026-07-12 evening regression of `check_concept_authority_coverage.py` (any 99.5% / none=2 / core gap=1) was caused by two newly-created merged-redirect stubs whose Summary wording ("Merged Redirect") did not match the script's stub-exclusion keyword ("Redirect stub"); fixed by broadening the script's stub detection and normalizing the two stub Summaries. No authority URLs needed to be added.

> 生成: 2026-07-12 · 脚本: `scripts/check_concept_authority_coverage.py`（含 `--strict`）
> 基线对比: `reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-11.json` vs `2026-07-12.json`

---

## 1. 退化现象

| 指标 | 07-11 基线 | 07-12 晚间（退化） | 修复后 |
|:---|---:|---:|---:|
| 扫描页数 | 460 | 463 | 461 |
| 任一权威 any | 100.0% | 99.6%（内容页 99.5%） | **100.0%** |
| none（无任何权威引用） | 0 | 2 | **0** |
| 核心 L1–L4 无 P0 缺口 | 0 | 1 | **0** |
| `--strict` exit | 0 | 1 | **0** |

## 2. 退化根因

**不是缺来源、不是目录移动导致的路径匹配失效**，而是脚本的重定向 stub 排除规则措辞过窄：

- 脚本的 `active_md()` 仅排除 Summary 含字面量 `"Redirect stub"` 且 <30 行的短页。
- 07-12 当日合并产生的两个重定向 stub 的 Summary 写的是 `"Merged Redirect"`（语义相同、措辞不同），未被排除规则识别，被当作内容页计入扫描；stub 本身按设计不含权威 URL（权威内容在目标页），于是：
  - 两页同时落入 `none_any`（none=2）；
  - 其中 `13_formal_methods.md` 位于 L4 且无 P0 URL，落入核心缺口（core gap=1）。

## 3. 逐页判定与处置

### 3.1 `concept/04_formal/04_model_checking/13_formal_methods.md`（none + 核心缺口）

- **判定**：重定向 stub（22 行），权威页为 `concept/07_future/04_research_and_experimental/02_formal_methods.md`。
- **目标页权威来源核验**：目标页正文含 8 处 P0/P1 权威域命中（doc.rust-lang.org / sigplan.org / plv 等），覆盖充分，无需补 URL。
- **处置**：Summary 规范化为 `Merged Redirect stub — ...`；无需补来源。

### 3.2 `concept/06_ecosystem/11_domain_applications/26_game_development.md`（none）

- **判定**：重定向 stub（17 行），权威页为同目录 `21_game_development.md`（07-12 同目录同主题双文件合并）。
- **目标页权威来源核验**：目标页含 2 处权威域命中，覆盖充分。
- **处置**：Summary 规范化为 `Merged Redirect stub — ...`；无需补来源。

### 3.3 疑似目录移动（02_process_ipc→08_process_ipc、panic/runtime、editions）

- **判定：未造成退化。** 脚本无路径前缀统计（内容口径仅排除 `00_meta/`、`sources/`、`quiz`、`placeholders/`）；层级判定经 `concept_config.LAYER_DIRS` 按目录段名匹配。
- **证据**：07-11 vs 07-12 `by_layer` 对比无 `L?` 增长（均为 3），L1–L3/L5 页数不变；L4 −1、L6 −1 恰为上述两个 stub 被误计所致，修复后层级分布恢复。

## 4. 修复清单

| 文件 | 修改 |
|:---|:---|
| `scripts/check_concept_authority_coverage.py` | stub 排除条件由 `"Redirect stub" in head` 扩展为 `("Redirect stub" in head or "Merged Redirect" in head)`，并补注释说明两种措辞均为 AGENTS.md §2 允许的重定向形式 |
| `concept/04_formal/04_model_checking/13_formal_methods.md` | Summary 改为 `Merged Redirect stub — ...`（兼容新旧两种排除规则） |
| `concept/06_ecosystem/11_domain_applications/26_game_development.md` | Summary 改为 `Merged Redirect stub — ...`（同上） |

> 说明：未新增任何权威 URL——退化页均为 stub，其目标权威页来源已充分；按 AGENTS.md §2，stub 不应重复权威页正文（含来源列表）。

## 5. 验证证据

```text
$ python scripts/check_concept_authority_coverage.py --strict
[concept-authority] scanned=461  P0=100.0%  P1=94.6%  P2=85.2%  any=100.0%  none=0
[concept-authority] content-scope n=383  P0=100.0%  P1=100.0%  P2=99.7%  any=100.0%
[concept-authority] core L1-L4 gaps (no P0): 0
[concept-authority] PASS (--strict): any=100% none=0 core_gaps=0
exit=0
```

JSON 复核（`reports/CONCEPT_AUTHORITY_COVERAGE_2026-07-12.json`）：

- `none_any`: `[]`
- `core_gaps_l1_l4_no_p0`: `[]`
- `content_scope.any`: `[383, 100.0]`

> 扫描数 461 vs 07-11 的 460：净增 1 个真实内容页（当日新增内容，本身已带权威来源），与退化无关。

## 6. 后续建议

- 新建合并重定向 stub 时，Summary 统一使用含 `"Redirect stub"` 的措辞（已写入两个 stub 页）。
- 若未来出现第三种 stub 措辞，优先在脚本侧用结构化信号（如存在 `权威来源` 指向块 + 短页）判定，而非继续枚举措辞。

---

*未执行 git commit（按要求）。*
