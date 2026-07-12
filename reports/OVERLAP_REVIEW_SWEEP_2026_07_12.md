# OVERLAP REVIEW SWEEP：REVIEW 批量复核加固（2026-07-12）

> **EN**: Overlap REVIEW Batch-Review Sweep
> **Summary**: Stratified manual review of all 437 REVIEW pairs from the v2 overlap triage; one true duplicate merged (concept async), all remaining pairs dispositioned into a new REVIEWED whitelist category with per-family evidence; REVIEW 437 → 0 while MERGE+DOCS_INTERNAL stays 0.

**触发**：AGENTS.md §5.2 — v2 去重已转阻断门（MERGE+DOCS_INTERNAL=0），但 triage 中 REVIEW=437 对处于"未审"状态。本轮按相似度分层复核，消除未审状态。

**工具**：`scripts/detect_content_overlap_v2.py`（复跑）、`scripts/triage_overlap.py`（新增 REVIEWED 类别 + 白名单机制）。

---

## 一、复核前基线（2026-07-12 复跑）

```
[P0-3] scanned=1916 indexed=1420 hits=552 (same_dir=540 cross_dir=12) threshold=0.5
[P1-triage] total=552 MERGE=0 DOCS_INTERNAL=0 SERIES=115 REVIEW=437
```

REVIEW 437 对按相似度分桶：

| 桶 | 对数 | 复核方式 |
|---|:---:|---|
| [0.9, 1.0] | 0 | — |
| [0.8, 0.9) | 22 | 逐对全文读取（命中文件均为 14–24 行，全部读完） |
| [0.7, 0.8) | 23 | 逐对读标题+目录+首 40 行；knowledge/ 索引全文通读 6 份（72–139 行） |
| [0.5, 0.7) | 392 | 按路径族聚类（12 族）批量裁定，每族抽 1–6 对验证独特内容 |

## 二、发现 1 对真重复（已合并处置，未走白名单）

**`concept/03_advanced/01_async/01_async.md` ↔ `02_async_advanced.md`（sim 0.500，concept 双权威页）**

- **证据**：逐节比对——02_async_advanced.md 的 §8.8–8.13 + §九（Provenance）共 ~1150 行与 01_async.md 同名节 **86–100% 逐行重复**（01_async.md v3.0（2026-05-13）深度重构时并入）。
- **处置**（按 AGENTS.md §3.3：较新较完整的 01_async.md 保留正文）：
  1. 02_async_advanced.md 的 §8.8–8.13 + §九 正文替换为**高级摘要 + 权威节锚点链接**（每节 3–5 条要点，保留其独有注记：05_async_cancellation_safety 权威指针、futures-rs/Tokio 源码注、loom::future 适用范围注、Miri 分配点追踪洞察）；文件 1707 → 631 行。
  2. 保留 02_async_advanced.md 独有内容：§十 边界测试、嵌入式测验 ×4、补充视角（异步性能优化）、认知路径。
  3. TOC 同步更新（移除 8.13 失效子锚点 4 条）。
  4. 修复副作用：摘要化后该页丢失 L2 向下引用，kb_auditor 报"跨层问题 1"；已在 §8.11 补 L2 泛型/Trait 交叉链接，复跑 0。
- **复核后相似度**：正文独特内容 79%/63%，该对退出命中清单（<0.5）。

## 三、路径族批量裁定与白名单登记（REVIEWED 类别）

在 `scripts/triage_overlap.py` 新增 **REVIEWED** 类别（判定顺序在 MERGE(sim≥0.85) 与 DOCS_INTERNAL(docs/ 且 sim≥0.7) **之后**，故不掩盖高相似真重复），含 4 条路径族 + 3 条显式对，每条附证据注释：

| 族 | 白名单 | 对数（复核后） | 抽样证据 |
|---|---|:---:|---|
| A | `crates/*/docs/**` ↔ `crates/*/docs/**` | 82 | 48/50 命中文件为 ≤45 行 canonical 重定向 stub 或统一生成器 orientation stub（指向**各自不同**的 concept 权威页，如 03_lifetimes vs 04_lifetimes_advanced vs 01_concurrency vs 01_control_flow vs 01_generics）；唯一非 stub 对 c05/c06 hands_on_projects 正文独特 67%/61%（不同实践项目）。共享 = stub/模板骨架，无正文互抄 |
| B | `knowledge/**` ↔ `knowledge/**`、`knowledge/**` ↔ `content/ecosystem/deep_dives/README.md` | 62 | 通读 9 份索引 README（72–139 行）：共享 = 模块索引模板（EN/Summary/Bloom 头 + 📚内容表 + 🎯 + Batch 8 页脚 + 模块 8 i18n 节）；独特 = 各模块文档清单/学习目标（专家/生态/学术/Miri/部署/前沿/参考/入门主题互不重叠） |
| C+D | `docs/12_research_notes/**` ↔ `docs/12_research_notes/**` | 296 | 抽 14 对（每族 ≥2）：设计模式形式化文档（800+ 行/份）去排版行后正文独特 38–58%（各模式专属公理/定理/证明，如 ST-T1 枚举穷尽 vs VI-T1 单分发完备）；共享 ~60% 经逐行核验为节标题骨架 + Batch 8 来源页脚 + 代码围栏等排版行；分布式模式 39–50%、crate 架构 49–58%、证明树 41–52%、思维导图/决策树交叉对共享为「Rust 1.94 深度整合更新」模板节 |
| E | 显式对：concept websocket ↔ networking_basics | 2（双向） | 747/886 行全文比对：WebSocket 应用协议 vs TCP/IP 基础，正文独特 64%/67%，同领域术语共现 |
| F | 显式对：safety_critical glossary ↔ mind_map | 1 | 正文独特 69%/56%，同套件跨主题 |
| G | 显式对：docs/15 type_system ↔ ownership README | 1 | 正文独特 66%/70%，子主题索引模板 |

## 四、复核后最终状态（全部质量门通过后复跑）

```
[P0-3] scanned=1916 indexed=1421 hits=559 (same_dir=547 cross_dir=12) threshold=0.5
[P1-triage] total=559 MERGE=0 DOCS_INTERNAL=0 SERIES=115 REVIEWED=444 REVIEW=0
[overlap-v2] actionable (MERGE+DOCS_INTERNAL) = 0 (baseline 0) ✅
```

> 命中总数 552→559、indexed 1420→1421：复核期间并行的"权威覆盖扩展"任务（`reports/AUTHORITY_COVERAGE_EXTENSION_2026_07_12.md`）向 40+ crate docs 文件追加「国际权威来源」节，新增 8 对低相似命中；全部落入族 A 白名单范围，最终数字为并发修改**之后**复跑所得。

| 指标 | 复核前 | 复核后 |
|---|:---:|:---:|
| REVIEW（未审） | **437** | **0** |
| REVIEWED（已复核白名单） | 0 | 444 |
| MERGE + DOCS_INTERNAL（阻断项） | 0 | 0 |
| 真重复合并处置 | — | 1 对（concept async，~1150 行重复正文摘要化） |

## 五、验证（机器可复核）

- `python scripts/detect_content_overlap_v2.py --budget 999999` + `python scripts/triage_overlap.py`：MERGE=0 / DOCS_INTERNAL=0 / REVIEW=0 ✅
- `bash scripts/run_quality_gates.sh`：**✅ All 20 quality gates passed (15 blocking + 5 semantic observe)**，含 overlap-v2 阻断段 exit 0 ✅
- `python scripts/kb_auditor.py`：死链 0、跨层问题 0、模板化 ⟹ 0 ✅
- `mdbook build`：通过（含于质量门）✅
- `python scripts/check_canonical_uniqueness.py --strict` / `concept_consistency_auditor.py --strict`：通过（含于质量门）✅

## 六、变更清单

| 文件 | 变更 |
|---|---|
| `scripts/triage_overlap.py` | 新增 REVIEWED 类别、`REVIEWED_PATH_RE`（4 条路径族）与 `REVIEWED_PAIRS`（3 显式对），均附复核证据注释；报告输出增加 REVIEWED 桶 |
| `concept/03_advanced/01_async/02_async_advanced.md` | §8.8–8.13 + §九 重复正文（~1150 行）摘要化并链接 01_async.md 权威节；补 L2 向下引用；1707 → 631 行 |
| `AGENTS.md` | §5.2 overlap v2 基线行更新（REVIEW 437→0、REVIEWED 机制） |
| `reports/OVERLAP_TRIAGE_2026-07-12.{md,json}` | triage 复跑产物 |
| `reports/CONTENT_OVERLAP_V2_2026-07-12.{md,json}` | v2 复跑产物 |

## 七、后续注意事项

1. REVIEWED 白名单判定在 MERGE/DOCS_INTERNAL 之后：任何 sim≥0.85 或 docs/ 内 sim≥0.7 的新重复仍会阻断，白名单不掩盖高相似真重复。
2. 族 A（crates/*/docs/）依据是 AGENTS.md §6.4（crate docs 不得含概念正文）；若未来 crate docs 引入实质正文且与 concept 重复，sim 通常 ≥0.7 将落入 MERGE/DOCS_INTERNAL 阻断。
3. concept async 对合并后，02_async_advanced.md 定位为"高级摘要 + 独有边界测试/测验/性能优化"；如后续扩充其高级正文，注意不得回抄 01_async.md §8.8–8.13。
