# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-07-12 · 扫描 concept/ 活跃 md: **461**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 461 | 100.0% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 436 | 94.6% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 393 | 85.2% |
| **任一权威（P0∪P1∪P2）** | **461** | **100.0%** |
| 无任何国际权威引用（缺口） | 0 | 0.0% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **383** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 383 | 100.0% |
| P1 学术/形式化 | 383 | 100.0% |
| P2 社区/生态 | 382 | 99.7% |
| **任一权威** | **383** | **100.0%** |

内容页 P2 缺口（1）: `concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 60 | 60 | 100.0% | 60 | 100.0% |
| L1 | 55 | 55 | 100.0% | 55 | 100.0% |
| L2 | 38 | 38 | 100.0% | 38 | 100.0% |
| L3 | 60 | 60 | 100.0% | 60 | 100.0% |
| L4 | 51 | 51 | 100.0% | 51 | 100.0% |
| L5 | 19 | 19 | 100.0% | 19 | 100.0% |
| L6 | 114 | 114 | 100.0% | 114 | 100.0% |
| L7 | 61 | 61 | 100.0% | 61 | 100.0% |
| L? | 3 | 3 | 100.0% | 3 | 100.0% |

## 核心缺口（L1-L4 且 无 P0 官方国际权威）

共 **0** 页。下表为前 60（按层级、页长降序，优先补权威来源小节）。

| 层级 | 文件 | 行数 |
|:---|:---|---:|

## 方法学与诚信

- 域分级来自现有 `maintenance/authority_coverage_dashboard.py`（单一来源），未新造口径。
- 『命中』= 正文含对应域的 URL 子串（`re.search`）；不区分链接/正文引用，偏宽松（覆盖率可能略高估，缺口清单偏保守可信）。
- 本审计只读，不修改任何文件；补缺口应基于 `concept/00_meta/02_sources/authority_source_map.md` 已核验映射 + 官方 URL，仅追加 References，不改正文事实。

---
*由 `scripts/check_concept_authority_coverage.py` 生成*