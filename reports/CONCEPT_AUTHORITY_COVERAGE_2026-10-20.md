# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-10-20 · 扫描 concept/ 活跃 md: **792**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 784 | 99.0% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 739 | 93.3% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 714 | 90.2% |
| **任一权威（P0∪P1∪P2）** | **792** | **100.0%** |
| 无任何国际权威引用（缺口） | 0 | 0.0% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **691** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 688 | 99.6% |
| P1 学术/形式化 | 680 | 98.4% |
| P2 社区/生态 | 690 | 99.9% |
| **任一权威** | **691** | **100.0%** |

内容页 P1 缺口（11）: `concept/06_ecosystem/01_cargo/24_cargo_basics.md` · `concept/06_ecosystem/04_web_and_networking/12_container_build_and_delivery_pipeline.md` · `concept/06_ecosystem/04_web_and_networking/13_grpc_tonic_prost_ecosystem.md` · `concept/06_ecosystem/05_systems_and_embedded/57_posix_syscall_crate_ecosystem.md` · `concept/06_ecosystem/11_domain_applications/29_time_and_date_ecosystem.md` · `concept/06_ecosystem/11_domain_applications/30_chrono_vs_jiff.md` · `concept/06_ecosystem/11_domain_applications/31_desktop_gui_ecosystem.md` · `concept/06_ecosystem/11_domain_applications/32_computer_vision_ecosystem.md` · `concept/06_ecosystem/11_domain_applications/33_audio_dsp_ecosystem.md` · `concept/07_future/00_version_tracking/rust_1_99_stabilized.md` · `concept/07_future/02_preview_features/21_rust_specification_preview.md`

内容页 P2 缺口（1）: `concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 76 | 76 | 100.0% | 76 | 100.0% |
| L1 | 60 | 60 | 100.0% | 60 | 100.0% |
| L2 | 45 | 45 | 100.0% | 45 | 100.0% |
| L3 | 78 | 78 | 100.0% | 78 | 100.0% |
| L4 | 132 | 132 | 100.0% | 132 | 100.0% |
| L5 | 55 | 55 | 100.0% | 55 | 100.0% |
| L6 | 265 | 258 | 97.4% | 265 | 100.0% |
| L7 | 78 | 77 | 98.7% | 78 | 100.0% |
| L? | 3 | 3 | 100.0% | 3 | 100.0% |

## 核心缺口（L1-L4 且 无 P0 官方国际权威）

共 **0** 页。下表为前 60（按层级、页长降序，优先补权威来源小节）。

| 层级 | 文件 | 行数 |
|:---|:---|---:|

## 方法学与诚信

- 域分级来自现有 `maintenance/authority_coverage_dashboard.py`（单一来源），未新造口径。
- 『命中』= 正文含对应域的 URL 子串（`re.search`）；不区分链接/正文引用，偏宽松（覆盖率可能略高估，缺口清单偏保守可信）。
- 本审计只读，不修改任何文件；补缺口应基于 `concept/00_meta/02_sources/01_authority_source_map.md` 已核验映射 + 官方 URL，仅追加 References，不改正文事实。

---
*由 `scripts/check_concept_authority_coverage.py` 生成*