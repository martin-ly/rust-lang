# 元数据一致性基线（语义质量门 P0-1）

**日期**: 2026-07-12  **扫描**: 480 concept 活跃文件（排除 archive）  **模式**: warning（不阻断）

| 规则 | 命中文件 | 占比 | 阈值 | 判定 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥 | 0 | 0.0% | >0 | pass |
| D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7） | 1 (基=296) | 0.2% | >=5% | pass |
| D3 关键字段同文件重声明 | 0 | 0.0% | >0 | pass |
| D4 文首块 Rust 版本号自矛盾 | 0 | 0.0% | >0 | pass |
| D5 稳定层正文残留 nightly/preview/unstable | 17 | 3.5% | >0 | FAIL |
| D6 Summary 低信息量模板套话 | 0 | 0.0% | >=3% | pass |

**受影响文件总数**: 18 / 480

## 各类 Top 样例

### D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（0）


### D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）（1）

- `concept/00_meta/04_navigation/13_foundations_gap_closure_index.md` — A/S/P=S 允许 [2, 3, 4] 与 Bloom [0] 无交集

### D3 关键字段同文件重声明（0）


### D4 文首块 Rust 版本号自矛盾（0）


### D5 稳定层正文残留 nightly/preview/unstable（17）

- `concept/00_meta/01_terminology/01_terminology_glossary.md` — 稳定层 nightly/preview 关键词 18 处
- `concept/02_intermediate/00_traits/01_traits.md` — 稳定层 nightly/preview 关键词 40 处
- `concept/02_intermediate/00_traits/04_advanced_traits.md` — 稳定层 nightly/preview 关键词 14 处
- `concept/02_intermediate/01_generics/01_generics.md` — 稳定层 nightly/preview 关键词 25 处
- `concept/04_formal/04_model_checking/08_miri.md` — 稳定层 nightly/preview 关键词 6 处
- `concept/04_formal/05_rustc_internals/01_rustc_query_system.md` — 稳定层 nightly/preview 关键词 13 处
- `concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md` — 稳定层 nightly/preview 关键词 16 处
- `concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md` — 稳定层 nightly/preview 关键词 13 处
- `concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md` — 稳定层 nightly/preview 关键词 4 处
- `concept/06_ecosystem/01_cargo/01_cargo_script.md` — 稳定层 nightly/preview 关键词 5 处
- `concept/06_ecosystem/01_cargo/02_public_private_deps.md` — 稳定层 nightly/preview 关键词 5 处
- `concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md` — 稳定层 nightly/preview 关键词 4 处

### D6 Summary 低信息量模板套话（0）


## WOULD-FAIL（接入 CI strict 时将阻断）

- D5 稳定层nightly残留 17 (>0)

## 机器可读

- JSON: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.json`
