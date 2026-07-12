# 元数据一致性基线（语义质量门 P0-1）

**日期**: 2026-07-12  **扫描**: 502 concept 活跃文件（排除 archive）  **模式**: warning（不阻断）

| 规则 | 命中文件 | 占比 | 阈值 | 判定 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥 | 0 | 0.0% | >0 | pass |
| D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7） | 1 (基=309) | 0.2% | >=5% | pass |
| D3 关键字段同文件重声明 | 1 | 0.2% | >0 | FAIL |
| D4 文首块 Rust 版本号自矛盾 | 2 | 0.4% | >0 | FAIL |
| D5 稳定层正文残留 nightly/preview/unstable | 14 | 2.8% | >0 | FAIL |
| D6 Summary 低信息量模板套话 | 4 | 0.8% | >=3% | pass |

**受影响文件总数**: 18 / 502

## 已登记白名单（人工复核确认的合法特例，不计入命中）

### D2 A/S/P ↔ Bloom 脱节豁免

- `concept/00_meta/04_navigation/13_foundations_gap_closure_index.md` — L0 导航索引页，无概念正文，A/S/P 内容分级不适用
- `concept/07_future/03_preview_features/33_autoverus_preview.md` — L7 预览跟踪页（非概念权威页），A/S/P 描述被跟踪对象属性

### D5 稳定层 nightly/preview 豁免

- `concept/00_meta/01_terminology/01_terminology_glossary.md` — 术语表：『特性门控(Feature Gate)』词条本身描述 nightly 机制；另含 1.97 新特性 nightly 状态跟踪小节
- `concept/02_intermediate/00_traits/01_traits.md` — 文首已显式声明不稳定特性警告；negative_impls/min_specialization/const_trait_impl 仍为 nightly-only
- `concept/02_intermediate/00_traits/04_advanced_traits.md` — 文首已显式声明不稳定特性警告；specialization/negative_impls/trait alias 仍为 nightly-only
- `concept/02_intermediate/01_generics/01_generics.md` — 文首已显式声明不稳定特性警告；generic_const_exprs/min_specialization/-Zshare-generics 仍为 nightly-only
- `concept/04_formal/04_model_checking/08_miri.md` — Miri 解释器上游仅发布 nightly 组件，工具链事实
- `concept/04_formal/05_rustc_internals/01_rustc_query_system.md` — rustc 内部 API/-Z 调试标志仅 nightly 可用，页面主题为 rustc 内部机制
- `concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md` — 新 trait solver -Znext-solver 仅 nightly 可用，页面主题为 rustc 内部机制
- `concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md` — 并行前端/Cranelift 后端/build-std 均为 nightly-only 工具链能力
- `concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md` — RUSTC_BOOTSTRAP 主题本身就是“在非 nightly 编译器上启用 unstable feature”
- `concept/06_ecosystem/01_cargo/01_cargo_script.md` — cargo script (-Zscript) 截至 1.97 仍为 nightly 特性，页面主题即该特性
- `concept/06_ecosystem/01_cargo/02_public_private_deps.md` — public 依赖完整语义 (-Zpublic-dependency) 截至 1.97 仍为 nightly 特性，页面主题即该特性
- `concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md` — public-dependency 实验特性完整检查需 nightly，页面主题即该特性
- `concept/06_ecosystem/01_cargo/22_build_std.md` — -Zbuild-std 截至 1.97 仍为 nightly 特性，页面主题即该特性
- `concept/06_ecosystem/11_domain_applications/03_webassembly.md` — #![feature(panic_handler)] 自定义 panic handler 截至 1.97 仍为 nightly-only（wasm32-unknown-unknown 场景）
- `concept/sources/INDEX.md` — 来源索引：Unstable Book(UNB) 作为权威来源条目及其 nightly 状态标注即索引内容本身

另有两类规则级排除：WASI Preview 1/2/3（WASM 规范版本专名）与 URL 路径中的 nightly（官方文档固定托管路径）。

## 各类 Top 样例

### D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（0）

### D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）（1）

- `concept/06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集

### D3 关键字段同文件重声明（1）

- `concept/06_ecosystem/00_toolchain/14_development_tools.md` — 内容分级 声明 2 次: ['[研究级]', '[研究级]']

### D4 文首块 Rust 版本号自矛盾（2）

- `concept/03_advanced/01_async/13_async_trait_object_safety.md` — 版本字段 distinct minor [89, 97]: 1.97.0+ (Edition 2024) · async-trait 0.1.89 · RTN 需 nightly（`#![feature(return_t
- `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md` — 版本字段 distinct minor [97, 99]: 1.97.0+ (Edition 2024)（`-Z` 选项实测环境：rustc 1.99.0-nightly 375b1431b 2026-07-10 / c

### D5 稳定层正文残留 nightly/preview/unstable（14）

- `concept/00_meta/05_quizzes/01_quiz_meta_framework.md` — 稳定层 nightly/preview 关键词 3 处
- `concept/01_foundation/02_type_system/02_never_type.md` — 稳定层 nightly/preview 关键词 4 处
- `concept/02_intermediate/00_traits/02_dispatch_mechanisms.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/02_intermediate/01_generics/03_type_level_programming.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/03_advanced/00_concurrency/05_atomics_and_memory_ordering.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/03_advanced/01_async/13_async_trait_object_safety.md` — 稳定层 nightly/preview 关键词 10 处
- `concept/03_advanced/03_proc_macros/09_macro_hygiene.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/04_formal/05_rustc_internals/12_attributes.md` — 稳定层 nightly/preview 关键词 2 处
- `concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/06_ecosystem/00_toolchain/07_rustdoc_196_changes.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md` — 稳定层 nightly/preview 关键词 100 处
- `concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md` — 稳定层 nightly/preview 关键词 4 处

### D6 Summary 低信息量模板套话（4）

- `concept/00_meta/04_navigation/15_quiz_registry.md` — Summary 为空
- `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md` — Summary 为空
- `concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md` — Summary 为空
- `concept/06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md` — Summary 为空

## WOULD-FAIL（接入 CI strict 时将阻断）

- D3 字段重声明 1 (>0)
- D4 版本自矛盾 2 (>0)
- D5 稳定层nightly残留 14 (>0)

## 机器可读

- JSON: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.json`
