# 元数据一致性基线（语义质量门 P0-1）

**日期**: 2026-07-18  **扫描**: 544 concept 活跃文件（排除 archive）  **模式**: strict

| 规则 | 命中文件 | 占比 | 阈值 | 判定 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥 | 0 | 0.0% | >0 | pass |
| D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7） | 0 (基=329) | 0.0% | >=5% | pass |
| D3 关键字段同文件重声明 | 0 | 0.0% | >0 | pass |
| D4 文首块 Rust 版本号自矛盾 | 0 | 0.0% | >0 | pass |
| D5 稳定层正文残留 nightly/preview/unstable | 0 | 0.0% | >0 | pass |
| D6 Summary 低信息量模板套话 | 8 | 1.5% | >=3% | pass |

**受影响文件总数**: 8 / 544

## 已登记白名单（人工复核确认的合法特例，不计入命中）

### D2 A/S/P ↔ Bloom 脱节豁免

- `concept/00_meta/04_navigation/13_foundations_gap_closure_index.md` — L0 导航索引页，无概念正文，A/S/P 内容分级不适用
- `concept/07_future/02_preview_features/33_autoverus_preview.md` — L7 预览跟踪页（非概念权威页），A/S/P 描述被跟踪对象属性

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
- `concept/00_meta/05_quizzes/01_quiz_meta_framework.md` — L0 测验框架页：quiz 题目/解析以 nightly feature(custom_borrowck)、rustc 插件 unstable 为概念辨析考点，非正文依赖
- `concept/01_foundation/02_type_system/02_never_type.md` — never_type feature 截至 1.97 仍未稳定，页面主题即 `!` 类型及其稳定化路径（含 nightly 边界标注）
- `concept/02_intermediate/00_traits/02_dispatch_mechanisms.md` — specialization 仍为 nightly 特性的边界标注（代码注释说明 stable 不可编译），非稳定层残留依赖
- `concept/02_intermediate/01_generics/02_const_generics.md` — 页面主题即 const generics 的 stable(min_const_generics) vs nightly(generic_const_exprs/adt_const_params) 边界
- `concept/02_intermediate/01_generics/03_type_level_programming.md` — generic_const_exprs nightly 边界为类型级编程 workaround 的对照内容（反例/边界说明）
- `concept/03_advanced/01_async/13_async_trait_object_safety.md` — RTN(return_type_notation) nightly-only 为解决方案谱系的组成路线之一，文首 Rust 版本字段已显式声明
- `concept/03_advanced/03_proc_macros/09_macro_hygiene.md` — Span::def_site() nightly 为 hygiene 跨边界手段的事实标注（对照说明）
- `concept/04_formal/05_rustc_internals/12_attributes.md` — RFC 3416 #![feature(...)] 结构化元数据为 rustc 内部治理主题，页面属 rustc_internals 系列
- `concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md` — quiz 题目考察 rustup stable/beta/nightly 工具链管理知识点，nightly 为考点内容本身
- `concept/06_ecosystem/00_toolchain/07_rustdoc_196_changes.md` — 页面主题即 Rust 1.97 稳定化两个原 nightly rustdoc 标志，nightly 为历史状态陈述
- `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md` — 页面主题即 nightly-only `-Z` 选项系统化清单（与既有 -Z 类白名单页同质）
- `concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md` — Tier 2/3 no_std 目标须 nightly + -Z build-std 为工具链事实；rustc book 仅 nightly 路径托管（URL 规则已排除）
- `concept/06_ecosystem/05_systems_and_embedded/12_gpu_programming_and_hpc.md` — rust-gpu 绑定固定编译器版本、std::simd portable SIMD 未稳定、nvptx64 目标须 nightly -Z build-std 均为截至 1.97 的工具链事实陈述（与既有 10_target_tier_platform_support.md 同质）
- `concept/06_ecosystem/13_quizzes/03_quiz_security_testing.md` — quiz 题目/解析以 cargo vet 工具链可用性与 #[bench] nightly 状态为考点，nightly 为考点内容本身
- `concept/sources/rfc_index.md` — RFC 索引：状态列记录各 RFC nightly/每日构建版状态，即索引内容本身（同 sources/INDEX.md 既有登记）
- `concept/00_meta/00_framework/semantic_space.md` — 元框架页：nightly/preview 作为版本演进维度概念名引用（语义空间坐标轴描述）
- `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述，非稳定层依赖
- `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/02_type_system/01_type_system.md` — 类型系统演进节：generic_const_exprs/-Znext-solver/never_type nightly 状态为客观事实陈述，附 Unstable Book 权威链接
- `concept/01_foundation/04_control_flow/01_control_flow.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/07_modules_and_items/07_type_aliases.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/07_modules_and_items/09_const_items_and_const_fn.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/07_modules_and_items/12_items.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/01_foundation/08_error_handling/02_error_handling_control_flow.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/02_intermediate/02_memory_management/01_memory_management.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/02_intermediate/03_error_handling/01_error_handling.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/02_intermediate/04_types_and_conversions/01_range_types.md` — Step trait 仍 nightly-only 为客观事实陈述（决定范围端点类型）
- `concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md` — assert_matches 历史 nightly 状态陈述（1.96 已稳定，版本演进上下文）
- `concept/02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md` — auto traits 实验性状态（E0658）为客观事实陈述
- `concept/03_advanced/01_async/06_async_boundary_panorama.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/03_advanced/02_unsafe/03_nll_and_polonius.md` — Polonius 借用检查器仅 nightly 可用为客观事实陈述（页面主题即其对比）
- `concept/03_advanced/03_proc_macros/02_proc_macro.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` — -Zunpretty/trace_macros 等 nightly 调试标志为工具链事实陈述（页面主题即调试手段）
- `concept/03_advanced/03_proc_macros/05_production_grade_macro_development.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/03_advanced/03_proc_macros/06_macro_glossary.md` — 术语条目：Span::def_site()/-Zunpretty nightly-only 为定义内容本身的客观事实
- `concept/03_advanced/06_low_level_patterns/01_custom_allocators.md` — allocator_api 仍 nightly-only 为客观事实陈述（页面主题即自定义分配器）
- `concept/04_formal/01_ownership_logic/02_ownership_formal.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/06_ecosystem/00_toolchain/01_toolchain.md` — WASI Preview 专名 + rustc_driver/Cranelift nightly 状态为工具链事实陈述
- `concept/06_ecosystem/00_toolchain/04_compiler_internals.md` — rustc 内部 API 仅 nightly 可用为工具链事实陈述（页面主题即编译器内部）
- `concept/06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md` — rustc_driver  nightly-only / StableMIR 状态对比为页面主题本身
- `concept/06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md` — 演进方向节：nightly 特性状态为版本演进上下文陈述
- `concept/06_ecosystem/09_testing_and_quality/04_benchmarking.md` — #[bench]/criterion nightly 状态为工具链事实陈述（页面主题即基准测试手段）
- `concept/06_ecosystem/01_cargo/04_cargo_196_features.md` — 迁移建议节：迁移窗口留 nightly CI 观察为工程实践陈述，非稳定层依赖
- `concept/06_ecosystem/05_systems_and_embedded/02_cross_compilation.md` — 反命题树节：自定义 target 无 std 预编译须 nightly build-std 为工具链事实
- `concept/06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md` — 演进方向节：Prusti/Kani 绑定特定 nightly/rustc 版本为生态事实陈述
- `concept/02_intermediate/00_traits/08_negative_impls.md` — negative_impls 特性截至 1.97.0 仍为 nightly-only，页面主题即该特性
- `concept/02_intermediate/00_traits/09_associated_type_defaults.md` — associated_type_defaults 特性截至 1.97.0 仍为 nightly-only，页面主题即该特性
- `concept/04_formal/00_type_theory/10_dependent_refinement_types.md` — 页面讨论 Rust const generics 的 stable/nightly 边界；nightly 为 generic_const_exprs/adt_const_params 边界标注
- `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md` — 页面讨论 Rust 关键字效应与 effect handlers 设计空间；nightly 为预览特性边界标注
- `concept/05_comparative/01_systems_languages/08_rust_vs_d.md` — 跨语言对比页客观陈述 D `-preview=dip1000` 标志名与 Rust 尚未稳定特性；nightly/preview 为对比事实本身
- `concept/05_comparative/02_managed_languages/11_rust_vs_fsharp.md` — 跨语言对比页客观陈述 Rust 实验性特性边界；nightly/preview 为对比事实本身

另有两类规则级排除：WASI Preview 1/2/3（WASM 规范版本专名）与 URL 路径中的 nightly（官方文档固定托管路径）。

## 各类 Top 样例

### D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（0）

### D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）（0）

### D3 关键字段同文件重声明（0）

### D4 文首块 Rust 版本号自矛盾（0）

### D5 稳定层正文残留 nightly/preview/unstable（0）

### D6 Summary 低信息量模板套话（8）

- `concept/00_meta/02_sources/01_authority_source_map.md` — Summary 为空
- `concept/00_meta/03_audit/01_concept_audit_guide.md` — Summary 为空
- `concept/01_foundation/02_type_system/01_type_system.md` — Summary 为空
- `concept/01_foundation/04_control_flow/03_let_chains.md` — Summary 为空
- `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` — Summary 为空
- `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` — Summary 为空
- `concept/07_future/00_version_tracking/rust_1_97_1.md` — Summary 为空
- `concept/07_future/02_preview_features/19_const_trait_preview.md` — Summary 为空

## WOULD-FAIL（接入 CI strict 时将阻断）

- 无（全部通过）

## 机器可读

- JSON: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-18.json`
