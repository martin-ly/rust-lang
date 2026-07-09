# Content Completeness Baseline Audit

> **Date**: 2026-07-09T04:21:38.304328+00:00
> **Scope**: `concept/**/*.md` (excluding `archive/`, `sources/`, `deprecated/`)
> **Total files scanned**: 470
> **Files flagged**: 432 (91.9%)

## 1. Methodology

This audit scans the canonical `concept/` tree for pages that pass `kb_auditor.py`
(no dead links, no templated theorem chains, cross-layer references consistent)
but still lack substantive body content. Detection heuristics:

| Heuristic | Definition | Rationale |
|:---|:---|:---|
| **Short page** | `< 100` lines and not already a redirect stub | Core concepts need enough depth for a canonical page. |
| **Incomplete markers** | `TODO`, `FIXME`, `XXX`, `待补充`, `待完善`, `占位`, `stub` (case-insensitive) | Explicit content gaps left by authors. |
| **Empty section** | A heading immediately followed by another heading or by a blank line then a heading | Section has no body; likely skeleton-enriched. |
| **Theorem chain, thin body** | `> 200` lines, `≥ 3` theorem chains, but `≤ 2` Rust code blocks OR `> 35%` metadata/boilerplate | Page has formal structure but little executable/illustrative substance. |
| **L6/L7 recent skeleton** | File modified in the last 21 days, in L6/L7, and matches any of the above | Recently enriched skeletons that still need body expansion. |

Files whose first lines identify them as redirect stubs are excluded from the **short page**
criterion but are still reported under `00_meta` navigation / placeholder batches if they are
placeholders rather than canonical redirects.

## 2. Findings Lists

### 2.1 Files < 100 lines (2)

| File | Layer | Lines | Title | Action hint |
|:---|:---|---:|:---|:---|
| `concept/00_meta/knowledge_topology/README.md` | L0 | 67 | 知识体系拓扑图谱集（Knowledge Topology Atlas） | 按 00_meta 治理规则处理 |
| `concept/00_meta/03_audit/template_deduplication_guide.md` | L0 | 92 | 模板去同质化指南 | 按 00_meta 治理规则处理 |

### 2.2 Files with incomplete markers (126)

Marker set: `TODO`, `FIXME`, `XXX`, `待补充`, `待完善`, `占位`, `stub`.
Some hits occur in legitimate TODO-tracker / methodology pages and are flagged separately
as *metadata noise*.

| File | Layer | Unique markers | Occurrences | Snippet (first hit) |
|:---|:---|---:|---:|:---|
| `concept/00_meta/00_framework/methodology.md` *(meta noise)* | L0 | 3 | 9 | L39: `- [6.1 TODO 标记](#61-todo-标记)` |
| `concept/00_meta/00_framework/semantic_space.md` | L0 | 2 | 7 | L70: `- [十、待补充与演进方向（TODOs）](#十待补充与演进方向todos)` |
| `concept/00_meta/00_framework/todos.md` *(meta noise)* | L0 | 2 | 39 | L1: `# 全局待办清单（Global TODO Tracker）` |
| `concept/00_meta/01_terminology/bilingual_template_v2.md` | L0 | 1 | 4 | L36: `> [RFC XXXX](.) ·` |
| `concept/00_meta/02_sources/sources.md` *(meta noise)* | L0 | 1 | 3 | L42: `- [九、待补充来源](#九待补充来源)` |
| `concept/00_meta/02_sources/topic_authority_alignment_map.md` | L0 | 1 | 4 | L32: `-`concept/00_meta/00_framework/todos.md`— 全局待办清单（Global TODO Tracker）` |
| `concept/00_meta/03_audit/audit_checklist.md` *(meta noise)* | L0 | 2 | 6 | L40: `- [十、TODO](#十todo)` |
| `concept/00_meta/03_audit/concept_consistency_audit_checklist.md` | L0 | 1 | 1 | L7: `> **Summary**: Redirect stub for the concept consistency audit checklist; authoritative content is in audit_checklist...` |
| `concept/00_meta/04_navigation/05_cross_reference_matrix.md` | L0 | 2 | 3 | L3: `> **Summary**: Redirect stub for the cross-reference matrix; the authoritative index is concept_index.md.` |
| `concept/00_meta/04_navigation/concept_index.md` *(meta noise)* | L0 | 2 | 4 | L83: `- [八、TODO](#八todo)` |
| `concept/00_meta/04_navigation/foundations_gap_closure_index.md` | L0 | 1 | 5 | L91: `### 6.1 SUMMARY.md 占位符 ✅ 已解决` |
| `concept/00_meta/04_navigation/inter_layer_map.md` *(meta noise)* | L0 | 2 | 5 | L46: `- [十、TODO](#十todo)` |
| `concept/00_meta/04_navigation/inter_layer_topology.md` | L0 | 1 | 1 | L5: `> **Summary**: Redirect stub for the cross-layer dependency and implication topology; authoritative content is in int...` |
| `concept/00_meta/04_navigation/learning_guide.md` | L0 | 1 | 1 | L573: `第 3 级: 详细解释（--explain E0xxx）` |
| `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md` | L0 | 2 | 5 | L62: `\|`placeholder_generic`\| [占位符页面](../placeholders/placeholder_generic.md) \| Placeholder \| This page is a generic plac...` |
| `concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md` | L0 | 2 | 4 | L60: `\| [占位符页面](../placeholders/placeholder_generic.md) \| L0 元信息层 \| — \| — \| — \| — \| — \|` |
| `concept/00_meta/knowledge_topology/08_concept_source_alignment_atlas.md` | L0 | 1 | 1 | L138: `\| [占位符页面](../placeholders/placeholder_generic.md) \| L0 元信息层 \| 3 \| 无需外部来源 \|` |
| `concept/00_meta/knowledge_topology/10_gap_and_action_plan.md` | L0 | 1 | 1 | L111: `4. 将本行动计划中的缺口列表与 [全局待办清单](../00_framework/todos.md) 同步。` |
| `concept/00_meta/placeholders/placeholder_generic.md` | L0 | 1 | 2 | L1: `# 占位符页面` |
| `concept/00_meta/README.md` | L0 | 2 | 3 | L45: `\|`placeholders/`\| SUMMARY.md 占位符 \| 待创建主题的导航占位 \|` |
| `concept/00_meta/trpl_3rd_ed_mapping.md` | L0 | 2 | 2 | L2: `> **Summary**: Redirect stub pointing to the full TRPL 3rd Ed chapter-to-concept mapping in docs/01_learning/learning...` |
| `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` | L1 | 1 | 1 | L11: `> **权威来源**: 本页为`Ownership-Borrowing-Lifetimes`知识拓扑的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | L1 | 2 | 12 | L97: `- [十一、待补充与演进方向（TODOs）](#十一待补充与演进方向todos)` |
| `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | L1 | 2 | 14 | L109: `- [十二、待补充与演进方向（TODOs）](#十二待补充与演进方向todos)` |
| `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | L1 | 1 | 1 | L41: `- v2.2 (2026-05-14): 完成 TODO 双项——§13 Lifetime Elision 完整形式化（三条规则 ∀/⇒ 形式化、正例+反例、Rust Reference 来源）；§14`impl Trait`与生...` |
| `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` | L1 | 2 | 9 | L71: `- [十七、待补充与演进方向（TODOs）](#十七待补充与演进方向todos)` |
| `concept/01_foundation/02_type_system/04_type_system.md` | L1 | 3 | 15 | L147: `- [十二、待补充与演进方向（TODOs）](#十二待补充与演进方向todos)` |
| `concept/01_foundation/02_type_system/14_coercion_and_casting.md` | L1 | 1 | 1 | L629: `todo!()` |
| `concept/01_foundation/02_type_system/31_never_type.md` | L1 | 1 | 4 | L363: `>     let s: String = todo!(); //`todo!()` 返回 `!`，coerce 为 String` |
| `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` | L1 | 1 | 2 | L157: `// 编译期验证占位符数量和类型` |
| `concept/01_foundation/06_strings_and_text/46_formatting_and_display.md` | L1 | 1 | 6 | L3: `> **本节关键术语**: 格式化（Formatting） ·`Display` trait · `Debug` trait · `format!`宏 · 格式化字符串（Format String） · 占位符（Placeholder）` |
| `concept/01_foundation/08_error_handling/13_panic_and_abort.md` | L1 | 1 | 4 | L83: `├── 未实现: unimplemented!(), todo!()` |
| `concept/02_intermediate/00_traits/01_traits.md` | L2 | 2 | 16 | L47: `- #[fundamental]（`Pin<P>`修正、透明性原理、与 non_exhaustive 对比）；更新 TODO 列表` |
| `concept/02_intermediate/00_traits/19_advanced_traits.md` | L2 | 1 | 1 | L90: `// 关联类型: Trait 中的类型占位符` |
| `concept/02_intermediate/00_traits/39_dispatch_mechanisms.md` | L2 | 1 | 1 | L18: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/02_intermediate/01_generics/02_generics.md` | L2 | 2 | 15 | L44: `更新 TODO 列表` |
| `concept/02_intermediate/01_generics/39_type_level_programming.md` | L2 | 1 | 1 | L18: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/02_intermediate/02_memory_management/03_memory_management.md` | L2 | 2 | 13 | L115: `- [十二、待补充与演进方向（TODOs）](#十二待补充与演进方向todos)` |
| `concept/02_intermediate/02_memory_management/08_interior_mutability.md` | L2 | 1 | 1 | L864: `\| 多线程 + 原子操作 \|`AtomicXxx`\| 最高性能 \|` |
| `concept/02_intermediate/02_memory_management/12_smart_pointers.md` | L2 | 1 | 1 | L889: `\| 多线程 + 原子操作 \|`AtomicXxx`\| 最高性能 \|` |
| `concept/02_intermediate/03_error_handling/04_error_handling.md` | L2 | 2 | 14 | L110: `- [十一、待补充与演进方向（TODOs）](#十一待补充与演进方向todos)` |
| `concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md` | L2 | 1 | 3 | L183: `todo!()` |
| `concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md` | L2 | 1 | 9 | L141: `-`with_xxx`— 带某个特定属性` |
| `concept/02_intermediate/06_macros_and_metaprogramming/13_dsl_and_embedding.md` | L2 | 1 | 2 | L279: `// - 参数数量与占位符匹配（运行时检查）` |
| `concept/02_intermediate/07_iterators_and_closures/15_iterator_patterns.md` | L2 | 1 | 1 | L573: `todo!()` |
| `concept/03_advanced/00_concurrency/10_concurrency_patterns.md` | L3 | 1 | 4 | L1670: `todo!()` |
| `concept/03_advanced/01_async/02_async.md` | L3 | 2 | 11 | L58: `- v4.0 (2026-05-13): Phase 4 TODO 清理——新增§8.9 Waker/Context 底层机制（VTable、自定义 Reactor）、§8.10 Stream/Sink trait 完整分析（异步（A...` |
| `concept/03_advanced/01_async/39_future_and_executor_mechanisms.md` | L3 | 1 | 1 | L18: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/03_advanced/02_unsafe/03_unsafe.md` | L3 | 4 | 15 | L105: `- [十一、待补充与演进方向（TODOs）](#十一待补充与演进方向todos)` |
| `concept/03_advanced/02_unsafe/12_unsafe_rust_patterns.md` | L3 | 1 | 1 | L9: `> **Summary**: Redirect stub for Unsafe Rust patterns; authoritative content is in 03_unsafe.md.` |
| `concept/03_advanced/03_proc_macros/04_macros.md` | L3 | 3 | 10 | L44: `- v4.0 (2026-05-13): Phase 4 TODO 清理——新增 proc_macro2/syn/quote 最佳实践、macro_rules! 重复模式完整语法、const fn + const generics 替...` |
| `concept/03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md` | L3 | 1 | 1 | L23: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md` | L3 | 1 | 1 | L23: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md` | L3 | 1 | 1 | L23: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/03_advanced/03_proc_macros/32_macro_glossary.md` | L3 | 1 | 1 | L12: `> **权威来源**: 本页为`Macro Glossary`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/03_advanced/03_proc_macros/33_macro_faq.md` | L3 | 1 | 1 | L12: `> **权威来源**: 本页为`Macro FAQ`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/03_advanced/03_proc_macros/34_syn_quote_reference.md` | L3 | 1 | 1 | L12: `> **权威来源**: 本页为`syn and quote Reference`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/03_advanced/03_proc_macros/35_macro_hygiene.md` | L3 | 1 | 1 | L12: `> **权威来源**: 本页为`Macro Hygiene`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/04_formal/00_type_theory/02_type_theory.md` | L4 | 2 | 6 | L935: `## 十二、待补充与演进方向（TODOs）` |
| `concept/04_formal/00_type_theory/14_lambda_calculus.md` | L4 | 1 | 1 | L251: `todo!()` |
| `concept/04_formal/00_type_theory/50_type_system_reference.md` | L4 | 1 | 1 | L55: `\| Inferred 类型 \|`_`\| 类型推断（Type Inference）占位 \|` |
| `concept/04_formal/01_ownership_logic/01_linear_logic.md` | L4 | 2 | 6 | L896: `## 十三、待补充与演进方向（TODOs）` |
| `concept/04_formal/01_ownership_logic/03_ownership_formal.md` | L4 | 2 | 7 | L826: `## 十、待补充与演进方向（TODOs）` |
| `concept/04_formal/01_ownership_logic/09_linear_logic_applications.md` | L4 | 1 | 1 | L305: `todo!()` |
| `concept/04_formal/02_separation_logic/04_rustbelt.md` | L4 | 2 | 16 | L92: `- [十三、待补充与演进方向（TODOs）](#十三待补充与演进方向todos)` |
| `concept/04_formal/04_model_checking/32_kani.md` | L4 | 1 | 1 | L348: `\| **标准库支持范围** \| 部分`std`API（如浮点运算、I/O、网络）建模不完整，可能报 "unsupported" 或需要 stub。 \|` |
| `concept/05_comparative/00_paradigms/03_paradigm_matrix.md` | L5 | 2 | 8 | L717: `## 十三、待补充与演进方向（TODOs）` |
| `concept/05_comparative/01_systems_languages/02_rust_vs_go.md` | L5 | 2 | 5 | L741: `## 十三、待补充与演进方向（TODOs）` |
| `concept/05_comparative/02_managed_languages/07_rust_vs_python.md` | L5 | 1 | 1 | L358: `├── 第三方库的类型 stub 不完整` |
| `concept/05_comparative/03_domain_comparisons/04_safety_boundaries.md` | L5 | 2 | 2 | L655: `## 十二、待补充与演进方向（TODOs）` |
| `concept/06_ecosystem/00_toolchain/01_toolchain.md` | L6 | 2 | 6 | L102: `- [十六、待补充与演进方向（TODOs）](#十六待补充与演进方向todos)` |
| `concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md` | L6 | 1 | 1 | L495: `\| 编译错误 \|`rustc --explain E0XXX`、`cargo check`\|` |
| `concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md` | L6 | 1 | 1 | L13: `> **代码状态**: [综述级 — 待补充可编译示例]` |
| `concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md` | L6 | 1 | 1 | L137: `\|`HasPlaceholders`\| 需要用户填写占位符 \|` |
| `concept/06_ecosystem/01_cargo/09_cargo_script.md` | L6 | 1 | 1 | L9: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` | L6 | 1 | 1 | L174: `\| 新转义序列 \|`\uXXXX` \| 增加 `\xHH`、`\e`等 \| 更灵活的字符串表示 \|` |
| `concept/06_ecosystem/02_core_crates/03_core_crates.md` | L6 | 2 | 2 | L1008: `## 十、待补充与演进方向（TODOs）` |
| `concept/06_ecosystem/03_design_patterns/02_patterns.md` | L6 | 2 | 3 | L1075: `\| 2 \| 注释标记"若再次出现则提取" \| 模块级`// TODO: extract if reused`\|` |
| `concept/06_ecosystem/03_design_patterns/31_microservice_patterns.md` | L6 | 1 | 1 | L309: `todo!()` |
| `concept/06_ecosystem/03_design_patterns/34_idioms_spectrum.md` | L6 | 2 | 7 | L101: `- [测验 4：`todo!()` 和 `unimplemented!()`宏在开发中有什么用途？（理解层）](#测验-4todo-和-unimplemented-宏在开发中有什么用途理解层)` |
| `concept/06_ecosystem/03_design_patterns/35_architecture_patterns.md` | L6 | 1 | 1 | L600: `todo!()` |
| `concept/06_ecosystem/03_design_patterns/41_workflow_theory.md` | L6 | 1 | 3 | L532: `todo!()` |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`Design Patterns Glossary`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/03_design_patterns/85_design_patterns_faq.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`Design Patterns FAQ`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md` | L6 | 1 | 1 | L19: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/06_ecosystem/04_web_and_networking/43_websocket_realtime_communication.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`WebSocket Real-Time Communication`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/05_systems_and_embedded/39_os_kernel.md` | L6 | 1 | 1 | L9: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/06_ecosystem/05_systems_and_embedded/53_embedded_graphics.md` | L6 | 1 | 1 | L9: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/06_ecosystem/06_data_and_distributed/04_application_domains.md` | L6 | 2 | 2 | L980: `## 十、待补充与演进方向（TODOs）` |
| `concept/06_ecosystem/06_data_and_distributed/23_database_access.md` | L6 | 1 | 2 | L218: `todos: toasty::HasMany<Todo>,` |
| `concept/06_ecosystem/07_security_and_cryptography/43_security_cryptography.md` | L6 | 1 | 1 | L516: `todo!()` |
| `concept/06_ecosystem/08_formal_verification/44_formal_ecosystem_tower.md` | L6 | 2 | 3 | L27: `- v1.1 (2026-05-13): 补充层级标记、来源标注、知识来源关系、待补充方向` |
| `concept/06_ecosystem/09_networking/05_formal_network_protocol_theory.md` | L6 | 1 | 1 | L23: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/06_ecosystem/09_networking/06_networking_basics.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`Networking Basics`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/11_domain_applications/06_blockchain.md` | L6 | 2 | 4 | L660: `## 八、待补充与演进方向（TODOs）` |
| `concept/06_ecosystem/11_domain_applications/07_game_ecs.md` | L6 | 2 | 2 | L1136: `## 九、待补充与演进方向（TODOs）` |
| `concept/06_ecosystem/11_domain_applications/49_game_engine_internals.md` | L6 | 1 | 1 | L992: `// ✅ 修正: 使用 Result + 占位资源` |
| `concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md` | L6 | 1 | 1 | L8: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`WebAssembly Glossary`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/11_domain_applications/60_wasm_faq.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`WebAssembly FAQ`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/11_domain_applications/61_wasm_javascript_interop.md` | L6 | 1 | 1 | L12: `> **权威来源**: 本页为`WebAssembly JavaScript Interop`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md` | L6 | 1 | 1 | L8: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/06_ecosystem/11_domain_applications/76_algorithm_engineering_practice.md` | L6 | 1 | 1 | L19: `> **来源**: 本文档由`crates/*/docs/`合规整改迁移而来。原始 crate 文档现为摘要占位符，指向本权威页：` |
| `concept/07_future/00_version_tracking/05_rust_version_tracking.md` | L7 | 1 | 1 | L947: `\| **cargo-semver-checks** \| 继续解决合并到 cargo 的 blockers \| 2026–2027 \| 🟡 跟踪中 \|`docs/06_toolchain/`待补充 \|` |
| `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | L7 | 1 | 1 | L12: `> **权威来源**: 本页为`Rust 1.90 Stabilized Features`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | L7 | 2 | 4 | L12: `> **权威来源**: 本页为`Rust 1.94 Stabilized Features`的权威概念页；crate 文档仅保留导航 stub。` |
| `concept/07_future/00_version_tracking/rust_1_98_preview.md` | L7 | 1 | 1 | L569: `## 八、待补充代码任务` |
| `concept/07_future/01_edition_roadmap/23_rust_edition_guide.md` | L7 | 1 | 1 | L3: `> **Summary**: Redirect stub for Rust Edition mechanism and migration guide; authoritative content is in 44_edition_g...` |
| `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | L7 | 2 | 2 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/10_derive_coerce_pointee_preview.md` | L7 | 2 | 3 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/11_const_trait_impl_preview.md` | L7 | 1 | 1 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/12_return_type_notation_preview.md` | L7 | 1 | 2 | L141: ``T::check(..)` 表示「调用 `T::check`返回的类型」。`..`占位符表示方法的泛型（Generics）参数由编译器推导。` |
| `concept/07_future/03_preview_features/13_unsafe_fields_preview.md` | L7 | 1 | 1 | L4: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/18_async_drop_preview.md` | L7 | 1 | 1 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/22_gen_blocks_preview.md` | L7 | 1 | 2 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/25_open_enums_preview.md` | L7 | 1 | 1 | L271: `> -`UNKNOWN`为编译器隐式添加的**未知变体占位符**` |
| `concept/07_future/03_preview_features/26_specialization_preview.md` | L7 | 1 | 1 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/39_arbitrary_self_types_preview.md` | L7 | 1 | 1 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/03_preview_features/45_std_autodiff_preview.md` | L7 | 1 | 1 | L3: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/04_research_and_experimental/01_ai_integration.md` | L7 | 2 | 2 | L297: `2. **Anti-unification**：将多个具体修复抽象为通用模板（如`h0.h1();` → `if (h0 == null) return; h0.h1();`），其中`h0`、`h1`为占位符。` |
| `concept/07_future/04_research_and_experimental/03_evolution.md` | L7 | 3 | 6 | L63: `- v1.25 (2026-06-08): Phase 3 深度瘦身完成：① 迁移 12 个活跃层级中的"已归档-in-place"重复文件至`concept/archive/`（L3 新增 5 个：02_async_program...` |
| `concept/07_future/04_research_and_experimental/29_ebpf_rust.md` | L7 | 1 | 3 | L233: `Rex（Rust for eBPF Extended）是 2025-2026 年间发表的一系列学术研究的实现项目，其核心命题是：**用 Rust 编译器替代 eBPF 验证器** [Rex: Safe Rust for eBPF, a...` |
| `concept/07_future/04_research_and_experimental/43_rust_for_linux.md` | L7 | 1 | 1 | L4: `> **代码状态**: [综述级 — 待补充代码]` |
| `concept/07_future/05_roadmaps/24_roadmap.md` | L7 | 1 | 1 | L831: `>`!`的稳定化是 Rust 类型系统成熟度的重要里程碑——它使"不可恢复错误"在类型层面得到精确表达，而非使用占位类型（`std::convert::Infallible`）。` |
| `concept/README.md` | L? | 1 | 1 | L112: `## 九、待补充与演进方向` |
| `concept/SUMMARY.md` | L? | 2 | 4 | L37: `- [占位符模板（Placeholder Generic）](00_meta/placeholders/placeholder_generic.md)` |

### 2.3 Files with empty sections (420)

| File | Layer | Empty section transitions |
|:---|:---|:---|
| `concept/README.md` | L? | ## 五、内容规范 → ### 5.1 文件命名规范; # 概念名称 → ## 一、权威定义（Wikipedia / 官方文档对齐）; ## 一、权威定义（Wikipedia / 官方文档对齐） → ## 二、概念属性矩阵 … and 8 more |
| `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | L7 | ## 改进的类型检查器（借用检查器优化） → ### Rust 1.91 改进概述; ### 核心改进 → #### 1. 借用检查器缓存机制; ## 增强的 const 上下文（对生命周期的影响） → ### Rust 1.91 改进概述 … and 52 more |
| `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | L7 | ## MaybeUninit 文档化 → ### Rust 1.92.0 改进概述; ### 核心改进 → #### 1. 文档化的表示和有效性; ## 联合体原始引用 → ### Rust 1.92.0 改进概述 … and 49 more |
| `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | L7 | ## Rust 1.94 关键特性 → ### 1.1 新增特性; ## 代码示例 → ### 2.1 基础用法; ## 迁移指南 → ### 3.1 从 Rust 1.93 迁移 … and 11 more |
| `concept/07_future/04_research_and_experimental/02_formal_methods.md` | L7 | ## 一、基础定义 → ### 1.1 形式化验证（Formal Verification）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：形式化验证 vs 测试（理解层）; ## 六、CI/CD 集成方案 → ### 6.1 GitHub Actions 集成 … and 10 more |
| `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | L7 | ## 1. 异步特性增强 → ### 1.1 异步Trait稳定化（RPITIT）; ## 2. GATs在网络编程中的应用 → ### 泛型关联类型（Generic Associated Types）; ## 3. let-else模式匹配 → ### 网络错误处理 … and 7 more |
| `concept/07_future/04_research_and_experimental/01_ai_integration.md` | L7 | ## 一、核心命题 → ## 认知路径（精简版）; ## 五、AI + Rust 工具链详解 → ## 五、AI 辅助 Rust 编程的机制剖析; ## 五、AI 辅助 Rust 编程的机制剖析 → ### 5.1 编译器作为确定性 RL 环境 … and 5 more |
| `concept/07_future/05_roadmaps/24_roadmap.md` | L7 | ## 一、核心概念：Edition 2027 的设计空间 → ### 1.1 Edition 演进节奏与政策; ## 二、类型系统前沿 → ### 2.1 Specialization 稳定化; ## 三、异步与执行模型 → ### 3.1 Async Traits 与静态分发 … and 5 more |
| `concept/07_future/00_version_tracking/05_rust_version_tracking.md` | L7 | ## 二、维度一：所有权与别名模型 → ### 2.1 `&raw const` / `&raw mut`（1.82 stable，[RFC 2582](https://rust-lang.github.io/rfcs//2582-raw-reference-mir-operator.html)）; ## 三、维度二：类型系统扩展 → ### 3.1 `+ use<'lt>` precise capturing（1.82 stable，[RFC 3617](https://rust-lang.github.io/rfcs//3617-precise-capturing.html)）; ## 四、维度三：异步与效果系统 → ### 4.1 Async closures（1.85 stable，[RFC 3668](https://rust-lang.github.io/rfcs//3668-async-closures.html)） … and 4 more |
| `concept/07_future/03_preview_features/08_safety_tags_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题定义：Unsafe 契约的表达缺口; ## 二、形式化语义 → ### 2.1 契约的谓词逻辑表示; ## 三、使用场景 → ### 3.1 AI 生成代码的安全标注 … and 4 more |
| `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` | L7 | ## 1. 语言层 → ### 1.1 `assert_matches!` / `debug_assert_matches!`; ## 2. 标准库层 → ### 2.1 `core::range` Copy 类型; ## 3. Cargo 与工具链 → ### 3.1 git + alternate registry 共存 … and 3 more |
| `concept/07_future/00_version_tracking/rust_1_98_preview.md` | L7 | ## 一、语言特性预览 → ### 1.1 Pin Ergonomics（&pin mut / &pin const）; ## 三、编译器与工具链预览 → ### 3.1 Cranelift Backend（生产级）; ## 四、Cargo 与生态预览 → ### 4.1 Public/Private Dependencies（RFC #3516） … and 3 more |
| `concept/07_future/03_preview_features/10_derive_coerce_pointee_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：自定义智能指针的样板代码; ## 二、技术细节 → ### 2.1 派生宏的展开逻辑; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 3 more |
| `concept/07_future/03_preview_features/12_return_type_notation_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：AFIT/RPITIT 的返回类型无法命名; ## 二、技术细节 → ### 2.1 语法形式与语义; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 3 more |
| `concept/07_future/03_preview_features/15_pin_ergonomics_preview.md` | L7 | ## 一、核心问题：Pin 的人机工程学危机 → ### 1.1 当前的五大痛点; ## 二、解决方案 1：Reborrow Traits（已推进） → ### 2.1 问题：`Pin<&mut T>` 不能自动 reborrow; ## 三、解决方案 2：Pinned Places（RFC 讨论中） → ### 3.1 核心想法：`pin` 关键字 … and 3 more |
| `concept/07_future/03_preview_features/22_gen_blocks_preview.md` | L7 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`gen` 块与 `async` 块有什么相似之处？（理解层）; ## 一、核心概念 → ### 1.1 从 async 到 gen 的泛化; ## 二、技术细节 → ### 2.1 生成器状态机 … and 3 more |
| `concept/07_future/03_preview_features/25_open_enums_preview.md` | L7 | ## 二、`#[non_exhaustive]` 的形式化语义 → ### 2.1 编译期影响：穷尽性检查的弱化; ## 三、跨语言对比：开放枚举的多种形态 → ### 3.1 Scala：Sealed Traits + 子类; ## 四、API 设计中的开放枚举模式 → ### 4.1 错误码枚举 … and 3 more |
| `concept/07_future/03_preview_features/26_specialization_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：泛型实现的表达力限制; ## 二、技术细节 → ### 2.1 特化语法与语义; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 3 more |
| `concept/07_future/03_preview_features/27_compile_time_execution.md` | L7 | ## 一、核心概念 → ### 1.1 const fn; ## 二、编译期能力边界 → ### 2.1 稳定的编译期操作; ## 三、应用模式 → ### 3.1 编译期计算 … and 3 more |
| `concept/07_future/04_research_and_experimental/03_evolution.md` | L7 | # 3. 手动修改 Cargo.toml: edition = "2024" → # 4. 重新构建验证; ### 3.7 未来语言设计方向 → #### 3.7.1 Effects System（效应系统）; ## 五、官方来源与追踪 → ### 5.1 Rust Lang Team Blog … and 3 more |
| `concept/07_future/04_research_and_experimental/28_rust_for_webassembly.md` | L7 | ## 一、权威定义与核心概念 → ### 1.1 Rust → Wasm 的编译模型; ## 二、前端框架深度对比 → ### 2.1 Yew：React 范式的 Rust 实现; ## 四、工具链与工程实践 → ### 4.1 目标三元组与编译配置 … and 3 more |
| `concept/07_future/01_edition_roadmap/44_edition_guide.md` | L7 | ## 一、核心概念 → ### 1.1 Edition 机制回顾; ## 二、技术细节 → ### 2.1 Gen Blocks; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | L7 | ## 二、技术机制：Retag Intrinsics + Shadow Stack → ### 2.1 核心设计哲学; ## 三、使用方法 (Nightly) → ### 3.1 基本使用; # Step 3: 如果 BSan 通过而 Miri 失败，说明 Miri 过于保守， → #         考虑用 UnsafeCodeGuidelines 讨论区的意见作为参考 … and 2 more |
| `concept/07_future/03_preview_features/07_mcdc_coverage_preview.md` | L7 | ## 一、核心概念 → ### 1.1 覆盖率等级的层次结构; ## 二、形式化语义 → ### 2.1 独立影响的形式化; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/09_parallel_frontend_preview.md` | L7 | ## 一、核心概念 → ### 1.1 Rust 编译器架构回顾; ## 二、技术方案 → ### 2.1 查询系统的并行化; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/11_const_trait_impl_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：常量上下文中的 Trait 鸿沟; ## 二、技术细节 → ### 2.1 常量 Trait 的约束继承; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题定义：编译期检查的边界; ## 三、形式化语义 → ### 3.1 借用标签的生命周期; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/35_ferrocene_preview.md` | L7 | ## 一、核心概念 → ### 1.1 安全关键软件的认证挑战; ## 二、技术细节 → ### 2.1 认证工具链的构成; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/38_cranelift_backend_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：LLVM 的编译时间瓶颈; ## 二、技术细节 → ### 2.1 架构对比：LLVM vs Cranelift; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/45_std_autodiff_preview.md` | L7 | ## 一、核心概念 → ### 1.1 自动微分（AD）是什么; ## 二、`std::autodiff` 设计预览 → ### 2.1 语法构想（基于 Project Goals 2026）; ## 三、技术挑战与状态 → ### 3.1 当前状态（2026-06） … and 2 more |
| `concept/07_future/04_research_and_experimental/43_rust_for_linux.md` | L7 | ## 二、技术细节 → ### 2.1 C 互操作与绑定生成; ### 3.4 生产级驱动案例（自 `docs/04_research/04_rust_for_linux.md` 合并） → #### Android Binder IPC; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 2 more |
| `concept/07_future/03_preview_features/13_unsafe_fields_preview.md` | L7 | ## 二、技术细节 → ### 2.1 语法与语义; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Unsafe Fields 预览的编译错误 → ### 10.1 边界测试：unsafe 字段的显式访问要求（编译错误） … and 1 more |
| `concept/07_future/03_preview_features/18_async_drop_preview.md` | L7 | ## 二、技术细节 → ### 2.1 当前 Workaround 模式; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：async drop 的编译错误 → ### 10.1 边界测试：异步析构的 `.await` 位置约束（编译错误） … and 1 more |
| `concept/07_future/03_preview_features/41_rust_specification_preview.md` | L7 | ## 二、技术细节 → ### 2.1 规范的内容层次; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 规范预览的编译错误 → ### 10.1 边界测试：规范未定义行为的边界（编译错误/运行时 UB） … and 1 more |
| `concept/07_future/03_preview_features/48_aarch64_sve_sme_preview.md` | L7 | ## 一、核心概念 → ### 1.1 从固定向量到可伸缩向量; ## 二、Rust 支持现状（截至 2026-06-06） → ### 2.1 Feature Gate; ## 三、技术挑战 → ### 3.1 Rust 类型系统适配 … and 1 more |
| `concept/07_future/04_research_and_experimental/21_rust_in_ai.md` | L7 | ## 二、技术细节 → ### 2.1 Candle：纯 Rust ML 框架; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust in AI 的编译错误 → ### 10.1 边界测试：`candle` 的张量形状不匹配（编译错误/运行时 panic） … and 1 more |
| `concept/07_future/04_research_and_experimental/29_ebpf_rust.md` | L7 | ## 6. Rust 实现示例 → ### 6.1 Aya XDP 程序骨架（内核态）; ## 8. 边界与限制 → ### 8.1 eBPF 指令复杂度限制; ## 十、边界测试：eBPF Rust 的编译错误 → ### 10.1 边界测试：eBPF 程序的栈大小限制（编译错误/验证失败） … and 1 more |
| `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | L7 | ## 1. 语言层 → ### 1.1 `cfg_select!` 宏; ## 2. 标准库层 → ### 2.1 `core::range` 模块; ## 3. 编译器与平台 → ### 3.1 `--remap-path-scope` 稳定化 |
| `concept/07_future/00_version_tracking/rust_1_97_preview.md` | L7 | ## 一、语言与编译器 → ### 1.1 `must_use` lint 扩展; ## 二、标准库 API → ### 2.1 `NonZero` 位操作; ## 三、目标平台与工具链 → ### 3.1 `cfg_target_has_atomic_equal_alignment` |
| `concept/07_future/01_edition_roadmap/19_rust_edition_preview.md` | L7 | ## 四、迁移前后代码对比 → ### Async closures; # 3. 手动检查 cargo fix 无法自动处理的变更 → # 4. 更新 Cargo.toml 中的 edition 字段; # 4. 更新 Cargo.toml 中的 edition 字段 → # edition = "2024" |
| `concept/07_future/03_preview_features/17_const_trait_preview.md` | L7 | ## 二、语法说明 → ### 2.1 声明 const trait; ## 三、与稳定 Rust 的对比及迁移建议 → ### 3.1 当前替代方案; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`const trait` 与 `const fn` 有什么区别？（理解层） |
| `concept/07_future/03_preview_features/30_stable_abi_preview.md` | L7 | ## 二、当前稳定 Rust 的 ABI 选择 → ### 2.1 `extern "C"` 与 `#[repr(C)]`; ## 四、与稳定 Rust 的对比及迁移建议 → ### 4.1 当前最佳实践; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：为什么 Rust 目前没有稳定的 ABI？（理解层） |
| `concept/07_future/03_preview_features/40_ergonomic_ref_counting_preview.md` | L7 | ## 一、核心概念 → ### 1.1 问题：引用计数的非人机工学; ## 二、设计方向与关键技术 → ### 2.1 可能的语言机制; ## 嵌入式测验（Embedded Quiz） → ### 测验 1："人机工程学的引用计数"指什么？（理解层） |
| `concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md` | L7 | ## 二、2026 年关键演进方向 → ### 2.1 Type-Checking Lints（最大能力缺口）; ## 三、对 Rust 生态的结构性影响 → ### 3.1 供应链稳定性; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`cargo-semver-checks` 如何检测 breaking change？（理解层） |
| `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` | L7 | ## 2. 主要稳定特性详解 → ### 2.1 `NonZero*` 位查询方法; ## 3. 迁移指南 → ### 3.1 从 Rust 1.96.x 迁移 |
| `concept/07_future/03_preview_features/04_effects_system.md` | L7 | ## 六、代数效果的数学基础 → ### 6.1 代数效果的形式化定义; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：什么是"效果系统"（Effect System）？它与类型系统有什么关系？（理解层） |
| `concept/07_future/03_preview_features/14_lifetime_capture_preview.md` | L7 | ## 二、语法说明：`use<'lt>` 与捕获规则 → ### 2.1 旧行为（Rust 2021 及之前）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1："生命周期捕获规则"的改进解决了什么问题？（理解层） |
| `concept/07_future/03_preview_features/16_type_alias_impl_trait_preview.md` | L7 | ## 二、语法说明与核心规则 → ### 2.1 模块级 TAIT; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Type Alias Impl Trait（TAIT）是什么？（理解层） |
| `concept/07_future/03_preview_features/31_safety_tags_preview.md` | L7 | ## 二、核心机制 → ### 2.1 声明安全标签：`#[safety::requires(...)]`; ## 三、为什么需要 Safety Tags？ → ### 3.1 降低 unsafe 代码审计成本 |
| `concept/07_future/03_preview_features/32_inline_const_pattern_preview.md` | L7 | ## 二、语法说明 → ### 2.1 稳定基础：Inline Const 表达式（Rust 1.79+）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`inline const` 模式是什么？它解决了什么问题？（理解层） |
| `concept/07_future/03_preview_features/33_autoverus_preview.md` | L7 | ## 二、Verus 核心机制 → ### 2.1 三段式程序结构; ## 三、AutoVerus：LLM 驱动的自动化证明 → ### 3.1 设计原则 |
| `concept/07_future/03_preview_features/34_must_not_suspend_preview.md` | L7 | ## 二、语法说明：如何启用与使用 → ### 2.1 启用 lint; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`must_not_suspend`  lint 的作用是什么？（理解层） |
| `concept/07_future/03_preview_features/37_rpitit_preview.md` | L7 | ## 二、语法说明 → ### 2.1 基础 RPITIT; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：RPITIT（Return Position Impl Trait In Traits）是什么？（理解层） |
| `concept/07_future/03_preview_features/42_field_projections_preview.md` | L7 | ## 五、演进路线 → ### 5.1 2026 年官方三步计划（Rust Project Goals 2026 — Beyond the `&`）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Pinned field projections 解决的是什么问题？（理解层） |
| `concept/07_future/03_preview_features/47_wasm_target_evolution.md` | L7 | ## 二、核心概念：target 命名与能力模型 → ### 2.1 `wasm32-unknown-unknown`; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：WASM 的 target 命名为什么从 `wasm32-unknown-unknown` 演进为更多变体？（理解层） |
| `concept/07_future/03_preview_features/49_rust_in_space.md` | L7 | ## 二、核心应用场景 → ### 2.1 卫星星载软件; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：为什么航天领域对 Rust 感兴趣？（理解层） |
| `concept/07_future/00_version_tracking/rust_1_93_stabilized.md` | L7 | ## 三、主要稳定特性 → ### 3.1 `MaybeUninit` 增强 API |
| `concept/07_future/03_preview_features/39_arbitrary_self_types_preview.md` | L7 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Arbitrary Self Types 允许什么目前不允许的操作？（理解层） |
| `concept/07_future/README.md` | L7 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L7 前沿趋势层（Future & Trends）》在本知识体系中扮演什么角色？（理解层） |
| `concept/06_ecosystem/00_toolchain/28_devops_and_ci_cd.md` | L6 | # .github/workflows/ci.yml 示例框架 → # ·name: CI; ## 三、DevOps 决策矩阵 → ### 3.1 发布自动化决策; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 31 more |
| `concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md` | L6 | ## 📐 知识结构 → ### 概念定义; ## 1. 零拷贝技术深度 → ### 1.1 传统拷贝的性能问题; ## 2. io_uring异步I/O → ### 2.1 io_uring架构原理 … and 24 more |
| `concept/06_ecosystem/11_domain_applications/76_algorithm_engineering_practice.md` | L6 | ## 📐 知识结构 → ### 概念定义; ## 1. 大规模系统设计 → ### 1.1 海量数据处理; ### 1.1 海量数据处理 → #### 外部排序 (External Sorting) … and 15 more |
| `concept/06_ecosystem/03_design_patterns/02_patterns.md` | L6 | # [derive(Debug, Diagnostic, thiserror::Error)] → # [error("配置解析失败")]; # [error("配置解析失败")] → # [diagnostic(; ## 十二、边界测试：设计模式的编译错误 → ### 12.1 边界测试：Builder 模式未消费 self（编译错误） … and 10 more |
| `concept/06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md` | L6 | ## 2. Trait vs 泛型实现对比 → ### 2.1 Strategy模式对比; ### 2.1 Strategy模式对比 → #### 方式 1：Trait Object (动态分派); ## 3. 同步 vs 异步实现对比 → ### 3.1 Observer模式对比 … and 10 more |
| `concept/06_ecosystem/03_design_patterns/35_architecture_patterns.md` | L6 | ## 三、分层架构 → ### 3.1 经典四层模型; # 零外部依赖（仅标准库 + uuid + chrono 等纯工具库） → # Cargo.toml (infrastructure crate); ## 四、六边形架构 → ### 4.1 端口（Ports） … and 9 more |
| `concept/06_ecosystem/03_design_patterns/34_idioms_spectrum.md` | L6 | ## 三、L0 词法级惯用法 → ### 3.1; ## 四、L1 类型级惯用法 → ### 4.1; ## 五、L2 接口级惯用法 → ### 5.1 … and 8 more |
| `concept/06_ecosystem/09_testing_and_quality/12_testing_strategies.md` | L6 | ## 二、技术细节 → ### 2.1 内置测试框架; ## 四、反命题与边界分析 → ### 4.1 反命题树; # L4: 属性测试（可选） → # - run: cargo test --features proptest … and 8 more |
| `concept/06_ecosystem/11_domain_applications/54_webassembly_advanced.md` | L6 | ## 一、权威定义 → ### 1.1 WebAssembly 作为通用字节码; ## 二、WASM 执行模型全景 → ### 2.1 浏览器宿主：JS 引擎集成; ## 三、Rust WASM 工具链深度 → ### 3.1 wasm-bindgen：JS 互操作的生成艺术 … and 8 more |
| `concept/06_ecosystem/11_domain_applications/49_game_engine_internals.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 游戏引擎的定义与边界; ## 三、引擎架构模式 → ### 3.1 主循环与更新阶段; ## 四、渲染管线 → ### 4.1 现代图形 API 演进 … and 7 more |
| `concept/06_ecosystem/00_toolchain/45_compiler_internals.md` | L6 | ## 三、前端：解析与 AST → ### 3.1 词法与语法分析; ## 四、HIR：高级中间表示 → ### 4.1 HIR 的设计目标; ## 五、类型系统实现 → ### 5.1 Trait 解析与 Chalk … and 6 more |
| `concept/06_ecosystem/03_design_patterns/73_pattern_composition_algebra.md` | L6 | ## 二、模式组合的基本操作 → ### 2.1 四种组合原语; ## 三、常见模式组合与冲突矩阵 → ### 3.1 协同组合（Synergistic Compositions）; ## 四、模式选择的形式化决策树 → ### 4.1 问题特征 → 模式选择 … and 6 more |
| `concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 共识问题的形式化定义; ## 三、Paxos 与 Multi-Paxos → ### 3.1 Paxos 核心协议; ## 四、Raft：可理解的共识 → ### 4.1 Raft 核心机制 … and 6 more |
| `concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 形式化验证的层次模型; ## 三、模型检验工具 → ### 3.1 Kani：基于 CBMC 的 Rust 验证器; ## 四、演绎验证工具 → ### 4.1 Prusti：Viper 分离逻辑验证器 … and 6 more |
| `concept/06_ecosystem/09_networking/06_networking_basics.md` | L6 | ## 📐 知识结构 → ### 概念定义; ## 1. 网络编程基础 → ### 1.1 OSI 模型与 TCP/IP; ## 2. TCP 连接管理 → ### 2.1 TCP 服务器 … and 6 more |
| `concept/06_ecosystem/11_domain_applications/46_machine_learning_ecosystem.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 Rust ML 生态定位; ## 三、深度学习框架 → ### 3.1 candle：纯 Rust 推理引擎; ## 四、传统机器学习 → ### 4.1 linfa：scikit-learn 风格算法库 … and 6 more |
| `concept/06_ecosystem/02_core_crates/03_core_crates.md` | L6 | ## 一、权威定义 → ### 1.1 Wikipedia 权威定义; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：serde 的核心机制（理解层）; ### 4.11 核心并发 Crate 深度解析 → #### crossbeam：无锁并发原语 … and 5 more |
| `concept/06_ecosystem/03_design_patterns/33_cqrs_event_sourcing.md` | L6 | ## 二、概念属性矩阵 → ### 2.1 CQRS+ES 模式对比矩阵; ## 三、CQRS 核心 → ### 3.1 命令端：写模型优化; ## 四、事件溯源核心 → ### 4.1 事件不可变性与追加模型 … and 5 more |
| `concept/06_ecosystem/03_design_patterns/38_formal_design_pattern_theory.md` | L6 | ## 2. 类型理论基础 → ### 2.1 简单类型λ演算; ## 3. 范畴论视角 → ### 3.1 Functor 与模式; ## 4. Curry-Howard 同构 → ### 4.1 类型即命题，程序即证明 … and 5 more |
| `concept/06_ecosystem/03_design_patterns/41_workflow_theory.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 工作流管理联盟（WfMC）定义; ## 三、形式化表示 → ### 3.1 工作流图; ## 四、Rust 中的工作流实现 → ### 4.1 异步机制与工作流同构性 … and 5 more |
| `concept/06_ecosystem/03_design_patterns/42_api_design_patterns.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 REST：表述性状态转移; ## 三、API 设计原则 → ### 3.1 RESTful 资源建模; ## 四、REST API 设计 → ### 4.1 路由与处理器 … and 5 more |
| `concept/06_ecosystem/04_web_and_networking/40_reactive_programming.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 Reactive Manifesto：响应式系统的四大特质; ## 二、概念属性矩阵 → ### 2.1 Reactive 编程模型对比矩阵; ## 三、Reactive Streams 核心 → ### 3.1 四元接口模型 … and 5 more |
| `concept/06_ecosystem/04_web_and_networking/43_websocket_realtime_communication.md` | L6 | ## 📐 知识结构 → ### 概念定义; ## 1. WebSocket 基础 → ### 1.1 WebSocket vs HTTP; ## 2. 使用 tokio-tungstenite → ### 2.1 基础客户端 … and 5 more |
| `concept/06_ecosystem/05_systems_and_embedded/52_robotics.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 机器人软件栈; ## 三、ROS2 Rust 生态 → ### 3.1 rclrs：官方 Rust 客户端库; ## 四、实时机器人系统 → ### 4.1 ROS2 执行器模型 … and 5 more |
| `concept/06_ecosystem/06_data_and_distributed/48_data_engineering.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 数据工程的分层架构; ## 三、数据摄取层（Ingestion） → ### 3.1 批处理摄取; ## 四、数据转换层（Transformation） → ### 4.1 DataFrame 转换 … and 5 more |
| `concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 量子比特与量子态; ## 三、Rust 量子计算生态 → ### 3.1 roqoqo / qoqo：量子电路表示工具包; ## 四、经典硬件上的量子模拟 → ### 4.1 态向量模拟 … and 5 more |
| `concept/06_ecosystem/11_domain_applications/61_wasm_javascript_interop.md` | L6 | ## 📐 知识结构 → ### 概念定义; ## 🔗 基础集成 → ### 加载 WASM 模块; ## ⚛️ React 集成 → ### 基本用法 … and 5 more |
| `concept/06_ecosystem/00_toolchain/01_toolchain.md` | L6 | ## 二、概念属性矩阵 → ### 2.1 核心工具矩阵; ## 三、Cargo 深层机制 → ### 3.1 Workspace 高级用法; ## 四、Cross-compilation（交叉编译） → ### 4.1 目标三元组（Target Triple） … and 4 more |
| `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` | L6 | ## 二、并行前端（Parallel Frontend） → ### 2.1 核心机制; # 当前状态: nightly 实验性，稳定版 1.96 未默认启用 → # 需要 nightly 工具链并通过 -Z threads 手动开启:; ## 三、Cranelift 后端 → ### 3.1 设计目标 … and 4 more |
| `concept/06_ecosystem/01_cargo/72_cargo_security_cves.md` | L6 | ## 一、核心概念 → ### 1.1 影响范围：仅第三方 registry; ## 二、缓解措施与安全实践 → ### 2.1 立即升级工具链; ### 2.4 安全的 Cargo.toml 与 registry 配置 → #### 示例 1：限制依赖来源，避免意外引入第三方 registry … and 4 more |
| `concept/06_ecosystem/06_data_and_distributed/55_rust_for_data_science.md` | L6 | ## 一、权威定义（Definition） → ### 1.1 数据科学的 Rust 定位; ## 三、数据处理与 ETL → ### 3.1 Polars：DataFrame 引擎; ## 四、统计分析与数值计算 → ### 4.1 统计生态 … and 4 more |
| `concept/06_ecosystem/07_security_and_cryptography/43_security_cryptography.md` | L6 | ## 三、对称加密 → ### 3.1 AES-GCM; ## 四、非对称加密与数字签名 → ### 4.1 ECC 与 Ed25519; ## 五、哈希与消息认证 → ### 5.1 哈希函数 … and 4 more |
| `concept/06_ecosystem/11_domain_applications/29_algorithms_competitive_programming.md` | L6 | ## 三、竞赛编程惯用法 → ### 3.1 Fast I/O; ## 四、复杂度在类型系统中的编码 → ### 4.1 Const Generics 编码数组边界; ## 五、形式验证与算法 → ### 5.1 VeriContest 案例研究 … and 4 more |
| `concept/06_ecosystem/11_domain_applications/60_wasm_faq.md` | L6 | ## 🌐 WASM 基础问题 → ### Q: WASM 和 JavaScript 有什么区别？; ## 🦀 Rust 编译问题 → ### Q: 如何将 Rust 代码编译为 WASM？; ## 🔗 JavaScript 集成问题 → ### Q: 如何在 React 中使用 WASM？ … and 4 more |
| `concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md` | L6 | ## 一、Cargo 依赖管理 → ### Q1. 以下 `Cargo.toml` 片段中，`^`、`~`、`=` 版本约束的含义是什么？; ## 二、Clippy 与代码质量 → ### Q4. 以下代码中，Clippy 会发出什么警告？如何修复？; ## 三、编译配置与目标平台 → ### Q6. 以下 `.cargo/config.toml` 配置的作用是什么？ … and 3 more |
| `concept/06_ecosystem/01_cargo/09_cargo_script.md` | L6 | ## 二、Frontmatter 语法详解 → ### 2.1 完整字段支持; ## 四、工程实践 → ### 4.1 快速 CLI 原型; ## 五、形式化定位 → ### 5.1 匿名 Crate 语义 … and 3 more |
| `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` | L6 | ## 二、`pubtime`：crate 版本发布时间字段 → ### 2.1 背景; ## 三、`CARGO_BIN_EXE_<crate>` 运行时可用 → ### 3.1 变更内容; ## 四、TOML v1.1 支持 → ### 4.1 变更内容 … and 3 more |
| `concept/06_ecosystem/03_design_patterns/05_system_design_principles.md` | L6 | ## 二、七项核心设计原则 → ### 2.1 内存安全：Capability-Based Security; ## 六、思维表征体系 → ### 6.1 设计原则依赖图; ## 七、定理推理链 → ### 定理一致性矩阵（系统设计专集） … and 3 more |
| `concept/06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | L6 | ## 2. 模式选择决策树 → ### 2.1 创建型模式决策树; ## 3. 场景驱动的模式选择 → ### 3.1 Web服务器场景; ## 4. 反模式与陷阱 → ### 4.1 过度工程 … and 3 more |
| `concept/06_ecosystem/03_design_patterns/85_design_patterns_faq.md` | L6 | ## 🎯 核心问题 → ### 基础概念; ### 基础概念 → #### Q1: 什么时候应该使用设计模式？; ### 模式选择 → #### Q4: Rust 中如何实现线程安全的单例模式？ … and 3 more |
| `concept/06_ecosystem/04_web_and_networking/24_cloud_native.md` | L6 | ## 一、核心概念 → ### 1.1 云原生定义; ## 二、Web 框架 → ### 2.1 Axum; ## 三、基础设施 → ### 3.1 服务网格 … and 3 more |
| `concept/06_ecosystem/04_web_and_networking/27_web_frameworks.md` | L6 | ## 四、中间件机制深度对比 → ### 4.1 中间件模型分类; ## 五、性能基准与资源效率 → ### 5.1 TechEmpower 基准解读; ## 六、选型决策框架 → ### 6.1 "选哪个框架？" 决策树 … and 3 more |
| `concept/06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md` | L6 | ## 一、Embedded-HAL 生态现状（2026-06） → ### 1.1 版本里程碑; ## 二、Embedded-HAL 1.0 核心变化 → ### 2.1 错误类型统一; ## 三、Embassy v0.5 生产就绪状态 → ### 3.1 Embassy 是什么 … and 3 more |
| `concept/06_ecosystem/06_data_and_distributed/04_application_domains.md` | L6 | ## 一、权威定义 → ### 1.1 Wikipedia 权威定义; # ![no_std] → # ![no_main]; # [derive(Parser)] → # [command(name = "mytool")] … and 3 more |
| `concept/06_ecosystem/06_data_and_distributed/23_database_access.md` | L6 | ## 一、核心概念 → ### 1.1 SQLx — 编译期检查; ## 二、查询模式 → ### 2.1 原始 SQL; ## 三、连接管理 → ### 3.1 连接池 … and 3 more |
| `concept/06_ecosystem/03_design_patterns/30_system_composability.md` | L6 | ## 认知路径（Cognitive Path） → ### 第 1 步：为什么 Rust 特别适合可组合系统？; ## 二、四大可组合模式 → ### 2.1 管道-过滤器 (Pipe-and-Filter); ## 四、反模式 → ### 4.1 过度组合导致的类型爆炸 … and 2 more |
| `concept/06_ecosystem/03_design_patterns/31_microservice_patterns.md` | L6 | ## 二、服务发现与注册 → ### 2.1 Consul / etcd 客户端集成; ## 四、熔断器 → ### 4.1 状态机模型 (Closed/Open/Half-Open); ## 十、综合示例 → ### 10.1 极简微服务（标准库实现） … and 2 more |
| `concept/06_ecosystem/03_design_patterns/39_frontier_research_and_innovative_patterns.md` | L6 | ## 2. Effect 系统 → ### 2.1 显式 Effect 标记; ## 3. Algebraic Effects → ### 3.1 Effect Handlers; ## 4. Session Types 高级应用 → ### 4.1 多方会话类型 (Multiparty Session Types) … and 2 more |
| `concept/06_ecosystem/04_web_and_networking/18_distributed_systems.md` | L6 | ## 一、核心概念 → ### 1.1 Rust 在分布式系统中的定位; ## 二、技术细节 → ### 2.1 gRPC 与 Protocol Buffers; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md` | L6 | ## 二、硬件抽象层 → ### 2.1 PAC — 外设访问 crate; ## 三、实时系统 → ### 3.1 实时约束; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/06_ecosystem/05_systems_and_embedded/25_cli_development.md` | L6 | ## 二、关键 crate → ### 2.1 clap; ## 三、打包与分发 → ### 3.1 单一二进制; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/06_ecosystem/06_data_and_distributed/36_stream_processing_ecosystem.md` | L6 | ## 二、timely-dataflow：Rust 的分布式数据流引擎 → ### 2.1 核心设计; ## 三、differential-dataflow：增量计算的 diff 代数 → ### 3.1 核心抽象; ## 六、Materialize：流式 SQL 数据库 → ### 6.1 架构三层 … and 2 more |
| `concept/06_ecosystem/09_networking/05_formal_network_protocol_theory.md` | L6 | ## 二、协议形式化定义 → ### 2.1 协议三元组; ## 三、状态机模型与验证 → ### 3.1 扩展有限状态机（EFSM）; ## 四、网络演算 → ### 4.1 时间 Petri 网 … and 2 more |
| `concept/06_ecosystem/10_performance/15_performance_optimization.md` | L6 | ## 二、技术细节 → ### 2.1 Criterion：统计性基准测试; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：性能优化的编译错误 → ### 10.1 边界测试：`unsafe` 性能优化的正确性假设（运行时 UB） … and 2 more |
| `concept/06_ecosystem/11_domain_applications/06_blockchain.md` | L6 | ## 一、Rust 在区块链领域的独特优势 → ### 1.1 内存安全 ⟹ 合约无重入/溢出漏洞; ## 二、Rust 链架构对比 → ### 2.1 Solana (Sealevel)：并行合约执行引擎; ## 三、智能合约安全形式化：与 EVM/Solidity 对比 → ### 3.1 漏洞类别消除矩阵 … and 2 more |
| `concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md` | L6 | ## 🌐 WASM 基础术语 → ### WebAssembly (WASM); ## 🦀 Rust 相关术语 → ### wasm32-unknown-unknown; ## 🔗 JavaScript 相关术语 → ### WebAssembly API … and 2 more |
| `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md` | L6 | ## 二、Rust for Linux → ### 2.1 项目背景; ## 三、Ferrocene：安全认证 Rust → ### 3.1 什么是 Ferrocene; ## 四、Android Rust 化 → ### 4.1 Google 的战略决策 … and 2 more |
| `concept/06_ecosystem/00_toolchain/13_logging_observability.md` | L6 | ## 二、技术细节 → ### 2.1 日志级别与过滤; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：日志与可观测性的编译错误 → ### 10.1 边界测试：`tracing` span 的生命周期（编译错误） … and 1 more |
| `concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` | L6 | ## 二、`target.'cfg(..)'.rustdocflags` → ### 2.1 背景; ## 三、弃用（Deprecation）渲染改进 → ### 3.1 变更内容; ## 四、侧边栏导航增强 → ### 4.1 变更内容 … and 1 more |
| `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` | L6 | ## 四、链接原生库 → ### 4.1 使用 `links` 字段; ## 五、常见模式与最佳实践 → ### 5.1 生成代码到 `OUT_DIR`; ## 六、反命题与边界 → ### 6.1 反命题树 … and 1 more |
| `concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md` | L6 | ## 三、发布流程：cargo publish → ### 3.1 准备工作; ## 四、Yank 与 Owner 管理 → ### 4.1 Yank（撤回）; ## 六、私有 Registry 与 Source Replacement → ### 6.1 配置私有 Registry … and 1 more |
| `concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md` | L6 | ## 二、Credential Providers → ### 2.1 内置 Providers; ## 三、Token 的存储与使用 → ### 3.1 `cargo login`; ## 五、Target Dir 与 Build Dir → ### 5.1 `target/` 目录 … and 1 more |
| `concept/06_ecosystem/01_cargo/87_build_std.md` | L6 | ## 为什么需要 build-std → ### 嵌入式场景; ## 使用方法 → ### 1. 安装 nightly 工具链; ## 典型配置示例 → ### 自定义 target JSON … and 1 more |
| `concept/06_ecosystem/04_web_and_networking/38_network_protocols.md` | L6 | ## 一、QUIC：基于 UDP 的安全传输协议 → ### 1.1 QUIC 的设计动机; ## 二、HTTP/3：基于 QUIC 的应用层协议 → ### 2.1 HTTP/3 与 HTTP/2 的对比; ## 三、eBPF：内核可编程与 Rust → ### 3.1 eBPF 的本质 … and 1 more |
| `concept/06_ecosystem/05_systems_and_embedded/17_cross_compilation.md` | L6 | ## 二、技术细节 → ### 2.1 交叉编译工具链; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：交叉编译的编译错误 → ### 10.1 边界测试：目标平台特性缺失（编译错误） … and 1 more |
| `concept/06_ecosystem/05_systems_and_embedded/56_c_to_rust_translation.md` | L6 | ## 三、学术研究前沿 → ### 3.1 Scylla（OOPSLA 2026）; ## 四、现有工具链 → ### 4.1 C2Rust 与后处理生态; ## 四-A、评估基准与近期学术成果 → ### CRUST-Bench：C-to-Safe-Rust 翻译的系统性评估（COLM 2025 Spotlight） … and 1 more |
| `concept/06_ecosystem/07_security_and_cryptography/19_security_practices.md` | L6 | ## 二、技术细节 → ### 2.1 输入验证与清洗; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：安全实践的编译错误 → ### 10.1 边界测试：密码学常量时间操作（运行时风险） … and 1 more |
| `concept/06_ecosystem/08_formal_verification/44_formal_ecosystem_tower.md` | L6 | ## 权威定义 → ### Wikipedia 权威定义; ## 待补充与演进方向（TODOs） → ### 8.1 核心 Crate MSRV 与 Edition 兼容性矩阵; ## 十、边界测试：形式化生态塔的编译错误 → ### 10.1 边界测试：Prusti 的前置条件验证（编译错误） … and 1 more |
| `concept/06_ecosystem/09_networking/02_network_security.md` | L6 | ## 2. 证书管理 → ### 2.1 自签名证书（仅开发与测试）; ## 3. 认证与授权 → ### 3.1 JWT; ## 5. DoS 防护 → ### 5.1 速率限制 … and 1 more |
| `concept/06_ecosystem/09_testing_and_quality/14_documentation.md` | L6 | ## 二、技术细节 → ### 2.1 文档注释语法; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：文档工具的编译错误 → ### 10.1 边界测试：`doctest` 中的隐式 `main`（编译错误） … and 1 more |
| `concept/06_ecosystem/09_testing_and_quality/16_testing.md` | L6 | ## 二、技术细节 → ### 2.1 属性测试（Property-Based Testing）; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：测试的编译错误 → ### 10.1 边界测试：`cargo test` 的编译失败与测试失败的区分 … and 1 more |
| `concept/06_ecosystem/09_testing_and_quality/17_benchmarking.md` | L6 | # 基准测试：Rust 代码性能测量与回归检测 → ## 一、为什么需要基准测试; ## 二、Criterion 基础用法 → ### 2.1 简单基准; ## 三、回归检测与 CI 集成 → ### 3.1 基线对比 … and 1 more |
| `concept/06_ecosystem/11_domain_applications/07_game_ecs.md` | L6 | ## 四、数据导向设计 (DOD) 与 Rust 零成本抽象的协同 → ### 4.1 零成本抽象的 DOD 验证; ## 五、并发渲染：Send/Sync 在多线程游戏循环中的保证 → ### 5.1 多线程渲染管线; ## 十、边界测试：游戏 ECS 的编译错误 → ### 10.1 边界测试：Bevy 的 Query 与组件缺失（编译错误） … and 1 more |
| `concept/06_ecosystem/11_domain_applications/11_webassembly.md` | L6 | ## 二、技术细节 → ### 2.1 wasm32 目标三元组; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：WebAssembly 的编译错误 → ### 10.1 边界测试：`wasm32` 目标的标准库限制（编译错误） … and 1 more |
| `concept/06_ecosystem/11_domain_applications/20_licensing_and_compliance.md` | L6 | ## 二、技术细节 → ### 2.1 许可证合规工具链; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：许可证与合规的编译错误 → ### 10.1 边界测试：`cargo deny` 的许可证冲突（编译错误/构建失败） … and 1 more |
| `concept/06_ecosystem/11_domain_applications/21_game_development.md` | L6 | ## 一、核心架构 → ### 1.1 ECS 设计模式; ## 二、图形渲染 → ### 2.1 WGPU — 跨平台图形; ## 十、边界测试：游戏开发的编译错误 → ### 10.1 边界测试：Bevy 的 Resource 与 System 参数（编译错误） … and 1 more |
| `concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md` | L6 | ## 二、Android AOSP → ### 2.1 AOSP 为什么选择 Rust; ## 三、Chromium → ### 3.1 Chromium 的 Rust 策略; ## 四、Bare Metal → ### 4.1 no_std 与 alloc |
| `concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md` | L6 | ## 四、Lint 与 Lint Pass → ### Lint 定义; ## 六、UI Tests 与 `--bless` → ### UI Test 是什么; ## 嵌入式测验 → ### 测验 1：一条 rustc 诊断至少包含哪三个核心部分？ |
| `concept/06_ecosystem/00_toolchain/71_compiler_testing.md` | L6 | ## 四、Tidy 与 Formatting → ### Tidy; ## 五、工具测试与 Book 文档测试 → ### 工具测试; ## 嵌入式测验 → ### 测验 1：`compiletest` 主要用于测试什么？ |
| `concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md` | L6 | ## 四、特性合并（Feature Unification） → ### 4.1 同一个 crate 在一个主版本内只编译一次; ## 八、Yanked 版本与冲突诊断 → ### 8.1 Yanked 版本; ## 嵌入式测验 → ### 测验 1：`serde = "1.2.3"` 与 `serde = "=1.2.3"` 的区别是什么？ |
| `concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md` | L6 | ## 二、内置 Profile → ### `dev` 默认配置; ## 七、`[lints]` 配置与继承 → ### 包级配置; ## 嵌入式测验 → ### 测验 1：`cargo test` 默认使用哪个 profile？ |
| `concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md` | L6 | ## 二、自定义子命令 → ### 命名约定; ## 三、`cargo metadata` 与 JSON 消息 → ### `cargo metadata`; ## 嵌入式测验 → ### 测验 1：自定义 Cargo 子命令的可执行文件命名规则是什么？ |
| `concept/06_ecosystem/03_design_patterns/32_event_driven_architecture.md` | L6 | ## 五、事件处理器 → ### 5.1 幂等性保证; ## 十、边界测试：事件驱动架构的编译错误 → ### 10.1 边界测试：事件类型的反序列化安全（运行时错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：事件驱动架构（EDA）与请求-响应架构的核心区别是什么？（理解层） |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | L6 | ## 设计模式基础 → ### 设计模式 (Design Pattern); ## Rust 特有概念 → ### Trait 对象; ## 并发与异步 → ### Actor 模式 |
| `concept/06_ecosystem/05_systems_and_embedded/08_wasi.md` | L6 | ## 三、WASI 架构与能力安全 → ### 3.1 WASI 的三层架构; ## 五、Rust `wasm32-wasip1` 或 `wasm32-wasip2` 目标 → ### 5.1 `no_std` + `wasm32` 的约束与模式; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：WASI（WebAssembly System Interface）的核心目标是什么？（理解层） |
| `concept/06_ecosystem/09_networking/04_network_programming_quick_start.md` | L6 | # Rust 网络编程快速入门 → ## 一、30 秒速览; ## 三、推荐学习路径 → ### 路径 1：快速实战（2 小时）; ## 五、基础代码示例 → ### 同步 TCP Echo 服务器 |
| `concept/06_ecosystem/11_domain_applications/26_game_development.md` | L6 | ## 二、渲染与图形 → ### 2.1 wgpu 与跨平台渲染; ## 十、边界测试：游戏开发的编译错误 → ### 10.1 边界测试：ECS 系统的组件借用冲突（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Rust 游戏开发中，`bevy_ecs` 的 archetype-based 存储相比传统 ECS 有什么优势？（理解层） |
| `concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md` | L6 | ## 六、链接与 LTO → ### 6.1 链接; ## 嵌入式测验 → ### 测验 1：`rustc` 默认使用哪个后端生成机器码？ |
| `concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md` | L6 | ## 五、Stable MIR / `rustc_public` → ### 5.1 问题; ## 嵌入式测验 → ### 测验 1：`rustc_driver` 和 `rustc_interface` 的主要区别是什么？ |
| `concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md` | L6 | ## 五、`cfg(bootstrap)` 与 `RUSTC_BOOTSTRAP` → ### `cfg(bootstrap)`; ## 嵌入式测验 → ### 测验 1：日常 rustc 开发通常需要构建到哪个 stage？ |
| `concept/06_ecosystem/01_cargo/10_public_private_deps.md` | L6 | ## 三、传递依赖可见性与 feature 统一 → ### 3.1 传递可见性; ## 七、迁移与实践 → ### 7.1 在现有 workspace 中逐步标注 |
| `concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md` | L6 | ## 四、本地 Registry 与 Directory Source → ### 4.1 Local Registry; ## 嵌入式测验 → ### 测验 1：Source replacement 的核心约束是什么？ |
| `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md` | L6 | ## 七、`[lints]` 与 `[hints]` → ### `[lints]`; ## 嵌入式测验 → ### 测验 1：发布到 crates.io 时，`license` 和 `license-file` 至少需要一个吗？ |
| `concept/06_ecosystem/05_systems_and_embedded/39_os_kernel.md` | L6 | ## 一、Rust for Linux：内核中的 Rust 代码 → ### 1.1 里程碑; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Rust 为什么适合编写操作系统内核？相比 C 有什么优势？（理解层） |
| `concept/06_ecosystem/05_systems_and_embedded/53_embedded_graphics.md` | L6 | ## 七、反命题与边界分析 → ### 7.1 反命题树; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`embedded-graphics` crate 在 Rust 嵌入式显示中提供什么功能？（理解层） |
| `concept/06_ecosystem/06_data_and_distributed/37_database_systems.md` | L6 | ## 二、TiKV：分布式事务与 Percolator 协议 → ### 2.1 Percolator 事务模型; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Rust 中为什么很少使用传统 ORM（如 Django ORM/Hibernate）的"隐式查询"模式？（理解层） |
| `concept/06_ecosystem/11_domain_applications/80_formal_algorithm_theory.md` | L6 | ## 四、正确性证明方法 → ### 4.1 循环不变式; ## 五、Rust 形式化验证实践 → ### 5.1 Kani 有界模型检查 |
| `concept/06_ecosystem/01_cargo/11_resolver_v3_public_feature_unification.md` | L6 | ## 二、关键清单片段 → ### Crate B |
| `concept/06_ecosystem/01_cargo/78_cargo_workspaces.md` | L6 | ## 二、Root Package vs Virtual Workspace → ### Root package |
| `concept/06_ecosystem/01_cargo/82_cargo_guide_practices.md` | L6 | ## 一、依赖管理实践 → ### 添加依赖 |
| `concept/06_ecosystem/01_cargo/83_cargo_configuration.md` | L6 | ## 二、常用配置项 → ### 替换 registry 源 |
| `concept/06_ecosystem/03_design_patterns/82_engineering_and_production_patterns.md` | L6 | ## 二、弹性模式 → ### 2.1 断路器（Circuit Breaker） |
| `concept/06_ecosystem/04_web_and_networking/41_http_client_development.md` | L6 | ## 2. 使用 reqwest → ### 2.1 基础请求 |
| `concept/06_ecosystem/09_networking/01_advanced_network_protocols.md` | L6 | # Rust 高级网络协议概览 → ## 1. 协议分类与适用场景 |
| `concept/06_ecosystem/11_domain_applications/77_data_structures_in_rust.md` | L6 | ## 1. 线性数据结构 → ### 1.1 `Vec<T>` — 动态数组 |
| `concept/06_ecosystem/11_domain_applications/78_algorithm_complexity_analysis.md` | L6 | ## 4. 递归分析 → ### 4.1 主定理（Master Theorem） |
| `concept/06_ecosystem/README.md` | L6 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L6 生态工程层（Ecosystem & Engineering）》在本知识体系中扮演什么角色？（理解层） |
| `concept/05_comparative/01_systems_languages/18_cpp_abi_object_model.md` | L5 | ## 二、ABI（Application Binary Interface）对比 → ### 2.1 什么是 ABI; ## 三、对象模型与内存布局 → ### 3.1 C++ 对象模型; ### 3.1 C++ 对象模型 → #### 3.1.1 简单类（POD） … and 9 more |
| `concept/05_comparative/00_paradigms/03_paradigm_matrix.md` | L5 | ## 一、权威定义 → ### 1.1 Wikipedia 权威定义; ## 七、反命题与边界分析 → ### 7.1 反命题: "Rust 是系统编程的最优解"; ## 八、扩展内容：形式化谱系与更多语言对比 → ### 8.1 编程语言形式化谱系 … and 5 more |
| `concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md` | L5 | ## 权威定义 → ### Wikipedia 权威定义; ## 七、2026 年的关键趋势总结 → ### 7.1 趋势一：AI × 形式方法的"三层闭环"; ## 分支C：AI 范式层（时代性追问） → ### C1：AI + Rust 形式化的具体工作流 … and 5 more |
| `concept/05_comparative/00_paradigms/05_execution_model_isomorphism.md` | L5 | ## 一、权威来源与同构性方法论 → ### 1.1 同构性的定义; ## 十三、思维表征体系 → ### 13.1 执行模型维度雷达图; ## 十四、定理推理链 → ### 定理一致性矩阵（执行模型同构性专集） … and 3 more |
| `concept/05_comparative/02_managed_languages/14_rust_vs_elixir.md` | L5 | ## 二、并发模型 → ### 2.1 BEAM 并发模型; ## 三、类型系统 → ### 3.1 静态 vs 动态; ## 六、反命题与适用场景 → ### 6.1 反命题树 … and 3 more |
| `concept/05_comparative/03_domain_comparisons/17_quiz_rust_vs_systems.md` | L5 | ## 一、内存安全对比 → ### Q1. 以下 C 代码有什么问题？Rust 如何防止同样的问题？; ## 二、并发模型对比 → ### Q3. 以下 C++ 代码存在什么数据竞争？Rust 如何防止？; ## 三、错误处理对比 → ### Q5. 以下 C 代码的错误处理有什么问题？Rust 的 `Result` 如何改进？ … and 3 more |
| `concept/05_comparative/01_systems_languages/02_rust_vs_go.md` | L5 | ## 一、权威定义 → ### 1.1 设计哲学对比; ## 六、反命题与边界分析 → ### 6.1 命题: "Rust 比 Go 更适合所有后端服务"; ## 七、代码示例对比 → ### 7.1 Rust Channel（所有权转移） … and 2 more |
| `concept/05_comparative/02_managed_languages/07_rust_vs_python.md` | L5 | ## 二、技术细节 → ### 2.1 错误处理：Result vs Exception; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 Python 的编译错误对比 → ### 10.1 边界测试：Python 的动态类型 vs Rust 的静态类型（编译错误） … and 2 more |
| `concept/05_comparative/02_managed_languages/11_rust_vs_kotlin.md` | L5 | ## 二、语言特性差异 → ### 2.1 类型推断与泛型; ## 三、工程实践差异 → ### 3.1 构建系统; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/05_comparative/02_managed_languages/12_rust_vs_scala.md` | L5 | ## 二、语言特性差异 → ### 2.1 类型推断; ## 三、工程实践差异 → ### 3.1 构建系统; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/05_comparative/02_managed_languages/13_rust_vs_csharp.md` | L5 | ## 二、语言特性差异 → ### 2.1 模式匹配; ## 三、工程实践差异 → ### 3.1 构建系统; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/05_comparative/02_managed_languages/15_rust_vs_typescript.md` | L5 | ## 二、技术细节 → ### 2.1 类型系统对比矩阵; ## 四、思维导图（Mermaid） → ### 4.1 类型系统哲学对比图; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 2 more |
| `concept/05_comparative/03_domain_comparisons/04_safety_boundaries.md` | L5 | ## 一、权威定义 → ### 1.1 Wikipedia 权威定义; ## 三、边界条件总表 → ### 2.1 内存安全边界; ## 四、失效条件分类学 → ### 3.1 按失效层级分类 … and 2 more |
| `concept/05_comparative/01_systems_languages/09_rust_vs_swift.md` | L5 | ## 二、工程实践差异 → ### 2.1 平台与生态; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 Swift 的编译错误对比 → ### 10.1 边界测试：Swift 的 ARC 与 Rust 的所有权（编译错误） … and 1 more |
| `concept/05_comparative/01_systems_languages/10_rust_vs_zig.md` | L5 | ## 二、工程实践差异 → ### 2.1 构建系统; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 Zig 的编译错误对比 → ### 10.1 边界测试：Zig 的 comptime vs Rust 的 const generics（编译错误） … and 1 more |
| `concept/05_comparative/01_systems_languages/19_rust_vs_ruby.md` | L5 | ## 二、工程实践差异 → ### 2.1 Web 开发生态; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 Ruby 的编译错误对比 → ### 10.1 边界测试：Ruby 的 duck typing vs Rust 的 trait bound（编译错误） … and 1 more |
| `concept/05_comparative/02_managed_languages/06_rust_vs_java.md` | L5 | ## 二、技术细节 → ### 2.1 运行时架构对比; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 Java 的编译错误对比 → ### 10.1 边界测试：Java 的泛型擦除 vs Rust 的单态化（编译错误） … and 1 more |
| `concept/05_comparative/02_managed_languages/08_rust_vs_javascript.md` | L5 | ## 二、技术细节 → ### 2.1 异步模型对比; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Rust 与 JavaScript 的编译错误对比 → ### 10.1 边界测试：JavaScript 的隐式转换 vs Rust 的显式转换（编译错误） … and 1 more |
| `concept/05_comparative/00_paradigms/16_cpp_rust_surface_features.md` | L5 | ## 二、构造与初始化 → ### 2.1 C++：构造函数与初始化列表; ## 五、友元 vs 模块可见性 → ### 5.1 C++ `friend` |
| `concept/05_comparative/README.md` | L5 | ## 四、对比分析的方法论框架 → ### 4.1 对比维度矩阵; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L5 对比分析层（Comparative Analysis）》在本知识体系中扮演什么角色？（理解层） |
| `concept/04_formal/00_type_theory/02_type_theory.md` | L4 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 类型论层次矩阵; ## 七、层次一致性标注（Layer Consistency Annotations） → ### 7.1 L4 → L1 下行映射 … and 6 more |
| `concept/04_formal/03_operational_semantics/20_axiomatic_semantics.md` | L4 | ## 二、概念属性矩阵 → ### 2.1 公理语义方法对比矩阵; ## 三、技术细节 → ### 3.1 Rust 赋值规则的公理化; ## 四、工具链映射 → ### 4.1 Prusti：Viper 后端的契约推导 … and 6 more |
| `concept/04_formal/00_type_theory/21_type_semantics.md` | L4 | ## 二、概念属性矩阵 → ### 2.1 类型语义方法对比矩阵; ## 三、Rust 特有类型的语义 → ### 3.1 借用语义：`&T` 与 `&mut T`; ## 四、子类型与变型的语义解释 → ### 4.1 生命周期子类型 … and 5 more |
| `concept/04_formal/03_operational_semantics/17_operational_semantics.md` | L4 | ## 二、技术细节 → ### 2.1 配置与转换规则; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 五、Rust 语义项目比较矩阵（RustSEM Comparison Matrix） → ### 5.1 引言：为什么没有单一形式化覆盖全部 Rust … and 3 more |
| `concept/04_formal/03_operational_semantics/18_evaluation_strategies.md` | L4 | ## 二、求值策略谱系 → ### 2.1 严格 vs 非严格求值; ## 三、Rust 的求值策略定位 → ### 3.1 默认策略：Call-by-Value + 严格求值; ## 四、Lambda 演算中的归约策略 → ### 4.1 三种归约策略 … and 3 more |
| `concept/04_formal/04_model_checking/05_verification_toolchain.md` | L4 | ## 三、a-mir-formality：Rust 类型系统规范 → ### 3.1 为什么需要类型系统规范？; ### 4.2 场景化 ROI 评估 → #### 场景 A: 安全关键网络协议（如 TLS/QUIC 实现）; ## 五、分层验证策略 → ### 5.1 五层防御模型 … and 3 more |
| `concept/04_formal/04_model_checking/13_formal_methods.md` | L4 | ## 二、关键工具 → ### 2.1 Kani — 模型检查; ## 三、应用模式 → ### 3.1 安全边界验证; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 3 more |
| `concept/04_formal/04_model_checking/23_programming_language_foundations.md` | L4 | ## 二、求值策略（Evaluation Strategy） → ### 2.1 三种基本策略; ## 三、副作用模型（Effect System） → ### 3.1 什么是副作用; ## 四、Continuation 与 CPS → ### 4.1 什么是 Continuation … and 3 more |
| `concept/04_formal/04_model_checking/25_quiz_formal_methods.md` | L4 | ## 一、分离逻辑与所有权 → ### Q1. 分离逻辑（Separation Logic）中，`*`（分离合取）运算符的含义是什么？; ## 二、类型安全与定理 → ### Q3. 以下"定理"（教学类比）描述的是什么性质？; ## 三、验证工具链 → ### Q5. Kani、Miri 和 BorrowSanitizer 的检测能力有何不同？ … and 3 more |
| `concept/04_formal/05_rustc_internals/19_rustc_query_system.md` | L4 | ## 二、查询系统的核心抽象 → ### 2.1 `TyCtxt`; ## 三、依赖图与 Red-Green 算法 → ### 3.1 Dep Graph（依赖图）; # 修改 greet 模块后编译：仅影响依赖该模块的节点 → # Linux/macOS … and 3 more |
| `concept/04_formal/00_type_theory/10_category_theory.md` | L4 | ## 一、核心概念 → ### 1.1 范畴的基本直觉; ## 二、技术细节 → ### 2.1 Option 作为单子; ## 十、边界测试：范畴论视角的编译错误 → ### 10.1 边界测试：`Option` 与 `Result` 的 monad 定律违反（编译错误） … and 2 more |
| `concept/04_formal/01_ownership_logic/03_ownership_formal.md` | L4 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 权威定义; ### 5.2 反命题决策树 → #### 决策树 1: "形式化所有权证明所有程序安全"; ## 九、Polonius：Loan-based 形式化语义 → ### 9.1 从区域到 Loans … and 2 more |
| `concept/04_formal/03_operational_semantics/12_denotational_semantics.md` | L4 | ## 二、Rust 的指称解释 → ### 2.1 类型即域; ## 十、边界测试：指称语义的编译错误 → ### 10.1 边界测试：非终止计算与 `loop {}` 的类型（编译错误）; ## 三、反命题与边界分析 → ### 3.1 反命题树 … and 2 more |
| `concept/04_formal/00_type_theory/06_subtype_variance.md` | L4 | ## 二、技术细节 → ### 2.1 生命周期位置的变型推导; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：子类型变异性的编译错误 → ### 10.1 边界测试：协变与逆变的生命周期误用（编译错误） … and 1 more |
| `concept/04_formal/00_type_theory/08_type_inference.md` | L4 | ## 二、技术细节 → ### 2.1 统一（Unification）; ## 十、边界测试：类型推断的编译错误 → ### 10.1 边界测试：泛型方法链中的类型推断失败（编译错误）; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 1 more |
| `concept/04_formal/00_type_theory/14_lambda_calculus.md` | L4 | ## 二、计算能力 → ### 2.1 Church 编码; ## 三、反命题与边界分析 → ### 3.1 反命题树; ## 十、边界测试：lambda 演算的编译错误 → ### 10.1 边界测试：Y 组合子与递归类型（编译错误） … and 1 more |
| `concept/04_formal/00_type_theory/27_type_checking_and_inference.md` | L4 | ## 三、`typeck` Query 与 `InferCtxt` → ### 3.1 `typeck` query; ## 五、相等约束与子类型约束 → ### 5.1 相等约束; ## 六、区域约束与求解 → ### 6.1 收集约束 … and 1 more |
| `concept/04_formal/01_ownership_logic/01_linear_logic.md` | L4 | ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 结构规则对比矩阵; ## 八、示例与反例 → ### 8.1 Rust 中的线性/仿射对应; ## 十、边界测试：线性逻辑的编译错误 → ### 10.1 边界测试：`!Copy` 类型的隐式移动（编译错误） … and 1 more |
| `concept/04_formal/01_ownership_logic/09_linear_logic_applications.md` | L4 | ## 二、技术细节 → ### 2.1 所有权即线性类型; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：线性逻辑应用的编译错误 → ### 10.1 边界测试：资源线性消耗与 `Drop` 的冲突（编译错误） … and 1 more |
| `concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` | L4 | ## 三、形式化模型（Teaching Analogies） → ### 3.1 区域约束系统（Region Constraints）; ## 四、NLL：数据流分析 + 约束求解 → ### 4.1 数据流方程; ## 六、可判定性与复杂性 → ### 6.1 终止性（Termination） … and 1 more |
| `concept/04_formal/02_separation_logic/11_separation_logic.md` | L4 | ## 二、技术细节 → ### 2.1 分离逻辑的基本断言; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：分离逻辑的编译错误 → ### 10.1 边界测试：独占资源的分割与重组（编译错误） … and 1 more |
| `concept/04_formal/03_operational_semantics/30_aeneas_symbolic_semantics.md` | L4 | ## 三、LLBC：显式借用演算 → ### 3.1 设计思想; ## 四、符号化执行语义 → ### 4.1 符号值与符号状态; ## 六、模拟关系与声音性 → ### 6.1 模拟关系 … and 1 more |
| `concept/04_formal/04_model_checking/31_miri.md` | L4 | ## 三、安装与基本用法 → ### 安装; # 若 Tree Borrows 通过但代码在 Stacked Borrows 下失败， → # 说明代码依赖了更宽松的别名规则；优先修复代码，; # 说明代码依赖了更宽松的别名规则；优先修复代码， → # 除非能证明该模式在官方内存模型中会被接受。 … and 1 more |
| `concept/04_formal/00_type_theory/29_type_inference_complexity.md` | L4 | ## 三、约束生成与 Robinson 合一 → ### 3.1 约束生成（Constraint Generation）; ## 七、复杂度：为什么是 PSPACE → ### 7.1 PSPACE 上界; ## 嵌入式测验 → ### 测验 1：HM 类型推断为什么能保持多项式时间？ |
| `concept/04_formal/02_separation_logic/04_rustbelt.md` | L4 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 权威定义; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：RustBelt 的安全保证范围（理解层）; ## 十一、边界测试：所有权公理的编译错误 → ### 11.1 边界测试：违反唯一所有权（编译错误） |
| `concept/04_formal/04_model_checking/32_kani.md` | L4 | ## 二、安装与基本用法 → ### 安装; ## 三、核心概念 → ### Harness：`#[kani::proof]`; ## 四、可运行示例 → ### 示例 1：简单函数安全证明 |
| `concept/04_formal/05_rustc_internals/35_name_resolution_and_hir.md` | L4 | ## 三、命名空间与作用域 Rib → ### 3.1 命名空间（Namespaces）; ## 七、反命题与边界 → ### 7.1 反命题树; ## 嵌入式测验 → ### 测验 1：`rustc` 的名称解析分为几个阶段？为什么需要分阶段？ |
| `concept/04_formal/05_rustc_internals/41_special_types_and_traits.md` | L4 | ## 二、特殊类型 → ### `Box<T>`; ## 六、`Copy` 与 `Clone` → ### `Copy`; ## 七、`Send` 与 `Sync` → ### `Send` |
| `concept/04_formal/00_type_theory/50_type_system_reference.md` | L4 | ## 📐 知识结构 → ### 概念定义; ## 1. 语法定义 → ### 1.1 核心语法 |
| `concept/04_formal/01_ownership_logic/37_behavior_considered_undefined.md` | L4 | ## 二、UB 清单 → ### 1. 数据竞争（Data races）; ## 三、悬垂指针与未对齐指针细节 → ### 悬垂指针 |
| `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` | L4 | ## 二、核心机制 → ### 2.1 声明安全标签：`#[safety::requires(...)]`; ## 三、为什么需要 Safety Tags？ → ### 3.1 降低 unsafe 代码审计成本 |
| `concept/04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md` | L4 | ## 二、核心机制 → ### 2.1 别名模型基础; ## 四、2026 目标与进展 → ### 4.1 目标 |
| `concept/04_formal/03_operational_semantics/15_hoare_logic.md` | L4 | ## 十、边界测试：Hoare 逻辑的编译错误 → ### 10.1 边界测试：前置条件与后置条件的类型编码（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Hoare 三元组（理解层） |
| `concept/04_formal/04_model_checking/16_aerospace_certification_formal_methods.md` | L4 | ## 十、边界测试：航空航天认证形式化方法的编译错误 → ### 10.1 边界测试：MISRA C 规则的 Rust 类比（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：DO-178C 标准中的 A/B/C/D/E 五个软件等级（DAL）分别对应什么失效条件？（理解层） |
| `concept/04_formal/04_model_checking/22_modern_verification_tools.md` | L4 | ## 快速开始：工具安装与运行 → ### Miri（Rust 官方动态分析器）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`cargo-kani` 与 `cargo-fuzz` 在验证方法上有什么区别？（理解层） |
| `concept/04_formal/04_model_checking/24_autoverus.md` | L4 | ## 二、Verus 核心机制 → ### 2.1 三段式程序结构; ## 三、AutoVerus：LLM 驱动的自动化证明 → ### 3.1 设计原则 |
| `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` | L4 | ## 三、Selection：候选装配与筛选 → ### 3.1 Candidate Assembly（候选装配）; ## 嵌入式测验 → ### 测验 1：什么是 obligation？ |
| `concept/04_formal/README.md` | L4 | ## 三、与上层概念的严格映射 → ### 3.1 映射精度评估; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L4 形式化理论层（Formal Methods）》在本知识体系中扮演什么角色？（理解层） |
| `concept/04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md` | L4 | ## 三、Tree Borrows 核心规则 → ### 3.1 树结构 |
| `concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md` | L4 | ## 嵌入式测验 → ### 测验 1：MIR 与 LLVM IR 的主要区别是什么？ |
| `concept/03_advanced/03_proc_macros/34_syn_quote_reference.md` | L3 | ## 1. syn 库概述 → ### 1.1 核心功能; # 常用 features: → # - "full": 完整 Rust 语法支持; # - "full": 完整 Rust 语法支持 → # - "derive": 仅 DeriveInput … and 12 more |
| `concept/03_advanced/03_proc_macros/35_macro_hygiene.md` | L3 | ## 1. 卫生性基础 → ### 1.1 什么是卫生性; ## 2. 声明宏卫生性 → ### 2.1 局部变量; ## 3. 过程宏 Span → ### 3.1 call_site() … and 12 more |
| `concept/03_advanced/00_concurrency/01_concurrency.md` | L3 | ## 一、权威定义（Definition） [Rust 并发基于所有权系统——每个值有唯一所有者（单一所有权，资源唯一性），所有权通过 move/转移在线程间传递（赋值、传参），owner 离开作用域时自动 drop/释放](../../00_meta/00_framework/methodology.md) → ### 1.1 Wikipedia 权威定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 Send/Sync 判定矩阵; ## 五、决策/边界判定树（Decision / Boundary Tree） → ### 5.1 "共享状态 vs 消息传递？" 决策树 … and 10 more |
| `concept/03_advanced/00_concurrency/10_concurrency_patterns.md` | L3 | ## 二、技术细节 → ### 2.1 通道模式; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验 → ### 测验 1：并发模式识别（记忆层） … and 7 more |
| `concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md` | L3 | ## 二、并行/分布式模式的统一谱系 → ### 2.1 谱系总览; ## 三、L1 单机共享内存模式 → ### 3.1 线程池模式; ## 四、L2 单机消息传递模式 → ### 4.1 Actor 模型 … and 7 more |
| `concept/03_advanced/02_unsafe/03_unsafe.md` | L3 | ## 十一、待补充与演进方向（TODOs） → ### 补充章节：FFI 与 repr 属性完整规范; # CI 集成（GitHub Actions 示例） → # .github/workflows/miri.yml; # .github/workflows/miri.yml → # - run: rustup toolchain install nightly --component miri … and 7 more |
| `concept/03_advanced/06_low_level_patterns/20_stream_processing_semantics.md` | L3 | ## 二、时间域：事件时间 vs 处理时间 vs 摄取时间 → ### 2.1 三种时间语义; ## 四、Watermark：事件时间进度的推断机制 → ### 4.1 Watermark 的形式化定义; ## 六、容错语义：Exactly-Once 的形式化 → ### 6.1 三种处理保证 … and 7 more |
| `concept/03_advanced/01_async/39_future_and_executor_mechanisms.md` | L3 | ## 📐 知识结构 → ### 概念定义; ## 1. Future Trait 详解 → ### 1.1 Future 的定义; ## 2. Poll 与 Waker 机制 → ### 2.1 完整执行流程 … and 6 more |
| `concept/03_advanced/03_proc_macros/04_macros.md` | L3 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 权威定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 宏类型对比矩阵; ## 七、示例与反例（Examples & Counter-examples） → ### 7.1 正确示例：`macro_rules!` 声明宏 … and 3 more |
| `concept/03_advanced/03_proc_macros/32_macro_glossary.md` | L3 | ## 🎨 宏类型术语 → ### Macro (宏); ## 🔧 声明宏术语 → ### macro_rules; ## ⚙️ 过程宏术语 → ### TokenStream … and 3 more |
| `concept/03_advanced/03_proc_macros/33_macro_faq.md` | L3 | ## 🎨 宏基础问题 → ### Q1: 声明宏 vs. 过程宏，何时使用哪个？; ## 🔧 声明宏问题 → ### Q4: 如何调试声明宏？; ## ⚙️ 过程宏问题 → ### Q7: 如何开始写第一个过程宏？ … and 3 more |
| `concept/03_advanced/06_low_level_patterns/18_network_programming.md` | L3 | ## 一、权威定义与核心概念 → ### 1.1 异步网络 IO 模型; ## 十、边界测试：网络编程的编译错误 → ### 10.1 边界测试：`TcpStream` 的 `move` 与分裂（编译错误）; ## 二、技术细节 → ### 2.1 Tokio TCP 服务端实现 … and 3 more |
| `concept/03_advanced/07_unsafe_internals/37_unsafe_collections_internals.md` | L3 | ## 三、技术细节与示例 → ### 3.1 Vec 的核心结构; ## 四、示例与反例 → ### 4.1 正确示例：手动实现 Vec 的 pop; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md` | L3 | ## 二、技术细节 → ### 2.1 原子操作详解; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验 → ### 测验 1：原子操作基础（记忆层） … and 2 more |
| `concept/03_advanced/01_async/24_async_closures.md` | L3 | ## 2. 语法与捕获语义 → ### 2.1 基础语法; ## 4. 实际应用模式 → ### 4.1 事件处理器; ## 5. 限制与边界 → ### 5.1 不是 dyn-compatible … and 2 more |
| `concept/03_advanced/01_async/26_async_patterns.md` | L3 | ## 一、核心概念 → ### 1.1 Future 与状态机; ## 二、技术细节 → ### 2.1 并发执行模式; ## 十、边界测试：异步模式的编译错误 → ### 10.1 边界测试：`Stream` 与 `Future` 的所有权混淆（编译错误） … and 2 more |
| `concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md` | L3 | ## 1. 进程定义与模型 → ### 1.1 进程理论基础; ## 2. 生命周期管理 → ### 2.1 进程状态机; ## 3. 进程属性与资源控制 → ### 3.1 基础属性配置 … and 2 more |
| `concept/03_advanced/02_unsafe/22_quiz_unsafe.md` | L3 | ## 一、Unsafe 基础语义 → ### Q1. 以下代码能否编译？`unsafe` 关键字的作用是什么？; ## 二、原始指针与内存安全 → ### Q3. 以下代码能否编译？存在什么风险？; ## 三、Unsafe Trait 与 FFI → ### Q5. 以下代码能否编译？解释 `Sync` 和 `Send` 的 `unsafe impl` … and 2 more |
| `concept/03_advanced/03_proc_macros/23_quiz_macros.md` | L3 | ## 一、声明宏基础 → ### Q1. 以下宏调用 `vec![1, 2, 3]` 展开后近似于什么代码？; ## 二、过程宏 → ### Q4. 以下代码的输出是什么？解释 `derive` 宏的工作原理; ## 三、宏的高级技巧 → ### Q6. 以下代码能否编译？`tt` 和 `expr` 的区别是什么？ … and 2 more |
| `concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md` | L3 | ## 二、版本兼容性 → ### 2.1 MSRV 管理; ## 三、错误诊断最佳实践 → ### 3.1 保留原始 Span; ## 四、文档生成 → ### 4.1 完整示例 … and 2 more |
| `concept/03_advanced/05_inline_assembly/13_inline_assembly.md` | L3 | ## 一、核心概念 → ### 1.1 为什么需要内联汇编; ## 二、平台差异矩阵 → ### 2.1 x86_64; ## 三、s390x 向量寄存器 (Rust 1.96+) → ### 3.1 背景：IBM Z 向量扩展 … and 2 more |
| `concept/03_advanced/06_low_level_patterns/14_custom_allocators.md` | L3 | ## 二、实践模式 → ### 2.1 bumpalo — Bump 分配器; ## 三、内存布局与对齐 → ### 3.1 Layout; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/03_advanced/06_low_level_patterns/15_zero_copy_parsing.md` | L3 | ## 二、关键技术 → ### 2.1 bytes crate; ## 三、序列化优化 → ### 3.1 rkyv; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/03_advanced/06_low_level_patterns/17_type_erasure.md` | L3 | ## 二、类型擦除模式 → ### 2.1 Box<dyn Trait>; ## 三、性能权衡 → ### 3.1 静态 vs 动态分发; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/03_advanced/00_concurrency/16_lock_free.md` | L3 | ## 二、关键数据结构 → ### 2.1 Treiber Stack; ## 三、Rust 无锁生态 → ### 3.1 crossbeam; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 1 more |
| `concept/03_advanced/00_concurrency/21_quiz_concurrency_async.md` | L3 | ## 一、并发基础：Send 与 Sync → ### Q1. 以下代码能否编译？解释 `Send` 和 `Sync` 的语义; ## 二、异步编程 → ### Q4. 以下代码的输出是什么？解释 `.await` 的作用; ## 三、综合应用 → ### Q7. 以下代码的输出是什么？解释 `join!` 与顺序 await 的区别 … and 1 more |
| `concept/03_advanced/01_async/02_async.md` | L3 | ## 十五、Stream trait 与流处理语义 → ### 15.1 Stream = 异步 Iterator; ## 十六、边界测试：异步规则的编译错误 → ### 16.1 边界测试：非 Send 类型跨 await 点（编译错误）; ## 嵌入式测验 → ### 测验 1：async fn 的本质（记忆层） … and 1 more |
| `concept/03_advanced/02_process_ipc/07_process_security_and_sandboxing.md` | L3 | ## 2. 权限最小化 → ### 2.1 用户/组降级; ## 3. 资源限制 → ### 3.1 rlimit; ## 4. 隔离机制 → ### 4.1 Linux Namespaces … and 1 more |
| `concept/03_advanced/03_proc_macros/07_proc_macro.md` | L3 | ## 一、核心概念 → ### 1.1 过程宏 vs macro_rules; ## 二、技术细节 → ### 2.1 TokenStream 操作; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 1 more |
| `concept/03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md` | L3 | ## 二、生成代码质量 → ### 2.1 可读性与文档; ## 三、编译时间优化 → ### 3.1 避免宏递归爆炸; ## 四、代码膨胀控制 → ### 4.1 静态 vs 动态分发 … and 1 more |
| `concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md` | L3 | ## 二、使用 cargo expand → ### 2.1 安装与基础用法; ## 三、在宏中打印诊断信息 → ### 3.1 过程宏中的 stderr 输出; ## 四、精确错误定位 → ### 4.1 使用 syn::Error … and 1 more |
| `concept/03_advanced/04_ffi/09_ffi_advanced.md` | L3 | ## 二、技术细节 → ### 2.1 复杂类型映射; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：高级 FFI 的编译错误 → ### 10.1 边界测试：可变静态变量在 FFI 中的线程安全（编译错误） … and 1 more |
| `concept/03_advanced/01_async/06_pin_unpin.md` | L3 | ## 二、技术细节 → ### 2.1 Pin API 的契约; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验 → ### 测验 1：Pin 的设计动机（记忆层） |
| `concept/03_advanced/02_unsafe/08_nll_and_polonius.md` | L3 | ## 二、技术细节 → ### 2.1 NLL 的实现机制; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：词法生命周期的问题（理解层） |
| `concept/03_advanced/04_ffi/05_rust_ffi.md` | L3 | ## 二、技术细节 → ### 2.1 extern 块的完整语法; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验 → ### 测验 1：FFI 边界安全性（记忆层） |
| `concept/03_advanced/01_async/25_async_advanced.md` | L3 | ## 十、边界测试：高级异步模式的编译错误 → ### 10.1 边界测试：`select!` 宏中分支完成后的变量使用（编译错误）; ## 嵌入式测验 → ### 测验 1：async fn in trait（记忆层） |
| `concept/03_advanced/02_process_ipc/06_process_monitoring_and_diagnostics.md` | L3 | ## 2. 状态监控 → ### 2.1 存活检查; ## 3. 资源监控 → ### 3.1 使用 `sysinfo` |
| `concept/03_advanced/02_unsafe/00_before_formal.md` | L3 | ## 推荐阅读顺序（按目标） → ### 目标：通过面试 / 写更好的代码; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：为什么 Rust 的形式化不是写 Rust 的必要条件？（理解层） |
| `concept/03_advanced/03_proc_macros/28_conditional_compilation.md` | L3 | ## 二、配置谓词 → ### 基本形式; ## 三、编译器内置配置选项 → ### 目标架构 |
| `concept/03_advanced/02_process_ipc/02_advanced_process_management.md` | L3 | ## 4. 资源限制与配额管理 → ### 4.1 进程级资源限制 |
| `concept/03_advanced/02_process_ipc/03_async_process_management.md` | L3 | ## 3. 异步生命周期管理 → ### 3.1 超时控制 |
| `concept/03_advanced/02_process_ipc/04_cross_platform_process_management.md` | L3 | ## 补充视角：跨平台命令抽象与测试策略 → ### 跨平台 Shell 抽象 |
| `concept/03_advanced/02_process_ipc/08_process_performance_engineering.md` | L3 | ## 4. 优化策略 → ### 4.1 减少进程创建开销 |
| `concept/03_advanced/02_process_ipc/09_process_testing_and_benchmarking.md` | L3 | ## 3. 进程测试技巧 → ### 3.1 超时保护 |
| `concept/03_advanced/02_unsafe/29_memory_model.md` | L3 | ## 九、常见内存模型反模式 → ### 9.1 读取未初始化 padding |
| `concept/03_advanced/04_ffi/27_linkage.md` | L3 | ## 二、Crate 类型 → ### `bin` — 可执行文件 |
| `concept/03_advanced/06_low_level_patterns/34_visibility_and_privacy.md` | L3 | ## 三、访问规则 → ### 1. Public item |
| `concept/03_advanced/README.md` | L3 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L3 高级概念层（Advanced）》在本知识体系中扮演什么角色？（理解层） |
| `concept/02_intermediate/01_generics/02_generics.md` | L2 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 对齐定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 泛型参数类型矩阵; ## 四、定理推理链（Theorem Chain） → ### 4.1 引理：参数多态 ⟹ System F 类型规则 … and 12 more |
| `concept/02_intermediate/00_traits/39_dispatch_mechanisms.md` | L2 | ## 📐 知识结构 → ### 概念定义; ## 1. 分派机制基础 → ### 1.1 什么是分派; ## 2. 静态分发 → ### 2.1 单态化 … and 10 more |
| `concept/02_intermediate/00_traits/01_traits.md` | L2 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 对齐定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 Trait 类型分类矩阵; ## 五、示例与反例（Examples & Counter-examples） → ### 5.1 正确示例：Trait 定义与实现 … and 5 more |
| `concept/02_intermediate/03_error_handling/04_error_handling.md` | L2 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 对齐定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 错误处理机制矩阵; ## 四、定理推理链（Theorem Chain） → ### 4.1 引理：Result<T,E> ⟹ 和类型强制错误处理 … and 5 more |
| `concept/02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md` | L2 | ## 一、RTTI 与动态类型识别 → ### 问题 1：C++ `dynamic_cast` 和 Rust `Any::downcast_ref` 的核心语义差异是什么？; ## 二、C 预处理器 vs Rust 宏 → ### 问题 2：C 预处理器 `#define SQUARE(x) ((x) * (x))` 与 Rust `macro_rules! square { ($x:expr) => { $x * $x } }` 的本质区别是什么？; ## 三、异常安全 → ### 问题 3：C++ 析构函数中抛出异常会发生什么？ … and 5 more |
| `concept/02_intermediate/01_generics/39_type_level_programming.md` | L2 | ## 1️⃣ 类型级自然数 (Peano Numbers) → ### 基础定义; ## 2️⃣ 类型级布尔逻辑 → ### 布尔类型; ## 3️⃣ 类型级列表 → ### HList (Heterogeneous List) … and 4 more |
| `concept/02_intermediate/02_memory_management/03_memory_management.md` | L2 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 对齐定义; ## 四、定理推理链（Theorem Chain） → ### 4.1 引理：Box<T> ⟹ 堆分配 + 唯一所有权; ## 五、示例与反例（Examples & Counter-examples） → ### 5.1 正确示例：Box 堆分配 … and 4 more |
| `concept/02_intermediate/04_types_and_conversions/06_range_types.md` | L2 | ## 一、核心概念 → ### 1.1 范围类型的数学语义; ## 二、形式化语义 → ### 2.1 `Copy` 的语义影响; ## 三、跨语言对比 → ### 3.1 Python：`range()` 函数 … and 4 more |
| `concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md` | L2 | ## 二、技术细节 → ### 2.1 impl Trait 在参数位置; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 七、C++ 运算符重载/类型转换 vs Rust Trait 系统 → ### 7.1 运算符重载机制对比 … and 4 more |
| `concept/02_intermediate/02_memory_management/24_quiz_memory_management.md` | L2 | ## 一、Box 与堆分配 → ### Q1. 以下代码能否编译？`Box::new` 与栈分配的区别是什么？; ## 二、Rc 与 Arc → ### Q3. 以下代码能否编译？`Rc` 和 `Arc` 的区别是什么？; ## 三、内部可变性模式 → ### Q5. 以下代码能否编译？`Cell<T>` 与 `RefCell<T>` 的区别是什么？ … and 3 more |
| `concept/02_intermediate/04_types_and_conversions/35_unions.md` | L2 | ## 三、技术细节与示例 → ### 3.1 基本用法; ## 四、示例与反例 → ### 4.1 正确示例：与 C 结构体互操作; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/02_intermediate/04_types_and_conversions/37_type_conversions.md` | L2 | ## 三、技术细节与示例 → ### 3.1 隐式强制（Coercion）; ## 四、示例与反例 → ### 4.1 正确示例：自定义错误类型; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md` | L2 | ## 二、构造函数 → ### 2.1 `new`; ## 三、谓词与查询 → ### 3.1 `is_`; ## 四、可变访问 → ### 4.1 `mut_` … and 3 more |
| `concept/02_intermediate/06_macros_and_metaprogramming/36_attributes_by_category.md` | L2 | ## 三、技术细节与示例 → ### 3.1 代码生成属性; ## 四、示例与反例 → ### 4.1 正确示例：组合使用属性; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/02_intermediate/01_generics/23_quiz_traits_and_generics.md` | L2 | ## 一、Trait 基础 → ### Q1. 以下代码能否编译？若不能，为什么？; ## 二、泛型与单态化 → ### Q4. 以下代码能否编译？`Option<T>` 和 `Result<T, E>` 的本质是什么？; ## 三、Trait 对象与动态分发 → ### Q6. 以下代码能否编译？`&dyn Drawable` 和 `impl Drawable` 的区别是什么？ … and 2 more |
| `concept/02_intermediate/06_macros_and_metaprogramming/05_assert_matches.md` | L2 | ## 二、形式化语义 → ### 2.1 与 `assert!` / `assert_eq!` 的对比; ## 三、使用场景与最佳实践 → ### 3.1 测试中的 Result/Option 断言; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/02_intermediate/07_iterators_and_closures/15_iterator_patterns.md` | L2 | ## 一、核心概念 → ### 1.1 Iterator Trait; ## 二、常用模式 → ### 2.1 map-filter-collect; ## 十、边界测试：迭代器模式的编译错误 → ### 10.1 边界测试：`Iterator::collect` 的目标类型歧义（编译错误） … and 2 more |
| `concept/02_intermediate/00_traits/09_serde_patterns.md` | L2 | ## 二、技术细节 → ### 2.1 Derive 宏的展开逻辑; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Serde 模式的编译错误 → ### 10.1 边界测试：反序列化时字段缺失（运行时错误） … and 1 more |
| `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` | L2 | ## 二、技术细节 → ### 2.1 HRTB 的实际应用; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：高级生命周期的编译错误 → ### 10.1 边界测试：自引用结构体与 `Pin`（编译错误） … and 1 more |
| `concept/02_intermediate/00_traits/19_advanced_traits.md` | L2 | ## 二、技术细节 → ### 2.1 关联类型 vs 泛型参数; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：高级 Trait 的编译错误 → ### 10.1 边界测试：关联类型与泛型参数冲突（编译错误） … and 1 more |
| `concept/02_intermediate/00_traits/31_derive_traits.md` | L2 | ## 二、标准库可派生 Trait 一览 → ### `Debug` — 调试输出; ### `PartialEq` / `Eq` — 相等性比较 → #### `PartialEq`; ### `PartialOrd` / `Ord` — 顺序比较 → #### `PartialOrd` … and 1 more |
| `concept/02_intermediate/02_memory_management/08_interior_mutability.md` | L2 | ## 一、核心概念 → ### 1.1 外部可变性与内部可变性的对比; ## 二、技术细节 → ### 2.1 `Cell<T>`：无借用语义的复制; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 1 more |
| `concept/02_intermediate/02_memory_management/11_cow_and_borrowed.md` | L2 | ## 二、技术细节 → ### 2.1 Cow 的核心操作; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Cow 与借用的编译错误 → ### 10.1 边界测试：`Cow` 的写时复制与借用冲突（编译错误） … and 1 more |
| `concept/02_intermediate/02_memory_management/12_smart_pointers.md` | L2 | ## 一、核心概念 → ### 1.1 智能指针谱系; ## 二、技术细节 → ### 2.1 RefCell 与 Cell：内部可变性; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 1 more |
| `concept/02_intermediate/03_error_handling/16_error_handling_deep_dive.md` | L2 | ## 二、技术细节 → ### 2.1 错误转换与 From Trait; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：错误处理的编译错误 → ### 10.1 边界测试：`thiserror` 与 `anyhow` 的混用（编译错误） … and 1 more |
| `concept/02_intermediate/04_types_and_conversions/07_closure_types.md` | L2 | ## 二、技术细节 → ### 2.1 编译器自动推导规则; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：闭包类型的编译错误 → ### 10.1 边界测试：闭包类型推断与 `fn` 指针的不兼容（编译错误） … and 1 more |
| `concept/02_intermediate/04_types_and_conversions/14_newtype_and_wrapper.md` | L2 | ## 二、技术细节 → ### 2.1 Deref 与自动解引用; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：Newtype 与包装器的编译错误 → ### 10.1 边界测试：Newtype 不继承原类型的 trait（编译错误） … and 1 more |
| `concept/02_intermediate/05_modules_and_visibility/10_module_system.md` | L2 | ## 二、技术细节 → ### 2.1 use 声明与路径解析; ## 三、反命题与边界分析 → ### 3.1 反命题树; ## 十、边界测试：模块系统的编译错误 → ### 10.1 边界测试：`pub(crate)` 与 `pub(super)` 的可见性层级（编译错误） … and 1 more |
| `concept/02_intermediate/06_macros_and_metaprogramming/13_dsl_and_embedding.md` | L2 | ## 二、技术细节 → ### 2.1 Parser Combinators; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：DSL 与嵌入的编译错误 → ### 10.1 边界测试：构建器模式的链式调用与所有权（编译错误） … and 1 more |
| `concept/02_intermediate/06_macros_and_metaprogramming/17_macro_patterns.md` | L2 | ## 二、技术细节 → ### 2.1 DRY 代码生成; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：宏模式的编译错误 → ### 10.1 边界测试：`macro_rules!` 的优先级与贪婪匹配（编译错误） … and 1 more |
| `concept/02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md` | L2 | ## 二、C++ 的 RTTI 机制 → ### 2.1 `typeid`：获取类型信息; ## 三、Rust 的动态类型识别 → ### 3.1 `Any` trait：显式的运行时类型擦除; ## 五、Rust 中的典型用例 → ### 5.1 错误类型的动态擦除 |
| `concept/02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md` | L2 | ## 二、C++ 的 `friend` 机制 → ### 2.1 基本用法; ## 三、Rust 的模块可见性 → ### 3.1 可见性修饰符; ## 五、Rust 中模拟 `friend` 的场景 → ### 5.1 同一 crate 内的亲密协作 |
| `concept/02_intermediate/06_macros_and_metaprogramming/21_metaprogramming.md` | L2 | ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十、边界测试：元编程的编译错误 → ### 10.1 边界测试：过程宏的 TokenStream 解析失败（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：`macro_rules!` 与过程宏（proc macro）在元编程中的根本区别是什么？（理解层） |
| `concept/02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md` | L2 | ## 二、C 预处理器：文本替换模型 → ### 2.1 `#define`：简单文本替换; ## 三、Rust 宏：语法树与卫生性 → ### 3.1 声明宏 `macro_rules!`; ## 五、迁移思维 → ### 5.1 什么时候用 `macro_rules!` 替代 `#define` |
| `concept/02_intermediate/00_traits/28_construction_and_initialization.md` | L2 | ## 二、C++ 的构造体系 → ### 2.1 构造函数与初始化列表; ## 三、Rust 的初始化模型 → ### 3.1 结构体字面量 |
| `concept/02_intermediate/00_traits/32_editions.md` | L2 | # 4. 更新 Cargo.toml 中的 edition 字段 → # edition = "2024"; # edition = "2024" → # 5. 重新编译并检查测试 |
| `concept/02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md` | L2 | ## 二、C++ 的异常保证体系 → ### 2.1 三种异常保证; ## 三、Rust 的错误处理模型 → ### 3.1 可恢复错误：`Result<T, E>` |
| `concept/02_intermediate/README.md` | L2 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L2 进阶概念层（Intermediate）》在本知识体系中扮演什么角色？（理解层） |
| `concept/01_foundation/04_control_flow/07_control_flow.md` | L1 | ## 一、核心概念 → ### 1.1 表达式 vs 语句; ## 二、技术细节 → ### 2.1 loop 与值返回; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 7 more |
| `concept/01_foundation/00_start/21_effects_and_purity.md` | L1 | ## 二、引用透明（Referential Transparency） → ### 2.1 定义; ## 三、副作用的分类与模型 → ### 3.1 副作用的通用分类; ## 四、Rust 的副作用控制机制 → ### 4.1 `&mut T` 作为写效果（Write Effect） … and 5 more |
| `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | L1 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 核心规则矩阵; ## 三、形式化理论根基（Formal Foundation） → ### 3.1 线性逻辑（Linear Logic） … and 5 more |
| `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | L1 | ## 一、权威定义（Definition） → ### 1.1 TRPL 官方定义; ## 二、概念属性矩阵（Attribute Matrix） → ### 2.1 借用类型核心矩阵; ## 三、形式化理论根基（Formal Foundation） → ### 3.1 分离逻辑（Separation Logic）视角 … and 5 more |
| `concept/01_foundation/02_type_system/04_type_system.md` | L1 | ## 一、权威定义（Definition） → ### 1.1 Wikipedia 定义; ## 权威来源索引 → ## 十二、边界测试：类型系统的编译错误; ## 十二、边界测试：类型系统的编译错误 → ### 12.1 边界测试：类型不匹配（编译错误） … and 5 more |
| `concept/01_foundation/03_values_and_references/20_variable_model.md` | L1 | ## 二、通用 PL 视角：变量的两种经典模型 → ### 2.1 环境模型（Environment Model）; ## 三、值类别（Value Categories）：从 C++ 到 Rust → ### 3.1 C++ 的值类别体系; ## 四、值语义 vs 引用语义 → ### 4.1 通用 PL 谱系 … and 5 more |
| `concept/01_foundation/02_type_system/31_never_type.md` | L1 | ## 一、核心概念 → ### 1.1 什么是 `!`; ## 二、控制流应用 → ### 2.1 发散函数; ## 三、穷尽性检查 → ### 3.1 Match 臂完备性 … and 4 more |
| `concept/01_foundation/00_start/34_pl_prerequisites.md` | L1 | ## 一、求值策略（Evaluation Strategies） → ### 1.1 为什么需要了解求值策略？; ## 二、副作用模型（Side Effects Model） → ### 2.1 什么是副作用？; ## 三、变量模型：环境 vs 存储 → ### 3.1 两个层面的变量 … and 3 more |
| `concept/01_foundation/00_start/47_std_io_and_process.md` | L1 | ## 三、技术细节与示例 → ### 3.1 标准输入输出; ## 四、示例与反例 → ### 4.1 正确示例：安全复制文件; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/01_foundation/02_type_system/22_data_abstraction_spectrum.md` | L1 | ## 二、数据抽象的六层谱系 → ### 2.1 第一层：内存布局抽象（C struct）; ## 三、关键对比：C++ 继承 vs Rust trait → ### 3.1 开放/封闭原则的差异; ## 四、代数数据类型的工程价值 → ### 4.1 消除空指针：Option<T> 替代 nullable … and 3 more |
| `concept/01_foundation/03_values_and_references/05_reference_semantics.md` | L1 | ## 一、核心概念 → ### 1.1 引用的多重含义; ## 二、技术细节 → ### 2.1 方法调用的自动引用; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 3 more |
| `concept/01_foundation/05_collections/17_collections_advanced.md` | L1 | ## 一、权威定义与核心概念 → ### 1.1 BTreeMap/BTreeSet：有序关联容器; ## 二、内存布局与性能特征 → ### 2.1 BTreeMap 节点布局; ## 四、思维导图（Mermaid） → ### 4.1 集合选型决策树 … and 3 more |
| `concept/01_foundation/06_strings_and_text/46_formatting_and_display.md` | L1 | ## 三、技术细节与示例 → ### 3.1 `Display` 与 `Debug`; ## 四、示例与反例 → ### 4.1 正确示例：错误类型实现 Display; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/01_foundation/07_modules_and_items/43_type_aliases.md` | L1 | ## 三、技术细节与示例 → ### 3.1 基本用法; ## 四、示例与反例 → ### 4.1 正确示例：简化复杂类型; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/01_foundation/07_modules_and_items/44_static_items.md` | L1 | ## 三、技术细节与示例 → ### 3.1 不可变静态项; ## 四、示例与反例 → ### 4.1 正确示例：全局配置常量; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/01_foundation/07_modules_and_items/45_const_items_and_const_fn.md` | L1 | ## 三、技术细节与示例 → ### 3.1 常量项; ## 四、示例与反例 → ### 4.1 正确示例：编译期配置计算; ## 五、反命题与边界分析 → ### 5.1 反命题树 … and 3 more |
| `concept/01_foundation/08_error_handling/32_error_handling_basics.md` | L1 | ## 一、核心概念 → ### 1.1 Result 类型; ## 二、错误转换与组合 → ### 2.1 From trait; ## 三、Panic 与不可恢复错误 → ### 3.1 panic! 宏 … and 3 more |
| `concept/01_foundation/11_quizzes/25_quiz_error_handling.md` | L1 | ## 一、Result 与 Option → ### Q1. 以下代码的输出是什么？; ## 二、Option 组合子 → ### Q4. 以下代码的输出是什么？; ## 三、Panic 与不可恢复错误 → ### Q6. 以下代码能否编译？`panic!` 与 `Result` 的区别是什么？ … and 3 more |
| `concept/01_foundation/11_quizzes/29_quiz_pl_foundations.md` | L1 | ## 一、变量模型 → ### 问题 1：在通用 PL 的"环境-存储"模型中，Rust 的所有权系统主要约束的是哪一层？; ## 二、求值策略 → ### 问题 2：Rust 默认使用哪种求值策略？`&T` 和 `&mut T` 在求值策略上分别对应什么？; ## 三、副作用与纯度 → ### 问题 3：在 Rust 中，`&mut T` 可以被建模为什么样的效果？ … and 3 more |
| `concept/01_foundation/00_start/06_zero_cost_abstractions.md` | L1 | ## 一、核心概念 → ### 1.1 零成本抽象的定义; ## 二、技术细节 → ### 2.1 编译期优化管道; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/00_start/15_closure_basics.md` | L1 | ## 一、核心概念 → ### 1.1 闭包的语法与捕获; ## 二、技术细节 → ### 2.1 闭包作为函数参数; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/02_type_system/10_numerics.md` | L1 | ## 一、核心概念 → ### 1.1 整数类型全景; ## 二、技术细节 → ### 2.1 类型转换与 as; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/02_type_system/14_coercion_and_casting.md` | L1 | ## 一、核心概念 → ### 1.1 强制（Coercion）与转换（Cast）的区别; ## 二、技术细节 → ### 2.1 as 转换的完整矩阵; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/07_modules_and_items/11_modules_and_paths.md` | L1 | ## 一、核心概念 → ### 1.1 模块层次结构; ## 二、技术细节 → ### 2.1 文件系统映射; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/08_error_handling/13_panic_and_abort.md` | L1 | ## 一、核心概念 → ### 1.1 Panic 的语义; ## 二、技术细节 → ### 2.1 自定义 Panic 处理; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/09_macros_basics/12_attributes_and_macros.md` | L1 | ## 一、核心概念 → ### 1.1 属性系统全景; ## 二、技术细节 → ### 2.1 模式匹配与重复; ## 四、反命题与边界分析 → ### 4.1 反命题树 … and 2 more |
| `concept/01_foundation/11_quizzes/24_quiz_type_system.md` | L1 | ## 一、标量与复合类型 → ### Q1. 以下代码的输出是什么？; ## 二、枚举与模式匹配 → ### Q4. 以下代码的输出是什么？; ## 三、类型转换与强制 → ### Q7. 以下代码能否编译？ … and 2 more |
| `concept/01_foundation/11_quizzes/26_quiz_modules_testing.md` | L1 | ## 一、模块系统 → ### Q1. 以下代码能否编译？解释 `mod`、`use` 和 `pub` 的关系; ## 二、单元测试与集成测试 → ### Q4. 以下测试代码的输出是什么？`#[cfg(test)]` 的作用是什么？; ## 三、工作区与 crate 结构 → ### Q7. 以下项目结构中，`crate`、`package` 和 `module` 的关系是什么？ … and 2 more |
| `concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md` | L1 | ## 一、闭包基础 → ### Q1. 以下代码能否编译？解释闭包的类型推断; ## 二、迭代器基础 → ### Q4. 以下代码的输出是什么？解释迭代器的惰性求值; ## 三、迭代器适配器 → ### Q6. 以下代码的输出是什么？解释 `filter`、`map` 和 `collect` 的组合 … and 2 more |
| `concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md` | L1 | ## 一、所有权规则 → ### Q1. 以下代码能否编译？若不能，原因是什么？; ## 二、借用规则 → ### Q4. 以下代码能否编译？若不能，原因是什么？; ## 三、生命周期基础 → ### Q7. 以下代码中，`result` 的生命周期由谁决定？ … and 2 more |
| `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` | L1 | ## 二、核心层知识图谱 → ### 2.1 所有权系统; ## 四、概念关系矩阵 → ### 核心概念相互依赖; ## 五、学习路径 → ### 初学者路径（0–3 个月） … and 1 more |
| `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | L1 | ## 一、权威定义（Definition） → ### 1.1 TRPL 官方定义; ## 八、边界测试：生命周期规则的编译错误 → ### 8.1 边界测试：生命周期标注缺失（编译错误）; ## 九、认知路径（Cognitive Path） → ### 10.5 边界测试：生命周期省略规则的三条规则（编译错误） … and 1 more |
| `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` | L1 | ## 二、技术细节 → ### 2.1 字符串切片与索引; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十二、边界测试：字符串与文本的编译错误 → ### 12.1 边界测试：`String` 与 `&str` 的生命周期不匹配（编译错误） … and 1 more |
| `concept/01_foundation/06_strings_and_text/18_strings_and_encoding.md` | L1 | ## 三、选型决策矩阵 → ### 3.1 字符串类型选型; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 十二、边界测试：字符串编码的编译错误 → ### 12.1 边界测试：无效 UTF-8 的字节切片转 `str`（运行时 panic） … and 1 more |
| `concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md` | L1 | ## 二、C++ 的 Move 语义 → ### 2.1 `std::move` 与移动构造函数; ## 三、Rust 的 Move 语义 → ### 3.1 所有权转移; ## 五、RVO 与 Copy Elision → ### 5.1 C++ 拷贝省略（RVO/NRVO） |
| `concept/01_foundation/03_values_and_references/19_value_vs_reference_semantics.md` | L1 | ## 二、值语义（Value Semantics） → ### 2.1 定义; ## 三、引用语义（Reference Semantics） → ### 3.1 定义; ## 四、Rust：值语义的极致 → ### 4.1 默认行为 |
| `concept/01_foundation/05_collections/08_collections.md` | L1 | ## 二、技术细节 → ### 2.1 容量管理与重新分配; ## 十四、边界测试：集合的编译错误 → ### 14.1 边界测试：`HashMap` 键未实现 `Hash` + `Eq`（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：Vec 与容量（理解层） |
| `concept/01_foundation/10_testing_basics/16_testing_basics.md` | L1 | ## 二、技术细节 → ### 2.1 单元测试; ## 四、反命题与边界分析 → ### 4.1 反命题树; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：单元测试通常放在哪里？集成测试又应该放在项目的哪个目录？（理解层） |
| `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` | L1 | ## 十、边界测试：高级生命周期的编译错误 → ### 10.1 边界测试：`for<'a>` HRTB 在 trait bound 中的误用（编译错误）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：生命周期省略的边界（理解层） |
| `concept/01_foundation/07_modules_and_items/39_items.md` | L1 | ## 三、常见 Item 示例 → ### 函数; ## 六、关联项与外部项 → ### 关联项（Associated items） |
| `concept/01_foundation/00_start/00_start.md` | L1 | ## 嵌入式测验 → ### 测验 1：本知识体系将 Rust 学习路径分为几个层级？（理解层） |
| `concept/01_foundation/00_start/37_operators_and_symbols.md` | L1 | ## 八、括号 → ### 圆括号 `()` |
| `concept/01_foundation/01_ownership_borrow_lifetime/28_ownership_inventories_brown_book.md` | L1 | ## 二、样题示例（基于 Inventory 方法论） → ### 样题 1：字符串替换链 |
| `concept/01_foundation/04_control_flow/40_patterns.md` | L1 | ## 四、模式形式 → ### Literal patterns |
| `concept/01_foundation/07_modules_and_items/12_functions.md` | L1 | ## 七、反例与边界测试 → ### 7.1 忘记返回表达式 |
| `concept/01_foundation/07_modules_and_items/13_use_declarations.md` | L1 | ## 六、反例与边界测试 → ### 6.1 导入私有项 |
| `concept/01_foundation/07_modules_and_items/14_structs.md` | L1 | ## 六、反例与边界测试 → ### 6.1 未实现 `Copy` 时的更新语法陷阱 |
| `concept/01_foundation/07_modules_and_items/15_enumerations.md` | L1 | ## 六、反例与边界测试 → ### 6.1 未处理 `None` |
| `concept/01_foundation/07_modules_and_items/16_implementations.md` | L1 | ## 六、反例与边界测试 → ### 6.1 在 `&self` 方法中修改字段 |
| `concept/01_foundation/08_error_handling/33_error_handling_control_flow.md` | L1 | ## 认知路径与推理骨架 → ### 认知路径 |
| `concept/01_foundation/10_testing_basics/42_useful_development_tools.md` | L1 | ## 四、配置示例 → ### `rustfmt.toml` |
| `concept/01_foundation/README.md` | L1 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《L1 基础概念层（Foundation）》在本知识体系中扮演什么角色？（理解层） |
| `concept/00_meta/04_navigation/quick_reference.md` | L0 | ### A → #### `async` / `await`; ### B → #### `Box<T>`; ### C → #### `const` / `const fn` … and 18 more |
| `concept/00_meta/00_framework/methodology.md` | L0 | ## 一、权威定义（Definition） → ## 二、概念属性矩阵（Attribute Matrix）; ## 二、概念属性矩阵（Attribute Matrix） → ## 三、形式化理论根基（Formal Foundation）; ## 三、形式化理论根基（Formal Foundation） → ## 四、思维导图（Mind Map） … and 15 more |
| `concept/00_meta/00_framework/decidability_spectrum.md` | L0 | ## 一、权威来源与梳理方法论 → ### 1.1 来源分级; ## 二、可判定性谱系总览 → ### 2.1 谱系全景图; ## 五、L2 类型系统层 → ### 5.1 局部类型推断 … and 8 more |
| `concept/00_meta/00_framework/expressiveness_multiview.md` | L0 | ## 一、权威来源与梳理方法论 → ### 1.1 理论视角与形式化根基; ## 二、计算语义视角 → ### 2.1 可计算性谱系; ## 三、类型语义视角 → ### 3.1 Curry-Howard 对应在 Rust 中的实例 … and 8 more |
| `concept/00_meta/03_audit/audit_checklist.md` | L0 | ## 二、定理一致性检查（Theorem Consistency） [形式化验证中的定理证明一致性 — 参照 TAPL (Pierce, 2002) 类型系统元理论; RustBelt (Jung et al., POPL 2018) 的协议验证框架](https://plv.mpi-sws.org/rustbelt/) → ### 2.1 每个核心文件的定理链; ## 三、反例与边界完备性检查（Counter-example Completeness） [边界测试方法论 — 参照 Torchiano et al. (2018) 关于软件工程知识库边界分析的研究](https://dl.acm.org/) → ### 3.1 每个核心概念的反例覆盖; ## 四、认知路径检查（Cognitive Path） [认知路径设计参照建构主义学习理论 — Bruner (1961) 发现学习理论; Ausubel (1968) 有意义学习理论; 概念文件的认知路径章节要求渐进式推导](../00_framework/methodology.md) → ### 4.1 渐进式推导 … and 7 more |
| `concept/00_meta/00_framework/concept_definition_decision_forest.md` | L0 | ## 二、所有权判定树 → ### 2.1 判定链; ## 三、借用判定树 → ### 3.1 判定链; ## 四、生命周期判定树 → ### 4.1 判定链 … and 6 more |
| `concept/00_meta/04_navigation/self_assessment.md` | L0 | ## L5 对比层：多语言范式（5 题） 题目基于 TRPL 跨章节对比 / 2024; [Rust Reference — Types, Traits / 2025](https://doc.rust-lang.org/reference/introduction.html); [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_Programming)(<https://en.wikipedia.org/wiki/Object-oriented_programming>) → ### Q31: Rust vs C++ RAII; ## L6 生态层：工程实践（5 题） 题目基于 Cargo Book / 2025; [Rust Reference — Crates, unsafe / 2025](https://doc.rust-lang.org/reference/introduction.html); Rust Internals — Edition System(<https://internals.rust-lang.org/>) → ### Q36: Cargo Workspace; ## L1 扩展层：所有权与类型系统（8 题） [来源: 题目基于 Rust Reference — Ownership, Lifetimes, Types / 2025; TRPL Ch4, Ch6, Ch10 / 2024; Rustonomicon — Life before Main](https://doc.rust-lang.org/nomicon/index.html) → ### Q41: 函数参数传递 … and 6 more |
| `concept/00_meta/00_framework/theorem_inference_forest.md` | L0 | ## 二、所有权定理树 → ### 2.1 推理链; ## 三、借用定理树 → ### 3.1 推理链; ## 四、生命周期定理树 → ### 4.1 推理链 … and 5 more |
| `concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md` | L0 | ## L0 元信息层 → ### 层内引用关系; ## L1 基础概念层 → ### 层内引用关系; ## L2 进阶概念层 → ### 层内引用关系 … and 5 more |
| `concept/00_meta/00_framework/fault_tree_analysis_collection.md` | L0 | ## 一、FTA 格式规范 → ### 1.1 符号系统; ## 二、内存安全失效树 → ### 2.1 顶事件; ## 三、并发安全失效树 → ### 3.1 顶事件 … and 4 more |
| `concept/00_meta/00_framework/semantic_space.md` | L0 | ## 一、表征空间的定义（Definition of Representational Space） → ### 1.1 什么是表征空间？; ## 二、语义封闭性（Semantic Closure） → ### 2.1 封闭世界假设; ## 三、能表达 vs 不能表达的边界（Expressibility Boundary） → ### 3.1 三维分类框架 … and 4 more |
| `concept/00_meta/04_navigation/problem_graph.md` | L0 | ## 二、内存安全设计问题树 → ### 全局层问题; ## 三、并发系统设计问题树 → ### 全局层问题; ## 四、异步系统设计问题树 → ### 全局层问题 … and 4 more |
| `concept/00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | L0 | ## 二、三层语义空间的同构映射 → ### 2.1 统一抽象框架; ## 三、分治算法 ↔ Composite + Parallel Split 的完整同构 → ### 3.1 算法层：归并排序[来源: [CLRS — Introduction to Algorithms, 4th Ed.](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)]; ## 四、动态规划 ↔ Memoization + Deferred Choice[来源: [Wikipedia — Dynamic Programming](https://en.wikipedia.org/wiki/Dynamic_programming)] → ### 4.1 算法层：斐波那契 DP … and 3 more |
| `concept/00_meta/01_terminology/bilingual_template_v2.md` | L0 | ## 四、示例与反例 → ### 4.1 正确示例; ## 五、反命题与边界分析 → ### 5.1 反命题树; ## 六、边界测试 → ### 6.1 边界测试：...（编译错误） … and 3 more |
| `concept/00_meta/04_navigation/intra_layer_model_map.md` | L0 | ## 一、L1 基础概念层：所有权 · 借用 · 生命周期 · 类型系统 → ### 1.1 四元关系拓扑; ## 二、L2 进阶概念层：Trait · 泛型 · 内存管理 · 错误处理 → ### 2.1 四元关系拓扑; ## 三、L3 高级概念层：并发 · 异步 · Unsafe · 宏 → ### 3.1 四元关系拓扑 … and 3 more |
| `concept/00_meta/04_navigation/learning_guide.md` | L0 | ## 一、如何使用本指南 → ### 1.1 选择你的起点; ## 二、按背景的详细起点指南 → ### 2.1 完全新手路径（无系统编程经验） 来源: [TRPL Ch1-3; Rust by Example; 前置依赖: 无; 认知负荷管理参照 Sweller — *Cognitive Load Theory* / 1988](https://doc.rust-lang.org/book/ch01-00-getting-started.html); ## 四、阅读策略与技巧 → ### 4.1 三遍阅读法 … and 3 more |
| `concept/00_meta/02_sources/rustbelt_predicate_map.md` | L0 | ## 二、所有权谓词 own(τ) 映射 → ### 2.1 数学定义; ## 三、共享谓词 shr(κ, ℓ) 映射 → ### 3.1 数学定义; ## 四、生命周期令牌 [α]₁ 映射 → ### 4.1 数学定义 … and 2 more |
| `concept/00_meta/02_sources/topic_authority_alignment_map.md` | L0 | ## 1. 当前项目概念层级（L0-L7） → ### L00（62 篇）; ### P0 官方核心（0 项） → ### P1 形式化/验证（0 项）; ### P1 形式化/验证（0 项） → ### P2 工业生态（0 项） … and 2 more |
| `concept/00_meta/03_audit/asp_marking_guide.md` | L0 | ## 一、标记定义与理论根基 → ### 1.1 A — Application（应用）; ## 二、标记规范 → ### 2.1 文件头部标注格式; ## 三、Rust 知识体系全量标记 → ### 3.1 L1 基础概念层 … and 2 more |
| `concept/00_meta/00_framework/competency_graph.md` | L0 | ## 三、自评工具 → ### 3.1 六维自评量表; ## 四、薄弱点诊断与训练路径 → ### 薄弱点 → 训练路径映射; ## 五、背景定制能力路径 → ### 路径 A：C++ 背景 … and 1 more |
| `concept/00_meta/04_navigation/inter_layer_map.md` | L0 | ## 四、关键跨层推理链（定理一致性） → ### 4.1 链 1: 内存安全完备性; ## 五、层间一致性检查点 → ### 5.1 定义一致性检查; ## 六、反事实与边界条件 → ### 6.1 什么情况下形式化保证失效？ … and 1 more |
| `concept/00_meta/04_navigation/learning_mvp_path_en.md` | L0 | ## Week 1: Rust Fundamentals & Ownership (12h) → ### Day 1: Hello World + Toolchain (2h); ## Week 2: Type System & Error Handling (12h) → ### Day 7: Structs, Enums & Pattern Matching (2h); ## Week 3: Concurrency & CLI Project (12h) → ### Day 13: Threads & Shared State (2h) … and 1 more |
| `concept/00_meta/00_framework/cognitive_dimension_matrix.md` | L0 | ## 一、理论框架 → ### 1.1 Krathwohl 知识维度（纵轴）; ## 二、Rust 知识体系全局双维矩阵 → ### 2.1 L1 基础概念层映射; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 知识体系双维认知矩阵（Krathwohl × Bloom）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/comprehensive_rust_mapping.md` | L0 | ## 一、课程概览 → ### 1.1 Comprehensive Rust 是什么; ## 二、章节映射表 → ### 2.1 Day 1 — Rust 基础; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Comprehensive Rust 课程映射》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md` | L0 | ## 二、主题簇地图 → ### 2.1 内存模型簇; ## 三、代码对比示例 → ### 错误处理; ## 四、推荐学习路径 → ### 路径 A：C++ 系统程序员快速迁移 |
| `concept/00_meta/00_framework/paradigm_transition_matrix.md` | L0 | ## 一、C++ → Rust 转换矩阵 → ### 1.1 核心转换模式; ## 六、学习难点与认知陷阱 → ### 6.1 通用认知陷阱; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 范式转换模式矩阵（Paradigm Transition Matrix）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/semantic_expressiveness.md` | L0 | ## 一、权威来源与梳理方法论 → ### 1.1 来源分级; ## 十一、演进路线图（与 L7 前沿对齐） → ### 11.1 各维度演进趋势; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust Semantic Expressiveness: A Panoramic Survey（Rust 语义表达力全景梳理）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/todos.md` | L0 | ## 一、高优先级 TODO（建议优先处理） [优先级排序基于概念依赖图的前置节点数量 — 前置越多的概念优先级越高](https://en.wikipedia.org/wiki/Topological_sorting) → ### L1 基础概念层; ## 四、质量审计检查清单 [审计方法论参照 IEEE 1012 — 软件验证与确认标准; Rust RFC 流程 — 设计决策的公开审查机制](https://standards.ieee.org/standard/1012-2012.html) → ### 4.1 已完成的门禁检查; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《全局待办清单（Global TODO Tracker）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/01_terminology/bilingual_template.md` | L0 | ## 二、概念定义 → ### 2.1 形式化定义; ## 六、思维表征 → ### 6.1 思维导图; ### 6.2 决策树/矩阵（如适用） → ## 七、反命题与边界 |
| `concept/00_meta/02_sources/authority_source_map.md` | L0 | ## 二、二级来源：跨语言权威入口 [跨语言对比方法论参照 concept/05_comparative/ 系列文件的对比框架](https://doc.rust-lang.org/reference/introduction.html) → ### C++; ## 三、网络权威锚点（永久链接） [永久链接选择标准: 域名稳定性 > 版本归档 > 社区镜像; 参照 PURL (Persistent Uniform Resource Locator) 标准和 DOI 数字对象标识符的设计原则](https://en.wikipedia.org/wiki/Persistent_uniform_resource_locator) → ### Rust 官方; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《权威来源映射表（Authority Source Map）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/04_navigation/career_landscape.md` | L0 | ## 一、核心数据 → ### 1.1 美国薪资范围（2026）; ## 二、技术细节 → ### 2.1 技能需求矩阵; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 职业市场全景：2026 年数据与分析》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/04_navigation/concept_index.md` | L0 | ## 一、索引使用说明 [倒排索引方法论参照信息检索标准 — Manning, Raghavan & Schütze, *Introduction to Information Retrieval* (Cambridge, 2008); 语义链接网络参照 Knowledge Graph 构建方法论](../00_framework/methodology.md) → ### 1.1 概念类型标记 [概念分类参照语义网络理论 — Collins & Quillian (1969) 层次语义网络模型; 概念的层级组织与属性继承](../00_framework/methodology.md); ## 五、按 Bloom 层级排序 [Bloom, B.S. et al. — *Taxonomy of Educational Objectives: The Classification of Educational Goals*. Handbook I: Cognitive Domain. Longman, 1956 (revised 2001); 认知层级作为知识结构组织的主轴](https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/) → ### 记忆（Remember）→ 理解（Understand）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《全局概念索引（Concept Index）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/04_navigation/learning_mvp_path.md` | L0 | ## Week 1: 基础能力构建 → ### Day 1-2: Hello World + 基础语法 [4h]; ## Week 2: 并发与工程化 → ### Day 8-9: 集合与迭代器 [4h]; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《MVP 学习路径：从零到多线程 CLI（40 小时）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/04_navigation/navigation.md` | L0 | ## 一、按层级导航（L0-L7） → ### L0 元信息层 — 方法论与索引; ## 二、按背景导航 → ### 完全新手（无系统编程经验）; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 知识体系全景导航（Navigation Hub）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/knowledge_topology/kg_tlo_alignment.md` | L0 | ## 2. BFO / DOLCE 核心类别速览 → ### 2.1 BFO 顶层二分法; ## 5. `kg_data_v2.json` 关键实体 TLO 映射示例 → ### 5.1 `ex:Ownership`（所有权）; ## 6. 边界案例与讨论 → ### 6.1 `Theory` 是 Abstract 还是 Information Content Entity？ |
| `concept/00_meta/00_framework/pattern_semantic_space_index.md` | L0 | ## 二、模式文件语义坐标系 → ### 2.1 横向：问题域维度; ## 四、推荐学习路径 → ### 路径 A：从单个模式到组合代数 |
| `concept/00_meta/00_framework/pl_foundations_roadmap.md` | L0 | ## 二、基座主题地图 → ### 2.1 变量与存储; ## 三、推荐学习路径 → ### 路径 A：从通用 PL 到 Rust |
| `concept/00_meta/02_sources/international_authority_index.md` | L0 | ## 三、工业与生态库 → ### 异步与网络; ## 四、跨语言权威入口 → ### C++ |
| `concept/00_meta/02_sources/sources.md` | L0 | ## 八、使用规范 → ### 8.1 引用规范; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《权威来源清单与知识来源关系分析》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/03_audit/quality_dashboard_v2.md` | L0 | ## 六、认知维度覆盖 → ### 6.1 Krathwohl × Bloom 双维覆盖; ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 知识体系思维表征覆盖率仪表板（Quality Dashboard v2）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/knowledge_topology/03_scenario_decision_tree_atlas.md` | L0 | ## 三、按场景索引 → ### 3.1 内存管理场景; ## 四、典型决策树示例 → ### 4.1 内存管理决策树 |
| `concept/00_meta/knowledge_topology/05_logical_reasoning_atlas.md` | L0 | ## 三、核心推理链 → ### 3.1 所有权与内存安全推理链; ## 四、推理路径图 → ### 4.1 从类型到形式化验证 |
| `concept/00_meta/00_framework/03_bloom_taxonomy.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Bloom Taxonomy（Bloom 分类法）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/boundary_extension_tree.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 安全边界扩展推理树》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/00_framework/knowledge_mindmap.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 知识体系全局思维导图（Knowledge Mindmap）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/01_terminology/terminology_glossary.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Rust 核心术语英中对照表》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/03_audit/08_concept_audit_guide.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《Concept Audit Guide（概念审计指南）》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/03_audit/grading_system.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：本文档《内容分级与受众标签体系》在 Rust 知识体系中属于哪一层级的元数据？（理解层） |
| `concept/00_meta/04_navigation/foundations_gap_closure_index.md` | L0 | ## 六、已知遗留问题 → ### 6.1 SUMMARY.md 占位符 ✅ 已解决 |
| `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md` | L0 | ## 一、按层级索引 → ### L0 元信息层 |
| `concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md` | L0 | ## 二、属性分布统计 → ### A/S/P 分布 |
| `concept/00_meta/knowledge_topology/04_example_counterexample_atlas.md` | L0 | ## 三、按层级索引 → ### 3.1 L1 基础概念层 |
| `concept/00_meta/knowledge_topology/08_concept_source_alignment_atlas.md` | L0 | ## 五、各层代表性来源对齐 → ### 5.1 L1 基础概念层 |
| `concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md` | L0 | ## 三、主要判定树 → ### 3.1 借用冲突判定树 |
| `concept/00_meta/knowledge_topology/10_gap_and_action_plan.md` | L0 | ## 三、优先修复任务 → ### P0：补全权威来源（L1–L4 核心概念） |
| `concept/00_meta/README.md` | L0 | ## 嵌入式测验（Embedded Quiz） → ### 测验 1：《Concept 元层》在本知识体系中扮演什么角色？（理解层） |

### 2.4 Theorem chains but thin body (40)

| File | Layer | Lines | Theorem chains | Code blocks | Metadata ratio |
|:---|:---|---:|---:|---:|:---|
| `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | L7 | 329 | 3 | 16 | 16% |
| `concept/07_future/03_preview_features/47_wasm_target_evolution.md` | L7 | 242 | 3 | 12 | 22% |
| `concept/07_future/00_version_tracking/50_nightly_rust.md` | L7 | 233 | 3 | 14 | 10% |
| `concept/07_future/03_preview_features/49_rust_in_space.md` | L7 | 231 | 3 | 4 | 12% |
| `concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md` | L7 | 220 | 3 | 2 | 16% |
| `concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md` | L6 | 517 | 3 | 44 | 11% |
| `concept/06_ecosystem/01_cargo/72_cargo_security_cves.md` | L6 | 476 | 4 | 16 | 12% |
| `concept/06_ecosystem/05_systems_and_embedded/56_c_to_rust_translation.md` | L6 | 455 | 6 | 10 | 11% |
| `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` | L6 | 366 | 4 | 20 | 7% |
| `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md` | L6 | 357 | 6 | 12 | 6% |
| `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md` | L6 | 325 | 3 | 18 | 9% |
| `concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md` | L6 | 308 | 3 | 16 | 11% |
| `concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md` | L6 | 300 | 3 | 16 | 11% |
| `concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md` | L6 | 299 | 3 | 18 | 13% |
| `concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md` | L6 | 295 | 3 | 18 | 13% |
| `concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md` | L6 | 294 | 3 | 16 | 12% |
| `concept/06_ecosystem/00_toolchain/71_compiler_testing.md` | L6 | 281 | 3 | 20 | 12% |
| `concept/06_ecosystem/01_cargo/78_cargo_workspaces.md` | L6 | 268 | 3 | 24 | 12% |
| `concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md` | L6 | 265 | 3 | 6 | 14% |
| `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` | L6 | 264 | 3 | 8 | 9% |
| `concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md` | L6 | 251 | 3 | 12 | 12% |
| `concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md` | L6 | 249 | 3 | 8 | 15% |
| `concept/06_ecosystem/01_cargo/10_public_private_deps.md` | L6 | 243 | 4 | 12 | 8% |
| `concept/05_comparative/00_paradigms/16_cpp_rust_surface_features.md` | L5 | 230 | 4 | 8 | 13% |
| `concept/04_formal/00_type_theory/50_type_system_reference.md` | L4 | 411 | 4 | 10 | 8% |
| `concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md` | L4 | 367 | 11 | 20 | 15% |
| `concept/04_formal/README.md` | L4 | 343 | 5 | 10 | 9% |
| `concept/04_formal/04_model_checking/31_miri.md` | L4 | 313 | 4 | 16 | 11% |
| `concept/04_formal/05_rustc_internals/40_names_and_resolution.md` | L4 | 216 | 4 | 10 | 12% |
| `concept/02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md` | L2 | 225 | 6 | 0 | 15% |
| `concept/01_foundation/00_start/00_start.md` | L1 | 267 | 6 | 18 | 10% |
| `concept/01_foundation/00_start/37_operators_and_symbols.md` | L1 | 258 | 9 | 0 | 12% |
| `concept/01_foundation/10_testing_basics/42_useful_development_tools.md` | L1 | 225 | 6 | 16 | 13% |
| `concept/00_meta/04_navigation/concept_index.md` | L0 | 785 | 4 | 0 | 4% |
| `concept/00_meta/04_navigation/learning_guide.md` | L0 | 658 | 3 | 18 | 9% |
| `concept/00_meta/04_navigation/inter_layer_map.md` | L0 | 626 | 12 | 18 | 6% |
| `concept/00_meta/00_framework/theorem_inference_forest.md` | L0 | 510 | 3 | 20 | 8% |
| `concept/00_meta/02_sources/rustbelt_predicate_map.md` | L0 | 412 | 9 | 22 | 7% |
| `concept/00_meta/04_navigation/intra_layer_model_map.md` | L0 | 335 | 11 | 12 | 13% |
| `concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md` | L0 | 314 | 244 | 0 | 2% |

### 2.5 L6/L7 recently skeleton-enriched pages still needing body expansion (167)

Criteria: modified in the last 21 days, layer L6 or L7, and flagged by at least one completeness heuristic.

| File | Layer | Lines | Last modified | Issue types |
|:---|:---|---:|:---|:---|
| `concept/06_ecosystem/00_toolchain/01_toolchain.md` | L6 | 1888 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/13_logging_observability.md` | L6 | 720 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/00_toolchain/28_devops_and_ci_cd.md` | L6 | 896 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/00_toolchain/45_compiler_internals.md` | L6 | 842 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` | L6 | 366 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md` | L6 | 560 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md` | L6 | 313 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md` | L6 | 300 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md` | L6 | 265 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md` | L6 | 290 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md` | L6 | 249 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/71_compiler_testing.md` | L6 | 281 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` | L6 | 236 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/01_cargo/09_cargo_script.md` | L6 | 697 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/01_cargo/10_public_private_deps.md` | L6 | 243 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/11_resolver_v3_public_feature_unification.md` | L6 | 178 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` | L6 | 520 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md` | L6 | 517 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md` | L6 | 295 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md` | L6 | 299 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md` | L6 | 294 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md` | L6 | 325 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md` | L6 | 308 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md` | L6 | 251 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/72_cargo_security_cves.md` | L6 | 476 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` | L6 | 264 | 2026-07-05 | todo, empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/78_cargo_workspaces.md` | L6 | 268 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/82_cargo_guide_practices.md` | L6 | 166 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/83_cargo_configuration.md` | L6 | 180 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/87_build_std.md` | L6 | 284 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/02_core_crates/03_core_crates.md` | L6 | 1342 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/02_patterns.md` | L6 | 3075 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/05_system_design_principles.md` | L6 | 742 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/30_system_composability.md` | L6 | 802 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/31_microservice_patterns.md` | L6 | 972 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/32_event_driven_architecture.md` | L6 | 1038 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/33_cqrs_event_sourcing.md` | L6 | 1461 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/34_idioms_spectrum.md` | L6 | 1393 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/35_architecture_patterns.md` | L6 | 1270 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md` | L6 | 788 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | L6 | 751 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/38_formal_design_pattern_theory.md` | L6 | 997 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/39_frontier_research_and_innovative_patterns.md` | L6 | 978 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/41_workflow_theory.md` | L6 | 1391 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/42_api_design_patterns.md` | L6 | 1298 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/73_pattern_composition_algebra.md` | L6 | 726 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/82_engineering_and_production_patterns.md` | L6 | 315 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | L6 | 257 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/85_design_patterns_faq.md` | L6 | 486 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/04_web_and_networking/18_distributed_systems.md` | L6 | 814 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/24_cloud_native.md` | L6 | 791 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/27_web_frameworks.md` | L6 | 1004 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/38_network_protocols.md` | L6 | 526 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md` | L6 | 2057 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/04_web_and_networking/40_reactive_programming.md` | L6 | 1080 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/41_http_client_development.md` | L6 | 186 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/43_websocket_realtime_communication.md` | L6 | 723 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/08_wasi.md` | L6 | 672 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/17_cross_compilation.md` | L6 | 671 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md` | L6 | 973 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/25_cli_development.md` | L6 | 788 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/39_os_kernel.md` | L6 | 415 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/52_robotics.md` | L6 | 1012 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/53_embedded_graphics.md` | L6 | 1045 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/56_c_to_rust_translation.md` | L6 | 455 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md` | L6 | 237 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/04_application_domains.md` | L6 | 1526 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/06_data_and_distributed/23_database_access.md` | L6 | 819 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/06_data_and_distributed/36_stream_processing_ecosystem.md` | L6 | 569 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/37_database_systems.md` | L6 | 543 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/48_data_engineering.md` | L6 | 940 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md` | L6 | 863 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/55_rust_for_data_science.md` | L6 | 612 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/07_security_and_cryptography/19_security_practices.md` | L6 | 1090 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/07_security_and_cryptography/43_security_cryptography.md` | L6 | 928 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/08_formal_verification/44_formal_ecosystem_tower.md` | L6 | 600 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md` | L6 | 942 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/09_networking/01_advanced_network_protocols.md` | L6 | 281 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/02_network_security.md` | L6 | 321 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/04_network_programming_quick_start.md` | L6 | 262 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/05_formal_network_protocol_theory.md` | L6 | 559 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/09_networking/06_networking_basics.md` | L6 | 859 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/09_testing_and_quality/12_testing_strategies.md` | L6 | 748 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/14_documentation.md` | L6 | 676 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/16_testing.md` | L6 | 762 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/17_benchmarking.md` | L6 | 158 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/10_performance/15_performance_optimization.md` | L6 | 1154 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/06_blockchain.md` | L6 | 919 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/07_game_ecs.md` | L6 | 1362 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/11_webassembly.md` | L6 | 674 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/20_licensing_and_compliance.md` | L6 | 701 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/21_game_development.md` | L6 | 698 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/26_game_development.md` | L6 | 721 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/29_algorithms_competitive_programming.md` | L6 | 1257 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/46_machine_learning_ecosystem.md` | L6 | 943 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/49_game_engine_internals.md` | L6 | 1133 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md` | L6 | 906 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/54_webassembly_advanced.md` | L6 | 1145 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md` | L6 | 368 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/60_wasm_faq.md` | L6 | 470 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/61_wasm_javascript_interop.md` | L6 | 469 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md` | L6 | 357 | 2026-07-05 | todo, empty_section, theorem_thin_body |
| `concept/06_ecosystem/11_domain_applications/76_algorithm_engineering_practice.md` | L6 | 1940 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/77_data_structures_in_rust.md` | L6 | 273 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/78_algorithm_complexity_analysis.md` | L6 | 181 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/80_formal_algorithm_theory.md` | L6 | 265 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/README.md` | L6 | 295 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/05_rust_version_tracking.md` | L7 | 2583 | 2026-07-05 | todo, empty_section |
| `concept/07_future/00_version_tracking/50_nightly_rust.md` | L7 | 233 | 2026-07-09 | theorem_thin_body |
| `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | L7 | 751 | 2026-07-09 | todo, empty_section |
| `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | L7 | 2406 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | L7 | 2354 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_93_stabilized.md` | L7 | 183 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | L7 | 412 | 2026-07-09 | todo, empty_section |
| `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | L7 | 327 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` | L7 | 315 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_97_preview.md` | L7 | 293 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` | L7 | 175 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_98_preview.md` | L7 | 575 | 2026-07-05 | todo, empty_section |
| `concept/07_future/01_edition_roadmap/19_rust_edition_preview.md` | L7 | 110 | 2026-07-09 | empty_section |
| `concept/07_future/01_edition_roadmap/23_rust_edition_guide.md` | L7 | 17 | 2026-07-05 | todo |
| `concept/07_future/01_edition_roadmap/44_edition_guide.md` | L7 | 782 | 2026-07-05 | empty_section |
| `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | L7 | 329 | 2026-07-09 | todo, empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/04_effects_system.md` | L7 | 1768 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/07_mcdc_coverage_preview.md` | L7 | 563 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/08_safety_tags_preview.md` | L7 | 653 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/09_parallel_frontend_preview.md` | L7 | 667 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/10_derive_coerce_pointee_preview.md` | L7 | 592 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/11_const_trait_impl_preview.md` | L7 | 626 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/12_return_type_notation_preview.md` | L7 | 503 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/13_unsafe_fields_preview.md` | L7 | 619 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/14_lifetime_capture_preview.md` | L7 | 240 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/15_pin_ergonomics_preview.md` | L7 | 312 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/16_type_alias_impl_trait_preview.md` | L7 | 236 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/17_const_trait_preview.md` | L7 | 234 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/18_async_drop_preview.md` | L7 | 758 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md` | L7 | 664 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/22_gen_blocks_preview.md` | L7 | 743 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/25_open_enums_preview.md` | L7 | 799 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/26_specialization_preview.md` | L7 | 743 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/27_compile_time_execution.md` | L7 | 739 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/30_stable_abi_preview.md` | L7 | 240 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/31_safety_tags_preview.md` | L7 | 156 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/32_inline_const_pattern_preview.md` | L7 | 251 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/33_autoverus_preview.md` | L7 | 172 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/34_must_not_suspend_preview.md` | L7 | 231 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/35_ferrocene_preview.md` | L7 | 653 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/37_rpitit_preview.md` | L7 | 258 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/38_cranelift_backend_preview.md` | L7 | 766 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/39_arbitrary_self_types_preview.md` | L7 | 350 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/40_ergonomic_ref_counting_preview.md` | L7 | 287 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/41_rust_specification_preview.md` | L7 | 643 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/42_field_projections_preview.md` | L7 | 392 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/45_std_autodiff_preview.md` | L7 | 326 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md` | L7 | 220 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/47_wasm_target_evolution.md` | L7 | 242 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/48_aarch64_sve_sme_preview.md` | L7 | 268 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/49_rust_in_space.md` | L7 | 231 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/07_future/04_research_and_experimental/01_ai_integration.md` | L7 | 1007 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/02_formal_methods.md` | L7 | 1663 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/03_evolution.md` | L7 | 2179 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/21_rust_in_ai.md` | L7 | 778 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/28_rust_for_webassembly.md` | L7 | 947 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/29_ebpf_rust.md` | L7 | 992 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/43_rust_for_linux.md` | L7 | 1018 | 2026-07-05 | todo, empty_section |
| `concept/07_future/05_roadmaps/24_roadmap.md` | L7 | 1067 | 2026-07-05 | todo, empty_section |
| `concept/07_future/README.md` | L7 | 298 | 2026-07-05 | empty_section |

## 3. Per-Layer Statistics

| Layer | Files | Avg lines | Flagged files | Short | TODO | Empty sections | Thin theorem body |
|:---|---:|---:|---:|---:|---:|---:|---:|
| L0 | 65 | 389.1 | 63 | 2 | 21 | 56 | 7 |
| L1 | 56 | 681.6 | 52 | 0 | 11 | 52 | 3 |
| L2 | 39 | 869.1 | 38 | 0 | 13 | 38 | 1 |
| L3 | 58 | 770.3 | 49 | 0 | 13 | 48 | 0 |
| L4 | 54 | 537.3 | 41 | 0 | 8 | 40 | 5 |
| L5 | 20 | 835.8 | 20 | 0 | 4 | 20 | 1 |
| L6 | 116 | 674.7 | 107 | 0 | 33 | 107 | 18 |
| L7 | 60 | 649.0 | 60 | 0 | 21 | 58 | 5 |
| L? | 2 | 338.0 | 2 | 0 | 2 | 1 | 0 |

## 4. Prioritized Remediation Batches

### P0 — L1–L3 core concepts that are short or have TODOs

| File | Layer | Lines | Issues | Recommended action |
|:---|:---|---:|:---|:---|
| `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` | L1 | 384 | todo, empty_section | 保留 stub（已是重定向页） |
| `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | L1 | 1833 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | L1 | 1953 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | L1 | 1475 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` | L1 | 1501 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/02_type_system/04_type_system.md` | L1 | 3138 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/02_type_system/14_coercion_and_casting.md` | L1 | 914 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/02_type_system/31_never_type.md` | L1 | 553 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` | L1 | 845 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/06_strings_and_text/46_formatting_and_display.md` | L1 | 419 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/01_foundation/08_error_handling/13_panic_and_abort.md` | L1 | 938 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/00_traits/01_traits.md` | L2 | 2967 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/00_traits/19_advanced_traits.md` | L2 | 957 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/00_traits/39_dispatch_mechanisms.md` | L2 | 2025 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/01_generics/02_generics.md` | L2 | 3108 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/01_generics/39_type_level_programming.md` | L2 | 653 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/02_memory_management/03_memory_management.md` | L2 | 2039 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/02_memory_management/08_interior_mutability.md` | L2 | 872 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/02_memory_management/12_smart_pointers.md` | L2 | 897 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/03_error_handling/04_error_handling.md` | L2 | 2575 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md` | L2 | 1246 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md` | L2 | 446 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/06_macros_and_metaprogramming/13_dsl_and_embedding.md` | L2 | 828 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/02_intermediate/07_iterators_and_closures/15_iterator_patterns.md` | L2 | 1322 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/00_concurrency/10_concurrency_patterns.md` | L3 | 2250 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/01_async/02_async.md` | L3 | 3441 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/01_async/39_future_and_executor_mechanisms.md` | L3 | 1040 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/02_unsafe/03_unsafe.md` | L3 | 3427 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/02_unsafe/12_unsafe_rust_patterns.md` | L3 | 33 | todo | 保留 stub（已是重定向页） |
| `concept/03_advanced/03_proc_macros/04_macros.md` | L3 | 2477 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md` | L3 | 339 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md` | L3 | 294 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md` | L3 | 336 | todo, empty_section | enrich in place（核心概念需补齐正文） |
| `concept/03_advanced/03_proc_macros/32_macro_glossary.md` | L3 | 657 | todo, empty_section | 保留 stub（已是重定向页） |
| `concept/03_advanced/03_proc_macros/33_macro_faq.md` | L3 | 777 | todo, empty_section | 保留 stub（已是重定向页） |
| `concept/03_advanced/03_proc_macros/34_syn_quote_reference.md` | L3 | 971 | todo, empty_section | 保留 stub（已是重定向页） |
| `concept/03_advanced/03_proc_macros/35_macro_hygiene.md` | L3 | 1019 | todo, empty_section | 保留 stub（已是重定向页） |

### P1 — L4 formal pages

| File | Layer | Lines | Issues | Recommended action |
|:---|:---|---:|:---|:---|
| `concept/04_formal/00_type_theory/02_type_theory.md` | L4 | 1739 | todo, empty_section | enrich in place |
| `concept/04_formal/00_type_theory/06_subtype_variance.md` | L4 | 635 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/08_type_inference.md` | L4 | 758 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/10_category_theory.md` | L4 | 809 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/14_lambda_calculus.md` | L4 | 753 | todo, empty_section | enrich in place |
| `concept/04_formal/00_type_theory/21_type_semantics.md` | L4 | 896 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/27_type_checking_and_inference.md` | L4 | 308 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/29_type_inference_complexity.md` | L4 | 407 | empty_section | enrich in place |
| `concept/04_formal/00_type_theory/50_type_system_reference.md` | L4 | 411 | todo, empty_section, theorem_thin_body | enrich in place（形式化页需补充证明/代码/示例） |
| `concept/04_formal/01_ownership_logic/01_linear_logic.md` | L4 | 1240 | todo, empty_section | enrich in place |
| `concept/04_formal/01_ownership_logic/03_ownership_formal.md` | L4 | 1640 | todo, empty_section | enrich in place |
| `concept/04_formal/01_ownership_logic/09_linear_logic_applications.md` | L4 | 744 | todo, empty_section | enrich in place |
| `concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` | L4 | 411 | empty_section | enrich in place |
| `concept/04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md` | L4 | 162 | empty_section | enrich in place |
| `concept/04_formal/01_ownership_logic/37_behavior_considered_undefined.md` | L4 | 164 | empty_section | enrich in place |
| `concept/04_formal/02_separation_logic/04_rustbelt.md` | L4 | 1423 | todo, empty_section | enrich in place |
| `concept/04_formal/02_separation_logic/11_separation_logic.md` | L4 | 838 | empty_section | enrich in place |
| `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` | L4 | 167 | empty_section | enrich in place |
| `concept/04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md` | L4 | 167 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/12_denotational_semantics.md` | L4 | 637 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/15_hoare_logic.md` | L4 | 908 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/17_operational_semantics.md` | L4 | 1076 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/18_evaluation_strategies.md` | L4 | 682 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/20_axiomatic_semantics.md` | L4 | 952 | empty_section | enrich in place |
| `concept/04_formal/03_operational_semantics/30_aeneas_symbolic_semantics.md` | L4 | 443 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/05_verification_toolchain.md` | L4 | 1535 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/13_formal_methods.md` | L4 | 757 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/16_aerospace_certification_formal_methods.md` | L4 | 1089 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/22_modern_verification_tools.md` | L4 | 527 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/23_programming_language_foundations.md` | L4 | 424 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/24_autoverus.md` | L4 | 183 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/25_quiz_formal_methods.md` | L4 | 616 | empty_section | enrich in place |
| `concept/04_formal/04_model_checking/31_miri.md` | L4 | 313 | empty_section, theorem_thin_body | enrich in place（形式化页需补充证明/代码/示例） |
| `concept/04_formal/04_model_checking/32_kani.md` | L4 | 384 | todo, empty_section | enrich in place |
| `concept/04_formal/05_rustc_internals/19_rustc_query_system.md` | L4 | 590 | empty_section | enrich in place |
| `concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md` | L4 | 367 | empty_section, theorem_thin_body | enrich in place（形式化页需补充证明/代码/示例） |
| `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` | L4 | 449 | empty_section | enrich in place |
| `concept/04_formal/05_rustc_internals/35_name_resolution_and_hir.md` | L4 | 331 | empty_section | enrich in place |
| `concept/04_formal/05_rustc_internals/40_names_and_resolution.md` | L4 | 216 | theorem_thin_body | enrich in place（形式化页需补充证明/代码/示例） |
| `concept/04_formal/05_rustc_internals/41_special_types_and_traits.md` | L4 | 185 | empty_section | enrich in place |
| `concept/04_formal/README.md` | L4 | 343 | empty_section, theorem_thin_body | enrich in place（形式化页需补充证明/代码/示例） |

### P2 — L6/L7 recently enriched skeletons

| File | Layer | Lines | Last modified | Issues |
|:---|:---|---:|:---|:---|
| `concept/06_ecosystem/00_toolchain/01_toolchain.md` | L6 | 1888 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/13_logging_observability.md` | L6 | 720 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/00_toolchain/28_devops_and_ci_cd.md` | L6 | 896 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/00_toolchain/45_compiler_internals.md` | L6 | 842 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` | L6 | 366 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md` | L6 | 560 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md` | L6 | 313 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md` | L6 | 300 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md` | L6 | 265 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md` | L6 | 290 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md` | L6 | 249 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/71_compiler_testing.md` | L6 | 281 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` | L6 | 236 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/01_cargo/09_cargo_script.md` | L6 | 697 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/01_cargo/10_public_private_deps.md` | L6 | 243 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/11_resolver_v3_public_feature_unification.md` | L6 | 178 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` | L6 | 520 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md` | L6 | 517 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md` | L6 | 295 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md` | L6 | 299 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md` | L6 | 294 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md` | L6 | 325 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md` | L6 | 308 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md` | L6 | 251 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/72_cargo_security_cves.md` | L6 | 476 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` | L6 | 264 | 2026-07-05 | todo, empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/78_cargo_workspaces.md` | L6 | 268 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/01_cargo/82_cargo_guide_practices.md` | L6 | 166 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/83_cargo_configuration.md` | L6 | 180 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/01_cargo/87_build_std.md` | L6 | 284 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/02_core_crates/03_core_crates.md` | L6 | 1342 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/02_patterns.md` | L6 | 3075 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/05_system_design_principles.md` | L6 | 742 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/30_system_composability.md` | L6 | 802 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/31_microservice_patterns.md` | L6 | 972 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/32_event_driven_architecture.md` | L6 | 1038 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/33_cqrs_event_sourcing.md` | L6 | 1461 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/34_idioms_spectrum.md` | L6 | 1393 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/35_architecture_patterns.md` | L6 | 1270 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md` | L6 | 788 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | L6 | 751 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/38_formal_design_pattern_theory.md` | L6 | 997 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/39_frontier_research_and_innovative_patterns.md` | L6 | 978 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/41_workflow_theory.md` | L6 | 1391 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/42_api_design_patterns.md` | L6 | 1298 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/73_pattern_composition_algebra.md` | L6 | 726 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/03_design_patterns/82_engineering_and_production_patterns.md` | L6 | 315 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | L6 | 257 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/03_design_patterns/85_design_patterns_faq.md` | L6 | 486 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/04_web_and_networking/18_distributed_systems.md` | L6 | 814 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/24_cloud_native.md` | L6 | 791 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/27_web_frameworks.md` | L6 | 1004 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/38_network_protocols.md` | L6 | 526 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md` | L6 | 2057 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/04_web_and_networking/40_reactive_programming.md` | L6 | 1080 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/41_http_client_development.md` | L6 | 186 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/04_web_and_networking/43_websocket_realtime_communication.md` | L6 | 723 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/08_wasi.md` | L6 | 672 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/17_cross_compilation.md` | L6 | 671 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md` | L6 | 973 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/25_cli_development.md` | L6 | 788 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/39_os_kernel.md` | L6 | 415 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/52_robotics.md` | L6 | 1012 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/53_embedded_graphics.md` | L6 | 1045 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/05_systems_and_embedded/56_c_to_rust_translation.md` | L6 | 455 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md` | L6 | 237 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/04_application_domains.md` | L6 | 1526 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/06_data_and_distributed/23_database_access.md` | L6 | 819 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/06_data_and_distributed/36_stream_processing_ecosystem.md` | L6 | 569 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/37_database_systems.md` | L6 | 543 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/48_data_engineering.md` | L6 | 940 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md` | L6 | 863 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/06_data_and_distributed/55_rust_for_data_science.md` | L6 | 612 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/07_security_and_cryptography/19_security_practices.md` | L6 | 1090 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/07_security_and_cryptography/43_security_cryptography.md` | L6 | 928 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/08_formal_verification/44_formal_ecosystem_tower.md` | L6 | 600 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md` | L6 | 942 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/09_networking/01_advanced_network_protocols.md` | L6 | 281 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/02_network_security.md` | L6 | 321 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/04_network_programming_quick_start.md` | L6 | 262 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_networking/05_formal_network_protocol_theory.md` | L6 | 559 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/09_networking/06_networking_basics.md` | L6 | 859 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/09_testing_and_quality/12_testing_strategies.md` | L6 | 748 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/14_documentation.md` | L6 | 676 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/16_testing.md` | L6 | 762 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/09_testing_and_quality/17_benchmarking.md` | L6 | 158 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/10_performance/15_performance_optimization.md` | L6 | 1154 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/06_blockchain.md` | L6 | 919 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/07_game_ecs.md` | L6 | 1362 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/11_webassembly.md` | L6 | 674 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/20_licensing_and_compliance.md` | L6 | 701 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/21_game_development.md` | L6 | 698 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/26_game_development.md` | L6 | 721 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/29_algorithms_competitive_programming.md` | L6 | 1257 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/46_machine_learning_ecosystem.md` | L6 | 943 | 2026-07-05 | empty_section |
| `concept/06_ecosystem/11_domain_applications/49_game_engine_internals.md` | L6 | 1133 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md` | L6 | 906 | 2026-07-05 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/54_webassembly_advanced.md` | L6 | 1145 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md` | L6 | 368 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/60_wasm_faq.md` | L6 | 470 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/61_wasm_javascript_interop.md` | L6 | 469 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md` | L6 | 357 | 2026-07-05 | todo, empty_section, theorem_thin_body |
| `concept/06_ecosystem/11_domain_applications/76_algorithm_engineering_practice.md` | L6 | 1940 | 2026-07-09 | todo, empty_section |
| `concept/06_ecosystem/11_domain_applications/77_data_structures_in_rust.md` | L6 | 273 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/78_algorithm_complexity_analysis.md` | L6 | 181 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/11_domain_applications/80_formal_algorithm_theory.md` | L6 | 265 | 2026-07-09 | empty_section |
| `concept/06_ecosystem/README.md` | L6 | 295 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/05_rust_version_tracking.md` | L7 | 2583 | 2026-07-05 | todo, empty_section |
| `concept/07_future/00_version_tracking/50_nightly_rust.md` | L7 | 233 | 2026-07-09 | theorem_thin_body |
| `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | L7 | 751 | 2026-07-09 | todo, empty_section |
| `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | L7 | 2406 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | L7 | 2354 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_93_stabilized.md` | L7 | 183 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | L7 | 412 | 2026-07-09 | todo, empty_section |
| `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | L7 | 327 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` | L7 | 315 | 2026-07-05 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_97_preview.md` | L7 | 293 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` | L7 | 175 | 2026-07-09 | empty_section |
| `concept/07_future/00_version_tracking/rust_1_98_preview.md` | L7 | 575 | 2026-07-05 | todo, empty_section |
| `concept/07_future/01_edition_roadmap/19_rust_edition_preview.md` | L7 | 110 | 2026-07-09 | empty_section |
| `concept/07_future/01_edition_roadmap/23_rust_edition_guide.md` | L7 | 17 | 2026-07-05 | todo |
| `concept/07_future/01_edition_roadmap/44_edition_guide.md` | L7 | 782 | 2026-07-05 | empty_section |
| `concept/07_future/02_stabilized_features/borrow_sanitizer.md` | L7 | 329 | 2026-07-09 | todo, empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/04_effects_system.md` | L7 | 1768 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/07_mcdc_coverage_preview.md` | L7 | 563 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/08_safety_tags_preview.md` | L7 | 653 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/09_parallel_frontend_preview.md` | L7 | 667 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/10_derive_coerce_pointee_preview.md` | L7 | 592 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/11_const_trait_impl_preview.md` | L7 | 626 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/12_return_type_notation_preview.md` | L7 | 503 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/13_unsafe_fields_preview.md` | L7 | 619 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/14_lifetime_capture_preview.md` | L7 | 240 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/15_pin_ergonomics_preview.md` | L7 | 312 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/16_type_alias_impl_trait_preview.md` | L7 | 236 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/17_const_trait_preview.md` | L7 | 234 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/18_async_drop_preview.md` | L7 | 758 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md` | L7 | 664 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/22_gen_blocks_preview.md` | L7 | 743 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/25_open_enums_preview.md` | L7 | 799 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/26_specialization_preview.md` | L7 | 743 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/27_compile_time_execution.md` | L7 | 739 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/30_stable_abi_preview.md` | L7 | 240 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/31_safety_tags_preview.md` | L7 | 156 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/32_inline_const_pattern_preview.md` | L7 | 251 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/33_autoverus_preview.md` | L7 | 172 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/34_must_not_suspend_preview.md` | L7 | 231 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/35_ferrocene_preview.md` | L7 | 653 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/37_rpitit_preview.md` | L7 | 258 | 2026-07-09 | empty_section |
| `concept/07_future/03_preview_features/38_cranelift_backend_preview.md` | L7 | 766 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/39_arbitrary_self_types_preview.md` | L7 | 350 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/40_ergonomic_ref_counting_preview.md` | L7 | 287 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/41_rust_specification_preview.md` | L7 | 643 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/42_field_projections_preview.md` | L7 | 392 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/45_std_autodiff_preview.md` | L7 | 326 | 2026-07-05 | todo, empty_section |
| `concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md` | L7 | 220 | 2026-07-05 | empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/47_wasm_target_evolution.md` | L7 | 242 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/07_future/03_preview_features/48_aarch64_sve_sme_preview.md` | L7 | 268 | 2026-07-05 | empty_section |
| `concept/07_future/03_preview_features/49_rust_in_space.md` | L7 | 231 | 2026-07-09 | empty_section, theorem_thin_body |
| `concept/07_future/04_research_and_experimental/01_ai_integration.md` | L7 | 1007 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/02_formal_methods.md` | L7 | 1663 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/03_evolution.md` | L7 | 2179 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/21_rust_in_ai.md` | L7 | 778 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/28_rust_for_webassembly.md` | L7 | 947 | 2026-07-05 | empty_section |
| `concept/07_future/04_research_and_experimental/29_ebpf_rust.md` | L7 | 992 | 2026-07-05 | todo, empty_section |
| `concept/07_future/04_research_and_experimental/43_rust_for_linux.md` | L7 | 1018 | 2026-07-05 | todo, empty_section |
| `concept/07_future/05_roadmaps/24_roadmap.md` | L7 | 1067 | 2026-07-05 | todo, empty_section |
| `concept/07_future/README.md` | L7 | 298 | 2026-07-05 | empty_section |

### P3 — `00_meta` navigation / placeholders

| File | Layer | Lines | Issues | Recommended action |
|:---|:---|---:|:---|:---|
| `concept/00_meta/03_audit/template_deduplication_guide.md` | L0 | 92 | short | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/05_cross_reference_matrix.md` | L0 | 14 | todo | 保留 stub（已是重定向页） |
| `concept/00_meta/04_navigation/career_landscape.md` | L0 | 231 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/concept_index.md` | L0 | 785 | todo, empty_section, theorem_thin_body | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/foundations_gap_closure_index.md` | L0 | 142 | todo, empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/inter_layer_map.md` | L0 | 626 | todo, empty_section, theorem_thin_body | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/inter_layer_topology.md` | L0 | 15 | todo | 保留 stub（已是重定向页） |
| `concept/00_meta/04_navigation/intra_layer_model_map.md` | L0 | 335 | empty_section, theorem_thin_body | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/learning_guide.md` | L0 | 658 | todo, empty_section, theorem_thin_body | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/learning_mvp_path.md` | L0 | 366 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/learning_mvp_path_en.md` | L0 | 268 | empty_section | 保留 stub（已是重定向页） |
| `concept/00_meta/04_navigation/navigation.md` | L0 | 289 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/problem_graph.md` | L0 | 509 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/quick_reference.md` | L0 | 817 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/04_navigation/self_assessment.md` | L0 | 2242 | empty_section | 按 00_meta 治理规则处理 |
| `concept/00_meta/knowledge_topology/README.md` | L0 | 67 | short | 按 00_meta 治理规则处理 |
| `concept/00_meta/placeholders/placeholder_generic.md` | L0 | 22 | todo | 保留 stub（已是重定向页） |

## 5. Summary & Next Steps

- **432** of **470** scanned files show at least one skeletal/incomplete signal.
- **P0** has **37** L1–L3 core concept pages needing immediate body enrichment or stub conversion.
- **P1** has **41** L4 formal pages with thin theorem/code ratio or explicit markers.
- **P2** has **167** L6/L7 pages recently skeleton-enriched and still incomplete.
- **P3** has **17** `00_meta` navigation / placeholder pages to evaluate for redirection.

Recommended workflow:

1. Resolve P0 core concepts first to preserve learning-path integrity.
2. Convert placeholder/navigation stubs that do not add unique content to canonical redirect stubs.
3. Archive or merge pages that duplicate an existing canonical source.
4. Re-run `python scripts/kb_auditor.py` and this audit after remediation to update the baseline.
