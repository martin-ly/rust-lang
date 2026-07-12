# 权威源主题覆盖完整性审计报告（五源 × 主题矩阵）

> **EN**: Authority Source Topic Coverage Audit
> **日期**: 2026-07-12
> **范围**: 验证 `concept/` 对五大国际权威源的**主题覆盖完整性**（非链接有无，而是关键主题是否有对应权威页）
> **方法**: FetchURL 取四源目录（Reference / Nomicon / Cargo / RFC Book TOC）+ GitHub API 取 merged RFC 清单（≥3400，2023–2026）+ 本地 `docs/03_reference/07_trpl_3rd_ed_diff.md`（TRPL 映射）；逐项 grep 映射到 `concept/`（NN_ 重编号后按 slug + 内容关键词双轨搜索）
> **判定**: ✅ 有深度覆盖（专页或专章）/ ⚠️ 仅提及无专页 / ❌ 无覆盖

---

## 0. 总览

| 权威源 | 主题总数 | ✅ 深度覆盖 | ⚠️ 仅提及 | ❌ 无覆盖 | 本轮处置 |
|:---|:---:|:---:|:---:|:---:|:---|
| The Rust Reference | 21 章 / 60+ 主题 | 21 / 全部 | 0 | 0 | 无需处置 |
| TRPL 3rd Edition | 21 章 | 17 | 4（项目驱动章，设计使然） | 0 | Ch14 由 ⚠️ 升 ✅（`16_cargo_workflow.md` 已存在，更新映射文件） |
| The Rustonomicon | 12 章 / 30+ 主题 | 12 / 全部 | 0（原 2 项 ⚠️ 本轮深化） | 0 | 深化 2 处（无界生命周期、drop flags） |
| Rust RFC Book（2023–2026 语义重要） | 40 项 | 40 | 0（原 6 项 ⚠️ 本轮深化） | 0（原 4 项 ❌ 本轮建页） | 新建 4 页 + 深化 6 处 + 7 项经评估不建页 |
| The Cargo Book | 6 大部 / 20+ 主题 | 全部 | 0 | 0 | 无需处置（22 个 cargo 专页） |
| **合计** | **~150** | **~140** | **4** | **0** | **新建 4 页，深化 8 处** |

---

## 1. The Rust Reference（doc.rust-lang.org/reference/）— 21 章全 ✅

| 章 | concept/ 权威页 | 档 |
|:---|:---|:---:|
| 1. Notation | `04_formal/06_notation/01_notation.md` | ✅ |
| 2. Lexical structure（shebang/keywords/identifiers/comments/whitespace/tokens） | `04_formal/05_rustc_internals/10_lexical_structure.md` · `01_foundation/00_start/06_keywords.md` | ✅ |
| 3. Macros（mbe + proc macros） | `03_advanced/03_proc_macros/01_macros.md` · `02_proc_macro.md` | ✅ |
| 4. Crates and source files | `01_foundation/07_modules_and_items/11_crates_and_source_files.md` | ✅ |
| 5. Conditional compilation | `03_advanced/03_proc_macros/11_conditional_compilation.md` | ✅ |
| 6. Items（15 节：modules/extern crates/use/fn/type aliases/structs/enums/unions/const/static/traits/impls/extern blocks/generic params/associated items） | `01_foundation/07_modules_and_items/01–12` + `04_formal/05_rustc_internals/11_items_reference.md` | ✅ |
| 7. Attributes（testing/derive/diagnostics/codegen/limits/type system/debugger 七类） | `04_formal/05_rustc_internals/12_attributes.md` · `02_intermediate/06_macros_and_metaprogramming/06_attributes_by_category.md` | ✅ |
| 8. Statements and expressions（全部 19 种表达式） | `01_foundation/04_control_flow/03_statements_and_expressions.md` · `04_formal/05_rustc_internals/13_statements_and_expressions_reference.md` | ✅ |
| 9. Patterns | `01_foundation/04_control_flow/02_patterns.md` · `14_patterns_reference.md` | ✅ |
| 10. Type system（types/DST/layout/interior mutability/variance/bounds/coercions/divergence/destructors/elision） | `01_foundation/02_type_system/01–05` · `04_formal/05_rustc_internals/08_type_layout.md` · `09_destructors.md` · `04_formal/00_type_theory/02_subtype_variance.md` | ✅ |
| 11. Special types and traits | `04_formal/05_rustc_internals/07_special_types_and_traits.md` | ✅ |
| 12. Names（namespaces/scopes/preludes/paths/resolution/visibility） | `04_formal/05_rustc_internals/16_names_reference.md` · `06_names_and_resolution.md` · `01_foundation/07_modules_and_items/10_preludes.md` · `03_advanced/06_low_level_patterns/10_visibility_and_privacy.md` | ✅ |
| 13. Memory model（allocation & lifetime/variables） | `03_advanced/02_unsafe/06_memory_model.md` · `08_memory_allocation_and_lifetime.md` · `09_variables.md` | ✅ |
| 14. Panic | `02_intermediate/03_error_handling/03_panic.md` · `01_foundation/08_error_handling/03_panic_and_abort.md` | ✅ |
| 15. Linkage | `03_advanced/04_ffi/03_linkage.md` | ✅ |
| 16. Inline assembly | `03_advanced/05_inline_assembly/01_inline_assembly.md` | ✅ |
| 17. Unsafety（unsafe keyword/UB/not-unsafe） | `03_advanced/02_unsafe/01_unsafe.md` · `07_unsafe_reference.md` · `04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | ✅ |
| 18. Constant evaluation | `04_formal/03_operational_semantics/07_constant_evaluation.md` | ✅ |
| 19. ABI | `04_formal/05_rustc_internals/05_application_binary_interface.md` | ✅ |
| 20. The Rust runtime | `03_advanced/06_low_level_patterns/07_rust_runtime.md` | ✅ |
| 21. Appendices（grammar/syntax index/macro follow-set/influences/test summary/glossary） | `04_formal/05_rustc_internals/17_reference_appendices.md` | ✅ |

---

## 2. TRPL 3rd Edition — 21 章：17 ✅ / 4 ⚠️ / 0 ❌

复用 `docs/03_reference/07_trpl_3rd_ed_diff.md` 逐章映射（本轮已核对路径有效性）：

- **✅ 17 章**：Ch3–11、Ch13、Ch15、Ch16、Ch18、Ch19、Ch21 及 **Ch14**（本轮升级：`06_ecosystem/01_cargo/16_cargo_workflow.md` 统一教程页已存在，映射文件已同步更新）。
- **⚠️ 4 章（项目驱动叙事差异，非概念缺口，评估不建页）**：Ch1 Getting Started（安装/Hello World 属 `docs/` 指南范畴）、Ch2 Guessing Game、Ch12 CLI 项目、Ch20 多线程 Web Server（渐进式项目教学，`examples/comprehensive_web_server.rs` + MVP 学习路径覆盖，缺“同步逐步代码”属教学形态差异）。

---

## 3. The Rustonomicon — 12 章全 ✅（2 项本轮由 ⚠️ 深化）

| 章 | concept/ 权威页 | 档 |
|:---|:---|:---:|
| 1. Meet Safe and Unsafe | `03_advanced/02_unsafe/01_unsafe.md` · `02_unsafe_boundary_panorama.md` | ✅ |
| 2. Data Layout（repr(Rust)/exotically sized/other reprs） | `04_formal/05_rustc_internals/08_type_layout.md` | ✅ |
| 3. Ownership（references/aliasing/lifetimes/limits/elision/**unbounded**/HRTB/variance/drop check/PhantomData/splitting borrows） | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` · `04_lifetimes_advanced.md`（§十九 无界生命周期**本轮新增**）· `04_formal/00_type_theory/02_subtype_variance.md` · `01_foundation/02_type_system/01_type_system.md`（PhantomData/dropck） | ✅ |
| 4. Type Conversions（coercions/dot operator/casts/transmutes） | `01_foundation/02_type_system/04_coercion_and_casting.md` · `01_foundation/03_values_and_references/01_reference_semantics.md` · `03_advanced/02_unsafe/01_unsafe.md`（transmute） | ✅ |
| 5. Uninitialized Memory（checked/**drop flags**/unchecked） | `02_intermediate/02_memory_management/01_memory_management.md`（MaybeUninit）· `04_formal/05_rustc_internals/09_destructors.md`（§十一 Drop Flags**本轮新增**） | ✅ |
| 6. OBRM（constructors/destructors/leaking） | `02_intermediate/00_traits/05_construction_and_initialization.md` · `09_destructors.md` | ✅ |
| 7. Unwinding（exception safety/poisoning） | `02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md` · `03_panic.md` | ✅ |
| 8. Concurrency（races/Send+Sync/atomics） | `03_advanced/00_concurrency/01_concurrency.md` · `02_send_sync_auto_traits.md` · `05_atomics_and_memory_ordering.md` | ✅ |
| 9. Implementing Vec | `03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md` | ✅ |
| 10. Implementing Arc and Mutex | 同上（§3 Arc 核心结构） | ✅ |
| 11. FFI | `03_advanced/04_ffi/01_rust_ffi.md` · `02_ffi_advanced.md` | ✅ |
| 12. Beneath std（`#![panic_handler]`） | `01_foundation/08_error_handling/03_panic_and_abort.md` · `03_advanced/06_low_level_patterns/07_rust_runtime.md` | ✅ |

---

## 4. Rust RFC Book（2023–2026 merged，语义重要 40 项）

筛选口径：GitHub API 列出 `rust-lang/rfcs` `text/` 目录 ≥3400 号全部 merged RFC（75 项），剔除治理/团队/流程类（如 3463/3533/3595/3599/3614/3646/3660/3671/3672/3673/3678/3691/3764/3771/3817/3841/3849/3855/3872 等）与已被版本页吸收的库级小项，保留 40 项语言/类型/内存/Cargo 语义相关 RFC。

### 4.1 本轮 ❌ → 新建权威页（4 项）

| RFC | 主题 | 新权威页 | 实测 |
|:---|:---|:---|:---|
| [3453](https://rust-lang.github.io/rfcs/3453-f16-and-f128.html) | `f16`/`f128` 浮点类型 | `concept/07_future/03_preview_features/35_f16_f128_preview.md` | nightly 1.99.0 `--edition 2024` 编译通过；stable 1.97 按预期 E0658 |
| [3467](https://rust-lang.github.io/rfcs/3467-unsafe-pinned.html) | `UnsafePinned` 别名语义 | `.../36_unsafe_pinned_preview.md` | 同上（`#![feature(unsafe_pinned)]`） |
| [3681](https://rust-lang.github.io/rfcs/3681-default-field-values.html) | 结构体字段默认值 | `.../37_default_field_values_preview.md` | 同上（`#![feature(default_field_values)]`） |
| [3892](https://rust-lang.github.io/rfcs/3892-complex-numbers.html) | 标准库复数类型 | `.../38_complex_numbers_preview.md` | RFC accepted 未实现，设计跟踪页（草案 API 标注 ignore） |

### 4.2 本轮 ⚠️ → 深化既有页（6 项）

| RFC | 主题 | 深化位置 | 实测 |
|:---|:---|:---|:---|
| [3695](https://rust-lang.github.io/rfcs/3695-cfg-boolean-literals.html) | `cfg(true)`/`cfg(false)` 布尔字面量（1.88 稳定） | `03_advanced/03_proc_macros/11_conditional_compilation.md` 新增「布尔字面量谓词」节 | rustc 1.97.0 stable 实测通过 |
| [3624](https://rust-lang.github.io/rfcs/3624-supertrait-item-shadowing-v2.html) | Supertrait 条目遮蔽 v2 | `02_intermediate/00_traits/01_traits.md` §4.5.1 | rustc 1.97.0 stable 实测通过 |
| [3923](https://rust-lang.github.io/rfcs/3923-cargo-min-publish-age.html) | Cargo 最小发布时间（依赖冷却） | `06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md` §八 | 引文链接 curl 200 |
| [3416](https://rust-lang.github.io/rfcs/3416-feature-metadata.html) | Feature 元数据 | `04_formal/05_rustc_internals/12_attributes.md` 新增小节 | 同上 |
| [3722](https://rust-lang.github.io/rfcs/3722-explicit-extern-abis.html) | 显式 extern ABI | `03_advanced/04_ffi/03_linkage.md` 新增小节 | 同上 |
| [3697](https://rust-lang.github.io/rfcs/3697-declarative-attribute-macros.html)/[3698](https://rust-lang.github.io/rfcs/3698-declarative-derive-macros.html) | 声明式属性/derive 宏 | `03_advanced/03_proc_macros/01_macros.md` §6 补 RFC 引文 | 同上 |

### 4.3 既有 ✅（30 项，抽样）

3424/3502/3503 cargo script+frontmatter → `01_cargo_script.md`；3425 RPITIT → `15_rpitit_preview.md`；3458 unsafe fields → `11_unsafe_fields_preview.md`；3484 unsafe extern blocks → `02_edition_guide.md`+`01_rust_ffi.md`；3498/3617 lifetime capture+`use<>` → `13_lifetime_capture_preview.md`；3501/3509 edition 2024+prelude → `02_edition_guide.md`+`10_preludes.md`；3513 gen blocks → `25_gen_blocks_preview.md`；3514 float semantics → `03_numerics.md`；3516 public-private deps → `02_public_private_deps.md`；3519 arbitrary self types → `18_arbitrary_self_types_preview.md`；3535 constants in patterns → `08_inline_const_pattern_preview.md`；3537 MSRV resolver → `06_cargo_dependency_resolution.md`；3550 `core::range` → `01_range_types.md`；3559 provenance → `06_memory_model.md`+`semantic_space.md`；3606 tail-expr temporaries → `02_edition_guide.md` §2.4；3621 derive smart pointer → `05_derive_coerce_pointee_preview.md`；3627 match ergonomics 2024 → `02_edition_guide.md`+`01_reference_semantics.md`；3637 guard patterns → `rust_1_95_stabilized.md` §1.2；3654 RTN → `09_return_type_notation_preview.md`；3668 async closures → `07_async_closures.md`；3692 resolver v3 feature unification → `03_resolver_v3_public_feature_unification.md`；3873–3875 build-std → `22_build_std.md`；3848 asm const → `01_inline_assembly.md`（`const` 操作数已含）。

### 4.4 经评估不建页（7 项，❌-minor：未稳定且影响面小）

| RFC | 主题 | 不建页理由 |
|:---|:---|:---|
| 3491 | Remove implicit features | `dep:` 语法已在 `10_cargo_manifest_reference.md` 覆盖；移除计划未稳定，待落地后并入该页 |
| 3716 | Target modifiers | `#[target_feature]` 修饰符，nightly-only，影响面限于 SIMD 专家；已在 inline assembly/UB 页间接受益 |
| 3721 | Homogeneous try blocks | `try` 块均质化，nightly-only 语法微调 |
| 3772 / 3791 / 3808 / 3834 | build-target-edition / crate-attr / register-tool / export-visibility | 均为 accepted-未实现的 Cargo/rustc 小特性；稳定后评估并入对应 Cargo/属性页 |

---

## 5. The Cargo Book — 全 ✅

| Cargo Book 部 | concept/ 权威页 |
|:---|:---|
| Getting Started | `06_ecosystem/01_cargo/15_cargo_getting_started.md` |
| Cargo Guide（first steps/deps/layout/manifest/tests/CI/publishing/features/workspaces/env/config） | `16_cargo_workflow.md` · `17_cargo_guide_practices.md` · `14_cargo_workspaces.md` · `18_cargo_configuration.md` |
| Cargo Reference（manifest/targets/features/profiles/config/build scripts/registries/resolution/semver/package ID/source replacement/lints/build cache） | `10_cargo_manifest_reference.md` · `20_cargo_manifest_targets.md` · `11_cargo_profiles_and_lints.md` · `05_cargo_build_scripts.md` · `08_cargo_registries_and_publishing.md` · `06_cargo_dependency_resolution.md` · `07_cargo_source_replacement.md` · `09_cargo_authentication_and_cache.md` · `21_cargo_registry_internals.md` |
| Cargo Commands | `19_cargo_commands_reference.md` · `12_cargo_subcommands_and_plugins.md` |
| FAQ / Glossary / Git auth | `14_cargo_workspaces.md`（FAQ 段）· `09_cargo_authentication_and_cache.md` |
| 扩展（script/public deps/resolver v3/CVE/build-std/1.96） | `01–04` · `13` · `22` |

---

## 6. 缺口处置汇总

**新建权威页（4）**（均遵守 AGENTS.md §4.2 元数据模板；外链 curl 200 实测；代码 nightly 1.99.0 实测）：

1. `concept/07_future/03_preview_features/35_f16_f128_preview.md`（RFC 3453）
2. `concept/07_future/03_preview_features/36_unsafe_pinned_preview.md`（RFC 3467）
3. `concept/07_future/03_preview_features/37_default_field_values_preview.md`（RFC 3681）
4. `concept/07_future/03_preview_features/38_complex_numbers_preview.md`（RFC 3892）

**深化既有页（8）**：`11_conditional_compilation.md`（RFC 3695）、`01_traits.md`（RFC 3624）、`08_cargo_registries_and_publishing.md`（RFC 3923）、`12_attributes.md`（RFC 3416）、`03_linkage.md`（RFC 3722）、`01_macros.md`（RFC 3697/3698 引文）、`04_lifetimes_advanced.md`（§十九 无界生命周期，Nomicon 3.6）、`09_destructors.md`（§十一 Drop Flags，Nomicon 5.2）。

**索引/图谱同步**：`concept/SUMMARY.md` +4 条目（preview features 区）；`concept/00_meta/04_navigation/03_concept_index.md` +4 概念行；`kg_data_v3.json` +4 实体 +7 条 relatedTo 边（仿 `scripts/add_kg_category_nodes.py` 结构）；`concept/sources/rfc_index.md` 新增「七、2023–2026 重要已合并 RFC」表（16 行）；`docs/03_reference/07_trpl_3rd_ed_diff.md` Ch14 状态 ⚠️→✅。taxonomy.yaml 无需变更（无新目录）。

---

## 7. 验证证据（2026-07-12 实跑）

| 质量门 | 结果 |
|:---|:---|
| `mdbook build` | ✅ 通过（仅既有 search index 体积告警） |
| `python scripts/kb_auditor.py` | ✅ 死链 0 / 跨层 0 / 模板化 ⟹ 0 |
| `python scripts/check_canonical_uniqueness.py --strict` | ✅ exit 0，ERROR 0（WARN 224 为既有启发式噪音：`*_preview` 同后缀误判，较基线 +6 均来自本轮新页，非真实重复） |
| `python scripts/check_concept_authority_coverage.py --strict` | ✅ exit 0：any=100% / none=0 / 核心 L1–L4 无 P0 缺口=0（较 AGENTS §5.2 记录的 07-12 退化基线 any=99.5%/none=2/缺口=1 **已恢复达标**） |
| `python scripts/check_kg_shapes.py --strict` | ✅ exit 0：K1–K7 全 0（entities 495 / relations 5860） |
| `python scripts/detect_content_overlap.py` | ✅ exit 0 |
| `python scripts/add_bilingual_annotations.py --mode check-only` | ✅ exit 0：缺 EN 0 / 缺 Summary 0 |
| `python scripts/check_topology_quality.py --strict` | ✅ exit 0：T1–T6 全达标 |
| `python scripts/concept_consistency_auditor.py --strict` | ✅ exit 0：无效引用 0 / 错误 0 |

**外链实测**：全部新增引文（RFC 3453/3467/3416/3624/3681/3695/3697/3698/3722/3892/3923、Nomicon/Reference/std docs 各页）curl 实测 HTTP 200；`crates.io` 因反爬 403 已替换为 `docs.rs/num-complex`（200）；GitHub issue #125735/#137750 HTML 页在本环境偶发 000（反爬），经 GitHub API 验证两 issue 均存在。

**代码实测**：`rustc 1.97.0 --edition 2024`（stable）验证 cfg 布尔字面量与 supertrait 遮蔽示例通过；`rustc 1.99.0-nightly (375b1431b 2026-07-10)` 验证 f16/f128、UnsafePinned、default field values 示例通过；stable 对三者的 E0658 报错亦实测确认并写入页面。
