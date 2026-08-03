# 语义对齐基线审计报告

**EN**: Semantic Alignment Baseline Audit Report
**Summary**: Quantified baseline of concept authority, version injection, cross-domain coverage, overlap, stub purity, naming, metadata, and code-block health before the alignment sprint.

> 生成时间: see file mtime

| 审计项 | 退出码 | 日志 |
|--------|--------|------|
| Concept authority coverage (--include-crates) | 0 | `tmp\semantic_baseline\authority.log` |
| Version semantic injection | 0 | `tmp\semantic_baseline\version.log` |
| Cross-domain semantic coverage | 0 | `tmp\semantic_baseline\cross_domain.log` |
| Content overlap v2 | 0 | `tmp\semantic_baseline\overlap.log` |
| Stub purity | 0 | `tmp\semantic_baseline\stub.log` |
| Naming convention | 0 | `tmp\semantic_baseline\naming.log` |
| Metadata consistency | 0 | `tmp\semantic_baseline\metadata.log` |
| Concept code blocks (stats-only) | 0 | `tmp\semantic_baseline\codeblocks_stats.log` |

## 详细日志摘要（尾部）

### Concept authority coverage (--include-crates) (rc=0)

```
[crates-authority] total=568 content=62 covered=62 (100.0%) gaps=0 dead_canonical=0
[concept-authority] scanned=658  P0=95.9%  P1=88.1%  P2=86.3%  any=100.0%  none=0
[concept-authority] content-scope n=563  P0=96.1%  P1=92.9%  P2=97.2%  any=100.0%
[concept-authority] core L1-L4 gaps (no P0): 0
[concept-authority] report: reports\CONCEPT_AUTHORITY_COVERAGE_2026-08-04.md
[concept-authority] PASS (--strict): any=100% none=0 core_gaps=0
```

### Version semantic injection (rc=0)

```
- `NonZero` 范围迭代 ← `00_meta/knowledge_topology/01_concept_definition_atlas.md`
- `From<T>` for `AssertUnwindSafe` / `LazyCell` / `LazyLock` → `02_intermediate/02_memory_management/02_interior_mutability.md`
- 「valid for read/write」定义重构 → `03_advanced/02_unsafe/06_memory_model.md`
- Cargo git + alternate registry 共存；CVE-2026-5222/5223 修复 → `06_ecosystem/01_cargo/06_cargo_dependency_resolution.md`

### 1.97
- `must_use` lint 扩展至 `Result<T, Uninhabited>` 与 `ControlFlow<Uninhabited, T>` (§2.1) → `01_foundation/04_control_flow/01_control_flow.md`
- `dead_code_pub_in_binary` lint (§2.2) → `06_ecosystem/00_toolchain/01_toolchain.md`
- 新稳定 target features (§2.3) → `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md`
- `cfg(target_has_atomic_primitive_alignment)` (§2.4) → `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md`
- import 中 `self` 的放宽 (§2.5) → `01_foundation/07_modules_and_items/11_crates_and_source_files.md`
- `{float}` 在未约束时回退到 `f32` (§2.6) → `01_foundation/02_type_system/03_numerics.md`
- v0 symbol mangling 默认启用 (§2.7) ← `03_advanced/04_ffi/03_linkage.md`
- 链接器输出默认显示 (`linker_messages` lint) (§2.8) ← `03_advanced/04_ffi/03_linkage.md`
- `nvptx64-nvidia-cuda` 基线提升 (§3.1) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- `Default for RepeatN` (§4.1) → `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md`
- `Copy for ffi::FromBytesUntilNulError` (§4.2) → `03_advanced/04_ffi/01_rust_ffi.md`
- `Send for std::fs::File` on UEFI (§4.3) → `06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`
- 整数位查询方法 (§4.4) → `01_foundation/02_type_system/03_numerics.md`
- `NonZero` 位查询方法 (§4.5) → `01_foundation/02_type_system/03_numerics.md`
- `char::is_control` 在 const 上下文稳定 (§4.6) → `01_foundation/06_strings_and_text/01_strings_and_text.md`
- `build.warnings` 配置 (§5.1) ← `06_ecosystem/00_toolchain/01_toolchain.md`, `06_ecosystem/01_cargo/23_cargo_197_features.md`, `07_future/05_quizzes/01_quiz_version_and_preview.md`
- `resolver.lockfile-path` 配置 (§5.2) ← `06_ecosystem/00_toolchain/01_toolchain.md`, `06_ecosystem/01_cargo/23_cargo_197_features.md`
- `cargo-clean` 目标目录校验 (§5.3) ← `06_ecosystem/01_cargo/23_cargo_197_features.md`
- `-m` 简写 (§5.4) → `06_ecosystem/01_cargo/19_cargo_commands_reference.md`
- `crates-io` 移除 `curl` 依赖 (§5.5) ← `06_ecosystem/01_cargo/23_cargo_197_features.md`
- `--emit` 标志 (§6.1) → `06_ecosystem/00_toolchain/07_rustdoc_196_changes.md`
- `--remap-path-prefix` (§6.2) ← `06_ecosystem/00_toolchain/07_rustdoc_196_changes.md`, `07_future/05_quizzes/01_quiz_version_and_preview.md`
- `pin!` 示例 (§7.1) ← `00_meta/knowledge_topology/04_example_counterexample_atlas.md`
- 空 `export_name` 示例 (§7.2) ← `00_meta/knowledge_topology/04_example_counterexample_atlas.md`

## 已映射 beta 特性（按版本分组）

### 1.98（beta）
- riscv: `d`, `e`, and `f` target_features are now stable in `cfg(target_feature = "?")` (§1.1) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Add deny-by-default `invalid_runtime_symbol_definitions` lint and warn-by-default `suspicious_runtime_symbol_definitions` lint (§1.2) → `03_advanced/04_ffi/01_rust_ffi.md`, `03_advanced/04_ffi/03_linkage.md`
- Allow shortening lifetime of `&mut` when unsize-coercing, even in an invariant position (§1.3) → `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`, `02_intermediate/04_types_and_conversions/07_type_conversions.md`
- Partially convert `ambiguous_glob_imports` lint into a hard error (§1.4) → `02_intermediate/05_modules_and_visibility/01_module_system.md`
- Lint on `core::ffi::c_void` as a return type (§1.5) → `03_advanced/04_ffi/01_rust_ffi.md`
- Where-bounds of the form `Type = Type` and `Type == Type` are no longer syntactically allowed (§1.6) → `02_intermediate/00_traits/01_traits.md`
- `repr(transparent)` stricter rules for trivial layout fields (§1.7) → `03_advanced/02_unsafe/06_memory_model.md`
- Add `T: PartialEq` bounds to derived `StructuralPartialEq` impls (§1.8) → `02_intermediate/00_traits/06_derive_traits.md`
- Fix parser error recovery treating `dyn` as a strict keyword (§1.9) → `02_intermediate/00_traits/01_traits.md`
- Resolver: Batched Import Resolution (§1.10) → `02_intermediate/05_modules_and_visibility/01_module_system.md`
- Reject arguments in attributes where no arguments are expected (§1.11) → `01_foundation/09_macros_basics/01_attributes_and_macros.md`
- Change `Location<'_>` lifetime to `'static` in `PanicHookInfo` (§1.12) → `02_intermediate/03_error_handling/03_panic.md`
- Windows-gnu targets now specify baseline tools versions (§2.1) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- On Emscripten the WASM exception handling ABI is now unconditionally used (§2.2) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Switch the destructors implementation for thread locals on Windows to use FLS (§2.3) → `04_formal/05_rustc_internals/09_destructors.md`
- Solaris: remove `File::lock` implementation, it has the wrong semantics (§2.4) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Document panic in `RangeInclusive::from(legacy::RangeInclusive)` (§3.1) → `02_intermediate/04_types_and_conversions/01_range_types.md`
- Add temporary scope to `assert_eq!` and `assert_ne!` (§3.2) → `02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md`
- Document that `ManuallyDrop`'s `Box` interaction has been fixed (§3.3) → `04_formal/05_rustc_internals/09_destructors.md`
- Ensure `Send`/`Sync` is not implemented for `std::env::Vars{,Os}` (§3.4) → `03_advanced/00_concurrency/02_send_sync_auto_traits.md`, `03_advanced/00_concurrency/04_send_sync_boundaries.md`
- Ensure `Send`/`Sync` impl for `std::process::CommandArgs` (§3.5) → `03_advanced/08_process_ipc/01_process_model_and_lifecycle.md`, `03_advanced/00_concurrency/02_send_sync_auto_traits.md`
- `String::from_utf16le` / `from_utf16be` / `_lossy` variants (§3.6) → `01_foundation/06_strings_and_text/02_strings_and_encoding.md`
- `str::strip_circumfix` (§3.7) → `01_foundation/06_strings_and_text/02_strings_and_encoding.md`
- `NonZero*` integer types: `from_str_radix` (§3.8) → `01_foundation/02_type_system/03_numerics.md`
- `{f32,f64}::algebraic_{add,sub,mul,div,rem}` (§3.9) → `01_foundation/02_type_system/03_numerics.md`
- LoongArch CRC intrinsics (§3.10) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Replace printables table with `unicode_data.rs` tables (§3.11) → `01_foundation/06_strings_and_text/02_strings_and_encoding.md`
- Implement fast path for `derive(PartialOrd)` when deriving `Ord` (§4.1) → `02_intermediate/00_traits/06_derive_traits.md`
- `derive(PartialOrd)` 快速路径暴露 `PartialOrd`/`Ord` 不一致 (§5.1) → `02_intermediate/00_traits/06_derive_traits.md`
- `repr(transparent)` 对 trivial 布局字段更严格 (§5.2) → `03_advanced/02_unsafe/06_memory_model.md`
- 等式谓词 `Type = Type` / `Type == Type` 被语法层拒绝 (§5.3) → `02_intermediate/00_traits/01_traits.md`
- Trait object 完全省略生命周期时推断更严格 (§5.4) → `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`, `02_intermediate/00_traits/01_traits.md`
- `transmute()` 在涉及 `repr` 属性时更严格地检查等大小 (§5.5) → `03_advanced/02_unsafe/06_memory_model.md`, `03_advanced/04_ffi/01_rust_ffi.md`
- `UNSAFE_CODE` lint 一致地覆盖所有 unsafe attributes (§5.6) → `03_advanced/02_unsafe/01_unsafe.md`, `01_foundation/09_macros_basics/01_attributes_and_macros.md`
- `ambiguous_glob_imports` 部分转为硬错误 (§5.7) → `02_intermediate/05_modules_and_visibility/01_module_system.md`
- 不接受参数的属性被传参时直接报错 (§5.8) → `01_foundation/09_macros_basics/01_attributes_and_macros.md`
- Windows-gnu 指定最低 mingw-w64 工具链版本 (§5.9) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Solaris/Illumos 移除 `File::lock` 实现 (§5.10) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- Emscripten 无条件使用 WASM 异常处理 ABI (§5.11) → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`

## 维护说明

- 未映射特性需在版本跟踪页添加指向 `concept/` 权威页的链接，
  或在对应 concept/ 权威页增加版本兼容性小节并回链版本页。
- 本脚本逻辑见 `scripts/check_version_semantic_injection.py`。

```

### Cross-domain semantic coverage (rc=0)

```
# Cross-Domain Semantic Coverage Baseline Report (2026_08_04)

> 检查 Rust 1.97 关键交叉/边界语义域在 `concept/` 中是否有非 stub 权威页。

## 汇总

- 总主题数：16
- 已覆盖：16 (100.0%)
- 未覆盖：0

## 未覆盖主题

未发现。
## 已覆盖主题

- ✅ `01_foundation/04_control_flow/03_let_chains.md` — let chains / if-let guards
- ✅ `03_advanced/04_ffi/05_unsafe_extern_blocks.md` — unsafe extern blocks (Edition 2024)
- ✅ `03_advanced/02_unsafe/08_async_in_unsafe_contexts.md` — async + unsafe boundary
- ✅ `03_advanced/04_ffi/04_async_ffi_boundary.md` — FFI + async boundary
- ✅ `06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md` — no_std + async
- ✅ `02_intermediate/01_generics/05_const_generics_and_trait_objects.md` — const generics + trait objects
- ✅ `03_advanced/01_async/14_gat_async_boundary.md` — GAT + async
- ✅ `03_advanced/00_concurrency/04_send_sync_boundaries.md` — Send/Sync boundary in trait objects / closures / async state machines
- ✅ `03_advanced/01_async/11_pin_projection_counterexamples.md` — Pin projection + structural projection
- ✅ `03_advanced/06_low_level_patterns/01_custom_allocators.md` — allocator_api / per-container allocators
- ✅ `01_foundation/04_control_flow/02_patterns.md` — match ergonomics / default binding mode in Edition 2024
- ✅ `04_formal/05_rustc_internals/09_destructors.md` — temporary scope / tail expression drop (Edition 2024)
- ✅ `07_future/02_preview_features/06_const_trait_impl_preview.md` — const trait impl (effects system)
- ✅ `07_future/02_preview_features/17_type_alias_impl_trait_preview.md` — RTN / RPITIT / TAIT precise capturing
- ✅ `03_advanced/01_async/01_async.md` — async fn / Future equivalence + Send across await
- ✅ `03_advanced/02_unsafe/01_unsafe.md` — unsafe op in unsafe fn (Edition 2024)

## 主题清单维护说明

清单位于 `scripts/check_cross_domain_coverage.py` 的 `CROSS_DOMAIN_TOPICS` 字典。
新增主题时，需给出候选 `concept/` 权威页路径；覆盖标准：任一候选存在且非 stub。

```

### Content overlap v2 (rc=0)

```
[P0-3] scanned=2003 indexed=1586 candidates=667016 hits=509 (same_dir=509 cross_dir=0) threshold=0.5
[P0-3] report: reports/CONTENT_OVERLAP_V2_2026-08-04.md
   [1.0] concept/07_future/00_version_tracking/rust_1_100_preview.md  <->  concept/07_future/00_version_tracking/rust_1_99_preview.md
   [1.0] crates/c10_networks/docs/07_rust_190_examples_collection.md  <->  crates/c10_networks/docs/08_rust_190_examples_part2.md
   [0.889] crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md  <->  crates/c09_design_pattern/docs/15_rust_190_comprehensive_enhancement_report.md
   [0.846] crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md  <->  crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md
   [0.846] crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md  <->  crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md
   [0.821] docs/05_practice/06_project_05_text_statistics.md  <->  docs/05_practice/14_project_13_database_engine.md
   [0.818] crates/c05_threads/docs/tier_01_foundations/02_navigation.md  <->  crates/c05_threads/docs/tier_01_foundations/03_glossary.md
   [0.818] crates/c04_generic/docs/00_master_index.md  <->  crates/c04_generic/docs/tier_01_foundations/01_project_overview.md
```

### Stub purity (rc=0)

```
# Stub Purity Baseline Report (2026_08_04)

> 依据 AGENTS.md §2 Canonical 规则与 §3.3 重定向 stub 模板：
> knowledge/docs/content/crates docs 中的 stub/redirect 文件不应保留通用概念完整正文。

## 汇总

- 扫描页数：1034
- 伪 stub（声明为 stub 但正文过长）：0
- 空壳页（未声明 stub 但正文极短）：0
- 高重复正文（vs concept/ 权威页相似度 > 0.25）：0

## 伪 stub (0)

未发现。

## 空壳页 (0)

未发现。

## 高重复正文 (0)

未发现。

## 判定标准

- 声明为 stub：正文含任一标记（如『本文件为学习入口 stub』、『redirect』等）。
- 伪 stub：声明为 stub，但去元数据后正文 > 25 行 或 > 2000 字节。
- 空壳页：未声明 stub，但去元数据后正文 < 5 行。
- 高重复正文：去代码块后与 concept/ 权威页相似度 > 0.25。

```

### Naming convention (rc=0)

```
[check_naming_convention] 扫描 23 个根目录: 1886 文件 / 243 目录
汇总: ERROR=0  WARN=0
✅ 命名规范检查通过（无 ERROR）。
```

### Metadata consistency (rc=0)

```
[P0-1] scanned=693 flagged_files=1
  D1 count=0 pct=0.0%  (Bloom 层级 ↔ 层次定位/层级 同文件互斥)
  D2 count=0 pct=0.0%  (A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）)
  D3 count=0 pct=0.0%  (关键字段同文件重声明)
  D4 count=0 pct=0.0%  (文首块 Rust 版本号自矛盾)
  D5 count=0 pct=0.0%  (稳定层正文残留 nightly/preview/unstable)
  D6 count=1 pct=0.1%  (Summary 低信息量模板套话)
  D2 base(asp&bloom)=409
[P0-1] report: reports/METADATA_CONSISTENCY_BASELINE_2026-08-04.md
```

### Concept code blocks (stats-only) (rc=0)

```
[extract] files=691 blocks=6579
  anno_ignore    2623
  compile_fail   1045
  pseudo         15
  nightly        35
  nostd          10
  dep_skip       31
  dep_untested   90
  dep            230
  candidate      2500
```
