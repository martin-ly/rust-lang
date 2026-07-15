# Version Semantic Injection Baseline Report (2026_07_15)

> 检查 Rust 1.90–1.97 稳定特性在版本跟踪页与 `concept/` 权威页之间的双向链接覆盖。

## 汇总

- 版本范围：1.90 – 1.97（共 8 个稳定版本）
- 提取特性数：74
- 已映射：74 (100.0%)
- 未映射：0

## 未映射特性

无。所有提取特性均已建立 concept/ 前向链接或存在带特征提及的 concept/ 回链。

## 已映射特性（按版本分组）

### 1.90

- `x86_64-unknown-linux-gnu` 默认使用 lld 链接器 → `03_advanced/04_ffi/03_linkage.md`
- `u{N}::{checked,overflowing,saturating,wrapping}_sub_signed` ← `01_foundation/02_type_system/03_numerics.md`
- `CStr` / `CString` / `Cow<CStr>` 互比 → `03_advanced/04_ffi/01_rust_ffi.md`
- `f32`/`f64` `floor`/`ceil`/`trunc`/`fract`/`round`/`round_ties_even` 进入 const → `01_foundation/02_type_system/03_numerics.md`
- Cargo 多包发布稳定（multi-package publishing） → `06_ecosystem/01_cargo/19_cargo_commands_reference.md`
- `x86_64-apple-darwin` 降为 Tier 2（含 host tools） → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`

### 1.91

- C 风格可变参数函数稳定（`sysv64`/`win64`/`efiapi`/`aapcs` ABI） → `03_advanced/04_ffi/01_rust_ffi.md`
- `dangling_pointers_from_locals` lint → `03_advanced/02_unsafe/01_unsafe.md`
- `{integer}::strict_*` 系列方法 → `01_foundation/02_type_system/03_numerics.md`
- `AtomicPtr::fetch_ptr_add/sub`、`fetch_or/and/xor` → `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md`
- `ptr::with_exposed_provenance(_mut)` → `03_advanced/02_unsafe/06_memory_model.md`
- Cargo `build.build-dir` 稳定 → `06_ecosystem/01_cargo/18_cargo_configuration.md`
- 内部升级 LLVM 21 → `06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md`

### 1.92

- `MaybeUninit` 表示与有效性正式文档化 → `03_advanced/02_unsafe/01_unsafe.md`
- 安全代码允许对联合体字段取 `&raw const/mut` → `03_advanced/02_unsafe/01_unsafe.md`
- 同一关联项允许多个边界（trait 对象除外） → `01_foundation/02_type_system/01_type_system.md`, `02_intermediate/00_traits/01_traits.md`
- `Box/Rc/Arc::new_zeroed(_slice)` ← `03_advanced/02_unsafe/01_unsafe.md`
- `RwLockWriteGuard::downgrade` → `03_advanced/00_concurrency/03_concurrency_patterns.md`
- `iter::Repeat::last/count` 改为 panic（兼容性变更） → `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md`
- `Location::file_as_c_str` → `02_intermediate/03_error_handling/03_panic.md`

### 1.93

- `asm_cfg` 稳定 → `03_advanced/02_unsafe/01_unsafe.md`, `03_advanced/05_inline_assembly/01_inline_assembly.md`
- `system` ABI C 风格可变参数函数稳定 → `03_advanced/04_ffi/01_rust_ffi.md`
- `MaybeUninit` 切片 API（`assume_init_ref/mut`、`write_copy/clone_of_slice`、`assume_init_drop`） → `03_advanced/02_unsafe/01_unsafe.md`
- `String::into_raw_parts` / `Vec::into_raw_parts` → `03_advanced/04_ffi/01_rust_ffi.md`
- `<[T]>::as_array` / `as_mut_array` → `01_foundation/05_collections/01_collections.md`
- `fmt::from_fn` / `fmt::FromFn` → `01_foundation/06_strings_and_text/03_formatting_and_display.md`
- `-Cjump-tables` 稳定（原 `-Zno-jump-tables`） → `06_ecosystem/00_toolchain/01_toolchain.md`
- `cargo clean --workspace` → `06_ecosystem/01_cargo/19_cargo_commands_reference.md`

### 1.94

- 29 个 RISC-V target feature 稳定（含 RVA22U64 / RVA23U64 profile 大部） → `06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`
- `<[T]>::array_windows` → `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md`
- `LazyCell` / `LazyLock::get` / `get_mut` / `force_mut` → `02_intermediate/02_memory_management/02_interior_mutability.md`
- `f32` / `f64::mul_add` → `01_foundation/02_type_system/03_numerics.md`
- `EULER_GAMMA` / `GOLDEN_RATIO` 浮点常量 → `01_foundation/02_type_system/03_numerics.md`
- Cargo `include` 配置键稳定 + TOML v1.1 解析 → `06_ecosystem/01_cargo/18_cargo_configuration.md`
- std 宏改为经 prelude 导入（兼容性变更） → `01_foundation/07_modules_and_items/10_preludes.md`, `01_foundation/09_macros_basics/01_attributes_and_macros.md`

### 1.95

- `cfg_select!` 宏 ← `00_meta/knowledge_topology/01_concept_definition_atlas.md`, `01_foundation/09_macros_basics/01_attributes_and_macros.md`
- `if let` guards on match arms → `01_foundation/04_control_flow/01_control_flow.md`
- 路径段关键字重命名导入 ← `00_meta/knowledge_topology/01_concept_definition_atlas.md`, `01_foundation/04_control_flow/01_control_flow.md`
- `core::range` 模块 → `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md`
- 原子 `update` / `try_update` → `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md`
- `Vec::push_mut` 等可变引用插入 → `01_foundation/05_collections/01_collections.md`
- `as_ref_unchecked` / `as_mut_unchecked` → `03_advanced/02_unsafe/01_unsafe.md`
- `--remap-path-scope` 稳定 → `03_advanced/04_ffi/03_linkage.md`

### 1.96

- `assert_matches!` / `debug_assert_matches!` → `02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md`
- `expr` metavariable 传入 `cfg` → `03_advanced/03_proc_macros/01_macros.md`
- `core::range` Copy 类型 → `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md`
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

## 维护说明

- 未映射特性需在版本跟踪页添加指向 `concept/` 权威页的链接，
  或在对应 concept/ 权威页增加版本兼容性小节并回链版本页。
- 本脚本逻辑见 `scripts/check_version_semantic_injection.py`。
