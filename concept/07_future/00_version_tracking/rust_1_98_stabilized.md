# Rust 1.98.0 稳定特性

> **EN**: Rust 1.98.0 Stabilized Features
> **Summary**: Rust 1.98.0 (stable 2026-08-20) 完整稳定特性汇总：语言语义、编译器/平台、标准库 API、宏/derive 与兼容性变更，均附权威来源与迁移要点。
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [综述级]
> **权威来源**: 本文件为 `concept/` 权威页（Rust 1.98 稳定特性的 canonical 汇总；基于 1.98.0 beta/RC 国际来源最终核对，稳定生效日为 2026-08-20）。
> **Rust 版本**: **1.98.0 stable**（基于 beta/RC；预计 2026-08-20 发布）
> **最后更新**: 2026-07-31
> **状态**: 🔄 基于 1.98.0 beta/RC 预填充；特性正文已按语言语义、编译器/平台、标准库/文档、宏/Derive、兼容性变更五组重新组织
>
> **权威来源**:
>
> · [Rust 1.98.0 Release Notes (beta)](https://releases.rs/docs/1.98.0/) ·
> [Rust Release Notes](https://doc.rust-lang.org/beta/releases.html) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [RFC Book](https://rust-lang.github.io/rfcs/) ·
> [Rust Blog](https://blog.rust-lang.org/) ·
> [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) ·
> [The Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/) ·
> [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) ·
> [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
> **后置概念**: [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md) · [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)

---

## 0. 1.98 特性矩阵

> **状态图例**：✅ = 已稳定（beta/RC 实测或 release notes 跟踪 issue 确认） · ⚠ = 兼容性变更
>
> **主要领域**：Lang = 语言语义 · Compiler/Platform = 编译器与平台 · Std API = 标准库 API · Macro/Derive = 宏与 Derive · Compat = 兼容性与破坏性变更

| # | 特性 | 主要领域 | 状态 | 权威来源 / 跟踪链接 / 相关概念 |
|:---:|:---|:---|:---|:---|
| 1 | riscv: `d`, `e`, and `f` target_features stable in `cfg(target_feature = "?")` | Lang | ✅ stabilized | [PR #156188](https://github.com/rust-lang/rust/pull/156188) · [#157534](https://github.com/rust-lang/rust/issues/157534) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 2 | Add `invalid_runtime_symbol_definitions` (deny) and `suspicious_runtime_symbol_definitions` (warn) lints | Lang | ✅ stabilized | [PR #155521](https://github.com/rust-lang/rust/pull/155521) · [#156519](https://github.com/rust-lang/rust/issues/156519) · [FFI/linkage](../../03_advanced/04_ffi/03_linkage.md) |
| 3 | Allow shortening lifetime of `&mut` when unsize-coercing, even in invariant position | Lang | ✅ stabilized | [PR #149219](https://github.com/rust-lang/rust/pull/149219) · [#156457](https://github.com/rust-lang/rust/issues/156457) · [lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [coercions](../../02_intermediate/04_types_and_conversions/07_type_conversions.md) |
| 4 | Partially convert `ambiguous_glob_imports` lint into a hard error | Lang | ✅ stabilized | [PR #149195](https://github.com/rust-lang/rust/pull/149195) · [#156648](https://github.com/rust-lang/rust/issues/156648) · [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md) |
| 5 | Lint on `core::ffi::c_void` as a return type | Lang | ✅ stabilized | [PR #156379](https://github.com/rust-lang/rust/pull/156379) · [#156853](https://github.com/rust-lang/rust/issues/156853) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md) |
| 6 | Syntactically reject where-bounds `Type = Type` and `Type == Type` | Lang | ⚠ compat change | [PR #153513](https://github.com/rust-lang/rust/pull/153513) · [#154816](https://github.com/rust-lang/rust/issues/154816) · [traits](../../02_intermediate/00_traits/01_traits.md) |
| 7 | `repr(transparent)` stricter rules for trivial layout fields | Lang | ⚠ compat change | [PR #155299](https://github.com/rust-lang/rust/pull/155299) · [#157730](https://github.com/rust-lang/rust/issues/157730) · [memory model](../../03_advanced/02_unsafe/06_memory_model.md) |
| 8 | Add `T: PartialEq` bounds to derived `StructuralPartialEq` impls | Lang | ✅ stabilized | [PR #156807](https://github.com/rust-lang/rust/pull/156807) · [#157865](https://github.com/rust-lang/rust/issues/157865) · [derive traits](../../02_intermediate/00_traits/06_derive_traits.md) |
| 9 | Fix parser error recovery treating `dyn` as a strict keyword | Lang | ✅ stabilized | [PR #157577](https://github.com/rust-lang/rust/pull/157577) · [#157579](https://github.com/rust-lang/rust/issues/157579) · [traits](../../02_intermediate/00_traits/01_traits.md) |
| 10 | Resolver: Batched Import Resolution | Lang | ✅ stabilized | [PR #145108](https://github.com/rust-lang/rust/pull/145108) · [#156651](https://github.com/rust-lang/rust/issues/156651) · [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md) |
| 11 | Reject arguments in attributes where no arguments are expected | Lang | ⚠ compat change | [PR #155193](https://github.com/rust-lang/rust/pull/155193) · [#156641](https://github.com/rust-lang/rust/issues/156641) · [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) |
| 12 | Change `Location<'_>` lifetime to `'static` in `PanicHookInfo` | Lang | ✅ stabilized | [PR #146561](https://github.com/rust-lang/rust/pull/146561) · [#148297](https://github.com/rust-lang/rust/issues/148297) · [panic](../../02_intermediate/03_error_handling/03_panic.md) |
| 13 | Windows-gnu targets now specify baseline tools versions | Compiler/Platform | ⚠ compat change | [PR #158020](https://github.com/rust-lang/rust/pull/158020) · [#158296](https://github.com/rust-lang/rust/issues/158296) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 14 | On Emscripten the WASM exception handling ABI is now unconditionally used | Compiler/Platform | ⚠ compat change | [PR #156928](https://github.com/rust-lang/rust/pull/156928) · [#158091](https://github.com/rust-lang/rust/issues/158091) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 15 | Switch Windows thread-local destructors to FLS | Compiler/Platform | ✅ stabilized | [PR #148799](https://github.com/rust-lang/rust/pull/148799) · [#156334](https://github.com/rust-lang/rust/issues/156334) · [destructors](../../04_formal/05_rustc_internals/09_destructors.md) |
| 16 | Solaris: remove `File::lock` implementation (return "unsupported") | Compiler/Platform | ⚠ compat change | [PR #157509](https://github.com/rust-lang/rust/pull/157509) · [#157510](https://github.com/rust-lang/rust/issues/157510) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 17 | Document panic in `RangeInclusive::from(legacy::RangeInclusive)` | Std API | ✅ stabilized | [PR #155421](https://github.com/rust-lang/rust/pull/155421) · [#158142](https://github.com/rust-lang/rust/issues/158142) · [range types](../../02_intermediate/04_types_and_conversions/01_range_types.md) |
| 18 | Add temporary scope to `assert_eq!` and `assert_ne!` | Std API | ✅ stabilized | [PR #155739](https://github.com/rust-lang/rust/pull/155739) · [#158022](https://github.com/rust-lang/rust/issues/158022) · [macro patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md) |
| 19 | Document that `ManuallyDrop`'s `Box` interaction has been fixed | Std API | ✅ stabilized | [PR #155750](https://github.com/rust-lang/rust/pull/155750) · [#156042](https://github.com/rust-lang/rust/issues/156042) · [destructors](../../04_formal/05_rustc_internals/09_destructors.md) |
| 20 | Ensure `Send`/`Sync` is not implemented for `std::env::Vars{,Os}` | Std API | ✅ stabilized | [PR #155153](https://github.com/rust-lang/rust/pull/155153) · [#156521](https://github.com/rust-lang/rust/issues/156521) · [Send/Sync](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) |
| 21 | Ensure `Send`/`Sync` impl for `std::process::CommandArgs` | Std API | ✅ stabilized | [PR #155113](https://github.com/rust-lang/rust/pull/155113) · [#156335](https://github.com/rust-lang/rust/issues/156335) · [process](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) · [Send/Sync](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) |
| 22 | `String::from_utf16le` / `from_utf16be` / `_lossy` variants | Std API | ✅ stabilized | [PR #116258](https://github.com/rust-lang/rust/pull/116258) · [#157822](https://github.com/rust-lang/rust/issues/157822) · [strings](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) |
| 23 | `str::strip_circumfix` | Std API | ✅ stabilized | [Issue #147946](https://github.com/rust-lang/rust/issues/147946) · [#157850](https://github.com/rust-lang/rust/issues/157850) · [strings](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) |
| 24 | `NonZero*` integer types: `from_str_radix` | Std API | ✅ stabilized | [Issue #152193](https://github.com/rust-lang/rust/issues/152193) · [#157847](https://github.com/rust-lang/rust/issues/157847) · [numerics](../../01_foundation/02_type_system/03_numerics.md) |
| 25 | `{f32,f64}::algebraic_{add,sub,mul,div,rem}` | Std API | ✅ stabilized | [PR #157029](https://github.com/rust-lang/rust/pull/157029) · [#157864](https://github.com/rust-lang/rust/issues/157864) · [numerics](../../01_foundation/02_type_system/03_numerics.md) |
| 26 | LoongArch CRC intrinsics | Std API | ✅ stabilized | [Issue #156908](https://github.com/rust-lang/rust/issues/156908) · [#157844](https://github.com/rust-lang/rust/issues/157844) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 27 | Replace printables table with `unicode_data.rs` tables | Std API | ✅ stabilized | [PR #155527](https://github.com/rust-lang/rust/pull/155527) · [#156782](https://github.com/rust-lang/rust/issues/156782) · [strings](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) |
| 28 | Implement fast path for `derive(PartialOrd)` when deriving `Ord` | Macro/Derive | ⚠ compat change | [PR #155598](https://github.com/rust-lang/rust/pull/155598) · [#159555](https://github.com/rust-lang/rust/issues/159555) · [derive traits](../../02_intermediate/00_traits/06_derive_traits.md) |
| 29 | If fully elided, trait object lifetime defaults resolve differently | Compat | ⚠ compat change | [PR #129543](https://github.com/rust-lang/rust/pull/129543) · [#156449](https://github.com/rust-lang/rust/issues/156449) · [lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [traits](../../02_intermediate/00_traits/01_traits.md) |
| 30 | Correctly check whether types have equal size in `transmute()` when `repr` attributes are involved | Compat | ⚠ compat change | [PR #155418](https://github.com/rust-lang/rust/pull/155418) · [#156852](https://github.com/rust-lang/rust/issues/156852) · [memory model](../../03_advanced/02_unsafe/06_memory_model.md) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md) |
| 31 | `UNSAFE_CODE` lint now consistently emitted for all unsafe attributes | Compat | ⚠ compat change | [PR #157201](https://github.com/rust-lang/rust/pull/157201) · [#157704](https://github.com/rust-lang/rust/issues/157704) · [unsafe](../../03_advanced/02_unsafe/01_unsafe.md) · [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) |

---

## 1. 语言语义

### 1.1 riscv: `d`, `e`, and `f` target_features are now stable in `cfg(target_feature = "?")`

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #156188](https://github.com/rust-lang/rust/pull/156188) · **release-notes 跟踪 issue**: [#157534](https://github.com/rust-lang/rust/issues/157534)

#### 变更动机

RISC-V 目标此前允许在 `cfg(target_feature = "...")` 中探测大量 target feature，但 `d`（双精度浮点）、`e`（嵌入式 RV32E 基线）和 `f`（单精度浮点）长期处于不稳定状态。1.98.0 将这三个 feature 提升为可在稳定 `cfg` 中探测，使嵌入式与 HPC 目标能够在稳定 Rust 下根据实际硬件能力做条件编译。

#### 语义影响

- 稳定 `cfg(target_feature = "d")`、`cfg(target_feature = "e")`、`cfg(target_feature = "f")` 现在可在 RISC-V target 上直接使用，无需 `#![feature(cfg_target_feature)]`。
- 与已有的稳定 RISC-V feature（如 `m`、`a`、`c`）保持一致，构成完整的 RV32I/RV64I 基础扩展探测集。
- 不改变代码生成，只影响条件编译的可用标识符集合。

#### 迁移注意

- 如果之前使用 nightly feature 来探测这些 feature，可移除对应的 `#![feature(...)]`。
- 在 `#[cfg(target_feature = "d")]` 分支中假设双精度浮点寄存器存在时，仍需确认目标 ABI 确实包含 `D` 扩展。

---

### 1.2 Add deny-by-default `invalid_runtime_symbol_definitions` lint and warn-by-default `suspicious_runtime_symbol_definitions` lint

**相关概念**: [FFI](../../03_advanced/04_ffi/01_rust_ffi.md) · [linkage](../../03_advanced/04_ffi/03_linkage.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155521](https://github.com/rust-lang/rust/pull/155521) · **release-notes 跟踪 issue**: [#156519](https://github.com/rust-lang/rust/issues/156519)

#### 变更动机

Rust 运行时依赖 `memcmp`、`memset`、`memmove`、`strlen` 等 C 运行时符号。如果 crate 或依赖库用 `#[no_mangle]` 定义了同名符号，会无声地覆盖运行时实现，导致未定义行为或难以调试的崩溃。1.98.0 引入两个 lint：

- `invalid_runtime_symbol_definitions`：直接定义与运行时冲突的符号（默认 deny）。
- `suspicious_runtime_symbol_definitions`：定义的符号签名/语义与运行时预期不符（默认 warn）。

#### 语义影响

- 覆盖核心运行时符号的代码现在会被 lint 捕获，而不是在链接或运行期才暴露问题。
- lint 当前主要针对 `core` 级运行时符号；后续版本会扩展到更多运行时符号。
- deny-by-default 意味着命中后会导致编译失败，必须显式处理。

#### 迁移注意

- 若自定义了 `memcmp`/`memset` 等用于 no-std 环境，需用 `#[allow(invalid_runtime_symbol_definitions)]` 并确保这是有意为之。
- 检查 no-std / embedded 项目中对 C 运行时符号的自定义实现，确认签名严格匹配 libc 语义。

---

### 1.3 Allow shortening lifetime of `&mut` when unsize-coercing, even in an invariant position

**相关概念**: [lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [coercions](../../02_intermediate/04_types_and_conversions/07_type_conversions.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #149219](https://github.com/rust-lang/rust/pull/149219) · **release-notes 跟踪 issue**: [#156457](https://github.com/rust-lang/rust/issues/156457)

#### 变更动机

在强制类型转换（unsized coercion）中，`&mut T` 到 `&mut dyn Trait` 以及通过 `CoerceUnsized` 的间接转换，此前不允许在逆变位置缩短生命周期。例如 `Cell<&'long mut i32>` 无法强制转换为 `Cell<&'short mut dyn Send>`。1.98.0 统一了 `&mut` 与 `&` 的生命周期缩短规则，使类型系统对智能指针和内部可变性包装器更一致。

#### 语义影响

- 在不变（invariant）上下文中，unsized coercion 现在可以缩短 `&mut` 的生命周期。
- 允许更多符合直觉的代码通过借用检查，例如把生命周期较长的 `Box<&'long mut T>` 传递给期望较短生命周期的接口。
- 只放宽合法转换，不会引入新的别名规则违规。

#### 迁移注意

- 绝大多数代码无需改动；这是放宽限制而非收紧。
- 若之前通过显式 `transmute` 或重新借用绕过此限制，可替换为更安全的 coercion。

---

### 1.4 Partially convert `ambiguous_glob_imports` lint into a hard error

**相关概念**: [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #149195](https://github.com/rust-lang/rust/pull/149195) · **release-notes 跟踪 issue**: [#156648](https://github.com/rust-lang/rust/issues/156648)

#### 变更动机

`use some_module::*;` 可能一次性引入多个同名项，产生歧义。此前 `ambiguous_glob_imports` 以 lint 形式报告，部分场景被允许继续编译。1.98.0 将其中一部分（无法通过显式 `use` 消歧的最直接歧义）提升为硬错误，防止运行时意外绑定到错误符号。

#### 语义影响

- 特定形式的歧义 glob import 现在直接编译失败，而不是只产生 warning。
- 未被纳入硬错误范围的歧义仍由 `ambiguous_glob_imports` lint 报告。
- 提升范围基于 RFC 对名称解析清晰性的长期目标。

#### 迁移注意

- 避免使用 `use ...::*` 覆盖可能重名的模块。
- 若触发错误，用显式 `use module::Item;` 替换 glob import，或重命名冲突项。

---

### 1.5 Lint on `core::ffi::c_void` as a return type

**相关概念**: [FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #156379](https://github.com/rust-lang/rust/pull/156379) · **release-notes 跟踪 issue**: [#156853](https://github.com/rust-lang/rust/issues/156853)

#### 变更动机

`core::ffi::c_void` 与 `std::ffi::c_void` 在 FFI 中常被误用为“任意指针”返回类型。由于 `c_void` 是不完整类型，直接把它作为函数返回类型会丢失类型信息并增加 `transmute` 误用风险。新 lint 在 `extern "C"` 声明或 Rust 函数签名把 `c_void` 作为返回类型时发出警告。

#### 语义影响

- 编译器会建议使用具体指针类型（如 `*mut c_void`）替代裸 `c_void` 返回类型。
- 不改变类型系统，只增加诊断引导。
- 属于 warn-by-default lint，不会中断现有构建，除非项目开启 `-D warnings`。

#### 迁移注意

- 将 `fn foo() -> c_void` 改为 `fn foo() -> *mut c_void` 或 `*const c_void`。
- 在需要兼容 C 头文件生成的绑定中，检查 bindgen 输出是否会产生此类签名。

---

### 1.6 Where-bounds of the form `Type = Type` and `Type == Type` are no longer syntactically allowed

**相关概念**: [traits / generic bounds](../../02_intermediate/00_traits/01_traits.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #153513](https://github.com/rust-lang/rust/pull/153513) · **release-notes 跟踪 issue**: [#154816](https://github.com/rust-lang/rust/issues/154816)

#### 变更动机

Rust 的 where 子句从未支持等式约束（equality predicate），但解析器此前错误地允许 `where T = U` 或 `where T == U` 的写法，并在后续阶段才拒绝。PR #153513 将这类等式谓词语法直接在解析层拒绝，产生更清晰的错误信息。

#### 语义影响

- `where T = U` 和 `where T == U` 现在会在解析阶段报错，而不是延迟到类型检查。
- 正确的关联类型等式约束仍通过 `where T::Assoc = U` 的关联类型语法表达（注意这是已经支持的关联类型等式，不是普通类型等式）。

#### 迁移注意

- 若代码中误写过 `where T = U`，改为正确的关联类型约束或重设计 trait bound。
- 宏生成代码中若拼接出此类 where 子句，需要修正模板。

---

### 1.7 `repr(transparent)` stricter rules for trivial layout fields

**相关概念**: [memory model / layout](../../03_advanced/02_unsafe/06_memory_model.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155299](https://github.com/rust-lang/rust/pull/155299) · **release-notes 跟踪 issue**: [#157730](https://github.com/rust-lang/rust/issues/157730)

#### 变更动机

`#[repr(transparent)]` 要求类型只有一个非零大小（non-ZST）字段，其余字段必须具有 "trivial" 布局。此前对 "trivial" 的定义过于宽松，允许 `repr(C)` 类型、私有字段类型和 `#[non_exhaustive]` 类型作为忽略字段。1.98.0 收紧规则，这些类型不再被视为 trivial，因为它们的外部布局可能随编译器或版本变化。

#### 语义影响

- `repr(C)` 类型、带私有字段的类型、`#[non_exhaustive]` 类型不能再用作 `repr(transparent)` 的忽略字段。
- 之前被编译器警告的 `repr_transparent_non_zst_fields` 场景现在提升为硬错误。

#### 迁移注意

- 检查所有 `#[repr(transparent)]` 类型，确保只有一个非 ZST 字段，其余字段是明确已知的 ZST（如 `PhantomData`）。
- 若需要包装多个字段，考虑 `repr(C)` 并显式管理布局，或只用 `PhantomData<T>` 作为标记字段。

---

### 1.8 Add `T: PartialEq` bounds to derived `StructuralPartialEq` impls

**相关概念**: [derive traits](../../02_intermediate/00_traits/06_derive_traits.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #156807](https://github.com/rust-lang/rust/pull/156807) · **release-notes 跟踪 issue**: [#157865](https://github.com/rust-lang/rust/issues/157865)

#### 变更动机

`#[derive(PartialEq)]` 自动实现的 `StructuralPartialEq` trait（用于 `const` 比较和模式匹配）此前对泛型参数没有 `PartialEq` bound，导致某些常量求值场景下出现不一致。1.98.0 为 derived `StructuralPartialEq` impl 增加 `T: PartialEq` bound，使其与 `PartialEq` 派生实现保持一致。

#### 语义影响

- 派生的 `StructuralPartialEq` 现在要求泛型字段类型实现 `PartialEq`。
- 这可能会暴露此前被掩盖的缺少 bound 错误，特别是在 `const` 比较或 `match` 结构比较中。
- 语义更正确，减少了 trait bound 不一致导致的编译器内部错误。

#### 迁移注意

- 若结构体/枚举有泛型字段且依赖 `StructuralPartialEq`，为相应类型参数添加 `T: PartialEq` bound。
- 检查 `const` 上下文中的相等比较是否因此产生新的 bound 要求。

---

### 1.9 Fix parser error recovery treating `dyn` as a strict keyword

**相关概念**: [traits / trait objects](../../02_intermediate/00_traits/01_traits.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #157577](https://github.com/rust-lang/rust/pull/157577) · **release-notes 跟踪 issue**: [#157579](https://github.com/rust-lang/rust/issues/157579)

#### 变更动机

`dyn` 在 Rust 2018 起是严格关键字，但某些语法错误恢复路径会把它当作普通标识符处理，导致诊断信息误导用户。PR #157577 修正了解析器错误恢复逻辑，使 `dyn` 在所有路径中都被识别为严格关键字。

#### 语义影响

- 修复解析器在错误恢复时的不一致行为，使 `dyn` 关键字的处理更统一。
- 正确代码不受影响；错误代码会获得更准确的诊断信息。

#### 迁移注意

- 无迁移成本。若之前依赖解析器把 `dyn` 当作标识符的某些边缘行为，现在会收到更清晰的错误提示。

---

### 1.10 Resolver: Batched Import Resolution

**相关概念**: [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #145108](https://github.com/rust-lang/rust/pull/145108) · **release-notes 跟踪 issue**: [#156651](https://github.com/rust-lang/rust/issues/156651)

#### 变更动机

rustc 的名称解析器在处理大量 `use` 导入时采用逐项解析策略，导致复杂 crate 的解析阶段耗时显著。PR #145108 将导入解析改为批量处理：解析器先收集同一作用域内的所有导入声明，再统一进行决议，减少重复查找和中间状态。

#### 语义影响

- 编译时间：大型项目（尤其依赖大量 glob import 或深层模块树的项目）的 name-resolution 阶段可能明显变快。
- 行为等价性：批量解析保持与旧算法相同的可见性和错误报告语义；只是执行顺序优化。
- 对 rust-analyzer 也有收益，因为名称解析是 IDE 响应性的关键路径。

#### 迁移注意

- 纯内部编译器优化，源代码无需改动。
- 若遇到解析顺序相关的边缘错误（理论上不应发生），请提交 regression issue。

---

### 1.11 Reject arguments in attributes where no arguments are expected

**相关概念**: [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155193](https://github.com/rust-lang/rust/pull/155193) · **release-notes 跟踪 issue**: [#156641](https://github.com/rust-lang/rust/issues/156641)

#### 变更动机

某些 attribute（如 `#[inline]`、`#[cold]`、`#[track_caller]`）不接受参数，但解析器此前在部分错误恢复路径中没有正确拒绝 `#[inline(true)]` 这类写法。1.98.0 统一检查逻辑，使无参 attribute 在带参数时报错。

#### 语义影响

- `#[attr(arg)]` 形式的 attribute 如果 `attr` 不期望参数，现在会直接编译错误。
- 改善诊断信息，避免用户误认为参数生效。

#### 迁移注意

- 检查代码中是否有 `#[inline(something)]`、`#[cold(...)]` 等误用，移除参数或使用正确的 attribute（如 `#[inline(always)]` 是 `#[inline]` 的合法参数化形式，不在此列）。
- 宏生成 attribute 时需确保参数与 attribute 定义匹配。

---

### 1.12 Change `Location<'_>` lifetime to `'static` in `PanicHookInfo`

**相关概念**: [panic / error handling](../../02_intermediate/03_error_handling/03_panic.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #146561](https://github.com/rust-lang/rust/pull/146561) · **release-notes 跟踪 issue**: [#148297](https://github.com/rust-lang/rust/issues/148297)

#### 变更动机

`std::panic::PanicHookInfo`（以及旧的 `PanicInfo`）通过 `location()` 返回 `&Location<'_>`，其生命周期与 panic 信息本身绑定。由于 panic hook 经常被存储或异步处理，这种绑定导致生命周期受限。PR #146561 将 `Location` 的生命周期改为 `'static`，因为 panic 位置信息本质上是编译期常量字符串。

#### 语义影响

- `PanicHookInfo::location` 现在返回 `&'static Location<'static>`。
- panic hook 可以更安全地保存 `Location` 引用，无需担心其生命周期。
- 这是 API 签名变更，可能破坏自定义 panic hook 的类型签名。

#### 迁移注意

- 更新自定义 panic hook 的签名以匹配新的 `'static` 生命周期。
- 若之前对 `Location` 生命周期做了不必要的人工延长，可简化代码。

---

## 2. 编译器与平台

### 2.1 Windows-gnu targets now specify baseline tools versions

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #158020](https://github.com/rust-lang/rust/pull/158020) · **release-notes 跟踪 issue**: [#158296](https://github.com/rust-lang/rust/issues/158296)

#### 变更动机

Windows GNU 目标（如 `x86_64-pc-windows-gnu`）长期依赖用户本地安装的 mingw-w64 工具链，版本碎片化导致链接错误、ABI 不兼容和 CI 不稳定。1.98.0 为这些目标指定了最低 mingw-w64 工具链版本基线，使编译器可以依赖一致的 CRT 和链接器能力。

#### 语义影响

- 官方构建与 target spec 中声明了最低 mingw-w64/gcc/binutils 版本。
- 旧版 mingw-w64 环境可能无法继续编译或链接 Windows-gnu 目标。
- 有助于逐步启用新的 Windows 平台特性（如更现代的异常处理）。

#### 迁移注意

- 在 Windows GNU 环境构建时，升级到 Rust 推荐的 mingw-w64 版本（通常随 rustup 组件或 MSYS2/WinLibs 提供）。
- CI 中固定 `x86_64-pc-windows-gnu` 镜像的 mingw 版本，避免低于基线。

---

### 2.2 On Emscripten the WASM exception handling ABI is now unconditionally used

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #156928](https://github.com/rust-lang/rust/pull/156928) · **release-notes 跟踪 issue**: [#158091](https://github.com/rust-lang/rust/issues/158091)

#### 变更动机

Emscripten 此前同时支持 WebAssembly 异常处理（WASM EH）和旧的 JavaScript 异常处理两套 ABI，并通过 `-Zemscripten-wasm-eh=false` 开关回退。随着浏览器对 WASM EH 的支持成熟，1.98.0 移除回退开关，统一使用 WASM EH ABI。

#### 语义影响

- `-Zemscripten-wasm-eh=false` 被移除；任何使用都会报错。
- 生成的 WASM 模块更小、性能更好，且与 Emscripten 默认行为一致。
- 需要部署环境的 JavaScript 运行时支持 WASM exception handling proposal。

#### 迁移注意

- 从构建脚本和 CI 配置中移除 `-Zemscripten-wasm-eh=false`。
- 若目标环境不支持 WASM EH（如旧版 Node.js 或浏览器），需要升级运行时或重新评估部署目标。

---

### 2.3 Switch the destructors implementation for thread locals on Windows to use FLS

**相关概念**: [destructors](../../04_formal/05_rustc_internals/09_destructors.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #148799](https://github.com/rust-lang/rust/pull/148799) · **release-notes 跟踪 issue**: [#156334](https://github.com/rust-lang/rust/issues/156334)

#### 变更动机

Windows 上 `thread_local!` 析构此前使用 TLS 回调机制，在动态加载库（DLL）和纤程（fiber）场景下存在析构顺序和重复析构问题。PR #148799 改为使用 Fiber Local Storage（FLS）作为底层析构机制，与 Windows 线程生命周期绑定更可靠。

#### 语义影响

- Windows 上线程局部存储的析构时序和 DLL 卸载行为更一致。
- 解决部分 fiber 场景下 TLS destructor 不被调用或被重复调用的问题。
- 不影响 Linux/macOS 等平台。

#### 迁移注意

- 源代码通常无需改动。
- 若 Windows 程序深度依赖 TLS destructor 的精确时序，应在 1.98.0 下重新测试，尤其是 DLL unload 路径。

---

### 2.4 Solaris: remove `File::lock` implementation, it has the wrong semantics

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #157509](https://github.com/rust-lang/rust/pull/157509) · **release-notes 跟踪 issue**: [#157510](https://github.com/rust-lang/rust/issues/157510)

#### 变更动机

Solaris/Illumos 上 `std::fs::File::lock` 的实现使用了错误的底层原语，导致文件锁语义与其他平台不一致。1.98.0 移除该实现，使 `File::lock` 在这些平台上返回 `ErrorKind::Unsupported`，避免静默的语义错误。

#### 语义影响

- 在 Solaris/Illumos 上，`File::lock` 现在返回 `Unsupported` 错误，而不是提供不可靠的锁。
- 其他平台的 `File::lock` 行为不变。

#### 迁移注意

- 若项目面向 Solaris/Illumos 并依赖 `File::lock`，需要改用平台特定的 `fcntl` advisory lock 或重新设计并发控制。
- 考虑通过 `std::io::ErrorKind::Unsupported` 检测并回退到替代方案。

---

## 3. 标准库与文档

### 3.1 Document panic in `RangeInclusive::from(legacy::RangeInclusive)`

**相关概念**: [range types](../../02_intermediate/04_types_and_conversions/01_range_types.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155421](https://github.com/rust-lang/rust/pull/155421) · **release-notes 跟踪 issue**: [#158142](https://github.com/rust-lang/rust/issues/158142)

#### 变更动机

`RangeInclusive::from` 转换旧版 `std::ops::RangeInclusive`（即 `legacy::RangeInclusive`）在起始值大于结束值时会 panic，但这一行为此前未在文档中明确说明。PR #155421 补全了 panic 条件文档，使 API 契约透明。

#### 语义影响

- 仅文档更新，不改变运行行为。
- 明确 `RangeInclusive::from(legacy::RangeInclusive { start, end })` 在 `start > end` 时 panic。

#### 迁移注意

- 检查调用 `RangeInclusive::from` 的位置，确保传入的范围满足 `start <= end`。
- 若范围可能为空，使用显式构造 `start..=end` 并在转换前校验。

---

### 3.2 Add temporary scope to `assert_eq!` and `assert_ne!`

**相关概念**: [macro patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155739](https://github.com/rust-lang/rust/pull/155739) · **release-notes 跟踪 issue**: [#158022](https://github.com/rust-lang/rust/issues/158022)

#### 变更动机

`assert_eq!(left, right)` 和 `assert_ne!(left, right)` 在展开时会将 `left` 和 `right` 绑定到临时变量，这些临时变量的作用域此前延伸到整个断言表达式。1.98.0 为这两个宏引入临时作用域，使比较操作产生的中间值在断言消息格式化后尽快释放，减少引用持有时间。

#### 语义影响

- 宏展开中用于保存 `left`/`right` 的临时变量拥有更严格的作用域。
- 解决某些场景下临时值存活过长导致的借用或析构顺序问题。
- 对大多数断言代码行为等价；只影响依赖临时值精确作用域的极端边缘代码。

#### 迁移注意

- 若自定义宏展开后依赖 `assert_eq!` 内部临时变量的生命周期，需要重新评估。
- 普通使用无需改动。

---

### 3.3 Document that `ManuallyDrop`'s `Box` interaction has been fixed

**相关概念**: [destructors](../../04_formal/05_rustc_internals/09_destructors.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155750](https://github.com/rust-lang/rust/pull/155750) · **release-notes 跟踪 issue**: [#156042](https://github.com/rust-lang/rust/issues/156042)

#### 变更动机

`ManuallyDrop<Box<T>>` 与 `ManuallyDrop::drop` 的交互存在历史问题：在某些路径下，`Box` 的析构语义与 `ManuallyDrop` 的显式控制产生冲突。PR #155750 修复了该问题，并在文档中明确 `ManuallyDrop` 与 `Box` 的正确用法。

#### 语义影响

- 修复了 `ManuallyDrop::drop(&mut ManuallyDrop<Box<T>>)` 场景下的双重释放/泄漏风险。
- 文档更新明确了如何安全地手动释放 `ManuallyDrop<Box<T>>`。

#### 迁移注意

- 若代码手动管理 `ManuallyDrop<Box<T>>` 的析构，请对照新文档检查是否使用了推荐模式。
- 推荐做法：先取出 `Box`，再 drop：`let b = unsafe { ManuallyDrop::take(&mut mb) }; drop(b);`。

---

### 3.4 Ensure `Send`/`Sync` is not implemented for `std::env::Vars{,Os}`

**相关概念**: [Send/Sync](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) · [Send/Sync boundaries](../../03_advanced/00_concurrency/04_send_sync_boundaries.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155153](https://github.com/rust-lang/rust/pull/155153) · **release-notes 跟踪 issue**: [#156521](https://github.com/rust-lang/rust/issues/156521)

#### 变更动机

`std::env::Vars` 和 `std::env::VarsOs` 在底层持有进程环境变量的迭代状态，这些状态不是线程安全的。此前由于实现细节，它们意外实现了 `Send` 和/或 `Sync`，允许跨线程共享。1.98.0 显式移除这些实现，修复自动 trait 边界。

#### 语义影响

- `std::env::Vars` 和 `std::env::VarsOs` 不再实现 `Send`/`Sync`。
- 任何将环境变量迭代器发送到其他线程或共享引用的代码现在会编译失败。

#### 迁移注意

- 在跨线程使用前将环境变量收集到 `Vec<(String, String)>` 等线程安全集合中。
- 检查依赖 `std::env::vars()` 在 async 或线程池中使用的代码。

---

### 3.5 Ensure `Send`/`Sync` impl for `std::process::CommandArgs`

**相关概念**: [process model](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) · [Send/Sync](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155113](https://github.com/rust-lang/rust/pull/155113) · **release-notes 跟踪 issue**: [#156335](https://github.com/rust-lang/rust/issues/156335)

#### 变更动机

`std::process::CommandArgs` 此前缺少显式的 `Send`/`Sync` 实现声明，导致在某些平台或编译器分析下无法跨线程传递命令参数迭代器。PR #155113 显式实现 `Send` 和 `Sync`，前提是底层数据满足条件。

#### 语义影响

- `CommandArgs` 现在保证实现 `Send`/`Sync`（只要内部 `OsString` 等类型满足）。
- 允许在异步或线程池上下文中共享命令参数。

#### 迁移注意

- 对已有代码通常是放宽限制，无需改动。
- 若之前依赖 `CommandArgs` 不实现 `Send`/`Sync` 的某些边界情况，需重新评估。

---

### 3.6 `String::from_utf16le` / `from_utf16be` / `_lossy` variants

**相关概念**: [strings / encoding](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #116258](https://github.com/rust-lang/rust/pull/116258) · **release-notes 跟踪 issue**: [#157822](https://github.com/rust-lang/rust/issues/157822)

#### 变更动机

`String::from_utf16` 假设输入为小端 UTF-16。处理 Windows API、网络协议或文件格式时经常需要显式指定 endianness。1.98.0 稳定显式 endian 版本：`from_utf16le`、`from_utf16be` 以及对应的 `_lossy` 变体。

#### 语义影响

- 新增方法：`String::from_utf16le`、`String::from_utf16be`、`String::from_utf16le_lossy`、`String::from_utf16be_lossy`。
- 语义与 `from_utf16` 相同，只是按显式字节序解码，无需调用者手动交换字节。

#### 迁移注意

- 替换手动的 UTF-16 字节交换 + `from_utf16` 调用。
- `_lossy` 变体在非法序列处替换为 `U+FFFD`，与 `from_utf16_lossy` 行为一致。

---

### 3.7 `str::strip_circumfix`

**相关概念**: [strings](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [Issue #147946](https://github.com/rust-lang/rust/issues/147946) · **release-notes 跟踪 issue**: [#157850](https://github.com/rust-lang/rust/issues/157850)

#### 变更动机

字符串处理中经常需要同时移除前缀和后缀（如括号、引号、标记符号）。单独调用 `strip_prefix` 和 `strip_suffix` 会创建多个临时结果。`strip_circumfix` 提供一次性检查并移除成对前缀后缀的能力，使代码更简洁。

#### 语义影响

- 新增 `str::strip_circumfix` 方法（具体签名以稳定文档为准，通常接受前缀和后缀 pattern）。
- 仅当字符串同时以指定前缀和后缀开头/结尾时才返回 `Some(&str)`。

#### 迁移注意

- 可替换手写的前后缀剥离逻辑，减少临时字符串分配。
- 注意前缀和后缀是独立匹配，不是对称括号语义；如需嵌套括号解析仍需专用解析器。

---

### 3.8 `NonZero*` integer types: `from_str_radix`

**相关概念**: [numerics](../../01_foundation/02_type_system/03_numerics.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [Issue #152193](https://github.com/rust-lang/rust/issues/152193) · **release-notes 跟踪 issue**: [#157847](https://github.com/rust-lang/rust/issues/157847)

#### 变更动机

`NonZeroU32`、`NonZeroI64` 等非零整数类型此前缺少按 radix 解析的构造函数，用户需要先解析为原始整数再调用 `NonZero::new`，无法直接获得解析错误信息。1.98.0 为所有 `NonZero*` 类型稳定 `from_str_radix`。

#### 语义影响

- 新增 `NonZeroU32::from_str_radix(s, radix)` 等方法，返回 `Result<Self, ParseIntError>`。
- 零值会作为解析错误返回，无需额外检查。

#### 迁移注意

- 替换 `NonZero::new(s.parse()?)?` 模式为 `NonZeroU32::from_str_radix(s, 10)?`。
- 注意错误类型与 `parse::<u32>()` 一致，便于统一处理。

---

### 3.9 `{f32,f64}::algebraic_{add,sub,mul,div,rem}`

**相关概念**: [numerics](../../01_foundation/02_type_system/03_numerics.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #157029](https://github.com/rust-lang/rust/pull/157029) · **release-notes 跟踪 issue**: [#157864](https://github.com/rust-lang/rust/issues/157864)

#### 变更动机

浮点运算的严格 IEEE-754 语义在某些高性能场景下限制了优化空间。`algebraic_add` / `algebraic_sub` / `algebraic_mul` / `algebraic_div` / `algebraic_rem` 系列方法允许编译器将运算当作代数运算进行重排和优化（如利用结合律），同时保留 NaN/无穷大等边界行为的基本契约。

#### 语义影响

- 新增 `f32` 和 `f64` 上的 `algebraic_*` 方法，并在 `const fn` 上下文中可用。
- 编译器可在这些调用点进行更激进的浮点优化，可能改变中间舍入顺序。
- 结果仍满足 `x algebraic_op y` 的数学关系，但可能与传统 `x + y` 的逐位结果不同。

#### 迁移注意

- 仅在性能关键且可接受非确定性舍入顺序的场景使用。
- 不要用于需要按位一致或严格 IEEE 结果的场景（如序列化、加密校验和、确定性仿真）。

---

### 3.10 LoongArch CRC intrinsics

**相关概念**: [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [Issue #156908](https://github.com/rust-lang/rust/issues/156908) · **release-notes 跟踪 issue**: [#157844](https://github.com/rust-lang/rust/issues/157844)

#### 变更动机

LoongArch 架构的 CRC 校验指令此前没有稳定的 stdarch intrinsic 封装。1.98.0 将相关 CRC 计算 intrinsic 稳定化，使在 LoongArch 目标上进行高效 CRC32/CRC 校验的代码可以在 stable Rust 中编写。

#### 语义影响

- 新增 `core::arch::loongarch64::*` 下与 CRC 相关的稳定 intrinsic。
- 需要目标 CPU 支持对应 CRC 扩展，并通过 `target_feature` 或编译选项启用。

#### 迁移注意

- 仅在 `loongarch64-*` 目标使用，并通过 `cfg(target_arch = "loongarch64")` 隔离平台相关代码。
- 在运行期检测目标 feature，避免在不支持 CRC 扩展的硬件上触发非法指令。

---

### 3.11 Replace printables table with `unicode_data.rs` tables

**相关概念**: [strings / Unicode](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md)

**状态**: ✅ stabilized in 1.98.0 · **来源**: [PR #155527](https://github.com/rust-lang/rust/pull/155527) · **release-notes 跟踪 issue**: [#156782](https://github.com/rust-lang/rust/issues/156782)

#### 变更动机

`core` 中用于 `char::is_ascii_graphic` 等判断的 "printables table" 是手工维护的 ASCII 可打印字符表，与 Unicode 标准不同步且容易出错。PR #155527 用基于官方 Unicode 数据的 `unicode_data.rs` 表替换它，使字符分类与 Unicode 版本一致。

#### 语义影响

- 字符可打印性、空白、控制字符等分类现在由 Unicode 数据驱动。
- 行为更标准、可维护，并为未来支持更广泛的 Unicode 属性奠定基础。
- 对 ASCII 范围的可打印字符判断通常不变；边缘控制字符的分类可能更精确。

#### 迁移注意

- 如果代码依赖 `char` 相关函数对特定控制字符的精确分类，请重新核对 Unicode 15/16 定义。
- 这主要是内部实现变更，大多数用户无感知。

---

## 4. 宏与 Derive

### 4.1 Implement fast path for `derive(PartialOrd)` when deriving `Ord`

**相关概念**: [derive traits](../../02_intermediate/00_traits/06_derive_traits.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155598](https://github.com/rust-lang/rust/pull/155598) · **release-notes 跟踪 issue**: [#159555](https://github.com/rust-lang/rust/issues/159555)

#### 变更动机

当同时为类型派生 `PartialOrd` 和 `Ord` 时，`#[derive(PartialOrd)]` 生成的实现现在会识别出存在 `Ord` 实现，并走一条快速路径：直接调用 `Ord::cmp` 再比较结果。这消除了冗余的 `partial_cmp` 调用，提升运行时性能。

#### 语义影响

- 派生的 `PartialOrd` 在同时存在派生 `Ord` 时，内部会调用 `cmp`。
- 如果类型的 `PartialOrd` 和 `Ord` 实现不一致（例如手动实现的 `Ord` 与派生的 `PartialOrd` 行为不同），快速路径会暴露这种不一致，导致排序结果改变。

#### 迁移注意

- 确保同时派生 `PartialOrd` 和 `Ord` 的类型，其语义完全一致。
- 若手动实现了其中一个 trait，建议同时手动实现另一个，或避免混用派生和手写实现。
- 受影响的代码通常表现为排序/比较结果变化，可通过单元测试快速发现。

---

## 5. 兼容性与破坏性变更

> 本节从「破坏性变更」视角重新组织那些在 §1–§4 中已经详细说明、但同时在 1.98.0 中构成兼容性风险的特性。每项均给出风险点、检测命令/检查动作与权威来源。

### 5.1 `derive(PartialOrd)` 快速路径暴露 `PartialOrd`/`Ord` 不一致

**相关概念**: [derive traits](../../02_intermediate/00_traits/06_derive_traits.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155598](https://github.com/rust-lang/rust/pull/155598) · **release-notes 跟踪 issue**: [#159555](https://github.com/rust-lang/rust/issues/159555) · **完整语义**: [§4.1](#41-implement-fast-path-for-derivepartialord-when-deriving-ord)

#### 变更动机

`derive(PartialOrd)` 在同时派生 `Ord` 时走快速路径，用 `cmp` 结果替代原来的 `partial_cmp` 链式比较。如果用户此前混用了手动和派生实现，或两个 trait 语义不一致，排序结果会变化。

#### 语义影响

- 同时派生 `PartialOrd` + `Ord` 的类型，其 `PartialOrd` 行为现在等于 `Ord::cmp == Less/Equal/Greater`。
- 手动 `Ord` + 派生 `PartialOrd` 的组合最容易暴露不一致。

#### 迁移注意

- 运行测试：`cargo test --workspace` 重点关注依赖 `sort`、`partial_cmp`、`cmp` 的断言。
- 对不一致的类型，统一改为全派生或全手动实现。

---

### 5.2 `repr(transparent)` 对 trivial 布局字段更严格

**相关概念**: [memory model / layout](../../03_advanced/02_unsafe/06_memory_model.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155299](https://github.com/rust-lang/rust/pull/155299) · **release-notes 跟踪 issue**: [#157730](https://github.com/rust-lang/rust/issues/157730) · **完整语义**: [§1.7](#17-reprtransparent-stricter-rules-for-trivial-layout-fields)

#### 变更动机

`#[repr(transparent)]` 此前允许 `repr(C)`、`#[non_exhaustive]` 或私有字段类型作为可忽略的 trivial 字段，这些类型的布局承诺不足以保证 transparent ABI 的稳定性。

#### 语义影响

- 上述类型作为 `repr(transparent)` 的辅助字段时，1.98.0 起产生硬错误。
- 只有明确 ZST（如 `PhantomData<T>`）才能安全地作为忽略字段。

#### 迁移注意

- 搜索：`rg "#\[repr\(transparent\)\]"`。
- 将非 ZST 辅助字段改为 `PhantomData` 或改用 `repr(C)` 显式布局。

---

### 5.3 等式谓词 `Type = Type` / `Type == Type` 被语法层拒绝

**相关概念**: [traits / generic bounds](../../02_intermediate/00_traits/01_traits.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #153513](https://github.com/rust-lang/rust/pull/153513) · **release-notes 跟踪 issue**: [#154816](https://github.com/rust-lang/rust/issues/154816) · **完整语义**: [§1.6](#16-where-bounds-of-the-form-type--type-and-type--type-are-no-longer-syntactically-allowed)

#### 变更动机

Rust where 子句从未支持普通类型等式约束，但解析器此前延迟到类型检查阶段才报错，导致诊断模糊。1.98.0 在解析层直接拒绝，使错误位置更明确。

#### 语义影响

- `where T = U` / `where T == U` 现在编译失败，位置在解析阶段。
- 关联类型等式（`where T::Assoc = U`）不受影响。

#### 迁移注意

- 搜索宏模板中的 `where $A = $B` 或 `where $A == $B` 并改写。
- 用 trait bound 或关联类型等式表达真实意图。

---

### 5.4 Trait object 完全省略生命周期时推断更严格

**相关概念**: [lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [traits](../../02_intermediate/00_traits/01_traits.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #129543](https://github.com/rust-lang/rust/pull/129543) · **release-notes 跟踪 issue**: [#156449](https://github.com/rust-lang/rust/issues/156449)

#### 变更动机

trait object 的默认生命周期规则存在历史不一致：某些完全省略生命周期的写法会根据上下文推断出不同的默认生命周期，导致代码在不同 rustc 版本或不同上下文下行为不同。PR #129543 使 trait reference 和关联类型路径正确地触发 trait object 生命周期默认值，修复了这些边缘情况。

#### 语义影响

- 极少数完全省略生命周期的 trait object 类型现在可能推断出更严格的边界，或被直接拒绝。
- 修复了 `dyn Trait` 在复杂路径（如关联类型路径）下的生命周期推断不一致问题。
- 对显式写出生命周期的代码没有影响。

#### 迁移注意

- 为所有公开的 `dyn Trait` 参数和字段显式标注生命周期，例如 `dyn Trait + 'static`。
- 若升级后出现生命周期错误，检查是否依赖了隐式默认生命周期的边缘推断。

---

### 5.5 `transmute()` 在涉及 `repr` 属性时更严格地检查等大小

**相关概念**: [memory model / transmute](../../03_advanced/02_unsafe/06_memory_model.md) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155418](https://github.com/rust-lang/rust/pull/155418) · **release-notes 跟踪 issue**: [#156852](https://github.com/rust-lang/rust/issues/156852)

#### 变更动机

`std::mem::transmute` 要求源类型和目标类型大小相等。当类型带有 `repr` 属性（如 `repr(C)`、`repr(transparent)`、`repr(packed)`）时，旧实现的大小相等检查在某些 newtype 场景下存在缺陷，可能错误地允许大小不同的类型之间转换。PR #155418 修复了该检查，确保 `repr` 属性被正确纳入大小比较。

#### 语义影响

- 某些此前编译通过的 `transmute` 调用现在会被正确拒绝。
- 主要影响通过 newtype 包装 `repr(C)`/`repr(transparent)` 类型后再 transmute 的代码。

#### 迁移注意

- 用 `std::mem::size_of` 在编译期或运行期校验转换双方大小。
- 考虑使用 `transmute_copy` 或显式字段映射替代不安全的 `transmute`。

---

### 5.6 `UNSAFE_CODE` lint 一致地覆盖所有 unsafe attributes

**相关概念**: [unsafe](../../03_advanced/02_unsafe/01_unsafe.md) · [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #157201](https://github.com/rust-lang/rust/pull/157201) · **release-notes 跟踪 issue**: [#157704](https://github.com/rust-lang/rust/issues/157704)

#### 变更动机

`#![deny(unsafe_code)]` 用于声明 crate 不使用 `unsafe`。此前某些 unsafe attribute（如 `#[no_mangle]` 在某些上下文）不会被 `UNSAFE_CODE` lint 捕获，导致 "无 unsafe" 声明不可靠。1.98.0 将 lint 逻辑前移到 attribute 解析阶段，确保所有 unsafe attribute 都被一致地计数。

#### 语义影响

- 所有需要在 `unsafe(...)` 包装中的 attribute 现在都会触发 `UNSAFE_CODE` lint。
- 使用 `#![deny(unsafe_code)]` 的 crate 若包含这些 attribute，将直接编译失败。

#### 迁移注意

- 审查 `#![deny(unsafe_code)]` crate 中使用的 attribute，确认哪些是 "unsafe attribute"。
- 若确实需要这些 attribute，可局部 `#[allow(unsafe_code)]` 并附加说明。

---

### 5.7 `ambiguous_glob_imports` 部分转为硬错误

**相关概念**: [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #149195](https://github.com/rust-lang/rust/pull/149195) · **release-notes 跟踪 issue**: [#156648](https://github.com/rust-lang/rust/issues/156648) · **完整语义**: [§1.4](#14-partially-convert-ambiguous_glob_imports-lint-into-a-hard-error)

#### 变更动机

歧义 glob import 此前仅通过 lint 报告，某些最直接的歧义仍可编译通过。1.98.0 将这部分提升为硬错误，防止错误绑定到同名符号。

#### 语义影响

- 最直接的歧义 glob import 现在编译失败。
- 其余歧义仍由 `ambiguous_glob_imports` lint 报告。

#### 迁移注意

- 搜索：`rg "use .*::\\*;"`。
- 用显式 `use module::Item;` 或 `use module::Item as X;` 替换。

---

### 5.8 不接受参数的属性被传参时直接报错

**相关概念**: [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #155193](https://github.com/rust-lang/rust/pull/155193) · **release-notes 跟踪 issue**: [#156641](https://github.com/rust-lang/rust/issues/156641) · **完整语义**: [§1.11](#111-reject-arguments-in-attributes-where-no-arguments-are-expected)

#### 变更动机

`#[inline]`、`#[cold]` 等属性本无参数，但此前错误恢复路径没有稳定拒绝 `#[inline(true)]`。1.98.0 统一检查，防止误用参数。

#### 语义影响

- 无参属性被传参时现在编译错误。
- 诊断更明确，避免用户以为参数生效。

#### 迁移注意

- 搜索：`rg "#\[inline\([^\]]+\)\]|#\[cold\([^\]]+\)\]|#\[track_caller\([^\]]+\)\]"`。
- 移除参数；`#[inline(always)]`/`#[inline(never)]` 仍是合法形式。

---

### 5.9 Windows-gnu 指定最低 mingw-w64 工具链版本

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #158020](https://github.com/rust-lang/rust/pull/158020) · **release-notes 跟踪 issue**: [#158296](https://github.com/rust-lang/rust/issues/158296) · **完整语义**: [§2.1](#21-windows-gnu-targets-now-specify-baseline-tools-versions)

#### 变更动机

Windows-gnu 目标长期依赖用户本地 mingw-w64 版本，碎片化导致链接与 ABI 问题。1.98.0 引入最低工具链版本基线，保证编译器可依赖一致的 CRT 与链接器能力。

#### 语义影响

- 低于基线的 mingw-w64 环境可能无法编译/链接 Windows-gnu 目标。
- 新基线为后续平台特性升级铺平道路。

#### 迁移注意

- 升级本地/CI 的 mingw-w64 到 Rust 推荐版本；通过 `rustup target add x86_64-pc-windows-gnu` 安装的组件通常已满足。
- CI 中固定工具链镜像版本。

---

### 5.10 Solaris/Illumos 移除 `File::lock` 实现

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #157509](https://github.com/rust-lang/rust/pull/157509) · **release-notes 跟踪 issue**: [#157510](https://github.com/rust-lang/rust/issues/157510) · **完整语义**: [§2.4](#24-solaris-remove-filelock-implementation-it-has-the-wrong-semantics)

#### 变更动机

Solaris/Illumos 上 `File::lock` 使用错误底层原语，导致文件锁语义与其他平台不一致。1.98.0 移除实现，避免静默错误。

#### 语义影响

- 这些平台上 `File::lock` 现在返回 `ErrorKind::Unsupported`。
- 其他平台行为不变。

#### 迁移注意

- 面向 Solaris/Illumos 的代码需改用平台特定 advisory lock（如 `fcntl`）或重新设计并发。
- 检测 `Unsupported` 错误并回退。

---

### 5.11 Emscripten 无条件使用 WASM 异常处理 ABI

**相关概念**: [target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ⚠ compatibility change in 1.98.0 · **来源**: [PR #156928](https://github.com/rust-lang/rust/pull/156928) · **release-notes 跟踪 issue**: [#158091](https://github.com/rust-lang/rust/issues/158091) · **完整语义**: [§2.2](#22-on-emscripten-the-wasm-exception-handling-abi-is-now-unconditionally-used)

#### 变更动机

Emscripten 此前提供 `-Zemscripten-wasm-eh=false` 回退到旧 JS 异常处理。随着 WASM EH 支持成熟，1.98.0 移除该开关并统一使用 WASM EH ABI。

#### 语义影响

- `-Zemscripten-wasm-eh=false` 不再合法，使用会报错。
- 输出模块更小、性能更好，但要求运行时支持 WASM exception handling。

#### 迁移注意

- 搜索构建脚本/CI 中的 `emscripten-wasm-eh=false` 并移除。
- 升级部署目标到支持 WASM EH 的 Node.js/浏览器版本。

---

## 6. 升级 1.98.0 检查清单

- [ ] 运行 `cargo check --workspace` 与 `cargo clippy --workspace`，确认无新增 lint/错误；
- [ ] 若自定义 panic hook 存储 `Location`，确认生命周期为 `'static`；
- [ ] 若使用 `derive(Ord)`，检查 `PartialOrd` 与 `Ord` 语义是否一致；
- [ ] 若使用 `repr(transparent)` 包装非 ZST / `repr(C)` / 私有字段类型，按新规则重构；
- [ ] 若在 Windows GNU 目标构建，验证 mingw-w64 工具链基线版本；
- [ ] 若目标平台为 Solaris/Illumos，移除对 `std::fs::File::lock` 的依赖；
- [ ] 若使用 Emscripten/WASM，移除 `-Zemscripten-wasm-eh`；
- [ ] 若使用 `transmute` 或依赖 trait object 默认生命周期，复核类型检查；
- [ ] 若涉及 `std::env::Vars`/`CommandArgs` 跨线程使用，确认 `Send`/`Sync` 边界；
- [ ] 若覆盖 C 运行时符号（`memcmp`/`memset` 等），处理新的 runtime symbol lint；
- [ ] 若生成属性宏，检查是否向无参属性传入了参数。

---

## 7. 批判性分析：与国际来源的对称差

**主要缺口**（2026-07-16 旧版仅覆盖 4 项 stabilized-in-beta 特性）已在本版补齐：

- **语言语义遗漏**：riscv `d`/`e`/`f` target features、`ambiguous_glob_imports` 硬错误、`c_void` 返回 lint、等式谓词语法拒绝、trait object 生命周期默认值修正、解析器 `dyn` 关键字恢复、`UNSAFE_CODE` lint 一致性、StructuralPartialEq PartialEq 边界、属性参数检查、PanicHookInfo `'static` Location 等。
- **标准库 API 遗漏**：`{f32,f64}::algebraic_*`、`String::from_utf16{le|be}`、`str::strip_circumfix`、`NonZero::from_str_radix`、LoongArch CRC intrinsics、`RangeInclusive::from` panic 文档、`ManuallyDrop`/`Box` 文档修正、assert_eq/assert_ne 临时作用域、`env::Vars` 与 `CommandArgs` 的 `Send`/`Sync` 调整、unicode_data.rs 表替换等。
- **编译器/平台遗漏**：Windows TLS destructor 切换到 FLS、Windows-gnu mingw-w64 基线、Emscripten WASM EH 移除、Solaris `File::lock` 移除等。
- **兼容性变更遗漏**：`repr(transparent)` 严格化、`transmute` 等大小检查、attribute 参数拒绝、derive(PartialOrd) 快速路径等。
- **原 RFC merged 跟踪项**（Named `Fn`、register_tool、todo! lint、public/private deps）状态仍停留在 RFC 阶段，已迁移到 [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md) 继续跟踪。

**与国际来源对齐**：本文件基于 GitHub milestone 145 的 31 条 release-notes 跟踪 issue、`releases.rs` 1.98.0 beta 页、Rust Forge 发布节奏与 nightly unstable book 核对；每个特性均给出上游 PR/issue 链接，并在矩阵/小节中给出相关 `concept/` 权威页链接。

---

## 8. 来源与延伸阅读

- [Rust 1.98.0 Release Notes (beta)](https://releases.rs/docs/1.98.0/)
- [Rust Release Notes](https://doc.rust-lang.org/beta/releases.html)
- [Rust Forge — Release Versions](https://forge.rust-lang.org/)
- [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
- [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
- [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)
- [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)
- [1.98 特性 × 领域反查矩阵](feature_domain_matrix_198.md)
- [1.98 兼容性迁移判定树](migration_198_decision_tree.md)

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((Rust 1.98.0 稳定特性))
    1 语言语义
      riscv target features d/e/f
      runtime symbol lints
      CoerceUnsized &mut lifetime shortening
      ambiguous_glob_imports hard error
      c_void return lint
      equality predicate syntax rejection
      repr(transparent) strict trivial fields
      StructuralPartialEq PartialEq bounds
      dyn keyword parser recovery
      batched import resolution
      attribute argument rejection
      PanicHookInfo static Location
    2 编译器与平台
      mingw-w64 baseline tools
      Emscripten WASM EH removal
      Windows TLS FLS destructors
      Solaris File::lock unsupported
    3 标准库与文档
      RangeInclusive panic docs
      assert_eq/assert_ne temporary scope
      ManuallyDrop Box docs
      env::Vars Send/Sync removal
      CommandArgs Send/Sync addition
      String::from_utf16{le|be}
      str::strip_circumfix
      NonZero::from_str_radix
      float_algebraic methods
      LoongArch CRC intrinsics
      unicode_data.rs printables
    4 宏与 Derive
      derive(PartialOrd) fast path
    5 兼容性与破坏性变更
      derive(PartialOrd) consistency
      repr(transparent) strict trivial fields
      equality predicate rejection
      trait object lifetime defaults
      transmute equal-size check
      UNSAFE_CODE unsafe attributes
      ambiguous_glob_imports hard error
      attribute argument rejection
      mingw-w64 baseline
      Solaris File::lock removal
      Emscripten WASM EH removal
```

---

## 9. 反例与边界

> 本节澄清 1.98.0 稳定特性最容易被误读的边界。

| 常见误解 | 反例 | 正确理解 |
|---|---|---|
| "`repr(transparent)` 多字段一直合法" | 包装 `repr(C)` 辅助字段此前只警告，1.98 起硬错误 | 仅允许一个非 ZST + ZST 标记字段 |
| "`derive(PartialOrd) + derive(Ord)` 总是安全" | 手写 `Ord` 与派生 `PartialOrd` 不一致时，快速路径会暴露 | 同时派生或同时手写，保持语义一致 |
| "`c_void` 返回 lint 是错误" | 它是 warn-by-default，仅在 `-D warnings` 时阻断 | 及时改为 `*mut c_void` 即可 |
| "`String::from_utf16le` 处理 BOM" | 它按显式字节序解码，不识别 BOM | 需先手动剥离 BOM 再调用 |
| "`NonZero::from_str_radix("0")` 返回 Ok" | 零值会返回 `ParseIntError` | 错误处理与 `parse::<u32>()` 一致 |
| "`UNSAFE_CODE` 只捕获 `unsafe` 块" | 1.98 起也捕获 unsafe attributes | `#![deny(unsafe_code)]` 范围扩大 |
| "trait object 生命周期省略不受影响" | 完全省略时部分 niche 场景会推断更严或报错 | 公开 API 中显式标注 `dyn Trait + 'static` |
| "`PanicHookInfo::location` 生命周期不变" | 1.98 起返回 `&'static Location<'static>` | 自定义 hook 签名需要更新 |
| "Solaris `File::lock` 仍可拿到锁" | 现在返回 `Unsupported` | 需改用平台特定 advisory lock |

---

## 10. 维护日志

- **2026-07-14**: 建立骨架，迁移自 `rust_1_98_preview.md` 特性矩阵。
- **2026-07-16**: 基于 1.98.0 beta 分支预填充 §1–§4；状态更新为「beta 已冻结，stable 前预填充」。
- **2026-07-31**: 对齐 GitHub milestone 145 的 31 条 release-notes 跟踪 issue、releases.rs 1.98.0 beta 与 nightly unstable book；补齐语言/编译器/标准库 API/兼容性全量特性；重写每个特性的动机/语义/迁移说明；矩阵增加 `concept/` 前向链接；新增批判性分析与对称差、思维导图、反例与边界表。
- **2026-08-01**: 按任务要求重新分组为「语言语义、编译器与平台、标准库与文档、宏与 Derive、兼容性与破坏性变更」五节；将 StructuralPartialEq、属性参数检查、PanicHookInfo `'static` 移入语言语义；新增 §5 兼容性视角子章节覆盖全部 11 项破坏性变更；调整小节格式使 `concept/` 前向链接位于标题后首行，提升 `check_version_semantic_injection.py` 映射识别率。
- **2026-08-20（预计）**: 1.98.0 stable 发布后最终核对官方 release notes，移除 beta 标注。
