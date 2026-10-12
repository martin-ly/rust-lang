# Rust 1.99.0 稳定特性

> **EN**: Rust 1.99.0 Stabilized Features
> **Summary**: Rust 1.99.0 (stable 2026-10-01) 完整稳定特性汇总：语言语义（C-variadic 函数定义、naked variadic、宏 outlined modules、asm! 128-bit 寄存器）、编译器/平台（PIE 默认化、riscv64-musl Tier 2）、标准库 API（VaList、Box/Vec parts、raw layout 三件套、fs::set_times）、Cargo/Rustdoc 与兼容性变更（no_mangle 泛型硬错误、Box::leak 反 unleak 指南），均附权威来源与迁移要点。
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [综述级]
> **权威来源**: 本文件为 `concept/` 权威页（Rust 1.99 稳定特性的 canonical 汇总；基于 2026-10-01 已发布的 1.99.0 stable 官方 release notes 与 Rust Blog 公告核对）。
> **Rust 版本**: **1.99.0 stable**（2026-10-01 发布；branched from master 2026-08-14）
> **最后更新**: 2026-10-12
> **状态**: ✅ 已对齐 1.99.0 stable（官方 release notes 最终核对）
>
> **权威来源**:
>
> · [Rust 1.99.0 Release Notes](https://releases.rs/docs/1.99.0/) ·
> [Rust Release Notes (stable)](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01) ·
> [Announcing Rust 1.99.0 (Rust Blog)](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [RFC Book](https://rust-lang.github.io/rfcs/) ·
> [Rust Blog](https://blog.rust-lang.org/) ·
> [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/) ·
> [The Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/) ·
> [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) ·
> [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.98 稳定特性](rust_1_98_stabilized.md)
> **后置概念**: [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md) · [Rust 1.100+ 远期跟踪](rust_1_100_preview.md)

---

## 0. 1.99 特性矩阵

> **状态图例**：✅ = 已稳定（1.99.0 stable release notes 确认） · ⚠ = 兼容性变更
>
> **主要领域**：Lang = 语言语义 · Compiler/Platform = 编译器与平台 · Std API = 标准库 API · Macro/Derive = 宏与 Derive · Cargo = Cargo · Compat = 兼容性与破坏性变更

| # | 特性 | 主要领域 | 状态 | 权威来源 / 跟踪链接 / 相关概念 |
|:---:|:---|:---|:---|:---|
| 1 | Stabilize C-variadic function definitions（`extern "C"`/`"C-unwind"` 的 `...` 参数列表 + `VaList`） | Lang | ✅ stabilized | [PR #155697](https://github.com/rust-lang/rust/pull/155697) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md) |
| 2 | Stabilize `#[unsafe(naked)]` C-variadic functions（`c_variadic_naked_functions`） | Lang | ✅ stabilized | [PR #159746](https://github.com/rust-lang/rust/pull/159746) · [inline asm](../../03_advanced/05_inline_assembly/01_inline_assembly.md) |
| 3 | Trait methods resolved on adjusted never type（产生 FCW） | Lang | ✅ stabilized | [PR #156047](https://github.com/rust-lang/rust/pull/156047) · [never type](../../01_foundation/02_type_system/02_never_type.md) |
| 4 | Coerce inference variables to trait objects when subtyping-related to a known `Sized` type | Lang | ✅ stabilized | [PR #157820](https://github.com/rust-lang/rust/pull/157820) · [coercion](../../01_foundation/02_type_system/04_coercion_and_casting.md) |
| 5 | Stabilize `#[my_macro] mod foo;`（outlined modules 允许出现在属性/derive 宏体内） | Macro/Derive | ✅ stabilized | [PR #157857](https://github.com/rust-lang/rust/pull/157857) · [proc macros](../../03_advanced/03_proc_macros/01_macros.md) |
| 6 | Stabilize 128-bit integers via vector registers in `asm!` on x86 | Lang | ✅ stabilized | [PR #159525](https://github.com/rust-lang/rust/pull/159525) · [inline asm](../../03_advanced/05_inline_assembly/01_inline_assembly.md) |
| 7 | Add allow-by-default `raw_borrows_via_references` lint | Lang | ✅ stabilized | [PR #138230](https://github.com/rust-lang/rust/pull/138230) · [unsafe reference](../../03_advanced/02_unsafe/07_unsafe_reference.md) |
| 8 | `unconditional_panic` lint 扩展至 chunks/windows 零尺寸调用 | Lang | ✅ stabilized | [PR #153563](https://github.com/rust-lang/rust/pull/153563) · [panic](../../02_intermediate/03_error_handling/03_panic.md) |
| 9 | `overflowing_literals` lint 修复重复取负（`--128_i8` 不再 lint） | Lang | ✅ stabilized | [PR #158302](https://github.com/rust-lang/rust/pull/158302) · [numerics](../../01_foundation/02_type_system/03_numerics.md) |
| 10 | POSIX symbols 加入 `invalid/suspicious_runtime_symbol_definitions` lints | Lang | ✅ stabilized | [PR #158522](https://github.com/rust-lang/rust/pull/158522) · [FFI/linkage](../../03_advanced/04_ffi/03_linkage.md) |
| 11 | Lint unused `#[path]` attributes on inline modules | Lang | ✅ stabilized | [PR #158835](https://github.com/rust-lang/rust/pull/158835) · [module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md) |
| 12 | `unreachable_cfg_select_predicates` lint 纳入 `unused` lint group | Lang | ✅ stabilized | [PR #159179](https://github.com/rust-lang/rust/pull/159179) · [Cargo lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) |
| 13 | 文档化：部分分配允许原地增长（不允许缩小） | Lang | ✅ stabilized | [PR #159729](https://github.com/rust-lang/rust/pull/159729) · [custom allocators](../../03_advanced/06_low_level_patterns/01_custom_allocators.md) |
| 14 | 保证 `UnsafeCell` 内容可不经 `get` 访问（`invalid_reference_casting` 相应调整） | Lang | ✅ stabilized | [PR #159730](https://github.com/rust-lang/rust/pull/159730) · [memory model](../../03_advanced/02_unsafe/06_memory_model.md) |
| 15 | `global_asm!` 计入全局启用的 target features | Lang | ✅ stabilized | [PR #160594](https://github.com/rust-lang/rust/pull/160594) · [inline asm](../../03_advanced/05_inline_assembly/01_inline_assembly.md) |
| 16 | Warn if invalid `doc` attribute used on a macro invocation | Lang | ✅ stabilized | [PR #161003](https://github.com/rust-lang/rust/pull/161003) · [attributes](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) |
| 17 | `-Ctarget-cpu` 转为 AVR/AMDGCN/NVPTX 的 target-modifier | Compiler/Platform | ✅ stabilized | [PR #150732](https://github.com/rust-lang/rust/pull/150732) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 18 | `static_position_independent_executables` 在所有 gnu/musl 目标启用 | Compiler/Platform | ✅ stabilized | [PR #158510](https://github.com/rust-lang/rust/pull/158510) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 19 | rustc 方法建议优先精确匹配 doc alias | Compiler/Platform | ✅ stabilized | [PR #160369](https://github.com/rust-lang/rust/pull/160369) · [rustdoc internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) |
| 20 | `riscv64-unknown-linux-musl` 晋升 Tier 2 with host tools | Compiler/Platform | ✅ stabilized | [PR #158766](https://github.com/rust-lang/rust/pull/158766) · [target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) |
| 21 | `RangeInclusive` 迭代优化（耗尽后 `start()/end()` 行为变化，非保证语义） | Std API | ⚠ compat change | [PR #155114](https://github.com/rust-lang/rust/pull/155114) · [range types](../../02_intermediate/04_types_and_conversions/01_range_types.md) |
| 22 | `transmute_copy` 放宽至 `?Sized`，改用 non-unwinding panic | Std API | ✅ stabilized | [PR #155989](https://github.com/rust-lang/rust/pull/155989) · [memory model](../../03_advanced/02_unsafe/06_memory_model.md) |
| 23 | Stabilized APIs：`VaList`、`Box::into_non_null/from_non_null`、`Vec::into_parts/from_parts`、`VecDeque::retain_back`、`size_of_val_raw`/`align_of_val_raw`/`Layout::for_value_raw`、`String::from_utf8_lossy_owned`、`FromUtf8Error::into_utf8_lossy`、`IntoIterator for Box<[T; N]>`、`FusedIterator for StepBy`、`fs::set_times(_nofollow)` | Std API | ✅ stabilized | [Rust Blog 1.99.0](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0) · [smart pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) · [collections](../../01_foundation/05_collections/01_collections.md) |
| 24 | `escape_debug_ext` 不再转义 U+FF9E/U+FF9F；`NumBuffer` 在 alloc/std 重导出 | Std API | ✅ stabilized | [PR #158057](https://github.com/rust-lang/rust/pull/158057) · [PR #161430](https://github.com/rust-lang/rust/pull/161430) · [strings](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) |
| 25 | Cargo 新内置 profile `debug`（当前与 `dev` 等价，为更快开发迭代做准备） | Cargo | ✅ stabilized | [Cargo #17214](https://github.com/rust-lang/cargo/pull/17214) · [Cargo profiles](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) |
| 26 | edition 2024+ workspace 成员可覆盖继承依赖的 `default-features`（RFC 3945） | Cargo | ✅ stabilized | [RFC 3945](https://github.com/rust-lang/rfcs/pull/3945) · [Cargo #17126](https://github.com/rust-lang/cargo/pull/17126) · [workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) |
| 27 | rustdoc 新增 `unused_footnote_definition` lint；trait impl 过滤智能化（平均提速 20%，最高 40%） | Cargo | ✅ stabilized | [PR #137858](https://github.com/rust-lang/rust/pull/137858) · [rustdoc internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) |
| 28 | 完全弃用 legacy integral modules（`std::i32::MAX` → `i32::MAX`） | Compat | ⚠ compat change | [PR #146882](https://github.com/rust-lang/rust/pull/146882) · [numerics](../../01_foundation/02_type_system/03_numerics.md) |
| 29 | `no_mangle_generic_items` 升级为硬错误 | Compat | ⚠ compat change | [PR #154585](https://github.com/rust-lang/rust/pull/154585) · [FFI/linkage](../../03_advanced/04_ffi/03_linkage.md) |
| 30 | `Box::leak` 文档反对 unleak 模式（改用 `Box::into_non_null`/`into_raw`） | Compat | ⚠ compat change | [PR #160323](https://github.com/rust-lang/rust/pull/160323) · [Rust Blog 1.99.0](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0) · [smart pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) |
| 31 | 其余兼容性变更（`Pin::new_unchecked` 不变量、extern static 引用不提升、union 匹配指南等，见 §6） | Compat | ⚠ compat change | [Release Notes](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01) |

---

## 1. 语言语义

### 1.1 C-variadic 函数定义稳定（`extern "C"` / `"C-unwind"` 的 `...`）

**相关概念**: [Rust FFI](../../03_advanced/04_ffi/01_rust_ffi.md) · [FFI 进阶](../../03_advanced/04_ffi/02_ffi_advanced.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #155697](https://github.com/rust-lang/rust/pull/155697) · [Rust Blog 1.99.0](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0)

Rust 1.99 之前只能**调用**外部定义的变参函数（如 `libc::printf`），现在可以在 Rust 中**定义**它们：`unsafe extern "C" fn my_logger(count: u32, mut args: ...) -> i32`。变参通过 `core::ffi::VaList`（与 C 的 `va_list` 二进制级 ABI 兼容）读取，用 `args.next_arg::<T>()` 逐参数取值；可读取的类型由 `VaArgSafe` trait 白名单约束，防止类型错配。这消除了混合 Rust/C 代码库中为暴露回调/日志函数而保留小型 C shim 的需要。详见 [Reference: functions](https://doc.rust-lang.org/reference/items/functions.html)。

### 1.2 `#[unsafe(naked)]` naked 变参函数稳定（`c_variadic_naked_functions`）

**相关概念**: [Inline assembly](../../03_advanced/05_inline_assembly/01_inline_assembly.md) · [Inline assembly 扩展](../../03_advanced/05_inline_assembly/02_inline_assembly_extended.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #159746](https://github.com/rust-lang/rust/pull/159746)

非 `"C"` ABI 的变参函数必须以 inline assembly 编写，`#![feature(c_variadic_naked_functions)]` 已稳定为 `#[unsafe(naked)]` 形式。面向嵌入式/低层场景，naked 函数不生成编译器序言/尾声代码，可精确控制调用约定。

### 1.3 Trait 方法在调整后的 never type 上解析（产生 FCW）

**相关概念**: [Never type](../../01_foundation/02_type_system/02_never_type.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #156047](https://github.com/rust-lang/rust/pull/156047)

延续 never type 稳定化（1.97 的 fallback 变化）路线：trait 方法解析现在作用于 adjusted never type，产生 fallback-composition warning（FCW），为最终完全稳定 `!` 铺路。

### 1.4 推理变量到 trait object 的强制转换（与 `Sized` 类型有 subtyping 关系时）

**相关概念**: [Coercion & casting](../../01_foundation/02_type_system/04_coercion_and_casting.md) · [Trait objects](../../02_intermediate/01_generics/05_const_generics_and_trait_objects.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #157820](https://github.com/rust-lang/rust/pull/157820)

当推理变量通过 subtyping 关联到一个已知 `Sized` 类型时，允许从推理变量强制转换到 trait object，减少一类 `Box::new` 显式包装需求。

### 1.5 `asm!` 在 x86 上以向量寄存器传递 128-bit 整数

**相关概念**: [Inline assembly](../../03_advanced/05_inline_assembly/01_inline_assembly.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #159525](https://github.com/rust-lang/rust/pull/159525)

`asm!` 的 `in("xmm0")` 等寄存器类现在可用于 `i128`/`u128` 传参（x86 SIMD 寄存器对），低层密码学/数学库受益。

### 1.6 新增/调整的 lints

**相关概念**: [Cargo profiles & lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) · [Unsafe reference](../../03_advanced/02_unsafe/07_unsafe_reference.md)

**状态**: ✅ stabilized in 1.99.0

- 新增 allow-by-default `raw_borrows_via_references` lint：检查立即退化为 raw borrow 的引用（[PR #138230](https://github.com/rust-lang/rust/pull/138230)）
- `unconditional_panic` 扩展至 chunks/windows 尺寸为 0 的函数调用（[PR #153563](https://github.com/rust-lang/rust/pull/153563)）
- `overflowing_literals` 修复重复取负：`--128_i8` 不再 lint，由 `arithmetic_overflow` 接管（[PR #158302](https://github.com/rust-lang/rust/pull/158302)）
- POSIX symbols 加入 `invalid_runtime_symbol_definitions`（deny）与 `suspicious_runtime_symbol_definitions`（warn）（[PR #158522](https://github.com/rust-lang/rust/pull/158522)）
- Lint unused `#[path]` attributes on inline modules（[PR #158835](https://github.com/rust-lang/rust/pull/158835)）
- `unreachable_cfg_select_predicates` 纳入 `unused` lint group（[PR #159179](https://github.com/rust-lang/rust/pull/159179)）
- 宏调用上的非法 `doc` 属性产生警告（[PR #161003](https://github.com/rust-lang/rust/pull/161003)）

### 1.7 UnsafeCell 与分配 grow 语义文档化

**相关概念**: [Memory model](../../03_advanced/02_unsafe/06_memory_model.md) · [Custom allocators](../../03_advanced/06_low_level_patterns/01_custom_allocators.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #159729](https://github.com/rust-lang/rust/pull/159729) · [PR #159730](https://github.com/rust-lang/rust/pull/159730)

- 明确文档化：部分分配允许**原地增长**（in-place grow），但没有任何分配允许缩小
- 保证 `UnsafeCell` 内容可不经 `get()` 访问；`invalid_reference_casting` lint 相应调整（[PR #159960](https://github.com/rust-lang/rust/pull/159960)）

### 1.8 `global_asm!` 计入全局 target features

**相关概念**: [Inline assembly](../../03_advanced/05_inline_assembly/01_inline_assembly.md) · [Target support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #160594](https://github.com/rust-lang/rust/pull/160594)

`global_asm!` 现在感知 `-Ctarget-feature` 等全局启用的 target features，汇编块可用性判定与函数级 `asm!` 一致。

---

## 2. 编译器与平台

### 2.1 `-Ctarget-cpu` 转为 AVR/AMDGCN/NVPTX 的 target-modifier

**相关概念**: [Target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #150732](https://github.com/rust-lang/rust/pull/150732)

这三个后端（AVR、AMD 显卡、NVIDIA PTX）的 `-Ctarget-cpu` 语义统一为 target-modifier 模型，与 x86/ARM 后端行为对齐。

### 2.2 `static_position_independent_executables` 在所有 gnu/musl 目标启用

**相关概念**: [Target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #158510](https://github.com/rust-lang/rust/pull/158510)

静态 PIE（position-independent executables）在全部 `*-linux-gnu` 与 `*-linux-musl` 目标默认启用，改善 ASLR 安全性。

### 2.3 rustc 方法建议优先精确匹配 doc alias

**相关概念**: [Rustdoc internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #160369](https://github.com/rust-lang/rust/pull/160369)

缺失方法报错时，rustc 优先建议 `#[doc(alias = "...")]` 精确匹配的名字，而非相似度搜索。为新手常用误称添加 doc alias 可同时改善编译错误建议与 rustdoc 搜索。

### 2.4 `riscv64-unknown-linux-musl` 晋升 Tier 2 with host tools

**相关概念**: [Target tier / platform support](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #158766](https://github.com/rust-lang/rust/pull/158766)

该目标提供 build host 工具（可在其上运行 rustc/cargo），RISC-V musl 生态（嵌入式 Linux、容器）获得官方支持。

---

## 3. 标准库 API

### 3.1 Raw pointer 布局信息三件套（`Layout::for_value_raw` / `size_of_val_raw` / `align_of_val_raw`）

**相关概念**: [Type layout](../../04_formal/05_rustc_internals/08_type_layout.md) · [Memory model](../../03_advanced/02_unsafe/06_memory_model.md) · [Unsafe reference](../../03_advanced/02_unsafe/07_unsafe_reference.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [Rust Blog 1.99.0](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0) · [docs: for_value_raw](https://doc.rust-lang.org/stable/core/alloc/struct.Layout.html.for_value_raw) · [docs: size_of_val_raw](https://doc.rust-lang.org/stable/core/mem/fn.size_of_val_raw.html) · [docs: align_of_val_raw](https://doc.rust-lang.org/stable/core/mem/fn.align_of_val_raw.html)

从裸指针取 size/alignment 的安全要求就此定案：`Sized` 类型 trivially safe（stable 上早已可行），新稳定的三个函数把能力扩展到 `?Sized`（动态大小）类型。custom allocator 与 FFI 布局桥接是主要用例。

### 3.2 Box / Vec 所有权转换 API

**相关概念**: [Smart pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) · [Collections](../../01_foundation/05_collections/01_collections.md) · [Collections 进阶](../../01_foundation/05_collections/02_collections_advanced.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [Release Notes](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01)

- `Box::into_non_null` / `Box::from_non_null`：Box ↔ `NonNull<T>` 往返（配合 §6 的 Box::leak 新指南，是 unleak 模式的官方替代）
- `Vec::into_parts` / `Vec::from_parts`：Vec ↔ (ptr, cap, len) 三部件拆解/重组
- `IntoIterator` for `Box<[T; N]>`（含 `&` 与 `&mut` 形式）
- `VecDeque::retain_back`

### 3.3 `core::ffi::VaList`（C-variadic 支撑类型）

**相关概念**: [Rust FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [docs: VaList](https://doc.rust-lang.org/stable/core/ffi/struct.VaList.html)

随 §1.1 C-variadic 定义一同稳定，见该节。

### 3.4 UTF-8 lossy 转换 API

**相关概念**: [Strings & encoding](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [Release Notes](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01)

- `String::from_utf8_lossy_owned`：直接产出 `String`，避免 `Cow<str>` 再克隆
- `string::FromUtf8Error::into_utf8_lossy`：从错误对象无损回收字节并做 lossy 转换

### 3.5 迭代器与文件系统 API

**相关概念**: [Iterator patterns](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [Release Notes](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01)

- `FusedIterator for StepBy<I>`
- `std::fs::set_times` / `std::fs::set_times_nofollow`：设置文件的 atime/mtime（nofollow 变体不跟随符号链接）

### 3.6 标准库行为变更

**相关概念**: [Range types](../../02_intermediate/04_types_and_conversions/01_range_types.md) · [Memory model](../../03_advanced/02_unsafe/06_memory_model.md) · [Strings & encoding](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md)

**状态**: ✅ stabilized in 1.99.0（⚠ 其中 RangeInclusive 属非保证语义变化）

- `RangeInclusive` 迭代在部分场景获得优化；副作用是**已耗尽**的 `RangeInclusive` 的 `start()`/`end()` 返回值与作为切片索引的行为可能改变——这些行为本就不保证稳定，故不算破坏性变更（[PR #155114](https://github.com/rust-lang/rust/pull/155114)）
- `transmute_copy` 放宽接受 `?Sized` 类型，且尺寸不匹配时改用 non-unwinding panic（[PR #155989](https://github.com/rust-lang/rust/pull/155989)）
- `escape_debug_ext` 不再转义 U+FF9E/U+FF9F（半角片假名）（[PR #158057](https://github.com/rust-lang/rust/pull/158057)）
- `core::fmt::NumBuffer` 在 `alloc`（及 `std`）重导出（[PR #161430](https://github.com/rust-lang/rust/pull/161430)）

---

## 4. 宏 / Derive

### 4.1 `#[my_macro] mod foo;`（outlined modules 在宏体内）稳定

**相关概念**: [Procedural macros](../../03_advanced/03_proc_macros/01_macros.md) · [Module system](../../02_intermediate/05_modules_and_visibility/01_module_system.md) · [Attributes & macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #157857](https://github.com/rust-lang/rust/pull/157857)

自定义属性宏或 derive 宏的**宏体内部**现在允许出现 outline module 声明（`mod foo;`，即模块实现放在独立文件）。proc macro 框架（如 builder/状态机生成器）可以把生成的模块直接 outline 到文件系统，而不必把全部代码内联展开。

### 4.2 宏相关 lint 变化

**相关概念**: [Declarative macros](../../02_intermediate/06_macros_and_metaprogramming/04_declarative_macros.md) · [Attributes & macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ✅ stabilized in 1.99.0（⚠ 含兼容性成分，详见 §6）

- 宏调用上的非法 `doc` 属性产生警告（[PR #161003](https://github.com/rust-lang/rust/pull/161003)）
- `#[repr(simd)]` 此前被意外允许出现在 stable 的宏调用上，已修复（[PR #158523](https://github.com/rust-lang/rust/pull/158523)）
- 展开为分号的宏现在即使来自**外部 crate** 也会 lint（`semicolon_in_expressions_from_non_local_macros`，见 §6）

---

## 5. Cargo 与 Rustdoc

### 5.1 Cargo：新内置 profile `debug`

**相关概念**: [Cargo profiles & lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [Cargo #17214](https://github.com/rust-lang/cargo/pull/17214) · [Cargo profiles docs](https://doc.rust-lang.org/nightly/cargo/reference/profiles.html)

新增内置 profile `debug`，为把 `dev` profile 从「重调试」迁移到「更快的开发迭代」默认值做准备。当前 `dev` 与 `debug` 完全等价，尚无行为差异——迁移预告，不是破坏性变更。

### 5.2 Cargo：workspace 依赖 `default-features` 覆盖（RFC 3945）

**相关概念**: [Cargo workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) · [Dependency resolution](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) · [Edition 2021→2024](../03_edition_differences/01_edition_2021_to_2024.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [RFC 3945](https://github.com/rust-lang/rfcs/pull/3945) · [Cargo #17126](https://github.com/rust-lang/cargo/pull/17126)

edition 2024 或更新的 workspace 成员现在可以覆盖继承的 workspace 依赖的 `default-features` 字段：`serde = { workspace = true, default-features = false }` 即使 workspace 定义启用了默认 features 也会关闭它们。早期 edition 下该写法被忽略并警告。

### 5.3 Cargo：CI 中默认关闭增量编译

**相关概念**: [DevOps & CI/CD](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md)

**状态**: ⚠ compat change · **来源**: [Cargo #17220](https://github.com/rust-lang/cargo/pull/17220)

检测到 `CI` 环境变量时，Cargo 默认禁用 incremental compilation（CI 通常没有可复用的增量缓存，增量元数据反而拖慢构建并增大磁盘占用）。

### 5.4 Rustdoc：新 lint 与 trait impl 过滤性能

**相关概念**: [Rustdoc internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) · [Rustdoc 1.96 changes](../../06_ecosystem/00_toolchain/07_rustdoc_196_changes.md)

**状态**: ✅ stabilized in 1.99.0 · **来源**: [PR #137858](https://github.com/rust-lang/rust/pull/137858) · [PR #159623](https://github.com/rust-lang/rust/pull/159623) 等

- 新增 `unused_footnote_definition` rustdoc lint
- 更智能的 trait impl 过滤：平均提速 20%，部分真实 crate 最高 40%

---

## 6. 兼容性变更

### 6.1 Legacy integral modules 完全弃用

**相关概念**: [Numerics](../../01_foundation/02_type_system/03_numerics.md)

**状态**: ⚠ compat change · **来源**: [PR #146882](https://github.com/rust-lang/rust/pull/146882)

`std::i32::MAX` 一类 legacy 常量模块完全弃用，应改用 `i32::MAX` 等类型关联常量。

### 6.2 `no_mangle_generic_items` 升级为硬错误

**相关概念**: [FFI linkage](../../03_advanced/04_ffi/03_linkage.md) · [FFI](../../03_advanced/04_ffi/01_rust_ffi.md)

**状态**: ⚠ compat change · **来源**: [PR #154585](https://github.com/rust-lang/rust/pull/154585)

对泛型条目使用 `#[no_mangle]` 从 warning 升级为 hard error（此前长期警告）。

### 6.3 `Box::leak` 反 unleak 指南

**相关概念**: [Smart pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) · [Custom allocators](../../03_advanced/06_low_level_patterns/01_custom_allocators.md)

**状态**: ⚠ compat change（文档指南，非语义变更） · **来源**: [PR #160323](https://github.com/rust-lang/rust/pull/160323) · [Rust Blog 1.99.0](https://blog.rust-lang.org/2026/10/01/Rust-1.99.0)

`Box::leak` 后「unleak」（重新构造 Box 再释放）的模式被官方文档明确反对：此类代码与当前及未来的编译器优化存在问题交互，且在 custom allocator 即将稳定的背景下尤其危险。应改用 `Box::into_non_null` 或 `Box::into_raw`（回收用 `Box::from_non_null`，见 §3.2）。语言语义无变化——旧代码仍可编译，但不应再这样写。

### 6.4 其他兼容性变更（摘要）

**相关概念**: [Pin & Unpin](../../03_advanced/01_async/08_pin_unpin.md) · [Unions](../../02_intermediate/04_types_and_conversions/06_unions.md) · [FFI linkage](../../03_advanced/04_ffi/03_linkage.md) · [Attributes & macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md)

**状态**: ⚠ compat change · **来源**: [Release Notes Compatibility Notes](https://doc.rust-lang.org/stable/releases.html#version-1990-2026-10-01)

- `Pin::new_unchecked` 的安全不变量轻微调整（[PR #156935](https://github.com/rust-lang/rust/pull/156935)）
- 不再对 extern static 的引用做 promotion（[PR #157641](https://github.com/rust-lang/rust/pull/157641)）
- `let` 模式的推断类型现在必须通过类型检查（[PR #157841](https://github.com/rust-lang/rust/pull/157841)）
- hermit/fs 返回 `unsupported()` 而非 `from_raw_os_error(22)`（[PR #158247](https://github.com/rust-lang/rust/pull/158247)）
- const-eval 在产出值类型含泛型时中止（[PR #159504](https://github.com/rust-lang/rust/pull/159504)）
- doc comment 代码块中「不作用于任何东西的属性」成为错误（[PR #159849](https://github.com/rust-lang/rust/pull/159849)）
- PowerPC inline ASM 小端序标量 float 寄存器 lane 修复（[PR #160441](https://github.com/rust-lang/rust/pull/160441)）
- doctest 过滤不再考虑 `doc(cfg())`（[PR #159014](https://github.com/rust-lang/rust/pull/159014)）
- associated const 类型中的匿名生命周期推断为 `'static`（[PR #156508](https://github.com/rust-lang/rust/pull/156508)）
- 展开为分号的宏对**非本地宏**也 lint：拆分为 `semicolon_in_expressions_from_non_local_macros`（[PR #159222](https://github.com/rust-lang/rust/pull/159222) · [PR #159700](https://github.com/rust-lang/rust/pull/159700)）。遇到该 lint 应报告给提供宏的 crate，而不是只在自己 crate 里静默
- Rust Reference 不再推荐「单一 pattern 匹配 union 并与其他值并列」（手写 tagged union 模式）：编译器可能在检查 scrutinee 其余部分前读取 union 内容，构成 UB（[reference #2303](https://github.com/rust-lang/reference/pull/2303)）

---

## 7. 内部变更（不影响公共接口）

### 7.1 rustc 升级到 LLVM 23

**相关概念**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) · [Rustc dev guide](https://rustc-dev-guide.rust-lang.org/)

**状态**: ✅ internal · **来源**: [PR #158734](https://github.com/rust-lang/rust/pull/158734)

rustc 后端升级到 LLVM 23。第三方报道基准显示平均编译 wall time 下降约 1.2%（两个月累计约 4.57% 提升，含其他优化）。不影响公共接口，但影响 codegen 质量与 `-Ctarget-cpu` 等选项的可用特性集。
