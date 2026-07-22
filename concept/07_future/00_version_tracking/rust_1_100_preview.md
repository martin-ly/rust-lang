# Rust 1.100+ 前沿特性预览

> **代码状态**: [跟踪级 — 待补充]
>
> **EN**: Rust 1.100+ Preview
> **Summary**: Rust 1.100 and beyond: nightly language features, compiler infrastructure, and ecosystem trends tracked for future stabilization.
> **Rust 版本**: 1.100.0 (nightly preview)
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [实验级]
> **权威来源**: 本文件为 `concept/` 权威页（1.100+ **周期跟踪** canonical）。
> **Canonical 分工**: 本页 = 周期跟踪（nightly 特性 / RFC 进展 / API 探测，随两周巡检滚动）；1.100.0 **稳定特性权威汇总** = `rust_1_100_stabilized.md`（待 1.100.0 分支进入 beta 后建立）。
> **跟踪版本**: nightly 1.100.0（预计 2026-11-12 进入 stable）
> **预计稳定时间**: **1.100.0 = 2026-11-12**（依据 [Rust Forge](https://forge.rust-lang.org/) 六周发布节奏）
> **当前阶段**: 🧪 Nightly 实验性 / 设计或 MCP 阶段
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **状态**: 特性集高度不确定，稳定时间和具体内容以官方发布为准
>
> **权威来源**:
>
> · [Rust Forge — Release Versions](https://forge.rust-lang.org/)
> · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
> · [TRPL](https://doc.rust-lang.org/book/title-page.html)
> · [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
> · [Rust Internals Forum](https://internals.rust-lang.org/)
> · [releases.rs — nightly 1.100.0](https://releases.rs/)
>
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md) · [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md)
> **后置概念**: Rust 1.101+ 前沿特性预览（待 1.100.0 进入 beta 后建立）

---

## 零、1.100 周期跟踪清单（2026-07-23 初始）

> **状态取值**：`stabilized in 1.100 beta`（已随 1.100.0 beta 分支合入）/ `RFC merged`（RFC 已合并，实现跟踪中）/ `FCP`（最终评论期）/ `nightly only`（nightly 可用，未排期）/ `design`（设计/MCP 阶段）。
> **实测来源**：[Rust Forge](https://forge.rust-lang.org/)（2026-07-23）· [releases.rs](https://releases.rs/)

| 特性 | 状态 | 跟踪链接 |
|:---|:---|:---|
| `gen` blocks / `yield_expr` | nightly only | [Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/language-features/gen-blocks.html) · [预览页](../02_preview_features/25_gen_blocks_preview.md) |
| `async_drop` | nightly only | [预览页](../02_preview_features/22_async_drop_preview.md) |
| Return Type Notation（RTN） | nightly only | [预览页](../02_preview_features/09_return_type_notation_preview.md) |
| Specialization | nightly only | [预览页](../02_preview_features/31_specialization_preview.md) |
| Effects system / keyword generics | experimental | [预览页](../02_preview_features/01_effects_system.md) |
| Safety tags | FCP / 讨论中 | [rfcs#3842](https://github.com/rust-lang/rfcs/pull/3842) · [预览页](../02_preview_features/03_safety_tags_preview.md) |
| `derive(CoercePointee)` | FCP finished | [预览页](../02_preview_features/05_derive_coerce_pointee_preview.md) |
| Type Alias Impl Trait（TAIT） | nightly only | [预览页](../02_preview_features/17_type_alias_impl_trait_preview.md) |
| `const_trait_impl`（`~const`） | nightly only | [预览页](../02_preview_features/06_const_trait_impl_preview.md) |
| Portable SIMD | nightly only | [预览页](../02_preview_features/29_aarch64_sve_sme_preview.md) |
| `f16` / `f128` | nightly only | [预览页](../02_preview_features/35_f16_f128_preview.md) |
| Arbitrary self types | nightly only | [预览页](../02_preview_features/18_arbitrary_self_types_preview.md) |
| Field projections | experimental | [Project Goals](https://rust-lang.github.io/rust-project-goals/2026/field-projections.html) · [预览页](../02_preview_features/23_field_projections_preview.md) |
| BorrowSanitizer | prototype | [Project Goals](https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html) · [预览页](../02_preview_features/24_borrow_sanitizer.md) |

> **维护约定**：每两周按 Rust Forge 发布节奏核对本表；1.100.0 进入 beta 后（预计 2026-09-25）将状态迁移更新，稳定后建立 `rust_1_100_stabilized.md`。

---

## 一、语言特性预览

本节聚焦 1.100 周期内仍在 nightly 或实验阶段的语言级特性。这些特性尚未确定是否能在 1.100.0 稳定，因此仅提供状态快照并指向各自的深度预览页。

### 1.1 `gen` blocks / 异步生成器

**状态**: 🧪 nightly only

`gen { yield x; }` 提供零成本的同步迭代器生成语法，`async gen` / `for await` 则面向异步 `Stream` 生产。

**深度文档**: [25_gen_blocks_preview.md](../02_preview_features/25_gen_blocks_preview.md)

### 1.2 Async Drop

**状态**: 🧪 nightly only

为异步上下文提供异步析构语义，解决 `Drop::drop` 不能 `.await` 的长期痛点。

**深度文档**: [22_async_drop_preview.md](../02_preview_features/22_async_drop_preview.md)

### 1.3 Return Type Notation（RTN）

**状态**: 🧪 nightly only

`fn foo() -> impl Trait<method(): Send>` 式语法，用于约束不透明返回类型关联项的 bound。

**深度文档**: [09_return_type_notation_preview.md](../02_preview_features/09_return_type_notation_preview.md)

### 1.4 Specialization

**状态**: 🧪 nightly only

允许为泛型 impl 的特定类型子集提供更优实现，卡在 `min_specialization` 的 soundness 论证上。

**深度文档**: [31_specialization_preview.md](../02_preview_features/31_specialization_preview.md)

---

## 二、编译器与工具链预览

本节跟踪影响 rustc 核心架构与日常开发体验的编译器基础设施进展。

### 2.1 Next-gen trait solver / Polonius

- **Next solver**: 新 trait 求解器持续 nightly 验证，目标是替代当前求解器。
- **Polonius**: 基于约束的借用检查新框架，旨在支持更复杂的非词法生命周期场景。

### 2.2 Cranelift backend

`cranelift` 后端持续改进 debug build 编译速度，部分配置已可在 nightly 体验。

**深度文档**: [16_cranelift_backend_preview.md](../02_preview_features/16_cranelift_backend_preview.md)

---

## 三、标准库与目标平台预览

本节汇总 1.100 周期内在标准库 API 与目标平台层面的实验性进展，目前以扩展浮点类型和可移植 SIMD 为代表。

### 3.1 `f16` / `f128`

**状态**: 🧪 nightly only

扩展浮点类型在特定硬件目标上逐步可用，ABI 与标准库集成仍在收敛。

**深度文档**: [35_f16_f128_preview.md](../02_preview_features/35_f16_f128_preview.md)

### 3.2 Portable SIMD / SVE / SME

**状态**: 🧪 nightly only

AArch64 SVE/SME 与可移植 SIMD 抽象持续推进中。

**深度文档**: [29_aarch64_sve_sme_preview.md](../02_preview_features/29_aarch64_sve_sme_preview.md)

---

## 四、Cargo 与生态预览

本节跟踪 1.100 周期内 Cargo 与生态层面的预览特性。

### 4.1 Public/Private Dependencies

**状态**: 🔄 RFC merged，Cargo 实现跟踪中

Cargo 将支持在依赖中标记 `public = true/false`，以区分「依赖类型出现在公共 API 中」与「仅内部使用」。

**深度文档**: [27_cargo_semver_checks_preview.md](../02_preview_features/27_cargo_semver_checks_preview.md)

### 4.2 cargo-script 稳定化

**状态**: 🧪 nightly 实验性

单文件 Rust 脚本（frontmatter 内嵌 `[dependencies]`）从 nightly 走向稳定。

**深度文档**: [01_cargo_script.md](../../06_ecosystem/01_cargo/01_cargo_script.md)

---

## 五、形式化与安全预览

### 5.1 Safety Tags

**状态**: 🧪 RFC 讨论中

`#[safety(...)]` 属性旨在为 unsafe 相关构造提供机器可读的语义标注。

**深度文档**: [03_safety_tags_preview.md](../02_preview_features/03_safety_tags_preview.md)

### 5.2 BorrowSanitizer

**状态**: 🧪 Rust Project Goal 2026；LLVM RFC 已发布

基于 LLVM 的 sanitizer，在运行时检测 Tree Borrows 违规。

**深度文档**: [24_borrow_sanitizer.md](../02_preview_features/24_borrow_sanitizer.md)

---

## 六、跟踪与更新机制

> **稳定特性汇总**：1.100.0 稳定后的权威汇总页为 `rust_1_100_stabilized.md`（待建立）；本页仅负责周期跟踪。

本页与下游页面保持以下更新约定：

| 机制 | 约定 |
|:---|:---|
| 更新频率 | 每个 6 周发布周期核对一次 beta 分支 release notes；周期内仅在跟踪项状态变化时更新 |
| 状态标记 | ✅ 已稳定 / 🔄 beta 中 / 🧪 nightly-only / ⏳ 待定 / ❌ 已撤回，五态互斥 |
| 事实源优先级 | 官方 release notes > rust-lang/rust PR 合并记录 > Project Goals 月度更新 > internals 讨论 |
| 登记规则 | 仅当 PR 合并进对应分支才登记；"计划中/讨论中"不进入特性表 |

---

## 七、来源与延伸阅读

- [Rust Forge — Release Versions](https://forge.rust-lang.org/)
- [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
- [TRPL](https://doc.rust-lang.org/book/title-page.html)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust Internals Forum](https://internals.rust-lang.org/)
- [releases.rs](https://releases.rs/)
- [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
- [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)
- [Rust 版本跟踪](01_rust_version_tracking.md)

---

> **权威来源**: [Rust Forge — Release Versions](https://forge.rust-lang.org/)
>
> **权威来源对齐变更日志**: 2026-07-23 建立，对齐 Rust 1.100.0 nightly 跟踪周期（预计 2026-11-12 进入 stable）。

**文档版本**: 1.0
**最后更新**: 2026-07-23
**状态**: 🧪 周期跟踪骨架
