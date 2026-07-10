# Rust Reference 对齐矩阵 {#rust-reference-对齐矩阵}

> **EN**: Rust Reference Alignment
> **Summary**: Rust Reference 对齐矩阵 Rust Reference Alignment.
> **概念族**: 权威来源对齐 / Rust Reference
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rust Reference 对齐矩阵 {#rust-reference-对齐矩阵}](#rust-reference-对齐矩阵-rust-reference-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、词法与语法 {#二词法与语法}](#二词法与语法-二词法与语法)
  - [三、类型系统（Type System） {#三类型系统}](#三类型系统-三类型系统)
  - [四、表达式与语句 {#四表达式与语句}](#四表达式与语句-四表达式与语句)
  - [五、Items 与 Modules {#五items-与-modules}](#五items-与-modules-五items-与-modules)
  - [六、Traits 与泛型（Generics） {#六traits-与泛型}](#六traits-与泛型-六traits-与泛型)
  - [七、Unsafe 与 FFI {#七unsafe-与-ffi}](#七unsafe-与-ffi-七unsafe-与-ffi)
  - [八、Attributes {#八attributes}](#八attributes-八attributes)
  - [九、版本差异 {#九版本差异}](#九版本差异-九版本差异)
  - [十、未覆盖缺口 {#十未覆盖缺口}](#十未覆盖缺口-十未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的概念、机制、反例与 [Rust Reference](https://doc.rust-lang.org/reference/) 的规范章节建立映射。

对齐状态：

- ✅ 已对齐：项目文档与 Reference 一致。
- 🔄 部分对齐：部分章节已覆盖，仍有细化空间。
- ⏳ 待对齐：尚未建立直接映射。

---

## 二、词法与语法 {#二词法与语法}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Lexical Elements](https://doc.rust-lang.org/reference/tokens.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 | 基础词法在类型基础中提及 |
| [Macros](https://doc.rust-lang.org/reference/macros.html) | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | 🔄 | 声明宏（Declarative Macro）/过程宏（Procedural Macro）有 crate 示例 |
| [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | crate、module、source file 规则 |

---

## 三、类型系统 {#三类型系统}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Types](https://doc.rust-lang.org/reference/types.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | ✅ | 基础类型、函数类型、trait 对象 |
| [Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 | ✅ | `dyn Trait` 大小不固定 |
| [Generics](https://doc.rust-lang.org/reference/items/generics.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | 泛型参数、约束 |
| [Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | ✅ | 生命周期参数、省略规则 |
| [Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html) | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | ✅ | 型变规则 |
| [Type Coercions](https://doc.rust-lang.org/reference/type-coercions.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 | 可扩展专门章节 |

---

## 四、表达式与语句 {#四表达式与语句}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Expressions](https://doc.rust-lang.org/reference/expressions.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | async 块表达式 |
| [Control Flow](https://doc.rust-lang.org/reference/expressions.html#control-flow-expressions) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | 🔄 | 基础控制流在 crate 中 |
| [Match Expressions](https://doc.rust-lang.org/reference/expressions/match-expr.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | 🔄 | 模式匹配（Pattern Matching）示例 |

---

## 五、Items 与 Modules {#五items-与-modules}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Items and Modules](https://doc.rust-lang.org/reference/items.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | 模块（Module）系统规范 |
| [Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | `pub`、`pub(crate)`、`pub(in path)` |
| [Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 | ✅ | `use` 路径相对/绝对 |
| [Linkage](https://doc.rust-lang.org/reference/linkage.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | ✅ | `crate-type`、`#[no_mangle]` |

---

## 六、Traits 与泛型 {#六traits-与泛型}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Traits](https://doc.rust-lang.org/reference/items/traits.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 定义、实现、关联类型 |
| [Implementations](https://doc.rust-lang.org/reference/items/implementations.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §5 | ✅ | Orphan 规则 |
| [Associated Items](https://doc.rust-lang.org/reference/items/associated-items.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §6 | ✅ | 关联类型歧义 |

---

## 七、Unsafe 与 FFI {#七unsafe-与-ffi}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ✅ | unsafe 操作边界 |
| [Unsafe Functions](https://doc.rust-lang.org/reference/items/functions.html#unsafe-functions) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 | ✅ | 裸指针操作 |
| [External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | ✅ | FFI 内存协议 |
| [Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ✅ | UB 边界 |

---

## 八、Attributes {#八attributes}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Attributes](https://doc.rust-lang.org/reference/attributes.html) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | 🔄 | `#[no_mangle]`、`#[repr]` 等部分覆盖 |
| [Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ | `cfg` 与 feature flag |

---

## 九、版本差异 {#九版本差异}

| Reference 章节 | 项目文档 | 状态 | 备注 |
|----------------|----------|------|------|
| [Editions](https://doc.rust-lang.org/edition-guide/) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | ✅ | Edition 差异映射 |
| [Unsafe Op in Unsafe Fn](https://doc.rust-lang.org/reference/items/functions.html#unsafe-functions) (2024) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 | ✅ | Edition 2024 lint 变化 |

---

## 十、未覆盖缺口 {#十未覆盖缺口}

1. `const` 求值与 `const fn` 的 Reference 章节可进一步细化。
2. 宏（Macro）展开 hygiene 与解析规则的 Reference 映射待扩展。
3. 异步（Async） trait / RPITIT 的 Reference 章节需随 Rust 1.97+ 更新。

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
