> **内容分级**: [综述级]

# 外部权威来源主题索引（External Authority Topic Index）
>
> **EN**: External Authority Topic Index
> **Summary**: A machine-readable index mapping all leaf topics from 9 international Rust authority sources to the corresponding `concept/` pages or marking them as "external-only" for granular/example-level coverage.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [维护者 / 研究者]
> **Bloom 层级**: L0-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 为每个外部权威主题提供项目内坐标或缺口标记
> **定位**: 将 TRPL、Reference、Rust By Example、Nomicon、Edition Guide、Async Book、rustc-dev-guide、API Guidelines、Unsafe Code Guidelines 的 SUMMARY 主题与项目 `concept/` 进行主题对齐，形成可持续的“权威来源 ↔ 项目概念”双向地图。
>
> **前置概念**: [Authority Source Map](01_authority_source_map.md) · [International Authority Index](05_international_authority_index.md) · [Topic-Authority Alignment Map](04_topic_authority_alignment_map.md)
> **后置概念**: [Concept Index](../04_navigation/03_concept_index.md) · [Global TODO Tracker](../00_framework/todos.md)
>
> **来源**:
> [TRPL](https://doc.rust-lang.org/book/) ·
> [Rust Reference](https://doc.rust-lang.org/reference/) ·
> [Rust By Example](https://doc.rust-lang.org/rust-by-example/) ·
> [The Rustonomicon](https://doc.rust-lang.org/nomicon/) ·
> [Edition Guide](https://doc.rust-lang.org/edition-guide/) ·
> [Async Book](https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html) ·
> [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) ·
> [API Guidelines](https://rust-lang.github.io/api-guidelines/) ·
> [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

---

> **对应 Crate**: N/A
> **对应练习**: N/A

## 📑 目录

- [外部权威来源主题索引（External Authority Topic Index）](#外部权威来源主题索引external-authority-topic-index)
  - [📑 目录](#-目录)
  - [一、对齐方法论](#一对齐方法论)
  - [二、TRPL 主题映射](#二trpl-主题映射)
  - [三、Rust Reference 主题映射](#三rust-reference-主题映射)
  - [四、Rust By Example 主题映射](#四rust-by-example-主题映射)
  - [五、The Rustonomicon 主题映射](#五the-rustonomicon-主题映射)
  - [六、Edition Guide 主题映射](#六edition-guide-主题映射)
  - [七、Async Book 主题映射](#七async-book-主题映射)
  - [八、rustc-dev-guide 主题映射](#八rustc-dev-guide-主题映射)
  - [九、API Guidelines 主题映射](#九api-guidelines-主题映射)
  - [十、Unsafe Code Guidelines 主题映射](#十unsafe-code-guidelines-主题映射)
  - [十一、未覆盖缺口清单](#十一未覆盖缺口清单)
  - [十二、维护流程](#十二维护流程)

---

## 一、对齐方法论

本索引采用以下规则判定一个外部主题是否被项目覆盖：

1. **精确匹配**：外部主题标题与项目 `concept/` 文件 `**EN**` 英文标题或中文标题高度一致。
2. **主题包含**：外部主题为项目某一概念的下位细分（如 Rust By Example 的某个具体示例），则标记为“示例级/外部独有”，不在 `concept/` 中复制。
3. **项目深化**：项目对同一主题提供了更深（L3-L4）或更广（L5-L7）的内容，则双向链接。
4. **真正缺口**：外部有系统权威页而项目未覆盖，且不属于示例/实现细节粒度的主题，列入 §十一 缺口清单。

符号约定：

- ✅ — 项目已覆盖，链接到 `concept/` 权威页
- ⚠️ — 项目已覆盖但需补充细节
- 📎 — 示例级/实现细节，由外部保留，项目不复制
- ❌ — 真正缺口，待补充

---

## 二、TRPL 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Getting Started | [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ✅ |
| Installation | [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ✅ |
| Hello, World! / Hello, Cargo! | [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ✅ |
| Programming a Guessing Game | 📎 示例级 | 📎 |
| Common Programming Concepts | [PL Prerequisites](../../01_foundation/00_start/01_pl_prerequisites.md) | ✅ |
| Variables and Mutability | [Variable Model](../../01_foundation/03_values_and_references/03_variable_model.md) | ✅ |
| Data Types | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | ✅ |
| Functions | [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | ✅ |
| Comments | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) | ✅ |
| Control Flow | [Control Flow](../../01_foundation/04_control_flow/01_control_flow.md) | ✅ |
| Understanding Ownership | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | ✅ |
| References and Borrowing | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | ✅ |
| The Slice Type | [Reference Semantics](../../01_foundation/03_values_and_references/01_reference_semantics.md) | ✅ |
| Using Structs | [Structs](../../01_foundation/07_modules_and_items/04_structs.md) | ✅ |
| Enums and Pattern Matching | [Enumerations](../../01_foundation/07_modules_and_items/05_enumerations.md) · [Patterns](../../01_foundation/04_control_flow/02_patterns.md) | ✅ |
| Packages, Crates, and Modules | [Modules and Paths](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) · [Crates and Source Files](../../01_foundation/07_modules_and_items/11_crates_and_source_files.md) | ✅ |
| Common Collections | [Collections](../../01_foundation/05_collections/01_collections.md) · [Collections Advanced](../../01_foundation/05_collections/02_collections_advanced.md) | ✅ |
| Error Handling | [Error Handling Basics](../../01_foundation/08_error_handling/01_error_handling_basics.md) · [Error Handling Control Flow](../../01_foundation/08_error_handling/02_error_handling_control_flow.md) | ✅ |
| Generic Types, Traits, and Lifetimes | [Generics](../../02_intermediate/01_generics/01_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | ✅ |
| Writing Automated Tests | [Testing Basics](../../01_foundation/10_testing_basics/01_testing_basics.md) | ✅ |
| An I/O Project | 📎 项目级示例 | 📎 |
| Iterators and Closures | [Iterator Patterns](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md) · [Closure Basics](../../01_foundation/00_start/03_closure_basics.md) | ✅ |
| More about Cargo | [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) 等 L6 Cargo 系列 | ✅ |
| Smart Pointers | [Smart Pointers](../../02_intermediate/02_memory_management/04_smart_pointers.md) | ✅ |
| Fearless Concurrency | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | ✅ |
| Async, Await, Futures, and Streams | [Async Programming](../../03_advanced/01_async/01_async.md) | ✅ |
| Object Oriented Programming Features | [Traits](../../02_intermediate/00_traits/01_traits.md) · [Advanced Traits](../../02_intermediate/00_traits/04_advanced_traits.md) §TRPL OOP 设计模式对照 | ✅ 已补充 |
| Patterns and Matching | [Patterns](../../01_foundation/04_control_flow/02_patterns.md) | ✅ |
| Advanced Features | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Advanced Traits](../../02_intermediate/00_traits/04_advanced_traits.md) · [Advanced Types](../../02_intermediate/04_types_and_conversions/04_type_system_advanced.md) · [Macros](../../03_advanced/03_proc_macros/01_macros.md) | ✅ |
| Final Project: Web Server | [Network Programming](../../03_advanced/06_low_level_patterns/04_network_programming.md) · [Web Frameworks](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | ✅ 核心概念已覆盖；逐步代码对照属示例级，保留在 TRPL |
| Appendix: Keywords / Operators / Derivable Traits / Dev Tools / Editions / Nightly Rust | [Keywords](../../01_foundation/00_start/06_keywords.md) · [Operators and Symbols](../../01_foundation/00_start/07_operators_and_symbols.md) · [Derive Traits](../../02_intermediate/00_traits/06_derive_traits.md) · [Useful Development Tools](../../01_foundation/10_testing_basics/02_useful_development_tools.md) · [Editions](../../07_future/00_version_tracking/02_editions.md) | ✅ |

---

## 三、Rust Reference 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Notation | [Notation](../../04_formal/06_notation/01_notation.md) | ✅ |
| Lexical structure / Keywords / Identifiers / Comments / Whitespace / Tokens | [Lexical Structure](../../04_formal/05_rustc_internals/10_lexical_structure.md) · [Keywords](../../01_foundation/00_start/06_keywords.md) | ✅ |
| Macros / Macros by example / Procedural macros | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Procedural Macro](../../03_advanced/03_proc_macros/02_proc_macro.md) | ✅ |
| Crates and source files | [Crates and Source Files](../../01_foundation/07_modules_and_items/11_crates_and_source_files.md) | ✅ |
| Conditional compilation | [Conditional Compilation](../../03_advanced/03_proc_macros/11_conditional_compilation.md) | ✅ |
| Items (Modules, Functions, Type aliases, Structs, Enums, Unions, Constants, Statics, Traits, Implementations, External blocks, Generics, Associated items) | [Items](../../01_foundation/07_modules_and_items/12_items.md) · [Items Reference](../../04_formal/05_rustc_internals/11_items_reference.md) · [Statements and Expressions Reference](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) · [Patterns Reference](../../04_formal/05_rustc_internals/14_patterns_reference.md) · [Type System Reference](../../04_formal/00_type_theory/09_type_system_reference.md) · [Names Reference](../../04_formal/05_rustc_internals/16_names_reference.md) | ✅ |
| Attributes | [Attributes](../../04_formal/05_rustc_internals/12_attributes.md) · [Attributes by Category](../../02_intermediate/06_macros_and_metaprogramming/06_attributes_by_category.md) | ✅ |
| Statements and expressions | [Statements and Expressions](../../01_foundation/04_control_flow/04_statements_and_expressions.md) | ✅ |
| Patterns | [Patterns](../../01_foundation/04_control_flow/02_patterns.md) · [Patterns Reference](../../04_formal/05_rustc_internals/14_patterns_reference.md) | ✅ |
| Type system / Types / Type layout / Interior mutability / Subtyping / Trait bounds / Type coercions / Destructors / Lifetime elision | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) · [Type System Reference](../../04_formal/00_type_theory/09_type_system_reference.md) · [Type Layout](../../04_formal/05_rustc_internals/08_type_layout.md) · [Interior Mutability](../../02_intermediate/02_memory_management/02_interior_mutability.md) · [Subtype Variance](../../04_formal/00_type_theory/02_subtype_variance.md) · [Destructors](../../04_formal/05_rustc_internals/09_destructors.md) · [Lifetimes Advanced](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | ✅ |
| Special types and traits | [Special Types and Traits](../../04_formal/05_rustc_internals/07_special_types_and_traits.md) | ✅ |
| Names / Namespaces / Scopes / Preludes / Paths / Name resolution / Visibility and privacy | [Names, Scopes and Resolution](../../04_formal/05_rustc_internals/06_names_and_resolution.md) · [Preludes](../../01_foundation/07_modules_and_items/10_preludes.md) · [Visibility and Privacy](../../03_advanced/06_low_level_patterns/10_visibility_and_privacy.md) | ✅ |
| Memory model / Memory allocation and lifetime / Variables | [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) · [Memory Allocation and Lifetime](../../03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) · [Variables](../../03_advanced/06_low_level_patterns/09_variables.md) | ✅ |
| Panic | [Panic Mechanism](../../02_intermediate/03_error_handling/03_panic.md) | ✅ |
| Linkage | [Linkage](../../03_advanced/04_ffi/03_linkage.md) | ✅ |
| Inline assembly | [Inline Assembly](../../03_advanced/05_inline_assembly/01_inline_assembly.md) | ✅ |
| Unsafety / unsafe keyword / Behavior considered undefined / Behavior not considered unsafe | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | ✅ |
| Constant evaluation | [Constant Evaluation](../../04_formal/03_operational_semantics/07_constant_evaluation.md) | ✅ |
| Application binary interface | [Application Binary Interface](../../04_formal/05_rustc_internals/05_application_binary_interface.md) | ✅ |
| The Rust runtime | [The Rust Runtime](../../03_advanced/06_low_level_patterns/07_rust_runtime.md) | ✅ |
| Appendices (Grammar, Syntax index, Macro ambiguity, Influences, Glossary) | [Reference Appendices](../../04_formal/05_rustc_internals/17_reference_appendices.md) | ✅ |

---

## 四、Rust By Example 主题映射

Rust By Example 的绝大多数主题为**示例级细分**，项目通过 `crates/`、`examples/` 和 `exercises/` 覆盖，不在 `concept/` 中重复。关键映射：

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Hello World / Comments / Formatted print / Display / Formatting | [Strings and Text](../../01_foundation/06_strings_and_text/01_strings_and_text.md) · [Display and Debug Formatting](../../01_foundation/06_strings_and_text/03_formatting_and_display.md) | ✅ |
| Primitives / Custom Types / Variable Bindings / Types / Conversion | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) · [Coercion and Casting](../../01_foundation/02_type_system/04_coercion_and_casting.md) | ✅ |
| Expressions / Flow of Control | [Control Flow](../../01_foundation/04_control_flow/01_control_flow.md) | ✅ |
| Functions / Methods / Closures | [Functions](../../01_foundation/07_modules_and_items/02_functions.md) · [Closure Basics](../../01_foundation/00_start/03_closure_basics.md) · [Closure Types](../../02_intermediate/04_types_and_conversions/02_closure_types.md) | ✅ |
| Modules / Crates / Cargo | [Modules and Paths](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) · [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | ✅ |
| Attributes / Generics / Traits | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Generics](../../02_intermediate/01_generics/01_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) | ✅ |
| Scoping rules / Lifetimes | [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [Lifetimes Advanced](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | ✅ |
| macro_rules! | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Macro Patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md) | ✅ |
| Error handling | [Error Handling Basics](../../01_foundation/08_error_handling/01_error_handling_basics.md) | ✅ |
| Std library types / Std misc | [Collections](../../01_foundation/05_collections/01_collections.md) · [Strings and Text](../../01_foundation/06_strings_and_text/01_strings_and_text.md) · [Standard I/O and Process](../../01_foundation/00_start/05_std_io_and_process.md) | ✅ |
| Testing | [Testing Basics](../../01_foundation/10_testing_basics/01_testing_basics.md) | ✅ |
| Unsafe Operations / Inline assembly | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Inline Assembly](../../03_advanced/05_inline_assembly/01_inline_assembly.md) | ✅ |
| 其余具体示例（Testcase: List、Combinators、map-reduce 等） | `examples/` / `crates/` / `exercises/` | 📎 |

---

## 五、The Rustonomicon 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Meet Safe and Unsafe / What Unsafe Can Do / Working with Unsafe | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Unsafe Boundary Panorama](../../03_advanced/02_unsafe/02_unsafe_boundary_panorama.md) | ✅ |
| Data Layout / repr(Rust) / Exotically Sized Types / Other reprs | [Type Layout](../../04_formal/05_rustc_internals/08_type_layout.md) · [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) | ✅ |
| Ownership / References / Aliasing / Lifetimes / HRTB / Subtyping / Drop Check / PhantomData | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) · [Lifetimes Advanced](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) · [Subtype Variance](../../04_formal/00_type_theory/02_subtype_variance.md) · [Unsafe Collections Internals](../../03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md) | ✅ |
| Type Conversions / Coercions / Casts / Transmutes | [Coercion and Casting](../../01_foundation/02_type_system/04_coercion_and_casting.md) · [Type Conversions](../../02_intermediate/04_types_and_conversions/07_type_conversions.md) | ✅ |
| Uninitialized Memory / Drop Flags | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [Unsafe Collections Internals](../../03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md) | ✅ |
| Ownership Based Resource Management / Constructors / Destructors / Leaking | [Destructors](../../04_formal/05_rustc_internals/09_destructors.md) · [Memory Allocation and Lifetime](../../03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) | ✅ |
| Unwinding / Exception Safety / Poisoning | [Exception Safety: C++ vs Rust](../../02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md) · [Panic Mechanism](../../02_intermediate/03_error_handling/03_panic.md) | ✅ |
| Concurrency / Races / Send and Sync / Atomics | [Send/Sync Boundary Judgment](../../03_advanced/00_concurrency/04_send_sync_boundaries.md) · [Atomics and Memory Ordering](../../03_advanced/00_concurrency/06_atomics_and_memory_ordering.md) | ✅ |
| Implementing Vec / Arc and Mutex | [Unsafe Collections Internals](../../03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md) | ✅ |
| FFI | [Rust FFI](../../03_advanced/04_ffi/01_rust_ffi.md) · [unsafe extern blocks](../../03_advanced/04_ffi/05_unsafe_extern_blocks.md) | ✅ |
| Beneath std / panic_handler | [The Rust Runtime](../../03_advanced/06_low_level_patterns/07_rust_runtime.md) | ✅ |

---

## 六、Edition Guide 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| What are editions? / Creating a new project / Transitioning / Advanced migrations | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) | ✅ |
| Rust 2015 / 2018 / 2021 各项变更 | [Editions](../../07_future/00_version_tracking/02_editions.md) · [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) | ✅ |
| Rust 2024 Language (gen keyword, let chains, unsafe extern, unsafe attributes, unsafe_op_in_unsafe_fn, static mut references, never type fallback, macro fragment specifiers) | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) · [Let Chains](../../01_foundation/04_control_flow/03_let_chains.md) · [unsafe extern blocks](../../03_advanced/04_ffi/05_unsafe_extern_blocks.md) · [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) | ✅ |
| Rust 2024 Standard library (prelude, IntoIterator for Box<[T]>, newly unsafe functions) | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) §2.5.5 | ✅ 已补充 |
| Rust 2024 Cargo (resolver, table/key names, inherited default-features) | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) §2.5.2/2.5.3 · [Cargo 1.97 新特性](../../06_ecosystem/01_cargo/23_cargo_197_features.md) · [Cargo Dependency Resolution](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | ✅ 已补充 |
| Rust 2024 Rustdoc (combined tests, nested include) | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) §2.5.4 · [Rustdoc 1.96–1.97 变更](../../06_ecosystem/00_toolchain/07_rustdoc_196_changes.md) | ✅ 已补充 |
| Rust 2024 Rustfmt (style edition, formatting fixes, raw identifier sorting, version sorting) | [Edition 2024 完全指南](../../07_future/01_edition_roadmap/02_edition_guide.md) §2.5.1 | ✅ 已补充 |

---

## 七、Async Book 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Part 1 Guide: Concurrent programming / Async and await / More async/await / IO and blocking / Composing futures / Channels, locking, synchronization / Tools / Destruction / Futures / Runtimes / Timers / Streams | [Async Programming](../../03_advanced/01_async/01_async.md) · [Async Advanced](../../03_advanced/01_async/02_async_advanced.md) · [Async Patterns](../../03_advanced/01_async/03_async_patterns.md) · [Future and Executor Mechanisms](../../03_advanced/01_async/04_future_and_executor_mechanisms.md) · [Stream Algebra and Backpressure](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) · [Tokio Runtime Internals](../../06_ecosystem/04_web_and_networking/10_tokio_runtime_internals.md) | ✅ |
| Part 2 Reference: Cancellation and cancellation safety | [Async Cancellation Safety](../../03_advanced/01_async/05_async_cancellation_safety.md) | ✅ |
| Part 2 Reference: Pinning | [Pin and Unpin](../../03_advanced/01_async/08_pin_unpin.md) · [Pin Projection Counterexamples](../../03_advanced/01_async/11_pin_projection_counterexamples.md) | ✅ |
| Part 2 Reference: Structured concurrency | [Structured Concurrency](../../03_advanced/01_async/16_structured_concurrency.md) | ✅（本轮新增） |
| Part 2 Reference: Async IO: readiness vs completion, and io_uring | [Async IOUring Preview](../../07_future/02_preview_features/39_async_ioring_preview.md) | ✅（本轮新增） |
| Part 2 Reference: Async and FFI | [Async FFI Boundary](../../03_advanced/04_ffi/04_async_ffi_boundary.md) | ✅ |
| Old chapters: Future trait / Waker / Executor / Streams / join! / select! / Spawning / async in traits | 见 [Async Programming](../../03_advanced/01_async/01_async.md) 各节 | ✅ |

---

## 八、rustc-dev-guide 主题映射

rustc-dev-guide 主题为**编译器实现细节**，项目 L4/L6 已有概述，部分可继续深化：

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| How to build and run the compiler / Tests / Debugging / Profiling | [Rust Compiler Internals](../../06_ecosystem/00_toolchain/04_compiler_internals.md) · [Compiler Testing](../../06_ecosystem/00_toolchain/13_compiler_testing.md) | ✅ |
| Queries / Incremental compilation / Salsa | [The Rustc Query System and Incremental Compilation](../../04_formal/05_rustc_internals/01_rustc_query_system.md) | ✅ |
| Syntax and AST / Lexing and parsing / Macro expansion / Name resolution / HIR / THIR / MIR | [Name Resolution and HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) · [MIR, Codegen and LLVM IR Primer](../../04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md) | ✅ |
| MIR construction / visitor / passes / optimizations / dataflow / drop elaboration | [MIR, Codegen and LLVM IR Primer](../../04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md) §2.2 | ✅ 已补充 |
| Type inference / Trait solving / Specialization / Chalk / Next-gen solver | [Type Checking and Inference in rustc](../../04_formal/00_type_theory/07_type_checking_and_inference.md) · [The Trait Solver in rustc](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) §6.5 | ✅ 已补充 |
| The borrow checker / NLL / Polonius / Region inference | [NLL and Polonius](../../03_advanced/02_unsafe/03_nll_and_polonius.md) · [Borrow Checking Decidability](../../04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | ✅ |
| Code generation / LLVM / Backend-agnostic codegen / Debug info | [LLVM Backend and Code Generation](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) · [rustc Driver, Interface and Stable MIR](../../06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | ✅ |
| Rustdoc internals / Search / GUI/JSON test suites | [Rustdoc Internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) | ✅ 已补充 |
| Sanitizers support | [Sanitizers](../../03_advanced/02_unsafe/09_sanitizers.md) | ✅ 已补充 |
| Notification groups / Compiler team / Walkthrough / Stability | 📎 流程/治理类，不属概念层 | 📎 |

---

## 九、API Guidelines 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Checklist | [Rust API Naming Conventions](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) §十 | ✅ 已补充 |
| Naming | [Rust API Naming Conventions](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) §十 | ✅ 已补充 |
| Interoperability / Macros / Documentation / Predictability / Flexibility / Type safety / Dependability / Debuggability / Future proofing / Necessities | [Rust API Naming Conventions](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) · [System Design Principles](../../06_ecosystem/03_design_patterns/03_system_design_principles.md) · [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) | ✅ Naming 逐项映射已补充；其余按专题页覆盖 |

---

## 十、Unsafe Code Guidelines 主题映射

| 外部主题 | 项目对应 | 状态 |
|:---|:---|:---:|
| Data layout / Structs and tuples / Scalars / Enums / Unions / Pointers / Function pointers / Arrays and Slices / Packed SIMD vectors | [Type Layout](../../04_formal/05_rustc_internals/08_type_layout.md) · [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) | ✅ |
| Validity / Unions / Function Pointers | [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) · [Unions](../../02_intermediate/04_types_and_conversions/06_unions.md) | ✅ |
| Optimizations / Return value optimization | [Performance Optimization](../../06_ecosystem/10_performance/01_performance_optimization.md) §RVO/NRVO 与 Copy Elision | ✅ 已补充 |

---

## 十一、未覆盖缺口清单

基于本轮审计，以下外部主题属于**真正缺口**或**需补充细节**，已纳入后续迭代计划：

| # | 缺口主题 | 外部来源 | 建议项目位置 | 优先级 |
|---:|---|---|---|:---:|
| 1 | Rust 2024 Rustfmt 细节 | Edition Guide | `concept/07_future/01_edition_roadmap/02_edition_guide.md` §2.5.1 | ✅ 已补充 |
| 2 | Rust 2024 Cargo table/key consistency、inherited default-features | Edition Guide | `concept/07_future/01_edition_roadmap/02_edition_guide.md` §2.5.2/2.5.3 | ✅ 已补充 |
| 3 | Rust 2024 Rustdoc combined tests / nested include | Edition Guide | `concept/07_future/01_edition_roadmap/02_edition_guide.md` §2.5.4 | ✅ 已补充 |
| 4 | Structured concurrency | Async Book | `concept/03_advanced/01_async/16_structured_concurrency.md`（本轮新增） | ✅ 已补充 |
| 5 | Async IO: readiness vs completion, io_uring | Async Book | `concept/07_future/02_preview_features/39_async_ioring_preview.md`（本轮新增） | ✅ 已补充 |
| 6 | Rustdoc internals | rustc-dev-guide | [Rustdoc Internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) | ✅ 已补充 |
| 7 | Sanitizers support | rustc-dev-guide | [Sanitizers](../../03_advanced/02_unsafe/09_sanitizers.md) | ✅ 已补充 |
| 8 | API Guidelines 逐项映射 | API Guidelines | `concept/02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md` §十 | ✅ 已补充 |
| 9 | TRPL OOP design patterns 对照 | TRPL | [Advanced Traits](../../02_intermediate/00_traits/04_advanced_traits.md) §TRPL OOP 设计模式对照 | ✅ 已补充 |
| 10 | Return value optimization 语义 | UCG | [Performance Optimization](../../06_ecosystem/10_performance/01_performance_optimization.md) §RVO/NRVO 与 Copy Elision | ✅ 已补充 |

---

## 十二、维护流程

1. **月度**：运行 `scripts/check_authority_freshness.py`，检查上游 stable 版本是否超过项目基线。
2. **季度**：复跑 `tmp/authority_alignment_audit.py`，生成新的 `tmp/authority_alignment_report.md`，对比本索引更新缺口清单。
3. **新增 concept/ 权威页时**：在本索引中添加对应外部来源的映射行，保持双向可追溯。
4. **上游新增主题时**：按 §十一 格式登记缺口，并按 AGENTS.md 的 canonical 规则判断是否需要新建权威页或仅链接。

---

> **维护规范**: 本索引与 `tmp/authority_alignment_audit.py` 联动，季度复跑后应同步更新缺口清单状态。
