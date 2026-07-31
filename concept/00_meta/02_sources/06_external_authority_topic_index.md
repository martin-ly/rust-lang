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
  - [十三、新增国际化来源映射（2026-07-31）](#十三新增国际化来源映射2026-07-31)
  - [十四、UCG / rustc-dev-guide / 形式化验证工具深度映射（P3）](#十四ucg--rustc-dev-guide--形式化验证工具深度映射p3)
    - [14.1 Unsafe Code Guidelines 细化映射](#141-unsafe-code-guidelines-细化映射)
    - [14.2 rustc-dev-guide 细化映射](#142-rustc-dev-guide-细化映射)
    - [14.3 形式化验证工具映射](#143-形式化验证工具映射)
    - [14.4 后续维护动作](#144-后续维护动作)
  - [十五、惯用法 / 算法 / 设计模式 / Rust 特有解决方案映射（F 专项，2026-07-31）](#十五惯用法--算法--设计模式--rust-特有解决方案映射f-专项2026-07-31)
    - [15.1 惯用法来源映射](#151-惯用法来源映射)
    - [15.2 算法来源映射](#152-算法来源映射)
    - [15.3 设计模式来源映射](#153-设计模式来源映射)
    - [15.4 Rust 特有解决方案来源映射](#154-rust-特有解决方案来源映射)
    - [15.5 维护动作](#155-维护动作)

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
| Macros / Macros by example / Procedural macros | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Procedural Macro](../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md) | ✅ |
| Crates and source files | [Crates and Source Files](../../01_foundation/07_modules_and_items/11_crates_and_source_files.md) | ✅ |
| Conditional compilation | [Conditional Compilation](../../03_advanced/03_proc_macros/11_conditional_compilation.md) | ✅ |
| Items (Modules, Functions, Type aliases, Structs, Enums, Unions, Constants, Statics, Traits, Implementations, External blocks, Generics, Associated items) | [Items](../../01_foundation/07_modules_and_items/12_items.md) · [Items Reference](../../04_formal/05_rustc_internals/11_items_reference.md) · [Statements and Expressions Reference](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) · [Patterns Reference](../../04_formal/05_rustc_internals/14_patterns_reference.md) · [Type System Reference](../../04_formal/00_type_theory/09_type_system_reference.md) · [Names Reference](../../04_formal/05_rustc_internals/16_names_reference.md) | ✅ |
| Attributes | [Attributes](../../04_formal/05_rustc_internals/12_attributes.md) · [Attributes by Category](../../02_intermediate/06_macros_and_metaprogramming/08_attributes_by_category.md) | ✅ |
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
| Constant evaluation | [Constant Evaluation](../../04_formal/03_operational_semantics/08_constant_evaluation.md) | ✅ |
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
| Functions / Methods / Closures | [Functions](../../01_foundation/07_modules_and_items/02_functions.md) · [Closure Basics](../../01_foundation/00_start/03_closure_basics.md) · [Closures](../../02_intermediate/07_iterators_and_closures/02_closures.md) | ✅ |
| Modules / Crates / Cargo | [Modules and Paths](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) · [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | ✅ |
| Attributes / Generics / Traits | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Generics](../../02_intermediate/01_generics/01_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) | ✅ |
| Scoping rules / Lifetimes | [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [Lifetimes Advanced](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | ✅ |
| macro_rules! | [Attributes and Macros](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) · [Declarative Macros](../../02_intermediate/06_macros_and_metaprogramming/04_declarative_macros.md) | ✅ |
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

---

## 十三、新增国际化来源映射（2026-07-31）

本轮全面对齐后新增/深化的国际权威来源及其项目映射：

| 来源 | 主题 | 项目对应页 | 状态 |
|:---|:---|:---|:---:|
| [Mara Bos — Rust Atomics and Locks](https://mara.nl/atomics/) | Memory ordering、happens-before、fences、consume ordering、 myths | `concept/04_formal/09_system_semantics/08_memory_ordering_and_atomics.md` | ✅ |
| [The Embedded Rust Book](https://docs.rust-embedded.org/book/) | no_std、peripherals、typestate、HAL design patterns | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`、`23_no_std_and_bare_metal_idioms.md`、`24_embedded_hal_and_driver_idioms.md` | ✅ |
| [Discovery Book](https://docs.rust-embedded.org/discovery/) | STM32F3DISCOVERY 入门实验 | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` 学习路径 | ✅ |
| [The Embedonomicon](https://docs.rust-embedded.org/embedonomicon/) | 自定义 target、链接脚本、启动序列 | `concept/06_ecosystem/05_systems_and_embedded/13_bare_metal_boot_linker_script.md`、`23_no_std_and_bare_metal_idioms.md` | ✅ |
| [Embassy](https://github.com/embassy-rs/embassy) | Async embedded executor | `concept/06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md`、`26_embedded_rtos_and_safety_critical_frameworks.md` | ✅ |
| [Hubris](https://github.com/oxidecomputer/hubris) / [Ariel OS](https://github.com/ariel-os/ariel-os) / [RTIC](https://github.com/rtic-rs/rtic) / [Tock](https://github.com/tock/tock) / [Ferrocene](https://ferrous-systems.com/ferrocene/) | 嵌入式 RTOS 与安全关键框架 | `concept/06_ecosystem/05_systems_and_embedded/26_embedded_rtos_and_safety_critical_frameworks.md` | ✅ |
| [Ferrous Systems — Booting a Cortex-M Microcontroller](https://rust-training.ferrous-systems.com/latest/book/booting-cortex-m) | 复位向量、向量表、`_start`、`.data`/`.bss`、启动 soundness | `concept/06_ecosystem/05_systems_and_embedded/27_no_std_startup_runtime_deep_dive.md`、`13_bare_metal_boot_linker_script.md` | ✅ |
| [cortex-m-rt](https://docs.rs/cortex-m-rt/) / [riscv-rt](https://docs.rs/riscv-rt/) | 目标运行时入口、`#[entry]`、链接脚本 | `concept/06_ecosystem/05_systems_and_embedded/27_no_std_startup_runtime_deep_dive.md`、`23_no_std_and_bare_metal_idioms.md` | ✅ |
| [Embassy Executor](https://docs.rs/embassy-executor/) / [RTIC Book — async tasks](https://rtic.rs/2/book/en/) | 裸机 async executor、Waker、ISR 驱动调度 | `concept/06_ecosystem/05_systems_and_embedded/28_custom_bare_metal_async_executor.md`、`11_async_no_std_embedded.md` | ✅ |
| [flip-link](https://github.com/knurling-rs/flip-link) / [ARM Compiler scatter files](https://developer.arm.com/documentation/100748/latest) | 栈溢出保护、scatter file、内存布局 | `concept/06_ecosystem/05_systems_and_embedded/29_embedded_memory_layout_and_heap_safety.md`、`13_bare_metal_boot_linker_script.md` | ✅ |
| [MISRARust: Mapping MISRA-C++ Coding Guidelines to the Rust Programming Language](https://arxiv.org/html/2605.23490v1) | MISRA-Rust 规则映射、编码规范 | `concept/06_ecosystem/05_systems_and_embedded/30_misra_rust_safety_critical_guidelines.md` | ✅ |
| [Ferrocene Language Specification](https://spec.ferrocene.dev/) / [Ferrocene core certification news](https://ferrous-systems.com/blog/ferrocene-libcore-news-release/) | 合格语言子集、core 库 SIL 2 认证 | `concept/06_ecosystem/05_systems_and_embedded/30_misra_rust_safety_critical_guidelines.md`、`19_safety_critical_bare_metal_os.md` | ✅ |
| [Rust Blog — What does it take to ship Rust in safety-critical?](https://blog.rust-lang.org/2026/01/14/what-does-it-take-to-ship-rust-in-safety-critical/) | 安全关键 Rust 生态现状、依赖生命周期、async runtime 鉴定 | `concept/06_ecosystem/05_systems_and_embedded/30_misra_rust_safety_critical_guidelines.md` | ✅ |
| [Safety-Critical Rust Consortium](https://rustfoundation.org/safety-critical-rust-consortium/) / [Safety-Critical Rust coding guidelines](https://github.com/rustfoundation/safety-critical-rust-coding-guidelines) | 编码指南、MC/DC、目标平台就绪清单 | `concept/06_ecosystem/05_systems_and_embedded/30_misra_rust_safety_critical_guidelines.md` | ✅ |
| [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | Idioms、design patterns、anti-patterns、FFI patterns | `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md`、`33_anti_patterns.md`、`concept/03_advanced/04_ffi/07_ffi_patterns.md` | ✅ |
| [Rust API Guidelines Checklist](https://rust-lang.github.io/api-guidelines/checklist.html) | C-XXXX 指南逐项映射 | `concept/00_meta/00_framework/rust_api_guidelines_canonical.md` | ✅ |
| [Mark Richards — Software Architecture Patterns 2nd ed.](https://www.oreilly.com/library/view/software-architecture-patterns/9781098134280/) | Layered、Event-driven、Microkernel、Microservices、Space-based、SOA、Pipeline | `concept/06_ecosystem/03_design_patterns/08_architecture_patterns.md`、`concept/04_formal/10_architecture_semantics/05_architecture_styles_formal_constraints.md` | ✅ |
| [BFO](https://basic-formal-ontology.org/) / [DOLCE](http://www.loa.istc.cnr.it/old/DOLCE.html) / [SUMO](https://www.ontologyportal.org/) | Top-level ontology alignment | `concept/04_formal/13_semantic_engineering/06_ai_ontology_and_rust_semantics.md` | ✅ |
| W3C OWL 2 / SHACL | KG formal semantics | `concept/04_formal/13_semantic_engineering/07_kg_owl_shacl_semantics.md` | ✅ |
| [Martin Fowler](https://martinfowler.com/) / [microservices.io](https://microservices.io/) | Microservices、CQRS、Event Sourcing、Circuit Breaker 等 | `concept/06_ecosystem/03_design_patterns/` 相关页 | ✅ |
| [Manning — Idiomatic Rust](https://www.manning.com/books/idiomatic-rust) / CLRS / Sedgewick / Knuth | Idioms、algorithms、complexity | `concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md`、`concept/06_ecosystem/10_performance/03_algorithms_and_complexity_idioms.md` | ✅ |
| [Kani](https://model-checking.github.io/kani/) / [Miri](https://github.com/rust-lang/miri) / [Creusot](https://github.com/creusot-rs/creusot) / [Verus](https://verus-lang.github.io/verus/guide/) / [Aeneas](https://github.com/AeneasVerif/aeneas) / [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) / [Flux](https://flux-rs.github.io/flux/) / [AutoVerus](https://github.com/secure-foundations/verus/tree/main/source/verus-std) | Rust 形式化验证工具链：模型检查、符号执行、演绎验证、精炼类型 | `concept/04_formal/04_model_checking/01_verification_toolchain.md`、`08_miri.md`、`09_kani.md`、`11_creusot.md`、`07_autoverus.md`、`concept/04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md`、`concept/04_formal/00_type_theory/14_flux.md` | ✅ |
| [MiniRust](https://github.com/RalfJung/minirust) / [Tree Borrows](https://github.com/RalfJung/tree-borrows) / [Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md) | Rust 操作语义、别名模型、内存模型 | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md`、`06_behavior_considered_undefined.md`、`concept/04_formal/03_operational_semantics/03_operational_semantics.md` | ✅ |

---

## 十四、UCG / rustc-dev-guide / 形式化验证工具深度映射（P3）

> 本节把 `Unsafe Code Guidelines`、`rustc-dev-guide` 以及 Rust 形式化验证生态的**具体章节/子项目**与项目 `concept/` 权威页做细化对齐，为 P5（MiniRust/Tree Borrows/计算语义模型）和季度国际来源审计提供可追溯基线。

### 14.1 Unsafe Code Guidelines 细化映射

| UCG 主题 / 子页 | 项目对应页 | 状态 |
|:---|:---|:---:|
| [Introduction / Scope](https://rust-lang.github.io/unsafe-code-guidelines/) | [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) §官方来源 | ✅ |
| [Data layout: Structs, Tuples, Enums, Unions](https://rust-lang.github.io/unsafe-code-guidelines/layout/structs-and-tuples.html) | [Type Layout](../../04_formal/05_rustc_internals/08_type_layout.md) · [Unions](../../02_intermediate/04_types_and_conversions/06_unions.md) | ✅ |
| [Validity](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#validity) / [What is undefined behavior?](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#undefined-behavior) | [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) · [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) | ✅ |
| [Stacked Borrows (wip)](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md) / [Tree Borrows](https://github.com/RalfJung/tree-borrows) | [Tree Borrows Deep Dive](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | ✅ |
| [Provenance](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#pointer-provenance) / [Strict Provenance](https://doc.rust-lang.org/std/ptr/index.html#strict-provenance) | [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md) · [Unsafe Patterns](../../03_advanced/02_unsafe/04_unsafe_rust_patterns.md) | ✅ |
| [Atomic orderings](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html#memory-ordering) | [Atomics and Memory Ordering](../../03_advanced/00_concurrency/06_atomics_and_memory_ordering.md) | ✅ |

### 14.2 rustc-dev-guide 细化映射

| rustc-dev-guide 主题 / 子页 | 项目对应页 | 状态 |
|:---|:---|:---:|
| [About this guide](https://rustc-dev-guide.rust-lang.org/) / [How to build and run](https://rustc-dev-guide.rust-lang.org/building/how-to-build-and-run.html) | [Compiler Internals](../../06_ecosystem/00_toolchain/04_compiler_internals.md) · [rustc Bootstrap](../../06_ecosystem/00_toolchain/12_rustc_bootstrap.md) | ✅ |
| [Queries and incremental](https://rustc-dev-guide.rust-lang.org/query.html) | [The Rustc Query System](../../04_formal/05_rustc_internals/01_rustc_query_system.md) | ✅ |
| [The lexer and parser](https://rustc-dev-guide.rust-lang.org/the-parser.html) / [Macro expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html) | [Lexical Structure](../../04_formal/05_rustc_internals/10_lexical_structure.md) · [Name Resolution and HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | ✅ |
| [MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) / [MIR passes](https://rustc-dev-guide.rust-lang.org/mir/mir_passes.html) / [Dataflow](https://rustc-dev-guide.rust-lang.org/mir/dataflow.html) | [MIR, Codegen and LLVM IR Primer](../../04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md) | ✅ |
| [Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) / [Trait solving](https://rustc-dev-guide.rust-lang.org/traits/resolution.html) | [Type Checking and Inference in rustc](../../04_formal/00_type_theory/07_type_checking_and_inference.md) · [The Trait Solver in rustc](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | ✅ |
| [Borrow checking](https://rustc-dev-guide.rust-lang.org/borrow_check.html) / [Region inference](https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html) / [Polonius](https://rustc-dev-guide.rust-lang.org/borrow_check/polonius.html) | [NLL and Polonius](../../03_advanced/02_unsafe/03_nll_and_polonius.md) · [Borrow Checking Decidability](../../04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | ✅ |
| [Codegen / LLVM](https://rustc-dev-guide.rust-lang.org/backend/index.html) / [Stable MIR](https://rustc-dev-guide.rust-lang.org/stable-mir.html) | [LLVM Backend and Code Generation](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) · [rustc Driver and Stable MIR](../../06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | ✅ |
| [Rustdoc](https://rustc-dev-guide.rust-lang.org/rustdoc.html) / [Rustdoc tests](https://rustc-dev-guide.rust-lang.org/rustdoc-internals/rustdoc-tests.html) | [Rustdoc Internals](../../06_ecosystem/00_toolchain/16_rustdoc_internals.md) | ✅ |
| [Sanitizers](https://rustc-dev-guide.rust-lang.org/sanitizers.html) | [Sanitizers](../../03_advanced/02_unsafe/09_sanitizers.md) | ✅ |

### 14.3 形式化验证工具映射

| 工具 | 官方入口 | 项目对应页 | 覆盖重点 |
|:---|:---|:---|:---|
| **Miri** | [rust-lang/miri](https://github.com/rust-lang/miri) · [Miri Book](https://miri-labs.github.io/book/) | [04_formal/04_model_checking/08_miri.md](../../04_formal/04_model_checking/08_miri.md) | UB 检测、Tree Borrows、unsafe 代码审计 |
| **Kani** | [model-checking.github.io/kani](https://model-checking.github.io/kani/) | [04_formal/04_model_checking/09_kani.md](../../04_formal/04_model_checking/09_kani.md) | 模型检查、`#[kani::proof]`、标准库 harness |
| **Creusot** | [creusot-rs.github.io](https://creusot-rs.github.io/) · [GitHub](https://github.com/creusot-rs/creusot) | [04_formal/04_model_checking/11_creusot.md](../../04_formal/04_model_checking/11_creusot.md) | Why3 后端、契约、幽灵类型 |
| **Verus** | [verus-lang.github.io/verus/guide/](https://verus-lang.github.io/verus/guide/) · [GitHub](https://github.com/verus-lang/verus) | [04_formal/04_model_checking/07_autoverus.md](../../04_formal/04_model_checking/07_autoverus.md) | 低级系统代码验证、 ownership 编码 |
| **Aeneas** | [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) · [charon](https://github.com/AeneasVerif/charon) | [04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md](../../04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md) | 符号语义、从 MIR 到 LLBC |
| **Prusti** | [pm.inf.ethz.ch/research/prusti.html](https://www.pm.inf.ethz.ch/research/prusti.html) · [GitHub](https://github.com/viperproject/prusti) | [04_formal/04_model_checking/04_modern_verification_tools.md](../../04_formal/04_model_checking/04_modern_verification_tools.md) | Viper 后端、分离逻辑 |
| **Flux** | [flux-rs.github.io/flux/](https://flux-rs.github.io/flux/) · [GitHub](https://github.com/flux-rs/flux) | [04_formal/00_type_theory/14_flux.md](../../04_formal/00_type_theory/14_flux.md) | 精炼类型、索引类型 |
| **Coq / RustBelt** | [PLV MPI-SWS — RustBelt](https://plv.mpi-sws.org/rustbelt/) · [Iris Project](https://iris-project.org/) | [04_formal/02_separation_logic/01_rustbelt.md](../../04_formal/02_separation_logic/01_rustbelt.md) | 分离逻辑、所有权协议 |

### 14.4 后续维护动作

1. **P5 联动**：将 MiniRust/Tree Borrows 的操作语义细节反向注入 [Tree Borrows Deep Dive](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) 与 [Operational Semantics](../../04_formal/03_operational_semantics/03_operational_semantics.md)。
2. **季度审计**：每季度用 `scripts/check_authority_freshness.py` 复核上述 URL 的 200/301 状态；失效链接在 §十一 登记并修复。
3. **新增工具**：若 Rust 形式化生态出现新工具（如 BorrowSanitizer 稳定化），按本表格式追加一行，并同步到 [Verification Toolchain](../../04_formal/04_model_checking/01_verification_toolchain.md)。

---

## 十五、惯用法 / 算法 / 设计模式 / Rust 特有解决方案映射（F 专项，2026-07-31）

本表记录 F 专项新建/补全页与国际权威来源的对应关系，用于季度审计与持续对齐。

### 15.1 惯用法来源映射

| 主题 | 项目页 | 国际权威来源 |
|:---|:---|:---|
| `Cow<T>` / clone-on-write | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [std::borrow::Cow](https://doc.rust-lang.org/std/borrow/enum.Cow.html) · [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) |
| 错误处理（`ok_or`/`map_err`/thiserror/anyhow） | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [Rust Book Ch.9](https://doc.rust-lang.org/book/ch09-00-error-handling.html) · [thiserror docs](https://docs.rs/thiserror) · [anyhow docs](https://docs.rs/anyhow) |
| Iterator 高级适配器 | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [std::iter::Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) |
| async 运行时惯用法 | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [Tokio Docs](https://docs.rs/tokio) · [Rust Async Book](https://rust-lang.github.io/async-book/) |
| no_std / 裸机惯用法 | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [The Embedded Rust Book](https://docs.rust-embedded.org/book/) · [cortex-m docs](https://docs.rs/cortex-m) |
| unsafe 惯用法边界 | [Rust 惯用法谱系全景](../../06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | [The Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) |

### 15.2 算法来源映射

| 主题 | 项目页 | 国际权威来源 |
|:---|:---|:---|
| 零拷贝解析 | [Rust 零拷贝解析](../../06_ecosystem/11_domain_applications/26_zero_copy_parsing_in_rust.md) | [nom docs](https://docs.rs/nom) · [winnow docs](https://docs.rs/winnow) · [serde lifetimes](https://serde.rs/lifetimes.html) |
| 所有权感知算法 | [所有权感知算法](../../06_ecosystem/11_domain_applications/27_ownership_aware_algorithms.md) | [The Rust Performance Book](https://nnethercote.github.io/perf-book/) · [std::slice](https://doc.rust-lang.org/std/slice/) |
| unsafe 算法不变式 | [unsafe 算法不变式](../../06_ecosystem/11_domain_applications/28_unsafe_algorithm_invariants.md) | [Rust Reference — Unsafe](https://doc.rust-lang.org/reference/unsafe-blocks.html) · [Rust Atomics and Locks](https://marabos.nl/atomics/) · [Kani docs](https://model-checking.github.io/kani/) |

### 15.3 设计模式来源映射

| 主题 | 项目页 | 国际权威来源 |
|:---|:---|:---|
| Builder / Factory / Adapter / Observer / Strategy | [设计模式概览](../../06_ecosystem/03_design_patterns/01_patterns.md) | [GoF — Design Patterns](https://en.wikipedia.org/wiki/Design_Patterns) · [refactoring.guru](https://refactoring.guru/design-patterns) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) |

### 15.4 Rust 特有解决方案来源映射

| 主题 | 项目页 | 国际权威来源 |
|:---|:---|:---|
| 编译期正确性 | [编译期正确性](../../01_foundation/00_start/08_compile_time_correctness.md) | [RFC 2000 Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html) · [Strom & Yemini 1986 Typestate](https://doi.org/10.1145/512644.512659) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) |
| fearless 重构 | [fearless 重构](../../01_foundation/00_start/09_fearless_refactoring.md) | [TRPL — Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html) · [Martin Fowler — Refactoring](https://refactoring.com/) |
| 所有权即资源管理 | [所有权即资源管理](../../06_ecosystem/03_design_patterns/34_ownership_as_resource_management.md) | [Rust Reference — Destructors](https://doc.rust-lang.org/reference/destructors.html) · [Rustonomicon — Drop Flags](https://doc.rust-lang.org/nomicon/destructors.html) |
| 作用域守卫与延迟清理 | [作用域守卫与延迟清理](../../06_ecosystem/03_design_patterns/35_scope_guard_and_deferred_cleanup.md) | [scopeguard crate](https://docs.rs/scopeguard) · [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) |

### 15.5 维护动作

1. 每季度审计上述链接可用性（`scripts/check_authority_freshness.py`）。
2. F 专项页内容更新后，同步调整本表映射关系。
3. 新增惯用法/算法/模式/Rust 方案页时，按本表格式追加一行。
