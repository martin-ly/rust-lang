# i18n 双语标注补全计划

> 生成日期: 2026-07-09
> 扫描工具: `scripts/add_bilingual_annotations.py --mode check-only`
> 扫描范围: `concept/`
> 扫描文件数: 445
> 当前未覆盖术语种类: 29

---

## 1. Methodology

1. 以 `scripts/add_bilingual_annotations.py --mode check-only` 的**当前输出**为权威基线（2026-07-09 运行），而非依赖历史 JSON。
2. 对每个未覆盖术语，随机抽取最多 5 个出现文件，查看正文/表格/元数据/链接/标题中的实际用法。
3. 按以下四类给出建议动作：
   - `annotate`：在正文中首次出现时追加 `（English Term）` 双语标注。
   - `en_summary`：文件缺失 `**EN**` 或 `**Summary**` 字段（当前扫描结果中为 0）。
   - `exception`：属于代码块、链接锚文本、原生英文、非独立用法或明显非 Rust 语义，不建议强制标注。
   - `manual_review`：上下文存在歧义（如一词多义、标题/目录行、元数据摘要中英混杂），需要人工判断。
4. 统计各类别数量，估算执行 `annotate` 动作时会触及的文件数。
5. 列出脚本明显误报/漏报点，供后续修复。

> **注意**：输入文件 `reports/uncovered_terms_current.json` 与当前扫描结果存在差异（JSON 包含 `Future`、`Vec`、`Result`、`Pin`、`Option`、`crate`、`trait`、`unsafe`、`panic`、`Send`、`HashMap`、`FFI` 等英文原生术语，但当前运行已不再报出）。本计划以当前 `check-only` 输出为准，差异原因见第 5 节。

---

## 2. Per-Term Annotation Plan

| # | Term | Example Files (≤5) | Context Snippet | Classification | Proposed Bilingual Text / Rationale |
|---|------|-------------------|-----------------|----------------|-------------------------------------|
| 1 | 借用 | `01_foundation/00_start/47_std_io_and_process.md`, `07_future/00_version_tracking/rust_1_91_stabilized.md`, `07_future/00_version_tracking/rust_1_92_stabilized.md` | "…都通过这些模块完成。它们遵循 Rust 的核心原则：所有权、借用、`Result` 错误处理。" | `annotate` | 借用（Borrowing） |
| 2 | 模块 | `01_foundation/00_start/00_start.md`, `01_foundation/06_strings_and_text/46_formatting_and_display.md`, `03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`, `03_advanced/03_proc_macros/35_macro_hygiene.md`, `06_ecosystem/01_cargo/82_cargo_guide_practices.md` | "…理解 crate、模块、依赖与版本控制的基本关系。" | `annotate` | 模块（Module） |
| 3 | 类型系统 | `01_foundation/00_start/00_start.md`, `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `04_formal/05_rustc_internals/47_attributes.md`, `04_formal/05_rustc_internals/52_reference_appendices.md`, `06_ecosystem/03_design_patterns/38_formal_design_pattern_theory.md` | "…`#[non_exhaustive]`、`#[must_use]` | 类型系统 | 影响类型/接口语义…" | `annotate` | 类型系统（Type System） |
| 4 | 可变借用 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `01_foundation/07_modules_and_items/12_functions.md`, `01_foundation/07_modules_and_items/16_implementations.md` | "\| 可变借用 \| 编译时 \| 零成本 \| 中 \| 完全安全 \|" | `annotate` | 可变借用（Mutable Borrow） |
| 5 | 不可变借用 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `01_foundation/07_modules_and_items/12_functions.md`, `01_foundation/07_modules_and_items/16_implementations.md` | "\| `&self` \| `obj.method()` \| 不可变借用 \|" | `annotate` | 不可变借用（Immutable Borrow） |
| 6 | 智能指针 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` | "\| 智能指针 \| 所有权 \| 线程安全 \| 运行时开销 \| 使用场景 \|" | `annotate` | 智能指针（Smart Pointer） |
| 7 | 运行时 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `01_foundation/07_modules_and_items/44_static_items.md`, `02_intermediate/00_traits/39_dispatch_mechanisms.md`, `03_advanced/02_process_ipc/08_process_performance_engineering.md`, `06_ecosystem/01_cargo/09_cargo_script.md` | "\| 动态分发 \| 运行时 \| 虚函数表 (vtable) \|" | `annotate` | 运行时（Runtime） |
| 8 | 内存安全 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `03_advanced/00_concurrency/11_atomics_and_memory_ordering.md`, `03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`, `04_formal/00_type_theory/50_type_system_reference.md`, `06_ecosystem/09_networking/02_network_security.md` | "…它通过 `Send` 和 `Sync` Trait，在编译时就消除了整类的、最阴险的并发 bug。这种安全保证…" / 表格含"内存安全" | `annotate` | 内存安全（Memory Safety） |
| 9 | 并发安全 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md`, `06_ecosystem/03_design_patterns/85_design_patterns_faq.md` | "\| 并发安全 \| 需要锁 \| Send/Sync 自动推导 ✅ \|" | `annotate` | 并发安全（Concurrency Safety） |
| 10 | 生命周期省略 | `01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`, `04_formal/05_rustc_internals/35_name_resolution_and_hir.md` | "…不可变/可变借用 → 生命周期入门 → 作用域管理 → 简单智能指针 → … → 生命周期省略 → trait 对象生命周期…" | `annotate` | 生命周期省略（Lifetime Elision） |
| 11 | 宏 | `01_foundation/06_strings_and_text/46_formatting_and_display.md`, `01_foundation/08_error_handling/32_error_handling_basics.md`, `06_ecosystem/11_domain_applications/59_wasm_glossary.md`, `07_future/00_version_tracking/rust_1_90_stabilized.md` | "…`Display` trait · `Debug` trait · `format!` 宏 · 格式化字符串…" | `manual_review` | 多数出现为 "`format!` 宏"、"`panic!` 宏" 等具体宏名 + 宏字样的组合，直接追加 "（Macro）" 会显得冗余；建议人工判断是否保留或改为 "`format!` 宏（Macro）"。 |
| 12 | 泛型 | `01_foundation/07_modules_and_items/14_structs.md`, `03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md`, `06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md`, `06_ecosystem/03_design_patterns/39_frontier_research_and_innovative_patterns.md`, `06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | "…将结构体与枚举、实现块、泛型、Trait 等后置概念链接。" | `annotate` | 泛型（Generics） |
| 13 | 枚举 | `01_foundation/07_modules_and_items/15_enumerations.md`, `01_foundation/07_modules_and_items/16_implementations.md`, `03_advanced/01_async/39_future_and_executor_mechanisms.md`, `04_formal/05_rustc_internals/40_names_and_resolution.md`, `06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | "…枚举、实现块、泛型、Trait 等后置概念链接。" / "Poll 枚举" | `annotate` | 枚举（Enum） |
| 14 | 所有权 | `01_foundation/07_modules_and_items/16_implementations.md`, `06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md` | "\| Receiver \| 调用方式 \| 所有权 \|…\| `self` \| `obj.method()` \| 获取所有权 \|" | `annotate` | 所有权（Ownership） |
| 15 | 一致性 | `02_intermediate/00_traits/32_editions.md`, `06_ecosystem/03_design_patterns/85_design_patterns_faq.md`, `06_ecosystem/04_web_and_networking/18_distributed_systems.md`, `06_ecosystem/09_testing_and_quality/12_testing_strategies.md` | "CAP 定理：一致性（Consistency）、可用性（Availability）、分区容错性（Partition Tolerance）不可同时满足。" | `exception` | 此处的"一致性"均指分布式 CAP/测试/工程一致性，并非 Rust 类型系统的 coherence/orphan-rule 概念，不应标注为 Coherence。 |
| 16 | 模式匹配 | `02_intermediate/04_types_and_conversions/35_unions.md`, `04_formal/05_rustc_internals/48_statements_and_expressions_reference.md`, `04_formal/05_rustc_internals/49_patterns_reference.md`, `04_formal/05_rustc_internals/52_reference_appendices.md`, `07_future/00_version_tracking/rust_1_91_stabilized.md` | "\| 模式匹配 \| 不支持 \| 需 unsafe \| 不能对 union 使用 `match` \|" | `annotate` | 模式匹配（Pattern Matching） |
| 17 | 零成本抽象 | `02_intermediate/06_macros_and_metaprogramming/36_attributes_by_category.md`, `03_advanced/03_proc_macros/34_syn_quote_reference.md`, `04_formal/05_rustc_internals/52_reference_appendices.md`, `06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md`, `06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | "`syn` 是 Rust 语法解析库，提供：… - 零成本抽象" | `annotate` | 零成本抽象（Zero-Cost Abstraction） |
| 18 | 原子操作 | `03_advanced/00_concurrency/10_concurrency_patterns.md`, `03_advanced/02_process_ipc/05_ipc_mechanisms.md`, `03_advanced/07_unsafe_internals/37_unsafe_collections_internals.md` | "…是否需要低延迟共享？是 → 共享状态 + 锁/原子操作。" | `annotate` | 原子操作（Atomic Operations） |
| 19 | 生命周期 | `03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`, `04_formal/05_rustc_internals/40_names_and_resolution.md`, `04_formal/05_rustc_internals/45_lexical_structure.md`, `04_formal/05_rustc_internals/46_items_reference.md`, `06_ecosystem/01_cargo/84_cargo_commands_reference.md` | "…通过进程模型 ⟹ 生命周期 ⟹ 资源控制的定理链理解 `wait` 与管道关闭顺序。" | `manual_review` | 进程/资源"生命周期"与 Rust 语言 lifetime 概念同名，需人工判断每个文件的真实语义后再决定是否标注为 Lifetimes。 |
| 20 | 异步 | `03_advanced/02_process_ipc/05_ipc_mechanisms.md`, `06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md`, `07_future/00_version_tracking/rust_1_91_stabilized.md` | "\| 消息队列 \| 异步/多生产多消费 \| 否 \| 中 \| 中 \|" | `annotate` | 异步（Async） |
| 21 | 错误处理 | `03_advanced/02_process_ipc/07_process_security_and_sandboxing.md`, `03_advanced/02_process_ipc/08_process_performance_engineering.md`, `03_advanced/03_proc_macros/32_macro_glossary.md`, `06_ecosystem/09_networking/06_networking_basics.md`, `06_ecosystem/11_domain_applications/54_webassembly_advanced.md` | "…解析 Rust 语法 - 提供 AST 数据结构 - 错误处理" | `annotate` | 错误处理（Error Handling） |
| 22 | 内联汇编 | `03_advanced/02_unsafe/12_unsafe_rust_patterns.md` | "…识别需要 unsafe 的场景：FFI、裸指针、内联汇编、自定义分配器等。" | `annotate` | 内联汇编（Inline Assembly） |
| 23 | 过程宏 | `03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md`, `03_advanced/03_proc_macros/33_macro_faq.md`, `03_advanced/03_proc_macros/34_syn_quote_reference.md`, `04_formal/05_rustc_internals/40_names_and_resolution.md`, `06_ecosystem/01_cargo/85_cargo_manifest_targets.md` | "…`syn` 是 Rust 语法解析库… - 精确的错误位置 - 零成本抽象"（上下文引用过程宏） | `annotate` | 过程宏（Procedural Macro） |
| 24 | 声明宏 | `03_advanced/03_proc_macros/33_macro_faq.md` | "**声明宏** (`macro_rules!`) 适用于：简单的代码模式、快速原型…" | `annotate` | 声明宏（Declarative Macro） |
| 25 | 结构体 | `03_advanced/03_proc_macros/35_macro_hygiene.md`, `04_formal/05_rustc_internals/40_names_and_resolution.md`, `04_formal/05_rustc_internals/47_attributes.md`, `04_formal/05_rustc_internals/48_statements_and_expressions_reference.md`, `04_formal/05_rustc_internals/49_patterns_reference.md` | "…宏生成的项（函数、结构体、模块）在展开位置可见…" | `annotate` | 结构体（Struct） |
| 26 | 类型推断 | `03_advanced/06_low_level_patterns/33_variables.md`, `04_formal/05_rustc_internals/52_reference_appendices.md`, `07_future/00_version_tracking/rust_1_91_stabilized.md` | "\| 类型推断 \| 支持 \| 必须标注 \| 必须标注 \|" | `annotate` | 类型推断（Type Inference） |
| 27 | 切片 | `04_formal/05_rustc_internals/49_patterns_reference.md` | "\| 数组/切片 \| 匹配数组或可变长度切片 \| `[a, b, ..]` \|" | `annotate` | 切片（Slice） |
| 28 | 闭包 | `04_formal/05_rustc_internals/52_reference_appendices.md`, `07_future/03_preview_features/30_stable_abi_preview.md` | "…又支持 Rust 特性（如 panic 协议、trait object、闭包）…" | `annotate` | 闭包（Closures） |
| 29 | 单态化 | `06_ecosystem/03_design_patterns/36_pattern_implementation_comparison.md`, `concept/SUMMARY.md` | "…⚠️ 代码膨胀 (单态化)…" | `annotate` | 单态化（Monomorphization） |

---

## 3. Counts per Classification

| Classification | Count | Terms |
|----------------|-------|-------|
| `annotate` | 26 | 借用、模块、类型系统、可变借用、不可变借用、智能指针、运行时、内存安全、并发安全、生命周期省略、泛型、枚举、所有权、模式匹配、零成本抽象、原子操作、异步、错误处理、内联汇编、过程宏、声明宏、结构体、类型推断、切片、闭包、单态化 |
| `exception` | 1 | 一致性 |
| `manual_review` | 2 | 宏、生命周期 |
| `en_summary` | 0 | — |

---

## 4. Estimated Files Modified

若对 `annotate` 类别的术语执行 `python scripts/add_bilingual_annotations.py --mode annotate`（脚本默认每文件每术语仅标注首次出现），按当前未覆盖文件集合去重后，预计会修改 **约 66 个文件**（实际数字可能因标题/目录行未触发标注而略低，落在 **60–70** 区间）。

> 计算方式：取所有 `annotate` 分类术语对应文件路径的并集，共 66 条唯一路径。

---

## 5. Script Miscounts to Fix

1. **元数据摘要（Summary）被当作正文统计**
   `collect_text_blocks()` 仅排除 `#` 标题和 fenced code block，未排除文件顶部的 `> **EN**: … > **Summary**: …` 元数据块。例如 `04_formal/05_rustc_internals/47_attributes.md` 的 Summary 里出现"类型系统"、"调试器"等，被计入未覆盖。但 Summary 按规范应为英文摘要，正确做法应是检查 Summary 是否为英文，而非要求在其中追加双语标注。

2. **目录/TOC 行被当作正文**
   文档中的目录列表（如 `- [4.2 生命周期省略](#42-生命周期省略)`）不是正文解释，而是标题锚点，却被计入未覆盖。`collect_text_blocks()` 应考虑跳过仅包含内部链接且文本与标题完全一致的 TOC 行。

3. **一词多义未区分**
   - `一致性` 在当前所有命中文件中均为 CAP/测试/工程"一致性"，不是 Rust 的 coherence/orphan rule。脚本把通用汉语词当作术语计数。
   - `生命周期` 在进程 IPC 文件中指"进程生命周期"，在 rustc internals 中指 Rust lifetime token/概念。脚本无法按语义消歧。

4. **组合式术语（X 宏 / Poll 枚举 / 异步 HashMap）**
   "`format!` 宏"、"`panic!` 宏"、"Poll 枚举"、"异步 HashMap" 等是具体名称 + 通用词的组合，直接对"宏"、"枚举"标注会破坏可读性。脚本的前向/后向边界检查（`(?<![A-Za-z0-9_\u4e00-\u9fff])...(?![A-Za-z0-9_\u4e00-\u9fff])`）把这类组合当作独立术语，建议增加组合模式白名单或改为 manual_review。

5. **输入 JSON 与当前扫描结果不一致**
   `reports/uncovered_terms_current.json` 包含 `Future`、`Vec`、`Result`、`Pin`、`Option`、`crate`、`trait`、`unsafe`、`panic`、`Send`、`HashMap`、`FFI` 等英文原生术语，但当前 `check-only` 已不再报出。这说明 JSON 是历史快照；建议后续将 `check-only --output-uncovered` 作为单一事实来源，避免使用 stale JSON 做计划。

---

## 6. Appendix: `check-only` Output

```text
$ python scripts/add_bilingual_annotations.py --mode check-only

扫描文件数: 445
缺少 EN 字段: 0
缺少 Summary 字段: 0
未覆盖术语种类: 29
```

---

*本计划由 `scripts/add_bilingual_annotations.py --mode check-only` 驱动，仅做标注规划，尚未修改 `concept/`、`knowledge/` 或 `docs/` 内容。*
