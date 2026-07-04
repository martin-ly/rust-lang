# 主题-权威来源对齐与缺口行动计划

**生成日期**：2026-07-05 04:48

## 执行摘要

本报告基于 `scripts/topic_authority_aligner.py` 对项目当前 `concept/` 资产与四类权威来源的自动对齐结果：

- 当前项目 `concept/` 主题数：**400**
- 权威来源主题数：**53**
- 已对齐主题：**34**（覆盖率 64.2%）
- 权威独有缺口：**19**
- 项目独有主题：**372**

## 1. 对称差矩阵

| 来源类别 | 权威主题数 | 已对齐 | 缺口 | 覆盖率 |
|----------|-----------|--------|------|--------|
| 形式化/验证生态 | 12 | 7 | 5 | 58.3% |
| 工业/应用生态 | 25 | 14 | 11 | 56.0% |
| 项目路线图 | 16 | 13 | 3 | 81.2% |

## 2. Top-30 缺口任务清单

> 每项任务包含：缺口标题、建议目录、依赖、验收标准。

| 优先级 | 缺口主题 | 建议目录 | 依赖 | 验收标准 |
|--------|----------|----------|------|----------|
| P0 | Iris: Higher-Order Concurrent Separation Logic Framework | concept/01_foundation/ 或 concept/03_advanced/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P0 | Borrow Sanitizer | concept/01_foundation/ 或 concept/03_advanced/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P0 | bindgen / cbindgen | concept/01_foundation/ 或 concept/03_advanced/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P0 | reqwest | concept/01_foundation/ 或 concept/03_advanced/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P1 | Verus: Verified Rust for Low-Level Systems | concept/04_formal/ 或 docs/research_notes/formal_methods/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P1 | Miri: Rust Interpreter for Undefined Behavior | concept/04_formal/ 或 docs/research_notes/formal_methods/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P1 | Ferrocene: Rust for Safety-Critical Systems | concept/04_formal/ 或 docs/research_notes/formal_methods/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | sqlx | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | Tauri | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | Dioxus | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | Leptos | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | egui | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | PyO3 | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P2 | rayon | concept/06_ecosystem/ 或 crates/cXX_*/docs/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P3 | cortex-m / riscv-rt | concept/07_future/ 或 content/emerging/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P3 | ring / rustls | concept/07_future/ 或 content/emerging/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P3 | Cranelift Backend | concept/07_future/ 或 content/emerging/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P3 | MCDC Coverage | concept/07_future/ 或 content/emerging/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |
| P3 | Rustdoc Search / Scraped Examples | concept/07_future/ 或 content/emerging/ | 权威来源链接 | 完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用） |

## 3. 重复/合并建议

未检测到明显标题重复。

## 4. 后续维护机制

1. **月度更新**：运行 `python scripts/topic_authority_aligner.py --phase all`，刷新 `concept/00_meta/topic_authority_alignment_map.md` 与本报告。
2. **季度评审**：由内容负责人审核 P0/P1 缺口，决定是否纳入下一个 sprint。
3. **新增文档规范**：每个新 `concept/` 文件需在 frontmatter 中标注 `authority_source` 与 `coverage_level`，便于自动对齐。
4. **验证门禁**：合并前必须运行 `kb_auditor.py`、`detect_content_overlap.py`、`cargo check --workspace`。

## 附录 A：权威来源列表

### 官方文档

- [The Rust Programming Language](https://doc.rust-lang.org/book)
- [The Rust Reference](https://doc.rust-lang.org/reference)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon)
- [Rust By Example](https://doc.rust-lang.org/rust-by-example)
- [The Cargo Book](https://doc.rust-lang.org/cargo)
- [The rustc Book](https://doc.rust-lang.org/rustc)
- [The Embedded Rust Book](https://doc.rust-lang.org/embedded-book)
- [The Rust Edition Guide](https://doc.rust-lang.org/edition-guide)
- [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book)
- [Rust and WebAssembly](https://rustwasm.github.io/docs/book)

### 形式化/验证生态

- [RustBelt: Logical Relations for Rust](https://plv.mpi-sws.org/rustbelt/)
- [Iris: Higher-Order Concurrent Separation Logic Framework](https://iris-project.org/)
- [Aeneas: Symbolic Semantics for Rust](https://github.com/AeneasVerif/aeneas)
- [Prusti: Deductive Verification for Rust](https://www.pm.inf.ethz.ch/research/prusti.html)
- [Kani: Rust Model Checker](https://model-checking.github.io/kani/)
- [Verus: Verified Rust for Low-Level Systems](https://verus-lang.github.io/verus/)
- [Miri: Rust Interpreter for Undefined Behavior](https://github.com/rust-lang/miri)
- [Tree Borrows / Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)
- [Ferrocene: Rust for Safety-Critical Systems](https://ferrocene.dev/)
- [Safety Tags / Type Safety Tags](https://rust-lang.github.io/rfcs/0000-safety-tags.html)
- [Borrow Sanitizer](https://github.com/rust-lang/miri/blob/master/BORROW_SANITIZER.md)
- [Rust Specification (lang-spec-rust-lang-org)](https://github.com/rust-lang/spec)

### 工业/应用生态

- [Tokio](https://tokio.rs/) — Async Runtime
- [Axum](https://docs.rs/axum/latest/axum/) — Web Framework
- [Actix-web](https://actix.rs/) — Web Framework
- [Sea-ORM](https://www.sea-ql.org/SeaORM/) — ORM
- [sqlx](https://github.com/launchbadge/sqlx) — Database Driver
- [Bevy](https://bevyengine.org/) — Game Engine
- [Tauri](https://tauri.app/) — GUI / Cross-platform
- [Dioxus](https://dioxuslabs.com/) — GUI / Cross-platform
- [Leptos](https://leptos.dev/) — GUI / Web
- [egui](https://www.egui.rs/) — GUI / Immediate Mode
- [PyO3](https://pyo3.rs/) — Python Interop
- [bindgen / cbindgen](https://rust-lang.github.io/rust-bindgen/) — FFI / C Interop
- [wasm-bindgen / web-sys](https://rustwasm.github.io/wasm-bindgen/) — WASM
- [crossbeam](https://docs.rs/crossbeam/latest/crossbeam/) — Concurrency
- [rayon](https://docs.rs/rayon/latest/rayon/) — Data Parallelism
- [parking_lot](https://docs.rs/parking_lot/latest/parking_lot/) — Synchronization
- [serde](https://serde.rs/) — Serialization
- [clap](https://docs.rs/clap/latest/clap/) — CLI
- [anyhow / thiserror](https://docs.rs/anyhow/latest/anyhow/) — Error Handling
- [reqwest](https://docs.rs/reqwest/latest/reqwest/) — Async HTTP Client
- [tonic](https://github.com/hyperium/tonic) — gRPC
- [tracing / opentelemetry](https://docs.rs/tracing/latest/tracing/) — Metrics / Observability
- [embedded-hal](https://docs.rs/embedded-hal/latest/embedded_hal/) — Embedded HAL
- [cortex-m / riscv-rt](https://docs.rs/cortex-m/latest/cortex_m/) — No-std / Bare Metal
- [ring / rustls](https://github.com/briansmith/ring) — Crypto

### 项目路线图

- [Rust Project Goals 2025 H1](https://rust-lang.github.io/rust-project-goals/2025h1/index.html) — Project Goals 2025 H1
- [Rust 2024 Edition](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) — Edition
- [Async Closures / Async Fn in Traits](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html) — Async
- [Specialization / Min Specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html) — Type System
- [Generic Associated Types (GATs)](https://rust-lang.github.io/rfcs/1598-generic_associated_types.html) — Type System
- [Type Alias Impl Trait (TAIT)](https://rust-lang.github.io/rfcs/2515-type-alias-impl-trait.html) — Type System
- [Return Type Notation (RTN)](https://rust-lang.github.io/rfcs/3654-new-return-type-notation.html) — Type System
- [Precise Capturing / Lifetime Capture](https://rust-lang.github.io/rfcs/0000-lifetime-capture.html) — Type System
- [Unsafe Fields / Unsafe extern blocks](https://rust-lang.github.io/rfcs/0000-unsafe-extern-blocks.html) — Unsafe
- [Arbitrary Self Types v2](https://rust-lang.github.io/rfcs/3519-arbitrary-self-types-v2.html) — Unsafe
- [Derive CoercePointee](https://rust-lang.github.io/rfcs/3693-derive-coerce-pointee.html) — Macros
- [Parallel Frontend](https://blog.rust-lang.org/inside-rust/2024/04/24/parallel-front-end.html) — Compiler
- [Cranelift Backend](https://github.com/bjorn3/rustc_codegen_cranelift) — Compiler
- [Cargo SemVer Checks](https://github.com/obi1kenobi/cargo-semver-checks) — Tooling
- [MCDC Coverage](https://github.com/rust-lang/rust/pull/124658) — Tooling
- [Rustdoc Search / Scraped Examples](https://doc.rust-lang.org/rustdoc/scraped-examples.html) — Tooling

## 附录 B：项目索引资产

- `concept/00_meta/topic_authority_alignment_map.md`：当前项目主题树与权威来源对齐图谱。
- `tmp/topic_inventory_current.json`：当前项目主题结构化数据。
- `tmp/topic_inventory_authoritative.json`：权威来源主题结构化数据。
- `tmp/topic_symmetric_diff.json`：完整对称差数据。
- `tmp/topic_alignment_matrix.tsv`：对齐矩阵（可用于电子表格透视）。
