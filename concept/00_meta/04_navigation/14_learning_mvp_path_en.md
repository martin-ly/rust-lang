# Rust Minimum Viable Learning Path (MVP Path)

> **Summary**: A 3-week beginner path to independently write a multi-threaded CLI in Rust, with runnable code and exercises for each stage.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **EN**: Rust Minimum Viable Learning Path
> **Target Audience**: Beginners with programming experience in at least one other language
> **Estimated Time**: 35–45 hours (≈ 3 weeks at 2 hours/day)
> **End Goal**: Independently write a multi-threaded command-line tool (CLI)
> **Design Principle**: Every stage must have runnable code; every concept must have corresponding exercises
> **主要来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Cargo Book](https://doc.rust-lang.org/cargo/index.html)
> ⚠️ **草案状态**: 本文件为英文 MVP 路径草案，其中部分链接指向的概念文件编号/名称可能与当前 `concept/` 目录结构不一致。请以中文版 [`08_learning_mvp_path.md`](08_learning_mvp_path.md) 为权威学习路径。
> **权威来源**: 本文件为 `concept/` 权威页。
---

## Path Overview

```text
Week 1: Rust Fundamentals & Ownership (12h) [Required]
    ├─ Day 1: Hello World + Toolchain (2h) [Required]
    ├─ Day 2: Ownership & Move Semantics (2h) [Required]
    ├─ Day 3: Borrowing & References (2h) [Required]
    ├─ Day 4: Basic Types & Collections (2h) [Required]
    └─ Day 5–6: Comprehensive Exercises + Checkpoint (4h) [Required]

Week 2: Type System & Error Handling (12h) [Required]
    ├─ Day 7: Structs, Enums & Pattern Matching (2h) [Required]
    ├─ Day 8: Traits & Generics Intro (2h) [Required]
    ├─ Day 9: Error Handling (2h) [Required]
    ├─ Day 10: Modules & Cargo (2h) [Required]
    └─ Day 11–12: Comprehensive Exercises + Checkpoint (4h) [Required]

Week 3: Concurrency & CLI Project (12h) [Required]
    ├─ Day 13: Threads & Shared State (2h) [Required]
    ├─ Day 14: Channels & Message Passing (2h) [Required]
    ├─ Day 15: Async/Await Intro (2h) [Recommended]
    ├─ Day 16: Building a CLI Tool (2h) [Required]
    └─ Day 17–18: Final Project + Review (4h) [Required]
```

---

## Week 1: Rust Fundamentals & Ownership (12h)

第一周聚焦「能编译、懂所有权」的最小可用能力，12 小时分配：

- **Day 1-2（4h）环境 + 基础语法**：rustup/cargo 工作流、`let`/`fn`/控制流、模式匹配入门——验收：能独立创建项目、读懂编译错误的第一行；
- **Day 3-4（4h）所有权核心**：move 语义、借用规则（`&`/`&mut` 排他性）、`String` vs `&str`——验收：能解释 E0382/E0502 各一个实例并修复；
- **Day 5-6（4h）结构体 + 错误处理入门**：`struct`/`impl`/`Option`/`Result`/`?`——验收：完成「读文件 + 解析 + 错误传播」小工具。

学习纪律：本周**不碰**生命周期标注、泛型、trait——所有代码用 owned 类型 + clone 过关，「丑但正确」是第一周的审美标准。

### Day 1: Hello World + Toolchain (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Install Rust via rustup | 15m | `rustc --version` shows ≥ 1.97.0 |
| Configure IDE (rust-analyzer) | 15m | Auto-completion works for `Vec::` |
| Read `concept/01_foundation/00_hello_world.md` | 30m | Can explain `fn main()`, `println!` |
| Write a temperature converter | 30m | `cargo run` produces correct output |
| Complete [exercises/src/ownership_borrowing/](../../exercises/src/ownership_borrowing) intro | 30m | `cargo test` passes first 3 tests |

**Key Concepts**: `rustc`, `cargo`, `fn`, `let`, mutability, macros.

### Day 2: Ownership & Move Semantics (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 45m | Can draw ownership transfer diagrams |
| Read `concept/01_foundation/02_move_semantics.md` | 30m | Predicts move vs. copy correctly |
| Solve rustlings `move_semantics` exercises | 30m | All tests pass |
| Take `L1 Ownership Quiz` | 15m | Score ≥ 3/4 |

**Key Concepts**: Ownership rules, `Copy` vs. `Drop`, move semantics, `clone()`.

### Day 3: Borrowing & References (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read `concept/01_foundation/03_borrowing.md` | 45m | Explains `&T` vs. `&mut T` |
| Read `concept/01_foundation/04_lifetimes_intro.md` | 30m | Understands lifetime elision rules |
| Solve rustlings `references` exercises | 30m | All tests pass |
| Debug borrow checker errors (intentional) | 15m | Fixes 3 compiler errors independently |

**Key Concepts**: Shared references, mutable references, aliasing XOR mutation, lifetime elision.

### Day 4: Basic Types & Collections (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read `concept/01_foundation/05_basic_types.md` | 30m | Knows `i32` vs. `u32`, `f64` vs. `f32` |
| Read `concept/01_foundation/06_collections.md` | 30m | Uses `Vec`, `HashMap`, `HashSet` correctly |
| Practice: Word frequency counter | 45m | Handles file I/O, counts words accurately |
| Take `L1 Collections Quiz` | 15m | Score ≥ 3/4 |

**Key Concepts**: Scalar types, compound types, `Vec`, `HashMap`, iterators.

### Day 5–6: Checkpoint (4h)

| Task | Time | Verification |
|:---|:---:|:---|
| Build a text file analyzer | 2h | Counts lines/words/chars, finds top words |
| Write unit tests for the analyzer | 1h | ≥ 80% test coverage |
| Code review checklist | 30m | No `unwrap()` in production paths |
| Reflect: Fill `Learning Journal` | 30m | Identifies 3 weak points to improve |

---

## Week 2: Type System & Error Handling (12h)

第二周聚焦「类型系统驱动设计」，12 小时分配：

- **Day 1-2（4h）trait 与泛型**：trait 定义/实现/约束、泛型函数与单态化直觉、`impl Trait` 两种位置——验收：为自定义类型实现 `Display`/`FromIterator`；
- **Day 3-4（4h）生命周期**：省略规则三条件、显式标注的两种必要场景（多引用参数、结构体持有引用）——验收：能解释 `'a` 标注是「关系声明」而非「延长时间」；
- **Day 5-6（4h）错误处理工程化**：`thiserror` 库错误、`anyhow` 应用错误、错误转换与上下文——验收：CLI 项目接入分层错误类型。

验收整合：本周产出「泛型化 + 错误分层」的 v2 版小工具，与第一周的 owned-only 版本对照——类型系统的表达收益应可量化（代码行数/错误路径覆盖）。

### Day 7: Structs, Enums & Pattern Matching (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read `concept/02_intermediate/02_structs.md` | 30m | Defines structs with methods |
| Read `concept/02_intermediate/03_enums.md` | 30m | Models state machines with enums |
| Practice: JSON-like data structure | 45m | Recursive enums, pattern matching |
| Solve rustlings `enums` + `pattern_matching` | 15m | All tests pass |

**Key Concepts**: Named fields, tuple structs, unit structs, `Option`, `Result`, `match`, `if let`.

### Day 8: Traits & Generics Intro (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/02_intermediate/00_traits/01_traits.md](../../02_intermediate/00_traits/01_traits.md) | 45m | Implements custom trait |
| Read `concept/02_intermediate/06_generics.md` | 30m | Writes generic `fn` and generic `struct` |
| Practice: Generic `Stack<T>` | 30m | Works for `i32`, `String`, custom types |
| Take `L2 Traits Quiz` | 15m | Score ≥ 3/4 |

**Key Concepts**: Trait definitions, `impl Trait for Type`, trait bounds, generic parameters.

### Day 9: Error Handling (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/02_intermediate/03_error_handling/01_error_handling.md](../../02_intermediate/03_error_handling/01_error_handling.md) | 45m | Chooses between `Result` and `panic!` |
| Read [concept/02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md](../../02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md) | 15m | Uses `assert_matches!` in tests |
| Practice: File parser with error propagation | 45m | Uses `?` operator, custom error type |
| Solve rustlings `error_handling` | 15m | All tests pass |

**Key Concepts**: `Result<T, E>`, `Option<T>`, `?` operator, `thiserror`, `anyhow`.

### Day 10: Modules & Cargo (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/01_foundation/07_modules_and_items/01_modules_and_paths.md](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | 30m | Organizes code into modules |
| Read `docs/06_toolchain/06_cargo_workspace_guide.md` | 30m | Creates multi-crate workspace |
| Practice: Split analyzer into lib + bin | 45m | `cargo test` and `cargo run` work |
| Configure `Cargo.toml`: dependencies, features | 15m | Adds `clap`, `serde` correctly |

**Key Concepts**: `mod`, `use`, `pub`, workspace, crates, dependencies.

### Day 11–12: Checkpoint (4h)

| Task | Time | Verification |
|:---|:---:|:---|
| Build a CSV parser library | 2h | Parses RFC 4180 CSV, handles errors |
| Write doc comments + `cargo doc` | 30m | Documentation builds without warnings |
| Add CI with GitHub Actions | 30m | `cargo test` passes on push |
| Reflect: Learning journal update | 30m | Compares Week 1 vs. Week 2 confidence |

---

## Week 3: Concurrency & CLI Project (12h)

本节聚焦「Week 3: Concurrency & CLI Project (12h)」，覆盖Day 13: Threads & Shared State (2h)、Day 14: Channels & Message Passing…、Day 15: Async/Await Intro (2h) [Rec…、Day 16: Building a CLI Tool (2h)等方面。论述顺序由定义到边界：先明确「Week 3: Concurrency & CLI Project (12h)」在「Rust Minimum Viable Learning Path (MVP Path)」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「Week 3: Concurrency & CLI Project (12h)」的判定标准，并指出它在全页论证链中的位置。

### Day 13: Threads & Shared State (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/03_advanced/00_concurrency/01_concurrency.md](../../03_advanced/00_concurrency/01_concurrency.md) | 45m | Explains `spawn`, `join`, `Mutex`, `Arc` |
| Read [concept/03_advanced/00_concurrency/03_concurrency_patterns.md](../../03_advanced/00_concurrency/03_concurrency_patterns.md) §1–2 | 30m | Identifies deadlock risks |
| Practice: Parallel word count | 30m | Uses `rayon` or manual threads |
| Take [L3 Concurrency Quiz](../../03_advanced/00_concurrency/09_quiz_concurrency_async.md) §一 | 15m | Score ≥ 3/4 |

**Key Concepts**: `std::thread`, `Mutex`, `Arc`, `RwLock`, data races, deadlocks.

### Day 14: Channels & Message Passing (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/03_advanced/00_concurrency/03_concurrency_patterns.md](../../03_advanced/00_concurrency/03_concurrency_patterns.md) §2.1 | 45m | Implements producer-consumer pattern |
| Practice: Multi-stage pipeline | 45m | Bounded channels, backpressure |
| Debug: Channel closed errors | 15m | Handles `SendError` gracefully |
| Benchmark: Channel vs. Mutex | 15m | Measures throughput difference |

**Key Concepts**: `mpsc::channel`, bounded vs. unbounded, `select!`, Actor pattern.

### Day 15: Async/Await Intro (2h) [Recommended]

| Task | Time | Verification |
|:---|:---:|:---|
| Read [concept/03_advanced/01_async/01_async.md](../../03_advanced/01_async/01_async.md) | 45m | Explains `Future`, `.await`, executor |
| Read [concept/03_advanced/01_async/03_async_patterns.md](../../03_advanced/01_async/03_async_patterns.md) §1–2 | 30m | Uses `tokio::select!` for timeouts |
| Practice: Async HTTP client | 30m | Fetches 3 URLs concurrently |
| Take [L3 Async Quiz](../../03_advanced/00_concurrency/09_quiz_concurrency_async.md) §二 | 15m | Score ≥ 2/3 |

**Key Concepts**: `async fn`, `.await`, `tokio`, `Future`, cancellation safety.

### Day 16: Building a CLI Tool (2h)

| Task | Time | Verification |
|:---|:---:|:---|
| Read `docs/03_guides/03_cli_development_guide.md` | 30m | Knows `clap` derive API |
| Design: File search tool (`grep`-like) | 30m | Spec: regex, recursive, line numbers |
| Implement core functionality | 45m | `cargo run -- "pattern" file.txt` works |
| Add tests for edge cases | 15m | Empty files, binary files, unicode |

**Key Concepts**: `clap`, `regex`, file I/O, error context, `tracing`.

### Day 17–18: Final Project + Review (4h)

| Task | Time | Verification |
|:---|:---:|:---|
| Implement: `rgrep` — multi-threaded grep | 2h | Parallel directory traversal, results correct |
| Add: Colored output, config file | 30m | `bat`-like syntax highlighting |
| Write: README + usage examples | 30m | New user can install and run in 5 min |
| Final review: Clippy + fmt + test | 30m | Zero warnings, all tests pass |
| Reflect: Final learning journal | 30m | Lists 10+ Rust concepts now understood |

---

## Resource Index

本节聚焦「Resource Index」，覆盖Required Reading、Cheat Sheets与Exercise Sources。论述顺序由定义到边界：先明确「Resource Index」在「Rust Minimum Viable Learning Path (MVP Path)」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「Resource Index」的判定标准，并指出它在全页论证链中的位置。

### Required Reading

| Topic | File | Bloom Level |
|:---|:---|:---:|
| Ownership | [concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | Understand |
| Borrowing | `concept/01_foundation/03_borrowing.md` | Understand |
| Traits | [concept/02_intermediate/00_traits/01_traits.md](../../02_intermediate/00_traits/01_traits.md) | Apply |
| Error Handling | [concept/02_intermediate/03_error_handling/01_error_handling.md](../../02_intermediate/03_error_handling/01_error_handling.md) | Apply |
| Concurrency | [concept/03_advanced/00_concurrency/01_concurrency.md](../../03_advanced/00_concurrency/01_concurrency.md) | Apply |

### Cheat Sheets

| Topic | File |
|:---|:---|
| Ownership & Borrowing | `docs/02_reference/quick_reference/02_ownership_borrowing_cheatsheet.md` |
| Type System | [docs/03_reference/quick_reference/27_type_system.md](../../../docs/03_reference/quick_reference/27_type_system.md) |
| Collections & Iterators | [docs/03_reference/quick_reference/08_collections_iterators_cheatsheet.md](../../../docs/03_reference/quick_reference/08_collections_iterators_cheatsheet.md) |
| Error Handling | [docs/03_reference/quick_reference/10_error_handling_cheatsheet.md](../../../docs/03_reference/quick_reference/10_error_handling_cheatsheet.md) |

### Exercise Sources

| Source | Location | Count |
|:---|:---|:---:|
| rustlings-style exercises | [exercises/src/](exercises/src) | 100+ |
| Crate examples | [crates/](crates) | 17 crates |
| Embedded quizzes | [concept/](concept) | 14 files with quizzes |
| Runnable quiz tests | [exercises/tests/](exercises/tests) | 39 tests |

---

## Self-Assessment Checklist

After completing this path, you should be able to:

- [ ] Explain ownership, borrowing, and lifetimes to another programmer
- [ ] Write `struct` and `enum` definitions with methods and trait implementations
- [ ] Handle errors with `Result` and `?` without panicking in library code
- [ ] Use `Mutex`, `Arc`, and channels for safe concurrency
- [ ] Build a CLI tool with `clap`, file I/O, and basic error handling
- [ ] Read and understand most Rust compiler errors
- [ ] Write unit tests and integration tests with `cargo test`

**Next Steps**:

- **Systems Programming**: [concept/03_advanced/05_inline_assembly/01_inline_assembly.md](../../03_advanced/05_inline_assembly/01_inline_assembly.md) + [crates/c13_embedded/](crates/c13_embedded)
- **Web Backend**: [concept/03_advanced/01_async/01_async.md](../../03_advanced/01_async/01_async.md) + [crates/c10_networks/](crates/c10_networks)
- **Formal Verification**: [concept/04_formal/03_ownership_formal.md](../../04_formal/01_ownership_logic/02_ownership_formal.md) + [concept/04_formal/05_verification_toolchain.md](../../04_formal/04_model_checking/01_verification_toolchain.md)

---

> **Version**: Rust 1.97.0+ (Edition 2024)
> **Last Updated**: 2026-06-09
> **Maintainer**: Rust Learning Community
