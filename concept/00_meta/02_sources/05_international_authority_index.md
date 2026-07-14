> **内容分级**: [综述级]

# International Authority Index（国际化权威来源索引）
>
> **EN**: International Authority Index
> **Summary**: A curated, categorized index of authoritative international sources for Rust: official docs, academic formalization, industrial ecosystems, standards bodies, and cross-language references.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者 / 进阶]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 为每个 Rust 概念提供可验证的国际权威来源映射
> **定位**: 集中维护 Rust 知识体系所需的国际权威来源 URL，便于 concept/、knowledge/、docs/ 各层统一引用，避免重复搜索与链接失效。
> **前置概念**: [Authority Source Map](01_authority_source_map.md) · [Sources](03_sources.md) · [Topic-Authority Alignment Map](04_topic_authority_alignment_map.md)
> **后置概念**: [Concept Index](../04_navigation/03_concept_index.md) · [Knowledge Mindmap](../00_framework/knowledge_mindmap.md)
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/index.html)

---

> **对应 Crate**: N/A
> **对应练习**: N/A

## 📑 目录

- [International Authority Index（国际化权威来源索引）](#international-authority-index国际化权威来源索引)
  - [📑 目录](#-目录)
  - [一、Rust 官方文档](#一rust-官方文档)
  - [二、形式化与验证生态](#二形式化与验证生态)
  - [三、工业与生态库](#三工业与生态库)
    - [异步与网络](#异步与网络)
    - [数据库与 ORM](#数据库与-orm)
    - [并发与并行](#并发与并行)
    - [GUI 与跨平台](#gui-与跨平台)
    - [游戏与图形](#游戏与图形)
    - [FFI 与互操作](#ffi-与互操作)
    - [嵌入式](#嵌入式)
    - [安全与密码学](#安全与密码学)
    - [序列化、CLI、错误处理、可观测性](#序列化cli错误处理可观测性)
  - [四、跨语言权威入口](#四跨语言权威入口)
    - [C++](#c)
    - [Haskell](#haskell)
    - [Go](#go)
    - [学术通用](#学术通用)
  - [五、标准与行业规范](#五标准与行业规范)
  - [六、社区权威博客与演讲](#六社区权威博客与演讲)
  - [七、使用建议](#七使用建议)

---

## 一、Rust 官方文档

| 来源 | URL | 适用主题 |
|:---|:---|:---|
| The Rust Programming Language (TRPL) | <https://doc.rust-lang.org/book/> | 入门、所有权、类型系统、并发、Async |
| The Rust Reference | <https://doc.rust-lang.org/reference/> | 语法、语义、Items、类型、Unsafe |
| The Rustonomicon | <https://doc.rust-lang.org/nomicon/> | Unsafe Rust、FFI、内存模型 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动的语法与标准库用法 |
| The Cargo Book | <https://doc.rust-lang.org/cargo/> | Cargo、Workspace、Features、Publishing |
| The Edition Guide | <https://doc.rust-lang.org/edition-guide/> | Edition 差异、迁移指南 |
| The rustc Book | <https://doc.rust-lang.org/rustc/> | 编译器选项、目标平台 |
| The Rustdoc Book | <https://doc.rust-lang.org/rustdoc/> | 文档生成、Scraped Examples |
| Asynchronous Programming in Rust | <https://rust-lang.github.io/async-book/> | Future、Pin、Waker、Executors |
| Rust and WebAssembly | <https://rustwasm.github.io/docs/book/> | WASM、wasm-bindgen、web-sys |
| The Embedded Rust Book | <https://doc.rust-lang.org/embedded-book/> | embedded-hal、no_std、Bare Metal |
| Rust RFCs | <https://rust-lang.github.io/rfcs/> | 语言特性设计、Roadmap |
| Rust Project Goals | <https://rust-lang.github.io/rust-project-goals/> | 项目目标与年度路线图 |
| Rust Blog / Inside Rust | <https://blog.rust-lang.org/> · <https://blog.rust-lang.org/inside-rust/> | 发布说明、内部实现更新 |

---

## 二、形式化与验证生态

| 来源 | URL | 说明 |
|:---|:---|:---|
| RustBelt (POPL 2018) | <https://plv.mpi-sws.org/rustbelt/> | Rust 形式化基础：所有权、类型系统 |
| Stacked Borrows | <https://plv.mpi-sws.org/rustbelt/stacked-borrows/> | 别名模型（已被 Tree Borrows 演进） |
| Tree Borrows | <https://plv.mpi-sws.org/rustbelt/> | 新的别名模型（PLDI 2025 Distinguished Paper） |
| Iris Project | <https://iris-project.org/> | 高阶并发分离逻辑框架 |
| Aeneas | <https://github.com/AeneasVerif/aeneas> | Rust 符号语义与验证 |
| Prusti | <https://www.pm.inf.ethz.ch/research/prusti.html> | 演绎验证（ETH Zürich） |
| Kani | <https://model-checking.github.io/kani/> | Rust 模型检查器（AWS） |
| Verus | <https://verus-lang.github.io/verus/guide/> | 低级系统验证 Rust |
| Miri | <https://github.com/rust-lang/miri> | UB 检测解释器 |
| Ferrocene | <https://ferrocene.dev/> | 安全关键领域 Rust |
| Safety Tags RFC | 待正式 RFC 编号 | 类型安全标签（预览） |
| Borrow Sanitizer MCP | <https://github.com/rust-lang/compiler-team/issues/958> | 运行时借用检查 sanitizer |
| a-mir-formality | <https://github.com/rust-lang/a-mir-formality> | Rust 核心类型系统形式化 |

---

## 三、工业与生态库

本节聚焦「工业与生态库」，覆盖异步与网络、数据库与 ORM、并发与并行、GUI 与跨平台等方面。论述顺序由定义到边界：先明确「工业与生态库」在「International Authority Index（国际化权威来源索引）」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「工业与生态库」的判定标准，并指出它在全页论证链中的位置。

### 异步与网络

| 来源 | URL |
|:---|:---|
| Tokio | <https://tokio.rs/> |
| Tokio Scheduler Internals（Carl Lerche, 2019） | <https://tokio.rs/blog/2019-10-scheduler> |
| futures-rs 官方文档 | <https://docs.rs/futures/latest/futures/> |
| Async WG 路线图（async-fundamentals-initiative） | <https://rust-lang.github.io/async-fundamentals-initiative/roadmap.html> |
| Writing an OS in Rust — Async/Await 章（phil-opp，深度实现源：手写 executor/Waker） | <https://os.phil-opp.com/async-await/> |
| async-std | <https://async.rs/> |
| Axum | <https://docs.rs/axum/latest/axum/> |
| Actix-web | <https://actix.rs/> |
| reqwest | <https://docs.rs/reqwest/latest/reqwest/> |
| tonic | <https://github.com/hyperium/tonic> |
| Quinn (QUIC) | <https://github.com/quinn-rs/quinn> |

### 数据库与 ORM

| 来源 | URL |
|:---|:---|
| Sea-ORM | <https://www.sea-ql.org/SeaORM/> |
| sqlx | <https://github.com/launchbadge/sqlx> |
| diesel | <https://diesel.rs/> |

### 并发与并行

| 来源 | URL |
|:---|:---|
| crossbeam | <https://docs.rs/crossbeam/latest/crossbeam/> |
| rayon | <https://docs.rs/rayon/latest/rayon/> |
| parking_lot | <https://docs.rs/parking_lot/latest/parking_lot/> |

### GUI 与跨平台

| 来源 | URL |
|:---|:---|
| Tauri | <https://tauri.app/> |
| Dioxus | <https://dioxuslabs.com/> |
| Leptos | <https://leptos.dev/> |
| egui | <https://www.egui.rs/> |
| Iced | <https://iced.rs/> |

### 游戏与图形

| 来源 | URL |
|:---|:---|
| Bevy | <https://bevyengine.org/> |
| wgpu | <https://wgpu.rs/> |

### FFI 与互操作

| 来源 | URL |
|:---|:---|
| bindgen | <https://rust-lang.github.io/rust-bindgen/> |
| cbindgen | <https://github.com/mozilla/cbindgen> |
| PyO3 | <https://pyo3.rs/> |
| wasm-bindgen | <https://rustwasm.github.io/wasm-bindgen/> |

### 嵌入式

| 来源 | URL |
|:---|:---|
| embedded-hal | <https://docs.rs/embedded-hal/latest/embedded_hal/> |
| cortex-m | <https://docs.rs/cortex-m/latest/cortex_m/> |
| riscv-rt | <https://docs.rs/riscv-rt/latest/riscv_rt/> |

### 安全与密码学

| 来源 | URL |
|:---|:---|
| ring | <https://github.com/briansmith/ring> |
| rustls | <https://github.com/rustls/rustls> |

### 序列化、CLI、错误处理、可观测性

| 来源 | URL |
|:---|:---|
| serde | <https://serde.rs/> |
| clap | <https://docs.rs/clap/latest/clap/> |
| anyhow | <https://docs.rs/anyhow/latest/anyhow/> |
| thiserror | <https://docs.rs/thiserror/latest/thiserror/> |
| tracing | <https://docs.rs/tracing/latest/tracing/> |

---

## 四、跨语言权威入口

本节聚焦「跨语言权威入口」，覆盖C++、Haskell、Go与学术通用。论述顺序由定义到边界：先明确「跨语言权威入口」在「International Authority Index（国际化权威来源索引）」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「跨语言权威入口」的判定标准，并指出它在全页论证链中的位置。

### C++

- **cppreference**: <https://en.cppreference.com/>
- **C++ Core Guidelines**: <https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines.html>
- **Itanium C++ ABI**: <https://itanium-cxx-abi.github.io/cxx-abi/abi.html>

### Haskell

- **GHC User Guide**: <https://downloads.haskell.org/ghc/latest/docs/users_guide/>
- **Typeclassopedia**: <https://wiki.haskell.org/Typeclassopedia>
- **Haskell Wiki**: <https://wiki.haskell.org/Haskell>

### Go

- **Go Spec**: <https://go.dev/ref/spec>
- **Effective Go**: <https://go.dev/doc/effective_go>
- **Go Memory Model**: <https://go.dev/ref/mem>

### 学术通用

- **TAPL (Pierce 2002)**: <https://www.cis.upenn.edu/~bcpierce/tapl/>
- **Software Foundations**: <https://softwarefoundations.cis.upenn.edu/>

---

## 五、标准与行业规范

| 来源 | URL | 说明 |
|:---|:---|:---|
| ISO/IEC 9899 (C Standard) | <https://www.iso.org/standard/74528.html> | C 语言标准 |
| ISO/IEC 14882 (C++ Standard) | <https://www.iso.org/standard/83626.html> | C++ 语言标准 |
| MISRA C:2012 | <https://misra.org.uk/> | 嵌入式 C 安全规范 |
| ISO 26262 | <https://www.iso.org/standard/68383.html> | 汽车功能安全 |
| IEC 61508 | <https://webstore.iec.ch/publication/66912> | 工业功能安全 |
| Linux Kernel BPF Docs | <https://docs.kernel.org/bpf/> | eBPF 文档 |

---

## 六、社区权威博客与演讲

| 作者 / 频道 | URL |
|:---|:---|
| Niko Matsakis | <https://smallcultfollowing.com/babysteps/> |
| Carl Lerche（Tokio 作者） | <https://tokio.rs/blog/> |
| Without Boats | <https://without.boats/> |
| Jon Gjengset | <https://thesquareplanet.com/blog/> · <https://www.youtube.com/@JonGjengset> |
| Ralf Jung | <https://www.ralfj.de/blog/> |
| dtolnay | <https://github.com/dtolnay> |

---

## 七、使用建议

1. **新增 concept/ 文件时**：优先从此索引选取 2–4 个相关权威来源写入 frontmatter 的 `> **来源**: ...`。
2. **引用学术来源时**：给出论文标题、会议/期刊、DOI 或项目主页。
3. **引用生态库时**：使用 docs.rs 或官方文档的 stable 链接；避免链接到特定版本号（除非讨论版本差异）。
4. **定期校验**：运行 `scripts/audit_source_links.py` 与 `scripts/audit_remaining_source_placeholders.py`，修复失效或泛化链接。
5. **发现新权威来源**：先更新本索引，再在概念页中引用，保持单一权威来源清单。
