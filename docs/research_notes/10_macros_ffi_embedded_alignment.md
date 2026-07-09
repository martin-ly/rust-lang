# 宏系统、FFI 与嵌入式生态权威来源对齐矩阵 {#宏系统ffi-与嵌入式生态权威来源对齐矩阵}

> **EN**: Macros FFI Embedded Alignment
> **Summary**: 宏系统、FFI 与嵌入式生态权威来源对齐矩阵 Macros FFI Embedded Alignment.
> **概念族**: 权威来源对齐 / 宏 / FFI / 嵌入式
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [宏系统、FFI 与嵌入式生态权威来源对齐矩阵 {#宏系统ffi-与嵌入式生态权威来源对齐矩阵}](#宏系统ffi-与嵌入式生态权威来源对齐矩阵-宏系统ffi-与嵌入式生态权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、宏系统 {#二宏系统}](#二宏系统-二宏系统)
  - [三、FFI {#三ffi}](#三ffi-三ffi)
  - [四、WebAssembly {#四webassembly}](#四webassembly-四webassembly)
  - [五、嵌入式生态 {#五嵌入式生态}](#五嵌入式生态-五嵌入式生态)
  - [六、与项目文档的映射 {#六与项目文档的映射}](#六与项目文档的映射-六与项目文档的映射)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中关于**宏系统**、**FFI**、**WebAssembly** 与**嵌入式生态**的内容与国际化权威来源建立映射，覆盖官方规范、生态工具链、主流 crate 与社区教材。

对齐维度：

1. **概念定义对齐** — 项目定义与权威来源是否一致。
2. **代码示例对齐** — 示例是否可运行且符合官方 API。
3. **版本特性对齐** — 是否标注最低 Rust 版本 / Edition。
4. **差异说明** — 若项目表述与来源有差异，需显式论证。
5. **反向追溯** — 从权威来源章节可反向找到项目文档。

---

## 二、宏系统 {#二宏系统}

| 权威来源 | 类型 | 项目文档 | 覆盖内容 | 状态 |
|----------|------|----------|----------|------|
| [The Rust Reference – Macros](https://doc.rust-lang.org/reference/macros.html) | 语言规范 | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | `macro_rules!`、卫生性、fragment specifiers、proc-macro | ✅ 已完成 |
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | 高级/unsafe 指南 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | 宏展开与 unsafe 边界、生命周期与类型布局 | ✅ 已完成 |
| [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/) | 社区教材 | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | 声明宏模式、递归、卫生性、调试技巧 | ✅ 已完成 |
| [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop) | 实战练习 | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | 派生宏、属性宏、函数宏、TokenStream 解析 | ✅ 已完成 |

---

## 三、FFI {#三ffi}

| 权威来源 | 类型 | 项目文档 | 覆盖内容 | 状态 |
|----------|------|----------|----------|------|
| [Rustonomicon – FFI](https://doc.rust-lang.org/nomicon/ffi.html) | 高级/unsafe 指南 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | `extern`、ABI、裸指针、所有权跨边界 | ✅ 已完成 |
| [Unsafe Code Guidelines – FFI](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html) | unsafe 指南 | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | FFI 内存协议、Validity Invariants | ✅ 已完成 |
| [bindgen](https://rust-lang.github.io/rust-bindgen/) | 工具/crate | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | C/C++ 头文件自动生成 Rust 绑定 | ✅ 已完成 |
| [cbindgen](https://github.com/mozilla/cbindgen) | 工具/crate | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 由 Rust 生成 C/C++ 头文件 | ✅ 已完成 |
| [cxx](https://cxx.rs/) | 跨语言互操作框架 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | Rust 与 C++ 安全互操作 | ✅ 已完成 |
| [windows-rs](https://github.com/microsoft/windows-rs) | 平台绑定 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | Windows API 的 Rust 绑定 | ✅ 已完成 |

---

## 四、WebAssembly {#四webassembly}

| 权威来源 | 类型 | 项目文档 | 覆盖内容 | 状态 |
|----------|------|----------|----------|------|
| [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) | 工具/crate | [crates/c12_wasm/](../../crates/c12_wasm/README.md) | Rust ↔ JavaScript 类型映射与互操作 | ✅ 已完成 |
| [wasm-pack](https://rustwasm.github.io/wasm-pack/) | 工具/crate | [crates/c12_wasm/](../../crates/c12_wasm/README.md) | WASM 包构建、测试与发布 | ✅ 已完成 |
| [The Rust and WebAssembly Book](https://rustwasm.github.io/book/) | 官方教程 | [crates/c12_wasm/](../../crates/c12_wasm/README.md) | wasm32 目标、JS glue、性能优化 | ✅ 已完成 |

---

## 五、嵌入式生态 {#五嵌入式生态}

| 权威来源 | 类型 | 项目文档 | 覆盖内容 | 状态 |
|----------|------|----------|----------|------|
| [embedded-hal](https://docs.rs/embedded-hal/) | 硬件抽象 trait | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 外设抽象、传感器/驱动接口 | ✅ 已完成 |
| [Embassy](https://embassy.dev/) | 异步运行时框架 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | `no_std` async、executor、中断驱动 | ✅ 已完成 |
| [RTIC](https://rtic.rs/) | 实时中断驱动并发框架 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 任务调度、资源锁、单态化（Monomorphization） | ✅ 已完成 |
| [The Embedded Rust Book](https://docs.rust-embedded.org/book/) | 官方教材 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | `no_std`、HAL、启动流程、panic 处理 | ✅ 已完成 |
| [Ferrous Systems Training](https://embedded-trainings.ferrous-systems.com/) | 社区培训教材 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 裸机调试、硬件实操、defmt | ✅ 已完成 |
| [probe-rs](https://probe.rs/) | 调试/烧录工具 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 片上调试、RTT、Flash 下载 | ✅ 已完成 |
| [defmt](https://defmt.ferrous-systems.com/) | 日志框架 | [crates/c13_embedded/](../../crates/c13_embedded/README.md) | 压缩日志、RTT 传输、probe-rs 集成 | ✅ 已完成 |

---

## 六、与项目文档的映射 {#六与项目文档的映射}

| 项目文档 | 生态覆盖 | 权威来源 |
|----------|----------|----------|
| [crates/c11_macro_system_proc/README.md](../../crates/c11_macro_system_proc/README.md) | 声明宏（Declarative Macro）、过程宏（Procedural Macro）、DSL、调试与性能 | Rust Reference、The Little Book of Rust Macros、proc-macro-workshop |
| [crates/c12_wasm/README.md](../../crates/c12_wasm/README.md) | wasm-bindgen、wasm-pack、WASI、浏览器/Node 集成 | wasm-bindgen、wasm-pack、The Rust and WebAssembly Book |
| [crates/c13_embedded/README.md](../../crates/c13_embedded/README.md) | `no_std`、HAL、RTIC、Embassy、FFI、probe-rs、defmt | Embedded Rust Book、embedded-hal、RTIC、Embassy、Ferrous Systems Training |
| [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | FFI 内存协议、裸指针、跨语言所有权 | Rustonomicon FFI、Unsafe Code Guidelines FFI |
| [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | unsafe/FFI 边界、Validity Invariants | Unsafe Code Guidelines |
| [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | 宏展开与 unsafe、类型布局、FFI | Rustonomicon |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. **宏系统**：proc-macro 单元测试与 `proc_macro2` 在 `no_std` 场景下的专门对齐文档。
2. **FFI**：跨语言异常安全（C++ exception / Rust panic 边界）与 `UnwindSafe` 的 FFI 映射。
3. **FFI**：`windows-rs` 生成代码与 `raw-dylib`、COM/WinRT 互操作的专门示例 crate。
4. **WebAssembly**：WASI 0.2 / component model 与 Rust 新 target（`wasm32-wasip2`）的对齐。
5. **WebAssembly**：`wasm-bindgen` 高级模式（内部可变性、闭包长期存活、JS 异常处理）的边界反例。
6. **嵌入式**：`no_std` 全局分配器（`embedded-alloc`、`alloc-cortex-m`）与 heap 安全边界。
7. **嵌入式**：RTIC v2 迁移、Embassy 与 `embassy-time` 时钟抽象的持续跟踪。
8. **嵌入式**：`probe-rs` 调试脚本自动化与 `defmt` 自定义解码器的实战映射。

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/) | [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop) | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [bindgen](https://rust-lang.github.io/rust-bindgen/) | [cbindgen](https://github.com/mozilla/cbindgen) | [cxx](https://cxx.rs/) | [windows-rs](https://github.com/microsoft/windows-rs) | [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) | [wasm-pack](https://rustwasm.github.io/wasm-pack/) | [The Rust and WebAssembly Book](https://rustwasm.github.io/book/) | [The Embedded Rust Book](https://docs.rust-embedded.org/book/) | [embedded-hal](https://docs.rs/embedded-hal/) | [Embassy](https://embassy.dev/) | [RTIC](https://rtic.rs/) | [probe-rs](https://probe.rs/) | [defmt](https://defmt.ferrous-systems.com/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [Unsafe Code Guidelines 对齐](10_unsafe_code_guidelines_alignment.md)
- [Rustonomicon 对齐](10_rustonomicon_alignment.md)
- [异步生态权威来源对齐](10_async_ecosystem_alignment.md)
- [C11 宏系统 crate](../../crates/c11_macro_system_proc/README.md)
- [C12 WASM crate](../../crates/c12_wasm/README.md)
- [C13 嵌入式 crate](../../crates/c13_embedded/README.md)
- [Unsafe 与 FFI 反例](formal_methods/60_unsafe_counterexamples.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
