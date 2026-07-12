# 工具链生态权威来源对齐矩阵 {#工具链生态权威来源对齐矩阵}

> **EN**: Toolchain Ecosystem Alignment
> **Summary**: 工具链生态权威来源对齐矩阵 Toolchain Ecosystem Alignment.
> **概念族**: 权威来源对齐 / 工具链生态
> **内容分级**: [核心级]
> **层级**: L0-L4
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [工具链生态权威来源对齐矩阵 {#工具链生态权威来源对齐矩阵}](#工具链生态权威来源对齐矩阵-工具链生态权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、编译器与核心工具 {#二编译器与核心工具}](#二编译器与核心工具-二编译器与核心工具)
  - [三、构建与包管理 {#三构建与包管理}](#三构建与包管理-三构建与包管理)
  - [四、代码质量工具 {#四代码质量工具}](#四代码质量工具-四代码质量工具)
  - [五、IDE 与编辑器 {#五ide-与编辑器}](#五ide-与编辑器-五ide-与编辑器)
  - [六、文档与发布 {#六文档与发布}](#六文档与发布-六文档与发布)
  - [七、交叉编译与目标平台 {#七交叉编译与目标平台}](#七交叉编译与目标平台-七交叉编译与目标平台)
  - [八、与项目文档的映射 {#八与项目文档的映射}](#八与项目文档的映射-八与项目文档的映射)
  - [九、未覆盖缺口 {#九未覆盖缺口}](#九未覆盖缺口-九未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/12_research_notes/` 中的工具链、构建、质量、发布内容与 Rust 官方工具链生态的权威来源建立映射，覆盖 rustc、Cargo、rustup、clippy、rustfmt、rust-analyzer、rustdoc 等核心组件。

---

## 二、编译器与核心工具 {#二编译器与核心工具}

| 工具 | 官方文档 | 项目文档 | 覆盖主题 |
|------|----------|----------|----------|
| rustc | [Compiler Docs](https://doc.rust-lang.org/rustc/) | [37_rustc_dev_guide_alignment.md](37_rustc_dev_guide_alignment.md) | 编译器选项、lint、target |
| rustup | [rustup book](https://rust-lang.github.io/rustup/) | [docs/09_toolchain/README.md](../../09_toolchain/README.md) | 工具链安装、切换、target |
| cargo | [Cargo Book](https://doc.rust-lang.org/cargo/) | [15_cargo_book_alignment.md](15_cargo_book_alignment.md) | 构建、依赖、workspace、features |

---

## 三、构建与包管理 {#三构建与包管理}

| 主题 | 官方来源 | 项目文档 | 备注 |
|------|----------|----------|------|
| Cargo.toml 配置 | [Cargo Book](https://doc.rust-lang.org/cargo/reference/manifest.html) | [15_cargo_book_alignment.md](15_cargo_book_alignment.md) | package、dependencies、profile |
| Workspace | [Cargo Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [crates/common/README.md](../../crates/common/README.md) | 多 crate 管理 |
| Features | [Cargo Features](https://doc.rust-lang.org/cargo/reference/features.html) | [10_cargo_194_features.md](10_cargo_194_features.md) | 条件编译、依赖组合 |
| Resolver v3 | [Resolver](https://doc.rust-lang.org/cargo/reference/resolver.html) | [examples/resolver_v3_practice/](../../examples/resolver_v3_practice/README.md) | 依赖解析 |
| Cargo script | [Cargo Scripts](https://doc.rust-lang.org/cargo/reference/unstable.html#script) | [examples/cargo_script_demo.rs](../../examples/cargo_script_demo.rs) | 单文件脚本 |

---

## 四、代码质量工具 {#四代码质量工具}

| 工具 | 官方/社区来源 | 项目文档 | 覆盖主题 |
|------|---------------|----------|----------|
| clippy | [Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html) | [.clippy.toml](../../.clippy.toml) | lint、性能、风格 |
| rustfmt | [rustfmt](https://github.com/rust-lang/rustfmt) | [Cargo.toml](../../Cargo.toml) | 代码格式化 |
| rustdoc | [rustdoc book](https://doc.rust-lang.org/rustdoc/) | [docs/09_toolchain/02_rustdoc_advanced.md](../../09_toolchain/02_rustdoc_advanced.md) | 文档、doctests |
| cargo test | [Cargo Tests](https://doc.rust-lang.org/cargo/commands/cargo-test.html) | [exercises/tests/](../../exercises/tests) | 单元/集成测试 |
| cargo bench | [Cargo Benchmarks](https://doc.rust-lang.org/cargo/commands/cargo-bench.html) | [../09_experiments/02_concurrency_performance.md](../09_experiments/02_concurrency_performance.md) | 基准测试 |

---

## 五、IDE 与编辑器 {#五ide-与编辑器}

| 工具 | 官方来源 | 项目文档 | 覆盖主题 |
|------|----------|----------|----------|
| rust-analyzer | [Manual](https://rust-analyzer.github.io/manual.html) | [.vscode/settings.json](../../.vscode/settings.json) | LSP、跳转、重构 |
| VS Code Rust 扩展 | [Marketplace](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer) | [.vscode/README.md](../../.vscode/README.md) | 编辑器配置 |

---

## 六、文档与发布 {#六文档与发布}

| 主题 | 官方来源 | 项目文档 | 备注 |
|------|----------|----------|------|
| rustdoc | [rustdoc book](https://doc.rust-lang.org/rustdoc/) | [docs/09_toolchain/02_rustdoc_advanced.md](../../09_toolchain/02_rustdoc_advanced.md) | 文档生成 |
| cargo doc | [Cargo Doc](https://doc.rust-lang.org/cargo/commands/cargo-doc.html) | [docs/09_toolchain/README.md](../../09_toolchain/README.md) | 生成 crate 文档 |
| cargo publish | [Publishing](https://doc.rust-lang.org/cargo/reference/publishing.html) | [15_cargo_book_alignment.md](15_cargo_book_alignment.md) | 发布到 crates.io |
| SemVer | [SemVer](https://semver.org/) | [17_community_best_practices_alignment.md](17_community_best_practices_alignment.md) | 版本兼容 |

---

## 七、交叉编译与目标平台 {#七交叉编译与目标平台}

| 主题 | 官方来源 | 项目文档 | 备注 |
|------|----------|----------|------|
| target triple | [Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html) | [docs/09_toolchain/README.md](../../09_toolchain/README.md) | 目标平台 |
| cross | [cross-rs](https://github.com/cross-rs/cross) | [crates/c13_embedded/README.md](../../crates/c13_embedded/README.md) | 交叉编译 |
| wasm32 | [wasm-bindgen](https://rustwasm.github.io/docs/wasm-bindgen/) | [crates/c12_wasm/README.md](../../crates/c12_wasm/README.md) | WebAssembly |

---

## 八、与项目文档的映射 {#八与项目文档的映射}

| 项目文档 | 覆盖工具链主题 | 权威来源 |
|----------|----------------|----------|
| [15_cargo_book_alignment.md](15_cargo_book_alignment.md) | Cargo 全生态 | Cargo Book |
| [37_rustc_dev_guide_alignment.md](37_rustc_dev_guide_alignment.md) | rustc 内部 | rustc-dev-guide |
| [docs/09_toolchain/README.md](../../09_toolchain/README.md) | 工具链综合 | rustup、rustc、rustdoc |
| [../10_tutorials_and_guides/16_tools_guide.md](../10_tutorials_and_guides/16_tools_guide.md) | 常用工具速查 | 官方文档 |
| [.clippy.toml](../../.clippy.toml) | Clippy 配置 | Clippy Lints |

---

## 九、未覆盖缺口 {#九未覆盖缺口}

1. `cargo-hack`、`cargo-minimal-versions` 等高级 CI 工具可补充。
2. `sccache`、`cranelift` 后端等编译加速工具可扩展。
3. 各 crate 的 MSRV 与工具链版本兼容矩阵可细化。

> **权威来源**: [Rustc Book](https://doc.rust-lang.org/rustc/) | [Cargo Book](https://doc.rust-lang.org/cargo/) | [rustup](https://rust-lang.github.io/rustup/) | [rustdoc](https://doc.rust-lang.org/rustdoc/) | [rust-analyzer](https://rust-analyzer.github.io/manual.html) | [Clippy](https://rust-lang.github.io/rust-clippy/master/index.html) | [rustfmt](https://github.com/rust-lang/rustfmt)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Cargo Book 对齐](15_cargo_book_alignment.md)
- [rustc-dev-guide 对齐](37_rustc_dev_guide_alignment.md)
- [工具使用指南](../10_tutorials_and_guides/16_tools_guide.md)
- [知识图谱索引](../06_concept_models/13_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneasverif.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
