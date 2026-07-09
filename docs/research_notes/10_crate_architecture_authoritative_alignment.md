# Crate 架构权威来源对齐矩阵 {#crate-架构权威来源对齐矩阵}

> **EN**: Crate Architecture Authoritative Alignment
> **Summary**: Crate 架构权威来源对齐矩阵 Crate Architecture Authoritative Alignment.
> **概念族**: 权威来源对齐 / Crate 架构
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Crate 架构权威来源对齐矩阵 {#crate-架构权威来源对齐矩阵}](#crate-架构权威来源对齐矩阵-crate-架构权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、P0 官方来源对齐 {#二p0-官方来源对齐}](#二p0-官方来源对齐-二p0-官方来源对齐)
    - [2.1 Cargo Book {#21-cargo-book}](#21-cargo-book-21-cargo-book)
    - [2.2 Rust Reference – Items and Crates {#22-rust-reference-items-and-crates}](#22-rust-reference--items-and-crates-22-rust-reference-items-and-crates)
    - [2.3 Rust API Guidelines {#23-rust-api-guidelines}](#23-rust-api-guidelines-23-rust-api-guidelines)
  - [三、P2 社区来源对齐 {#三p2-社区来源对齐}](#三p2-社区来源对齐-三p2-社区来源对齐)
    - [3.1 Rust Design Patterns {#31-rust-design-patterns}](#31-rust-design-patterns-31-rust-design-patterns)
    - [3.2 Rust Modules Guide {#32-rust-modules-guide}](#32-rust-modules-guide-32-rust-modules-guide)
    - [3.3 SemVer 与 cargo book 实战 {#33-semver-与-cargo-book-实战}](#33-semver-与-cargo-book-实战-33-semver-与-cargo-book-实战)
    - [3.4 crates.io 政策 {#34-cratesio-政策}](#34-cratesio-政策-34-cratesio-政策)
  - [四、Crate 架构主题覆盖 {#四crate-架构主题覆盖}](#四crate-架构主题覆盖-四crate-架构主题覆盖)
    - [4.1 Workspace 组织 {#41-workspace-组织}](#41-workspace-组织-41-workspace-组织)
    - [4.2 Public / Private API {#42-public-private-api}](#42-public--private-api-42-public-private-api)
    - [4.3 Feature 设计 {#43-feature-设计}](#43-feature-设计-43-feature-设计)
    - [4.4 错误类型 {#44-错误类型}](#44-错误类型-44-错误类型)
    - [4.5 日志与 Tracing {#45-日志与-tracing}](#45-日志与-tracing-45-日志与-tracing)
    - [4.6 配置管理 {#46-配置管理}](#46-配置管理-46-配置管理)
    - [4.7 CLI 设计 {#47-cli-设计}](#47-cli-设计-47-cli-设计)
    - [4.8 库 vs 二进制 {#48-库-vs-二进制}](#48-库-vs-二进制-48-库-vs-二进制)
    - [4.9 MSRV 策略 {#49-msrv-策略}](#49-msrv-策略-49-msrv-策略)
  - [五、项目文档映射 {#五项目文档映射}](#五项目文档映射-五项目文档映射)
  - [六、未覆盖缺口 {#六未覆盖缺口}](#六未覆盖缺口-六未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中关于 **Crate 架构** 的内容与 P0 官方、P2 社区权威来源建立映射，覆盖 workspace 组织、公开/私有 API 边界、feature 设计、错误处理（Error Handling）、日志、配置、CLI、库/二进制拆分、MSRV 策略等关键工程主题。目标是为项目中的 crate 架构决策提供可追溯的权威依据。

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [crates.io policies](https://crates.io/policies)

---

## 二、P0 官方来源对齐 {#二p0-官方来源对齐}

### 2.1 Cargo Book {#21-cargo-book}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §6 | ✅ | workspace 组织与依赖统一 |
| [Features](https://doc.rust-lang.org/cargo/reference/features.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ | feature flag 正交设计 |
| [The crate-type field](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) §3 | ✅ | lib / bin / cdylib / staticlib |
| [SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 公开 API 变更与版本升级 |
| [Publishing](https://doc.rust-lang.org/cargo/reference/publishing.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | `cargo publish` 与 API 稳定性 |
| [rust-version field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | ✅ | MSRV 声明机制 |
| [Config Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html) | [Cargo.toml](../../Cargo.toml) | ✅ | dev/release 优化配置 |

### 2.2 Rust Reference – Items and Crates {#22-rust-reference-items-and-crates}

| Rust Reference 章节 | 项目文档 | 状态 | 备注 |
|---------------------|----------|------|------|
| [Items](https://doc.rust-lang.org/reference/items.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §2 | ✅ | 模块（Module）、函数、类型、trait 等条目 |
| [Crates and source files](https://doc.rust-lang.org/reference/crates-and-source-files.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §1 | ✅ | crate root、edition、module tree |
| [Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §4 | ✅ | `pub`、`pub(crate)`、`pub(in path)` |
| [Use declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §4 | ✅ | 重导出与 API 塑形 |

### 2.3 Rust API Guidelines {#23-rust-api-guidelines}

| API Guidelines 章节 | 项目文档 | 状态 | 备注 |
|---------------------|----------|------|------|
| [Naming](https://rust-lang.github.io/api-guidelines/naming.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 公开 API 命名与 SemVer |
| [Future-proofing](https://rust-lang.github.io/api-guidelines/future-proofing.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §3 | ✅ | Sealed trait / 非公开 trait |
| [Type Safety](https://rust-lang.github.io/api-guidelines/type-safety.html) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §四 | ✅ | 类型状态、Builder |
| [Documentation](https://rust-lang.github.io/api-guidelines/documentation.html) | [10_code_doc_formal_mapping.md](10_code_doc_formal_mapping.md) | ✅ | 公开 API 文档要求 |
| [Versioning](https://rust-lang.github.io/api-guidelines/naming.html#c-semver) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 语义化版本 |

---

## 三、P2 社区来源对齐 {#三p2-社区来源对齐}

### 3.1 Rust Design Patterns {#31-rust-design-patterns}

| Design Patterns 章节 | 项目文档 | 状态 | 备注 |
|----------------------|----------|------|------|
| [Idioms](https://rust-unofficial.github.io/patterns/idioms/index.html) | [software_design_theory/06_rust_idioms.md](software_design_theory/06_rust_idioms.md) | ✅ | RAII、Newtype、类型状态 |
| [Anti-patterns](https://rust-unofficial.github.io/patterns/anti_patterns/index.html) | [software_design_theory/07_anti_patterns.md](software_design_theory/07_anti_patterns.md) | ✅ | 过度工程、全局可变状态 |
| [Builder](https://rust-unofficial.github.io/patterns/patterns/creational/builder.html) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §四 | ✅ | Clap / Reqwest 风格 Builder |
| [Strategy](https://rust-unofficial.github.io/patterns/patterns/behavioural/strategy.html) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §四 | ✅ | Wgpu / Tower 后端抽象 |

### 3.2 Rust Modules Guide {#32-rust-modules-guide}

| 来源 | 项目文档 | 状态 | 备注 |
|------|----------|------|------|
| [Rust Modules Guide](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | ✅ | 模块分层、职责划分 |
| [Cargo Guide – Project Layout](https://doc.rust-lang.org/cargo/guide/project-layout.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §2 | ✅ | package 目录结构 |

### 3.3 SemVer 与 cargo book 实战 {#33-semver-与-cargo-book-实战}

| 来源 | 项目文档 | 状态 | 备注 |
|------|----------|------|------|
| [SemVer for Rust](https://doc.rust-lang.org/cargo/reference/semver.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 破坏性变更判定 |
| [cargo-public-api](https://github.com/EmbarkStudios/cargo-public-api) 实战 | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | API 变化检测 |
| [cargo-hack](https://github.com/taiki-e/cargo-hack) 实战 | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ | feature 组合测试 |

### 3.4 crates.io 政策 {#34-cratesio-政策}

| 来源 | 项目文档 | 状态 | 备注 |
|------|----------|------|------|
| [crates.io Package Policies](https://crates.io/policies) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 命名、 squatting、安全披露 |
| [crates.io Security](https://crates.io/security) | [10_cicd_supply_chain_alignment.md](10_cicd_supply_chain_alignment.md) | ✅ | 供应链安全 |

---

## 四、Crate 架构主题覆盖 {#四crate-架构主题覆盖}

### 4.1 Workspace 组织 {#41-workspace-组织}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| 多 crate 分层 | [Cargo Book – Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §6 | ✅ |
| 统一依赖版本 | [Workspace Dependencies](https://doc.rust-lang.org/cargo/reference/workspaces.html#the-dependencies-table) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §6 | ✅ |
| 循环依赖规避 | [Cargo Book – Resolver](https://doc.rust-lang.org/cargo/reference/resolver.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §1 | ✅ |

### 4.2 Public / Private API {#42-public-private-api}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| 可见性规则 | [Rust Reference – Visibility](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §4 | ✅ |
| Sealed trait | [Rust API Guidelines – Future-proofing](https://rust-lang.github.io/api-guidelines/future-proofing.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §3 | ✅ |
| 内部类型不外泄 | [Rust API Guidelines – Type Safety](https://rust-lang.github.io/api-guidelines/type-safety.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §3 | ✅ |

### 4.3 Feature 设计 {#43-feature-设计}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| Feature 正交化 | [Cargo Book – Features](https://doc.rust-lang.org/cargo/reference/features.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ |
| Feature resolver v2/v3 | [The Features 2.0 Resolver](https://doc.rust-lang.org/cargo/reference/features.html#feature-resolver-version-2) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ |
| 可选依赖 | [Optional Dependencies](https://doc.rust-lang.org/cargo/reference/features.html#optional-dependencies) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §二 | ✅ |

### 4.4 错误类型 {#44-错误类型}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| `std::error::Error` | [Rust Standard Library](https://doc.rust-lang.org/std/error/trait.Error.html) | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) | ✅ |
| thiserror / anyhow | [thiserror docs](https://docs.rs/thiserror) / [anyhow docs](https://docs.rs/anyhow) | [crates/common/README.md](../../crates/common/README.md) | 🔄 |
| 库错误 vs 应用错误 | [Rust API Guidelines – Errors](https://rust-lang.github.io/api-guidelines/interoperability.html#c-fail) | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) | ✅ |

### 4.5 日志与 Tracing {#45-日志与-tracing}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| `log` crate  facade | [Rust Cookbook – Logging](https://rust-lang-nursery.github.io/rust-cookbook/development_tools/debugging/log.html) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §二 | ✅ |
| `tracing` 架构 | [tokio.rs – tracing](https://tokio.rs/tokio/topics/tracing) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §二 | ✅ |
| 结构化日志 | [Tracing – Spans](https://docs.rs/tracing) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §四 | ✅ |

### 4.6 配置管理 {#46-配置管理}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| 环境变量与 `.env` | [Cargo Book – Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) | [crates/common/README.md](../../crates/common/README.md) | 🔄 |
| 配置文件序列化 | [Serde docs](https://serde.rs/) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §二 | ✅ |
| `LazyLock` 全局配置 | [Rust Standard Library](https://doc.rust-lang.org/std/sync/struct.LazyLock.html) | [10_rust_194_research_update.md](10_rust_194_research_update.md) | ✅ |

### 4.7 CLI 设计 {#47-cli-设计}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| Clap Builder / Derive | [Clap docs](https://docs.rs/clap) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §二 | ✅ |
| CLI 12-factor | [Rust CLI Book](https://rust-cli.github.io/book/index.html) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) §六 | ✅ |
| 二进制入口与 lib 共享 | [Cargo Book – Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6 | ✅ |

### 4.8 库 vs 二进制 {#48-库-vs-二进制}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| Package layout | [Cargo Book – Project Layout](https://doc.rust-lang.org/cargo/guide/project-layout.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) §2 | ✅ |
| Crate types | [Cargo Book – crate-type](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field) | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) §3 | ✅ |
| 一个 package 多个 bin | [Cargo Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) | [crates/common/README.md](../../crates/common/README.md) | 🔄 |

### 4.9 MSRV 策略 {#49-msrv-策略}

| 主题 | 权威来源 | 项目文档 | 状态 |
|------|----------|----------|------|
| `rust-version` 字段 | [Cargo Book – rust-version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | ✅ |
| Edition 迁移 | [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/) | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | ✅ |
| MSRV 测试矩阵 | [Cargo Book – Resolver](https://doc.rust-lang.org/cargo/reference/resolver.html) | [crates/integration_tests/README.md](../../crates/integration_tests/README.md) | 🔄 |

---

## 五、项目文档映射 {#五项目文档映射}

| 文档 | 作用 |
|------|------|
| [Crate 架构主索引](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | 21 个工业级 crate 的架构全景、学习路径、设计模式横切分析 |
| [Crate 架构反例边界](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) | 循环依赖、feature 组合爆炸、SemVer 破坏等 7 类边界案例 |
| [crates/common/README.md](../../crates/common/README.md) | 公共代码、错误类型、配置、日志抽象示例 |
| [crates/integration_tests/README.md](../../crates/integration_tests/README.md) | 集成测试、MSRV/版本矩阵实践入口 |
| [Cargo Book 对齐矩阵](10_cargo_book_alignment.md) | Cargo 官方文档与项目内容的总映射 |
| [社区最佳实践对齐矩阵](10_community_best_practices_alignment.md) | API Guidelines、Rust Design Patterns、Performance Book 总映射 |
| [Rust Reference 对齐矩阵](10_rust_reference_alignment.md) | 语言规范 items/modules/visibility 映射 |
| [版本演进对齐矩阵](10_version_evolution_alignment.md) | rust-version、Edition、MSRV 策略映射 |
| [错误处理与网络/Web 生态对齐矩阵](10_error_handling_network_web_alignment.md) | 错误类型与生态 crate 映射 |

---

## 六、未覆盖缺口 {#六未覆盖缺口}

1. **具体 crate 的 workspace 拆分案例**：当前以反例和主索引为主，缺少一个真实 multi-crate workspace 的逐步演进示例。
2. **feature 组合测试自动化**：`cargo-hack` 与 CI 集成的详细脚本未单独成文。
3. **配置管理最佳实践**：环境变量、配置文件、secret 管理的完整决策树待补充。
4. **MSRV 自动检测与 `cargo-msrv` 流程**：未与 CI 流水线建立显式映射。
5. **库/二进制混合 package 的测试策略**：`src/lib.rs` 与 `src/main.rs` 协同测试的示例可细化。
6. **crates.io 发布与 yank/deprecation 流程**：与 SemVer 结合的操作流程待补充。

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [crates.io policies](https://crates.io/policies)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Cargo Book 对齐矩阵](10_cargo_book_alignment.md)
- [社区最佳实践对齐矩阵](10_community_best_practices_alignment.md)
- [Rust Reference 对齐矩阵](10_rust_reference_alignment.md)
- [版本演进对齐矩阵](10_version_evolution_alignment.md)
- [错误处理与网络/Web 生态对齐矩阵](10_error_handling_network_web_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [模块系统代码实践](formal_modules/70_module_patterns_and_refactoring.md)
- [模块系统规范](formal_modules/10_module_system_specification.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
