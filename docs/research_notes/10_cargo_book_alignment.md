# Cargo Book 对齐矩阵 {#cargo-book-对齐矩阵}

> **EN**: Cargo Book Alignment
> **Summary**: Cargo Book 对齐矩阵 Cargo Book Alignment.
> **概念族**: 权威来源对齐 / Cargo Book
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Cargo Book 对齐矩阵 {#cargo-book-对齐矩阵}](#cargo-book-对齐矩阵-cargo-book-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、Package 与项目结构 {#二package-与项目结构}](#二package-与项目结构-二package-与项目结构)
  - [三、依赖管理 {#三依赖管理}](#三依赖管理-三依赖管理)
  - [四、Workspace {#四workspace}](#四workspace-四workspace)
  - [五、Features {#五features}](#五features-五features)
  - [六、Build 脚本与配置 {#六build-脚本与配置}](#六build-脚本与配置-六build-脚本与配置)
  - [七、发布与注册 {#七发布与注册}](#七发布与注册-七发布与注册)
  - [八、高级配置 {#八高级配置}](#八高级配置-八高级配置)
  - [九、未覆盖缺口 {#九未覆盖缺口}](#九未覆盖缺口-九未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中关于 crate、模块、workspace、依赖、发布的内容与 [Cargo Book](https://doc.rust-lang.org/cargo/) 建立映射。

---

## 二、Package 与项目结构 {#二package-与项目结构}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Cargo.toml](https://doc.rust-lang.org/cargo/reference/manifest.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | ✅ | package、edition、rust-version |
| [Package Layout](https://doc.rust-lang.org/cargo/guide/project-layout.html) | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | ✅ | src/lib.rs、src/main.rs |
| [Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6 | ✅ | lib/bin/example/test |
| [Crate-types](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6 | ✅ | rlib/cdylib/staticlib |

---

## 三、依赖管理 {#三依赖管理}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §6 | ✅ | 版本统一 |
| [SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | SemVer 规则 |
| [Resolver](https://doc.rust-lang.org/cargo/reference/resolver.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §6 | 🔄 | resolver v3 待专门说明 |

---

## 四、Workspace {#四workspace}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §5 | ✅ | workspace 配置 |
| [Workspace Dependencies](https://doc.rust-lang.org/cargo/reference/workspaces.html#the-dependencies-table) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §5 | ✅ | workspace.dependencies |

---

## 五、Features {#五features}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Features](https://doc.rust-lang.org/cargo/reference/features.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ | feature flag 组合 |
| [The Features 2.0 Resolver](https://doc.rust-lang.org/cargo/reference/features.html#feature-resolver-version-2) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | ✅ | resolver v2/v3 |

---

## 六、Build 脚本与配置 {#六build-脚本与配置}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Build Scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html) | [examples/build_script_practice/](../../examples/build_script_practice/README.md) | ✅ | build.rs 示例 |
| [Config](https://doc.rust-lang.org/cargo/reference/config.html) | [10_authoritative_alignment_guide.md](10_authoritative_alignment_guide.md) | 🔄 | .cargo/config.toml |

---

## 七、发布与注册 {#七发布与注册}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Publishing](https://doc.rust-lang.org/cargo/reference/publishing.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | SemVer 与发布 |
| [cargo publish](https://doc.rust-lang.org/cargo/commands/cargo-publish.html) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 | ✅ | 发布流程 |

---

## 八、高级配置 {#八高级配置}

| Cargo Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html) | [Cargo.toml](../../Cargo.toml) | ✅ | dev/release 配置示例 |
| [Lints](https://doc.rust-lang.org/cargo/reference/lints.html) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §2 | 🔄 | lint 配置随版本变化 |

---

## 九、未覆盖缺口 {#九未覆盖缺口}

1. `cargo-vendor` / 离线构建流程未专门展开。
2. `cargo tree` 与依赖审计可单独成文。
3. `cargo metadata` 在工具链集成中的应用待补充。

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [模块系统代码实践](formal_modules/70_module_patterns_and_refactoring.md)
- [Crate 架构反例](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md)
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
