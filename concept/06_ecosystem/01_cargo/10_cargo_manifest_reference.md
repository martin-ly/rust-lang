> **内容分级**: [参考级]
> **本节关键术语**: Manifest · `Cargo.toml` · `[package]` · `[dependencies]` · `[features]` · `[profile]` · `[workspace]` · `[lints]` · `[patch]` — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
# Cargo Manifest 参考速查

> **EN**: Cargo Manifest Reference
> **Summary**: A comprehensive but concise reference of `Cargo.toml` sections and fields, aligned with the Cargo Book Manifest Format.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [中级 → 高级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把 `Cargo.toml` 的核心字段按用途整理成可速查的参考表，方便快速查阅而非从头阅读。
> **前置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **后置概念**: [Cargo Profiles and Lints](11_cargo_profiles_and_lints.md) · [Cargo Source Replacement](07_cargo_source_replacement.md)

---

> **来源**: [Cargo — Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) ·
> [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)

---

## 📑 目录

- [Cargo Manifest 参考速查](#cargo-manifest-参考速查)
  - [📑 目录](#-目录)
  - [一、`[package]` 元数据](#一package-元数据)
  - [二、Target 表](#二target-表)
  - [三、依赖表](#三依赖表)
  - [四、`[features]`](#四features)
  - [五、`[workspace]`](#五workspace)
  - [六、`[profile.*]`](#六profile)
  - [七、`[lints]` 与 `[hints]`](#七lints-与-hints)
    - [`[lints]`](#lints)
    - [`[hints]`](#hints)
  - [八、覆盖与替换](#八覆盖与替换)
  - [九、其他表](#九其他表)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：发布到 crates.io 时，`license` 和 `license-file` 至少需要一个吗？](#测验-1发布到-cratesio-时license-和-license-file-至少需要一个吗)
    - [测验 2：`[dev-dependencies]` 在什么场景下使用？](#测验-2dev-dependencies-在什么场景下使用)
    - [测验 3：`[patch]` 与 `[source]` 的主要区别是什么？](#测验-3patch-与-source-的主要区别是什么)
    - [测验 4：`workspace.lints` 会自动被成员包继承吗？](#测验-4workspacelints-会自动被成员包继承吗)
  - [权威来源索引](#权威来源索引)

---

## 一、`[package]` 元数据

| 字段 | 必需 | 说明 |
|:---|:---:|:---|
| `name` | ✅ | 包名（crate 名），crates.io 限制 ASCII、64 字符 |
| `version` | 发布时 | SemVer，如 `1.2.3`；无则默认 `0.0.0` |
| `edition` | ❌ | Rust Edition，`2015`/`2018`/`2021`/`2024`；默认 `2015` |
| `rust-version` | ❌ | MSRV，如 `"1.97.0"` |
| `authors` | ❌ | 已废弃，但兼容 |
| `description` | 发布 crates.io | 纯文本简介 |
| `documentation` | ❌ | 文档 URL；未设置则自动指向 docs.rs |
| `readme` | ❌ | README 路径；`true`/`false` 控制自动探测 |
| `homepage` | ❌ | 主页；不要与 repository/documentation 重复 |
| `repository` | ❌ | 源码仓库 URL |
| `license` / `license-file` | 发布时 | SPDX 表达式或自定义许可证文件 |
| `keywords` | ❌ | crates.io 最多 5 个 |
| `categories` | ❌ | crates.io 预定义分类，最多 5 个 |
| `build` | ❌ | build script 路径，默认 `build.rs`；`false` 禁用 |
| `links` | ❌ | 链接的原生库名，如 `"git2"` |
| `exclude` / `include` | ❌ | 打包时排除/包含规则，gitignore 语法 |
| `publish` | ❌ | `false` 或 registry 白名单，防止误发布 |
| `metadata` | ❌ | 外部工具使用的自定义元数据 |
| `default-run` | ❌ | `cargo run` 默认二进制 |
| `resolver` | ❌ | `1`/`2`/`3`；工作区通常在根设置 |

```toml
[package]
name = "my-crate"
version = "0.1.0"
edition = "2024"
rust-version = "1.97.0"
description = "A short description"
license = "MIT OR Apache-2.0"
repository = "https://github.com/you/my-crate"
```

> 来源: [The Cargo Book](https://doc.rust-lang.org/cargo/index.html)` section](<https://doc.rust-lang.org/cargo/reference/manifest.html#the-package-section>)

---

## 二、Target 表

| 表 | 说明 | 示例 |
|:---|:---|:---|
| `[lib]` | 库目标 | `name = "my_crate"`, `path = "src/lib.rs"` |
| `[[bin]]` | 二进制目标 | `name = "cli"`, `path = "src/main.rs"` |
| `[[example]]` | 示例 | `name = "demo"`, `path = "examples/demo.rs"` |
| `[[test]]` | 集成测试 | `name = "integration"`, `path = "tests/integration.rs"` |
| `[[bench]]` | 基准测试 | `name = "bench_foo"`, `path = "benches/bench_foo.rs"` |

公共 target 配置：`name`、`path`、`test`、`edition`、`required-features`、`crate-type` 等。

---

## 三、依赖表

| 表 | 用途 |
|:---|:---|
| `[dependencies]` | 运行时（Runtime）依赖 |
| `[dev-dependencies]` | 测试/示例/基准依赖 |
| `[build-dependencies]` | build.rs 依赖 |
| `[target.'cfg(unix)'.dependencies]` | 平台特定依赖 |
| `[target.x86_64-pc-windows-msvc.dependencies]` | 特定 target 依赖 |

版本要求写法：

| 写法 | 含义 |
|:---|:---|
| `"1.2.3"` | `^1.2.3` |
| `"=1.2.3"` | 精确 |
| `"~1.2.3"` | `1.2.x` |
| `">=1.2, <2.0"` | 自定义范围 |

依赖的高级形式：

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { git = "https://github.com/tokio-rs/tokio", branch = "main" }
local = { path = "../local" }
private = { version = "1.0", registry = "my-registry" }
```

---

## 四、`[features]`

```toml
[features]
default = ["std"]
std = []
serde = ["dep:serde", "bitflags/serde"]
```

- `default` 在没有 `--no-default-features` 时自动启用；
- `feature = ["dep:crate"]` 用于启用可选依赖；
- 可使用 `?` 弱依赖：`["dep:serde", "tokio?/rt"]`。

---

## 五、`[workspace]`

工作区根 `Cargo.toml`：

```toml
[workspace]
members = ["crates/*", "tools/*"]
resolver = "3"

[workspace.package]
edition = "2024"
version = "0.1.0"

[workspace.dependencies]
serde = "1.0.217"
```

成员包继承：

```toml
[package]
name = "foo"
version.workspace = true
edition.workspace = true

[dependencies]
serde = { workspace = true }
```

---

## 六、`[profile.*]`

```toml
[profile.release]
opt-level = 3
lto = "thin"
strip = "symbols"

[profile.dev.package."*"]
opt-level = 2
```

常用设置：`opt-level`、`debug`、`lto`、`panic`、`incremental`、`codegen-units`、`overflow-checks`、`debug-assertions`、`strip`。

> 详见 [Cargo Profiles and Lints](11_cargo_profiles_and_lints.md)。

---

## 七、`[lints]` 与 `[hints]`

「`[lints]` 与 `[hints]`」部分包含 `[lints]` 与  `[hints]` 两条主线，本节依次说明。

### `[lints]`

```toml
[lints.rust]
unsafe_code = "forbid"

[lints.clippy]
enum_glob_use = "deny"
```

- 影响当前包，不影响依赖；
- 工作区可定义 `workspace.lints`，成员继承需 `lints.workspace = true`。

### `[hints]`

```toml
[hints]
# 目前尚无稳定 hint
```

> 注意：Cargo lints 目前仍需每日构建版工具链。

---

## 八、覆盖与替换

| 机制 | 表 | 用途 |
|:---|:---|:---|
| 依赖覆盖 | `[patch]` | 临时替换某个依赖 |
| 源替换 | `[source]` | 镜像/vendoring |
| 已废弃 | `[replace]` | 用 `patch` 替代 |

```toml
[patch.crates-io]
serde = { path = "../serde-fix" }
```

---

## 九、其他表

| 表 | 说明 |
|:---|:---|
| `[badges]` | 已废弃，crates.io 不再显示 |
| `[package.metadata.*]` | 外部工具自定义数据，Cargo 忽略 |
| `[workspace.metadata.*]` | 工作区级外部工具数据 |

---

## 嵌入式测验

本节将「嵌入式测验」分解为若干主题：测验 1：发布到 crates.io 时，`license` 和 `l…、测验 2：`[dev-dependencies]` 在什么场景下使用？、测验 3：`[patch]` 与 `[source]` 的主要区别是什…与测验 4：`workspace.lints` 会自动被成员包继承吗？。

### 测验 1：发布到 crates.io 时，`license` 和 `license-file` 至少需要一个吗？

<details>
<summary>✅ 答案与解析</summary>

是的。crates.io 要求提供 `license` 或 `license-file` 之一。

</details>

---

### 测验 2：`[dev-dependencies]` 在什么场景下使用？

<details>
<summary>✅ 答案与解析</summary>

用于测试、示例和基准测试，不会成为发布 crate 的运行时（Runtime）依赖。

</details>

---

### 测验 3：`[patch]` 与 `[source]` 的主要区别是什么？

<details>
<summary>✅ 答案与解析</summary>

`[patch]` 临时替换具体依赖；`[source]` 整体替换下载源（如镜像或 vendoring），不改变 crate 身份。

</details>

---

### 测验 4：`workspace.lints` 会自动被成员包继承吗？

<details>
<summary>✅ 答案与解析</summary>

不会。成员包必须显式写 `[lints] workspace = true` 才能继承工作区 lint 配置。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Cargo Book — The Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) | ✅ 一级 | Manifest 官方参考 |
| [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | ✅ 一级 | Workspace 官方参考 |
| [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | ✅ 一级 | 依赖语法官方参考 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/index.html)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.97.0 / Cargo manifest format

**文档版本**: 1.0
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Cargo Book manifest 参考文档
