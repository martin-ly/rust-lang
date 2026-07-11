# Cargo Manifest 目标与元数据（Cargo Manifest Targets）

> **内容分级**: [参考级]
> **本节关键术语**: Cargo Target · Lib Target · Bin Target · Test Target · Example Target · Bench Target · Rust Version · Package ID Specification — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Manifest Targets
> **Summary**: Cargo `Cargo.toml` target definitions for Rust 1.97.0+: lib, bin, test, example, bench targets, `rust-version`, Package ID Specifications, and per-target configuration.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 补充 `64_cargo_manifest_reference.md` 未涉及的 target、rust-version、pkgid 等子主题。
> **前置概念**: [Cargo Manifest Reference](64_cargo_manifest_reference.md) · [Cargo Workflow](81_cargo_workflow.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Cargo Build Scripts](59_cargo_build_scripts.md)

---

> **来源**: [Cargo Book — The Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) · [Cargo Book — Cargo Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) · [Cargo Book — Rust Version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) · [Cargo Book — Package ID Specifications](https://doc.rust-lang.org/cargo/reference/pkgid-spec.html)

---

## 一、Cargo Target 类型

一个 package 可包含以下 target：

| Target | 默认入口 | 说明 |
|:---|:---|:---|
| lib | `src/lib.rs` | 库，可被其他 crate 依赖 |
| bin | `src/main.rs` | 可执行文件 |
| bin (多个) | `src/bin/*.rs` | 额外可执行文件 |
| example | `examples/*.rs` | 示例 |
| test | `tests/*.rs` | 集成测试 |
| bench | `benches/*.rs` | 基准测试 |

## 二、自动发现 vs 显式声明

Cargo 默认按约定路径自动发现 target。当需要覆盖默认路径、名称或配置时，使用显式声明：

```toml
[[bin]]
name = "server"
path = "src/server.rs"

[[test]]
name = "integration"
path = "tests/integration/main.rs"

[[example]]
name = "demo"
required-features = ["serde"]
```

显式声明可覆盖默认路径和名称，也可禁用自动发现：

```toml
[package]
autobins = false
autoexamples = false
autotests = false
autobenches = false
```

## 三、`rust-version` 字段

```toml
[package]
name = "my-crate"
version = "0.1.0"
edition = "2024"
rust-version = "1.96"
```

- 声明 package 所需的最低 Rust 版本。
- Cargo 会在工具链版本过低时给出明确错误。
- resolver v3 会利用 `rust-version` 进行 MSRV-aware 版本选择。

## 四、Package ID Specification

Cargo 使用 Package ID Spec 唯一标识依赖图中的 package：

```text
name
name@version
name@version:source_url
```

用途：

- `cargo update -p <spec>`
- `cargo tree -p <spec>`
- `cargo metadata --format-version 1 | jq '.packages[] | .id'`

示例：

```bash
cargo tree -p serde@1.0.217
cargo update -p tokio --precise 1.42.0
```

## 五、Target 配置项

常见 target 级配置：

| 字段 | 说明 |
|:---|:---|
| `name` | target 名称 |
| `path` | 源文件路径 |
| `test` | 是否作为测试编译 |
| `bench` | 是否作为 benchmark 编译 |
| `doc` | 是否包含在文档中 |
| `edition` | 该 target 使用的 edition |
| `crate-type` | lib 的 crate 类型 |
| `required-features` | 构建前必须启用的 features |

## 六、Lib 的 `crate-type`

```toml
[lib]
name = "mylib"
crate-type = ["cdylib", "staticlib", "rlib"]
```

| 类型 | 用途 |
|:---|:---|
| `lib` / `rlib` | Rust 静态库（默认） |
| `dylib` | Rust 动态库 |
| `cdylib` | C 兼容动态库 |
| `staticlib` | C 兼容静态库 |
| `proc-macro` | 过程宏（Procedural Macro） |

## 七、`required-features` 示例

```toml
[features]
default = []
serde = ["dep:serde"]

[[bin]]
name = "cli-with-serde"
path = "src/cli_with_serde.rs"
required-features = ["serde"]
```

未启用 `serde` 时，`cargo build` 不会编译该 binary target。

## 八、Target 选择决策表

| 需求 | 推荐 Target |
|:---|:---|
| 提供可复用 Rust API | `src/lib.rs`（lib） |
| 提供 CLI 入口 | `src/main.rs`（bin） |
| 多个 CLI 工具 | `src/bin/*.rs`（multi-bin） |
| 演示库用法 | `examples/*.rs` |
| 集成测试 | `tests/*.rs` |
| 性能基准 | `benches/*.rs` |
| 暴露给 C/Python | `[lib] crate-type = ["cdylib"]` |

## 九、与 Workspace 的关联

在 workspace 中，target 输出目录统一在 workspace root 的 `target/` 下，但每个 member 仍独立声明自己的 target。Workspace root 的 `[profile]` 与 `[workspace.lints]` 会影响所有成员 target。

详见 [Cargo Workspaces](78_cargo_workspaces.md) 与 [Cargo Build Scripts](59_cargo_build_scripts.md)。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

> **权威来源**: [Cargo Book — Cargo Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/semver — 生态权威 API 文档](https://docs.rs/semver) · [docs.rs/toml — 生态权威 API 文档](https://docs.rs/toml)
- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
