# Cargo Manifest 目标与元数据（Cargo Manifest Targets）

> **内容分级**: [参考级]
> **本节关键术语**: Cargo Target · Lib Target · Bin Target · Test Target · Example Target · Bench Target · Rust Version · Package ID Specification — [完整对照表](../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Manifest Targets
> **Summary**: Cargo `Cargo.toml` 中的 target 定义：lib、bin、test、example、bench，以及 `rust-version`、`package` 元数据和 Package ID Specification。
> **受众**: [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 补充 `64_cargo_manifest_reference.md` 未涉及的 target、rust-version、pkgid 等子主题。
> **前置概念**: [Cargo Manifest Reference](64_cargo_manifest_reference.md) · [Cargo Workflow](81_cargo_workflow.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Cargo Build Scripts](59_cargo_build_scripts.md)

---

> **来源**: [Cargo Book — The Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Cargo Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) ·
> [Cargo Book — Rust Version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) ·
> [Cargo Book — Package ID Specifications](https://doc.rust-lang.org/cargo/reference/pkgid-spec.html)

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

## 二、显式声明 Target

```toml
[[bin]]
name = "server"
path = "src/server.rs"

[[test]]
name = "integration"
path = "tests/integration/main.rs"
```

显式声明可覆盖默认路径和名称。

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
- 不影响依赖解析，仅作为元数据与编译前置检查。

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
| `crate-type` | lib 的 crate 类型：`lib`, `bin`, `cdylib`, `staticlib`, `rlib` 等 |

---

> **权威来源**: [Cargo Book — Cargo Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html)
> **内容分级**: [参考级]
