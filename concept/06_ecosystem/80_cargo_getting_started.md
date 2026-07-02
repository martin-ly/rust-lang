# Cargo 入门（Cargo Getting Started）

> **内容分级**: [参考级]
> **本节关键术语**: Cargo · Crate · Package · Manifest · `Cargo.toml` — [完整对照表](../00_meta/terminology_glossary.md)
>
> **EN**: Cargo Getting Started
> **Summary**: Cargo 的定位与入门：安装验证、`cargo new` 创建 package、构建运行、依赖管理基础，以及 Cargo 在 Rust 工具链中的角色。
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 让初学者在 5 分钟内理解 Cargo 是什么、能做什么、如何创建并运行第一个 Rust package。
> **前置概念**: [Toolchain](01_toolchain.md) · [Rust Installation](../00_meta/learning_mvp_path.md)
> **后置概念**: [Cargo Workflow](81_cargo_workflow.md) · [Cargo Dependency Resolution](60_cargo_dependency_resolution.md) · [Cargo Manifest Reference](64_cargo_manifest_reference.md)

---

> **来源**: [Cargo Book — Getting Started](https://doc.rust-lang.org/cargo/getting-started/index.html) ·
> [Cargo Book — First Steps with Cargo](https://doc.rust-lang.org/cargo/getting-started/first-steps.html) ·
> [Cargo Book — Why Cargo Exists](https://doc.rust-lang.org/cargo/why-cargo-exists.html)

---

## 一、Cargo 是什么

**Cargo** 是 Rust 的官方构建系统、包管理器和项目编排工具。它与 `rustc` 一起随 Rust 工具链发布，负责：

| 职责 | 说明 |
|:---|:---|
| 构建 | 调用 `rustc` 编译 package 及其依赖 |
| 依赖管理 | 从 crates.io 或其他 registry 下载并解析依赖 |
| 项目脚手架 | 通过 `cargo new`/`cargo init` 创建标准项目结构 |
| 测试与文档 | `cargo test`、`cargo doc`、`cargo bench` |
| 发布 | `cargo publish` 将 package 发布到 crates.io |

## 二、为什么需要 Cargo

Rust 项目通常由多个 crate 和大量依赖组成。手工调用 `rustc` 管理依赖、feature、版本极其复杂。Cargo 提供声明式配置（`Cargo.toml`）和统一工作流，使项目可复现、可协作、可扩展。

## 三、创建第一个 Package

```bash
cargo new hello_cargo --bin
cd hello_cargo
cargo run
```

生成的标准结构：

```text
hello_cargo/
├── Cargo.toml
├── Cargo.lock
└── src/
    └── main.rs
```

## 四、核心命令速览

| 命令 | 作用 |
|:---|:---|
| `cargo build` | 编译当前 package |
| `cargo run` | 编译并运行 |
| `cargo check` | 快速检查语法/类型，不生成二进制 |
| `cargo test` | 运行测试 |
| `cargo doc` | 生成 rustdoc 文档 |
| `cargo add <crate>` | 添加依赖 |

## 五、Cargo.toml 初识

```toml
[package]
name = "hello_cargo"
version = "0.1.0"
edition = "2024"

[dependencies]
```

- `[package]` 描述当前 package 元数据。
- `[dependencies]` 声明外部依赖。
- `edition` 指定 Rust 语言版本（2024、2021、2018 等）。

---

> **权威来源**: [Cargo Book — Getting Started](https://doc.rust-lang.org/cargo/getting-started/index.html)
> **内容分级**: [参考级]
