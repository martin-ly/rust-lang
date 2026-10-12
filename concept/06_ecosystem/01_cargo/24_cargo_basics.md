# Cargo 基础总览（Cargo Basics）

> **内容分级**: [综述级]
> **本节关键术语**: Cargo · Package · Manifest · `Cargo.toml` · Target · Feature — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
> **EN**: Cargo Basics
> **Summary**: A foundational map of Cargo for Rust 1.99.0+: what Cargo is relative to `rustc`, the five core commands (`new`/`build`/`run`/`check`/`test`), the essential `Cargo.toml` fields, a first look at workspaces and features, and a diagnostic table for the most common Cargo errors.
> **Rust 版本**: 1.99.0+ (Edition 2024)
> **受众**: [初学者]
> **Bloom 层级**: L1-L3
> **权威来源**: 本文件为 `concept/` 权威页（范围仅限 Cargo 基础命令与 `Cargo.toml` 核心字段的总览；依赖解析、workspace、manifest 全字段等专题由各自权威页维护，见第七节边界表）。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 提供一张 Cargo「基础地图」：先建立命令与 manifest 的整体心智模型，再按边界表跳转到各专题权威页深读。
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
> **前置概念**: [Toolchain](../00_toolchain/01_toolchain.md) · [Cargo 入门](15_cargo_getting_started.md)
> **后置概念**: [Cargo Workspaces](14_cargo_workspaces.md) · [Cargo Manifest Reference](10_cargo_manifest_reference.md) · [Cargo Commands Reference](19_cargo_commands_reference.md) · [Cargo Dependency Resolution](06_cargo_dependency_resolution.md)

---

> **来源**: [Cargo Book — Why Cargo Exists](https://doc.rust-lang.org/cargo/index.html) · [Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html) · [Cargo Book — The Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) · [TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) · [Rust Reference — Crates and Modules](https://doc.rust-lang.org/reference/crates-and-modules.html)

---

## 一、Cargo 在工具链中的定位

`rustc` 是编译器，Cargo 是**构建系统 + 包管理器 + 项目编排器**。日常 Rust 开发几乎不直接调用 `rustc`：Cargo 负责发现 package、解析并下载依赖、按 profile 调用 `rustc`、运行测试与文档工具。官方建议把 Cargo 作为默认入口（[Cargo Book — Why Cargo Exists](https://doc.rust-lang.org/cargo/index.html)）。

| 层 | 工具 | 职责 |
|:---|:---|:---|
| 编译器 | `rustc` | 单 crate 编译、单文件检查 |
| 构建/包管理 | `cargo` | 依赖解析、构建编排、测试、发布 |
| 工具链管理 | `rustup` | 安装/切换 toolchain 与组件 |

> **心智模型**: Cargo 把「一个 crate 的编译问题」升级为「一个 package 及其依赖图的工程问题」。理解 Cargo 的基础 = 理解 **命令 → manifest → 依赖图** 这条主线。

---

## 二、五个核心命令

以下命令覆盖日常开发的主循环（[Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html)）：

| 命令 | 作用 | 关键细节 |
|:---|:---|:---|
| `cargo new <name>` | 创建新 package（默认二进制；`--lib` 建库） | 生成 `Cargo.toml` + `src/main.rs`（或 `src/lib.rs`）；在已有目录内用 `cargo init` |
| `cargo build` | 编译 package 及其依赖 | 默认 debug profile；产物在 `target/debug/`；`--release` 走优化 profile |
| `cargo run` | 编译并立即运行二进制 | 等价于 `cargo build` + 执行；`--` 之后的参数传给程序 |
| `cargo check` | 只做类型检查/借用检查，不生成二进制 | 比 `cargo build` 快，是日常「快速验证」首选 |
| `cargo test` | 编译并运行测试 | 覆盖单元测试、集成测试（`tests/`）、文档测试三种测试形态 |

最小工作流（[TRPL Ch01](https://doc.rust-lang.org/book/ch01-03-testing.html)）：

```bash
cargo new hello_cargo
cd hello_cargo
cargo run          # 编译 + 运行
cargo check        # 快速验证，不产出二进制
cargo test         # 运行测试
```

### 命令与 rustc 的对应关系

| 直接 rustc 做法 | Cargo 等价 | Cargo 额外收益 |
|:---|:---|:---|
| `rustc main.rs` | `cargo build` | 依赖解析、增量缓存、profile 管理 |
| `rustc --test` 后手动执行 | `cargo test` | 测试发现、文档测试、集成测试编排 |
| 手写 `--extern` 链接第三方库 | `[dependencies]` + `cargo build` | 版本解析、lockfile 锁定 |

> **注意**: `cargo check` 不产出可执行文件，因此不能替代 `cargo build`/`cargo run`；它验证的是「能否通过编译」，不是「产物行为」。

---

## 三、`Cargo.toml` 核心字段

`Cargo.toml`（manifest）是 Cargo 读取的唯一项目描述文件（[Cargo Book — Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html)）。一个最小可用的 manifest：

```toml
[package]
name = "hello_cargo"
version = "0.1.0"
edition = "2024"
rust-version = "1.99.0"

[dependencies]
```

| 字段 | 所属段 | 作用 | 备注 |
|:---|:---|:---|:---|
| `name` | `[package]` | package 名称，发布到 registry 时的唯一标识 | 不能与 crate 名规则冲突 |
| `version` | `[package]` | SemVer 版本号 | 发布 crates.io 必填 |
| `edition` | `[package]` | 语言 Edition（`2015`/`2018`/`2021`/`2024`） | Edition 2024 隐式启用 resolver v3 |
| `rust-version` | `[package]` | MSRV（最低可编译的 Rust 版本） | 低于该版本时 Cargo 提前报错而非 rustc 报错 |
| `resolver` | `[package]`/`[workspace]` | 依赖解析算法版本（`1`/`2`/`3`） | 通常由 `edition` 推断，virtual workspace 必须显式给出 |
| `[dependencies]` | — | 正常编译依赖 | 版本为 SemVer 要求，如 `"1.0"` 表示 `>=1.0.0, <2.0.0` |
| `[dev-dependencies]` | — | 仅测试/示例/基准用到的依赖 | 不传递给下游消费者 |
| `[build-dependencies]` | — | `build.rs` 脚本用到的依赖 | 与运行时依赖分离 |
| `[features]` | — | 条件编译开关（见第五节） | 默认 feature 列表写在 `default = [...]` |
| `[workspace]` | — | 声明多 package 工作区（见第四节） | 成员共享一个 `Cargo.lock` 与 `target/` |

依赖声明的三种常见形态：

```toml
[dependencies]
serde = "1"                                        # 仅版本要求
rand = { version = "0.9", default-features = false }  # 表形式：关默认 feature
mylib = { path = "../mylib" }                      # path 依赖（本地 crate）
```

> **版本要求语义**: `"1.2.3"` 是 caret 要求 `>=1.2.3, <2.0.0`；`"~1.2.3"` 是 tilde 要求 `>=1.2.3, <1.3.0`；`"*"` 接受任意版本。详见 [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)。
