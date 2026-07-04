# Cargo 命令参考（Cargo Commands Reference）

> **内容分级**: [参考级]
> **本节关键术语**: cargo build · cargo test · cargo check · cargo run · cargo add · cargo publish — [完整对照表](../00_meta/terminology_glossary.md)
>
> **EN**: Cargo Commands Reference
> **Summary**: Cargo 子命令分类速查：通用命令、构建命令、manifest 命令、package 命令、发布命令、报告命令及其最常用的选项。 Classified quick reference of Cargo subcommands: general, build, manifest, package, publish, and report commands.
> **受众**: [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 覆盖开发者日常最高频的 Cargo 命令，作为官方命令参考的浓缩权威页。
> **前置概念**: [Cargo Getting Started](80_cargo_getting_started.md) · [Cargo Workflow](81_cargo_workflow.md) · [Cargo Configuration](83_cargo_configuration.md)
> **后置概念**: [Cargo Manifest Targets](85_cargo_manifest_targets.md) · [Cargo Registry Internals](86_cargo_registry_internals.md) · [DevOps and CI/CD](28_devops_and_ci_cd.md)

---

> **来源**: [Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — cargo build](https://doc.rust-lang.org/cargo/commands/cargo-build.html) ·
> [Cargo Book — cargo test](https://doc.rust-lang.org/cargo/commands/cargo-test.html) ·
> [Cargo Book — cargo publish](https://doc.rust-lang.org/cargo/commands/cargo-publish.html)

---

## 一、命令分类

| 分类 | 说明 | 代表命令 |
|:---|:---|:---|
| 通用 | 信息、帮助 | `cargo --version`, `cargo --help` |
| 构建 | 编译、检查、文档 | `build`, `check`, `doc`, `run`, `test`, `bench` |
| Manifest | 操作依赖与元数据 | `add`, `remove`, `update`, `tree`, `metadata` |
| Package | 创建、安装、搜索 | `new`, `init`, `install`, `uninstall`, `search` |
| 发布 | crates.io 生命周期（Lifetimes） | `package`, `publish`, `yank`, `owner`, `login` |
| 报告 | 诊断与统计 | `report`, `report future-incompatibilities` |

## 二、高频构建命令

| 命令 | 核心用途 | 常用选项 |
|:---|:---|:---|
| `cargo build` | 编译 | `--release`, `--bin`, `--lib`, `--workspace` |
| `cargo check` | 快速类型检查 | `--all-targets`, `--workspace` |
| `cargo run` | 编译并运行 | `--release`, `--bin`, `--` 参数分隔 |
| `cargo test` | 运行测试 | `--test`, `--lib`, `--nocapture`, `--workspace` |
| `cargo doc` | 生成文档 | `--open`, `--no-deps` |
| `cargo clippy` | lint 检查 | `-- -D warnings` |
| `cargo fmt` | 格式化 | `--check` |

## 三、Manifest 命令

| 命令 | 用途 |
|:---|:---|
| `cargo add <crate>` | 添加依赖 |
| `cargo remove <crate>` | 移除依赖 |
| `cargo update` | 更新 `Cargo.lock` 中的版本 |
| `cargo tree` | 可视化依赖树 |
| `cargo metadata` | 输出机器可读项目元数据 |
| `cargo locate-project` | 输出 `Cargo.toml` 路径 |

## 四、发布命令

| 命令 | 用途 |
|:---|:---|
| `cargo package` | 打包成 `.crate` 文件 |
| `cargo publish` | 发布到 registry |
| `cargo yank` | 撤销已发布版本 |
| `cargo owner` | 管理 crate 所有者 |
| `cargo login` / `cargo logout` | 登录/登出 registry |

## 五、报告命令

```bash
# 查看未来不兼容报告
cargo report future-incompatibilities
```

该命令汇总依赖中可能导致未来编译失败的代码模式。

---

> **权威来源**: [Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html)
> **内容分级**: [参考级]
