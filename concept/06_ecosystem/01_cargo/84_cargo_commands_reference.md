# Cargo 命令参考（Cargo Commands Reference）

> **内容分级**: [参考级]
> **本节关键术语**: cargo build · cargo test · cargo check · cargo run · cargo add · cargo publish — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Commands Reference
> **Summary**: A classified quick reference of Cargo subcommands for Rust 1.97.0+: general, build, manifest, package, publish, report, and inspection commands, plus common options and plugin integration points.
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 覆盖开发者日常最高频的 Cargo 命令，作为官方命令参考的浓缩权威页。
> **前置概念**: [Cargo Getting Started](80_cargo_getting_started.md) · [Cargo Workflow](81_cargo_workflow.md) · [Cargo Configuration](83_cargo_configuration.md)
> **后置概念**: [Cargo Manifest Targets](85_cargo_manifest_targets.md) · [Cargo Registry Internals](86_cargo_registry_internals.md) · [DevOps and CI/CD](../00_toolchain/28_devops_and_ci_cd.md)

---

> **来源**: [Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html) · [Cargo Book — cargo build](https://doc.rust-lang.org/cargo/commands/cargo-build.html) · [Cargo Book — cargo test](https://doc.rust-lang.org/cargo/commands/cargo-test.html) · [Cargo Book — cargo publish](https://doc.rust-lang.org/cargo/commands/cargo-publish.html)

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
| 检查 | 依赖/安全/许可证 | `audit`, `deny`（第三方插件） |

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
| `cargo update -p <spec> --precise <ver>` | 精确更新某个依赖 |
| `cargo tree` | 可视化依赖树 |
| `cargo tree -e features` | 查看 feature unification |
| `cargo metadata` | 输出机器可读项目元数据 |
| `cargo locate-project` | 输出 `Cargo.toml` 路径 |

## 四、Package 与发布命令

| 命令 | 用途 |
|:---|:---|
| `cargo new <name>` | 创建新 package |
| `cargo init` | 在现有目录初始化 package |
| `cargo install <crate>` | 安装二进制 crate |
| `cargo package` | 打包成 `.crate` 文件 |
| `cargo publish` | 发布到 registry |
| `cargo yank --vers <ver>` | 撤回已发布版本 |
| `cargo owner` | 管理 crate 所有者 |
| `cargo login` / `cargo logout` | 登录/登出 registry |

## 五、报告与诊断命令

```bash
# 查看未来不兼容报告
cargo report future-incompatibilities

# 查看编译耗时（需 nightly 或已稳定版本）
cargo build --timings

# 检查依赖重复
cargo tree --duplicates
```

`cargo report` 汇总依赖中可能导致未来编译失败的代码模式。

## 六、常用全局选项

| 选项 | 作用 |
|:---|:---|
| `--workspace` / `-p <pkg>` | 作用于整个 workspace 或指定 package |
| `--release` | 使用 `release` profile |
| `--target <triple>` | 指定目标平台 |
| `--features <f>` / `--all-features` / `--no-default-features` | 控制 feature |
| `--offline` | 离线模式 |
| `--locked` | 要求 `Cargo.lock` 与 `Cargo.toml` 完全匹配 |
| `--config <path>` | 临时加载额外配置 |

## 七、命令选择决策表

| 任务 | 推荐命令 |
|:---|:---|
| 快速类型检查 | `cargo check` |
| 本地运行 | `cargo run` |
| 运行全部测试 | `cargo test --workspace` |
| 查看依赖为何被引入 | `cargo tree -i <crate>` |
| 更新依赖 | `cargo update` |
| 发布前检查 | `cargo publish --dry-run` |
| 检查安全漏洞 | `cargo audit` |
| 单文件脚本执行 | `cargo run --manifest-path script.rs`（见 [Cargo Script](09_cargo_script.md)） |

## 八、常用命令组合示例

```bash
# 本地完整检查
cargo fmt --check && cargo clippy --workspace -- -D warnings && cargo test --workspace

# 发布前验证
cargo check --release && cargo test --release && cargo publish --dry-run

# 仅构建某个 member
cargo build -p member_name --release

# 带 feature 的构建
cargo build --features serde,tokio --no-default-features

# 生成并打开文档
cargo doc --workspace --no-deps --open
```

## 九、获取帮助与 manpage

```bash
# 查看命令帮助
cargo build --help
cargo help publish

# 生成 shell 补全脚本（通过 rustup）
rustup completions bash cargo > ~/.config/bash_completion.d/cargo
```

Rust 1.96 进一步改进了嵌套子命令的 manpage，例如：

```bash
cargo help report future-incompat
```

详见 [Cargo 1.96 新特性与工具链变更](76_cargo_196_features.md)。

## 十、与插件的集成

第三方工具通常以 `cargo-<name>` 可执行文件形式出现，例如 `cargo-expand`、`cargo-watch`、`cargo-audit`。详情见 [Cargo 子命令与插件生态](66_cargo_subcommands_and_plugins.md)。

想要观察 resolver v3 的 feature unification，可运行：

```bash
cargo tree -p c17_resolver_v3_public_demo -e features
```

完整示例见 [`crates/c17_resolver_v3_public_demo`](../../../crates/c17_resolver_v3_public_demo/)。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

> **权威来源**: [Cargo Book — Commands](https://doc.rust-lang.org/cargo/commands/index.html)

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
