# Cargo 工作流（Cargo Workflow）

> **内容分级**: [参考级]
> **本节关键术语**: Package Layout · `Cargo.toml` · `Cargo.lock` · Workspace · Target Directory — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Workflow
> **Summary**: The daily Cargo development workflow for Rust 1.97.0+: standard package layout, the roles of `Cargo.toml` and `Cargo.lock`, onboarding existing projects, common commands, dependency updates, and workspace integration.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 覆盖从“创建 package”到“在团队中维护依赖锁定”的完整日常流程。
> **前置概念**: [Cargo Getting Started](80_cargo_getting_started.md) · [Modules and Paths](../../01_foundation/07_modules_and_items/11_modules_and_paths.md)
> **后置概念**: [Cargo Guide Practices](82_cargo_guide_practices.md) · [Cargo Workspaces](78_cargo_workspaces.md) · [Cargo Dependency Resolution](60_cargo_dependency_resolution.md)

---

> **来源**: [Cargo Book — Creating a New Package](https://doc.rust-lang.org/cargo/guide/creating-a-new-project.html) · [Cargo Book — Working on an Existing Package](https://doc.rust-lang.org/cargo/guide/working-on-an-existing-project.html) · [Cargo Book — Cargo.toml vs Cargo.lock](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html) · [Cargo Book — Package Layout](https://doc.rust-lang.org/cargo/guide/project-layout.html)

---

## 一、标准 Package 布局

Cargo 约定俗成的目录结构：

```text
my_project/
├── Cargo.toml
├── Cargo.lock
├── src/
│   ├── main.rs          # 二进制入口（与 package 同名）
│   ├── lib.rs           # 库入口
│   └── bin/
│       └── extra.rs     # 额外二进制
├── tests/               # 集成测试
├── benches/             # 基准测试
├── examples/            # 示例
└── build.rs             # 构建脚本（可选）
```

| 目录/文件 | 用途 |
|:---|:---|
| `src/main.rs` | 可执行文件入口 |
| `src/lib.rs` | 库入口 |
| `src/bin/` | 多个可执行文件 |
| `tests/` | 集成测试，每个文件编译为独立测试二进制 |
| `benches/` | 基准测试 |
| `examples/` | 可运行示例 |

## 二、`Cargo.toml` vs `Cargo.lock`

| 文件 | 作用 | 是否应提交 |
|:---|:---|:---:|
| `Cargo.toml` | 声明依赖范围（如 `^1.2`）、package 元数据、features | ✅ 是 |
| `Cargo.lock` | 记录精确解析版本，保证可复现构建 | 二进制项目 ✅；库项目通常 ❌ |

`Cargo.lock` 保证可复现构建；库 crate 发布到 crates.io 时不带 lock 文件，允许下游自由解析兼容版本。

## 三、在现有项目上工作

```bash
# 克隆并进入项目
git clone <repo>
cd <repo>

# 检查能否编译
cargo check

# 运行测试
cargo test

# 查看依赖树
cargo tree
```

如果项目使用 workspace，通常从 workspace root 运行：

```bash
cargo check --workspace
cargo test --workspace
```

## 四、常用开发命令

| 命令 | 场景 |
|:---|:---|
| `cargo check` | 快速反馈，不生成产物 |
| `cargo build --release` | 优化构建 |
| `cargo run --bin foo` | 运行指定二进制 |
| `cargo test --test integration` | 运行指定集成测试 |
| `cargo clean` | 清理 target 目录 |
| `cargo doc --open` | 生成并打开文档 |
| `cargo clippy -- -D warnings` | 将警告视为错误 |
| `cargo fmt --check` | CI 中检查格式 |

## 五、更新依赖的安全流程

```bash
# 1. 查看当前依赖树
cargo tree

# 2. 更新所有依赖到最新兼容版本
cargo update

# 3. 仅更新某个依赖
cargo update -p serde

# 4. 精确锁定到某个版本
cargo update -p serde --precise 1.0.217

# 5. 忽略 MSRV 约束，验证最新版本（resolver v3）
cargo update --ignore-rust-version
```

建议在更新后运行 `cargo test` 与 `cargo clippy`，必要时使用 `cargo audit` 检查安全漏洞。

## 六、与 Workspace 的衔接

当项目包含多个 crate 时，应使用 workspace。workspace root 通常包含：

```toml
[workspace]
members = ["crates/*"]
resolver = "3"

[workspace.package]
edition = "2024"
rust-version = "1.97.0"

[workspace.dependencies]
serde = "1.0"
```

Workspace 优势：

- 一个 `Cargo.lock` 覆盖所有成员；
- 统一的 `target/` 输出目录；
- 通过 `workspace.dependencies` 统一依赖版本；
- 通过 `workspace.lints` 统一 lint 配置。

详见 [Cargo Workspaces](78_cargo_workspaces.md)。

## 七、是否提交 `Cargo.lock`？

| 项目类型 | 是否提交 `Cargo.lock` | 原因 |
|:---|:---:|:---|
| 二进制/应用 | ✅ | 保证 CI、部署、协作者使用相同版本 |
| 库 crate | ❌ | 下游会自行解析；提交 lock 无意义 |
| Workspace（含二进制） | ✅ | 共享 lockfile，确保整体可复现 |
| Workspace（纯库） | ❌ | 与单库项目同理 |

## 八、典型日常循环

```bash
cargo check          # 快速类型检查
cargo test           # 本地测试
cargo clippy         # lint
cargo build --release # 发布前构建
cargo doc --no-deps  # 生成文档
```

想要体验 resolver v3 与 `public = true` 的 feature unification，可查看 [`crates/c17_resolver_v3_public_demo`](../../../crates/c17_resolver_v3_public_demo/)。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

> **权威来源**: [Cargo Book — Guide](https://doc.rust-lang.org/cargo/guide/index.html)

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
