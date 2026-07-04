# Cargo 工作流（Cargo Workflow）

> **内容分级**: [参考级]
> **本节关键术语**: Package Layout · `Cargo.toml` · `Cargo.lock` · Workspace · Target Directory — [完整对照表](../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Workflow
> **Summary**: Cargo 日常开发工作流：标准 package 布局、`Cargo.toml` 与 `Cargo.lock` 的分工、在现有项目上工作、以及多 package 场景下的最佳实践。
> **受众**: [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 覆盖从“创建 package”到“在团队中维护依赖锁定”的完整日常流程。
> **前置概念**: [Cargo Getting Started](80_cargo_getting_started.md) · [Modules and Paths](../01_foundation/07_modules_and_items/11_modules_and_paths.md)
> **后置概念**: [Cargo Guide Practices](82_cargo_guide_practices.md) · [Cargo Workspaces](78_cargo_workspaces.md) · [Cargo Dependency Resolution](60_cargo_dependency_resolution.md)

---

> **来源**: [Cargo Book — Creating a New Package](https://doc.rust-lang.org/cargo/guide/creating-a-new-project.html) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Working on an Existing Package](https://doc.rust-lang.org/cargo/guide/working-on-an-existing-project.html) ·
> [Cargo Book — Cargo.toml vs Cargo.lock](https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html) ·
> [Cargo Book — Package Layout](https://doc.rust-lang.org/cargo/guide/project-layout.html)

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
| `Cargo.toml` | 声明依赖范围（如 `^1.2`） | ✅ 是 |
| `Cargo.lock` | 记录精确解析版本 | 二进制项目 ✅；库项目通常 ❌ |

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

## 四、常用开发命令

| 命令 | 场景 |
|:---|:---|
| `cargo check` | 快速反馈，不生成产物 |
| `cargo build --release` | 优化构建 |
| `cargo run --bin foo` | 运行指定二进制 |
| `cargo test --test integration` | 运行指定集成测试 |
| `cargo clean` | 清理 target 目录 |

## 五、与 Workspace 的衔接

当项目包含多个 crate 时，应使用 workspace。详见 [Cargo Workspaces](78_cargo_workspaces.md)。

---

> **权威来源**: [Cargo Book — Guide](https://doc.rust-lang.org/cargo/guide/index.html)
> **内容分级**: [参考级]
