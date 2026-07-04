> **内容分级**: [专家级]

# Cargo 1.96 新特性与工具链变更

> **EN**: Cargo 1.96 Feature Highlights
> **Summary**: Systematic coverage of Cargo and toolchain changes stabilized in Rust 1.96: `pubtime` registry field, runtime `CARGO_BIN_EXE_<crate>`, TOML v1.1 support, nested subcommand manpages, and related security fixes.
> **受众**: [进阶 / 工程]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Process / Platform
> **双维定位**: P×App — 将 Cargo 1.96 工具链变更应用于构建、发布与依赖治理
> **前置概念**: · [Rust vs Go](../05_comparative/02_rust_vs_go.md) [Toolchain](01_toolchain.md) · [Public/Private Dependencies](10_public_private_deps.md) · [Cargo Security](72_cargo_security_cves.md) · [Security Practices](19_security_practices.md)
> **后置概念**: [Rust Version Tracking](../07_future/05_rust_version_tracking.md) · [Rust 1.96 Stabilized](../07_future/rust_1_96_stabilized.md)
> **版本状态**: 当前稳定 patch 为 **1.96.1**；特性集与 Rust 1.96.0 一致。

---

> **来源**: [Cargo 1.96 CHANGELOG](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) ·
> [Cargo Book — Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) ·
> [Cargo Book — Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) ·
> [TOML v1.1 Specification](https://toml.io/en/v1.1.0)


---

> **过渡**: 从 Cargo 1.96 新特性与工具链变更 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Cargo 1.96 新特性与工具链变更 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Cargo 1.96 新特性与工具链变更 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: Cargo 1.96 新特性与工具链变更 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Cargo 1.96 新特性与工具链变更 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Cargo 1.96 新特性与工具链变更 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


## 📑 目录

- [Cargo 1.96 新特性与工具链变更](#cargo-196-新特性与工具链变更)
  - [📑 目录](#-目录)
  - [一、特性总览](#一特性总览)
  - [二、`pubtime`：crate 版本发布时间字段](#二pubtimecrate-版本发布时间字段)
    - [2.1 背景](#21-背景)
    - [2.2 数据来源](#22-数据来源)
    - [2.3 典型应用](#23-典型应用)
    - [2.4 当前限制](#24-当前限制)
  - [三、`CARGO_BIN_EXE_<crate>` 运行时（Runtime）可用](#三cargo_bin_exe_crate-运行时可用)
    - [3.1 变更内容](#31-变更内容)
    - [3.2 使用示例](#32-使用示例)
    - [3.3 为什么重要](#33-为什么重要)
    - [3.4 与 Build Dir Layout v2 的关系](#34-与-build-dir-layout-v2-的关系)
  - [四、TOML v1.1 支持](#四toml-v11-支持)
    - [4.1 变更内容](#41-变更内容)
    - [4.2 主要语法改进](#42-主要语法改进)
    - [4.3 Cargo.toml 示例](#43-cargotoml-示例)
    - [4.4 发布兼容性注意](#44-发布兼容性注意)
  - [五、嵌套子命令 manpage](#五嵌套子命令-manpage)
    - [5.1 变更内容](#51-变更内容)
    - [5.2 收益](#52-收益)
  - [六、相关安全修复](#六相关安全修复)
  - [七、迁移建议与陷阱](#七迁移建议与陷阱)
    - [7.1 推荐迁移路径](#71-推荐迁移路径)
    - [7.2 常见陷阱](#72-常见陷阱)

---

## 一、特性总览

Rust 1.96 在 Cargo 与工具链层面的核心变更可归纳为四类：

| 特性 | 用户可见变化 | 典型应用场景 |
|:---|:---|:---|
| **`pubtime` 字段** | crate index 与 lockfile 可记录版本发布时间 | 依赖冷却策略、Renovate/Dependabot 时间规则、历史依赖重放 |
| **`CARGO_BIN_EXE_<crate>` 运行时可用** | 测试运行时可读取 `env!("CARGO_BIN_EXE_foo")` / `std::env::var` | 集成测试调用 `[[bin]]` 目标，替代从 `[[test]]` 路径推断 |
| **TOML v1.1 解析** | `Cargo.toml` 与 `.cargo/config.toml` 支持多行 inline table、新转义序列等 | 更紧凑的依赖表、跨行 inline 配置 |
| **嵌套子命令 manpage** | `cargo help report future-incompat` 等可展示完整 manpage | CI 文档化、离线工具链参考 |

> **关键洞察**: Cargo 正在从"构建执行器"演进为"构建可观测平台"——`pubtime`、结构化日志、细粒度锁共同支持大规模 Rust monorepo 和企业 CI 的可预测性。

---

## 二、`pubtime`：crate 版本发布时间字段

### 2.1 背景

`pubtime` 是 Cargo 1.96 在 crate index 与 lockfile 中新增的**版本发布时间字段**。它允许工具基于"该版本已发布多久"做决策，而不只是基于语义版本号。

### 2.2 数据来源

- crates.io 在 crate 发布时记录 UTC 时间。
- index 条目中的 `pubtime` 以 RFC 3339 / ISO 8601 格式呈现。
- lockfile（`Cargo.lock`）在重新生成时可保留该字段（取决于 Cargo 版本与格式版本）。

### 2.3 典型应用

| 场景 | 说明 |
|:---|:---|
| **依赖冷却（cooldown）** | 团队可配置"新版本发布 N 天后才允许自动升级"，降低恶意发布或回归的即时影响 |
| **Renovate/Dependabot 规则** | 基于 `pubtime` 设置最小发布年龄（`minimumReleaseAge`），过滤过新的补丁 |
| **审计与合规** | 追溯某个依赖版本在特定时间点是否已可用 |
| **可复现构建** | 结合 lockfile 历史快照，重放构建时的依赖时间线 |

```toml
# Cargo.lock 片段（概念示例，格式以实际 Cargo 版本为准）
[[package]]
name = "serde"
version = "1.0.228"
source = "registry+https://github.com/rust-lang/crates.io-index"
pubtime = "2026-05-20T12:34:56Z"
```

### 2.4 当前限制

- `pubtime` 本身**不强制**冷却策略；需要外部工具或 CI 策略消费该字段。
- 第三方 registry 需要实现该字段才能与 crates.io 行为一致。

---

## 三、`CARGO_BIN_EXE_<crate>` 运行时可用

### 3.1 变更内容

在 Rust 1.96 之前，`CARGO_BIN_EXE_<crate>` 环境变量仅在**编译时**通过 `env!()` 使用；运行时 `std::env::var` 无法读取到。

Rust 1.96 将其扩展为**运行时也可用**，方便集成测试在运行时定位同 workspace 中的二进制产物。

### 3.2 使用示例

```rust
// 在 integration test 中调用 workspace 内的 foo binary
#[test]
fn test_cli_help() {
    let bin_path = std::env::var("CARGO_BIN_EXE_foo")
        .expect("CARGO_BIN_EXE_foo should be set by cargo");

    let output = std::process::Command::new(&bin_path)
        .arg("--help")
        .output()
        .expect("failed to execute foo");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Usage:"));
}
```

### 3.3 为什么重要

| 旧做法 | 新做法 |
|:---|:---|
| 通过 `std::env::current_exe()` 或 `[[test]]` 路径推断 binary 位置 | 直接使用 `std::env::var("CARGO_BIN_EXE_<name>")` |
| 容易在 Build Dir Layout v2 等变更后失效 | 使用 Cargo 提供的稳定接口 |
| 只能在编译期通过 `env!(...)` 嵌入 | 运行时可动态获取 |

### 3.4 与 Build Dir Layout v2 的关系

Rust 1.96 继续推进 Build Dir Layout v2（中间产物按构建单元哈希隔离）。`CARGO_BIN_EXE_*` 的运行时可用性降低了工具直接依赖 `target/` 内部路径的风险，是迁移到 Layout v2 的配套稳定接口。

---

## 四、TOML v1.1 支持

### 4.1 变更内容

Cargo 1.96 合并了 TOML v1.1 解析支持（cargo#16415）。主要影响 `Cargo.toml` 与 `.cargo/config.toml` 的写法。

### 4.2 主要语法改进

| 特性 | TOML v1.0 | TOML v1.1 | 说明 |
|:---|:---|:---|:---|
| 多行 inline table | 不允许 | 允许 | inline table 内可换行，提高可读性 |
| 新转义序列 | `\uXXXX` | 增加 `\xHH`、`\e` 等 | 更灵活的字符串表示 |
| 可选秒 | 必须写秒 | 时间可省略秒 | `2026-05-28T12:34` 合法 |

### 4.3 Cargo.toml 示例

```toml
# TOML v1.1 允许多行 inline table
[dependencies]
serde = { version = "1.0", features = [
    "derive",
    "std",
] }

[package.metadata.my-cfg]
# 多行 inline table 使复杂元数据更易读
extra = { name = "demo", flags = ["a", "b"] }
```

### 4.4 发布兼容性注意

- `cargo package` 在生成发布 tarball 时，会**将 TOML v1.1 特性重写为 TOML 0.5 兼容格式**，以保证旧版 Cargo 能解析。
- 如果你的 MSRV 对应的 Cargo 版本不支持 TOML v1.1，仍建议保持保守写法，或验证 `cargo package` 后的清单。

---

## 五、嵌套子命令 manpage

### 5.1 变更内容

Rust 1.96 为 Cargo 的**嵌套子命令**提供了完整的 manpage 支持。例如：

```bash
# 之前：help 可能只有简短提示
# 之后：可查看完整 manpage
$ cargo help report future-incompat
$ cargo help report
```

### 5.2 收益

- **CI 文档化**: 可在无网络环境下查阅完整子命令文档。
- **诊断工具**: `cargo report` 系列子命令（`future-incompat`、`timings` 等）的用法更易于离线获取。
- **shell 补全与 apropos**: manpage 索引改善命令发现性。

---

## 六、相关安全修复

Rust 1.96 修复了两个 Cargo CVE，这些修复与工具链行为直接相关：

| CVE | 影响 | 修复 |
|:---|:---|:---|
| **CVE-2026-5222** | `.git` 后缀 URL 规范化可能导致非预期协议选择 | 限制 `.git` 后缀规范化到 git 协议 |
| **CVE-2026-5223** | 含 symlink 的 tarball 可能逃逸目标目录 | 拒绝包含 symlink 的 tarball |

详见 [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](72_cargo_security_cves.md)。

---

## 七、迁移建议与陷阱

### 7.1 推荐迁移路径

1. **审计直接依赖 `target/` 内部路径的脚本**
   - 搜索 `target/debug/deps`、`target/release` 等硬编码路径。
   - 替换为 `CARGO_BIN_EXE_*`、`OUT_DIR`、`env!()` 等稳定接口。

2. **消费 `pubtime`**
   - 在 Renovate/Dependabot 配置中引入 `minimumReleaseAge`。
   - 在内部 registry 或审计工具中记录 `pubtime`。

3. **谨慎使用 TOML v1.1**
   - 确认团队 MSRV 的 Cargo 版本。
   - 对关键 crate，执行 `cargo package --allow-dirty` 并检查生成的 `Cargo.toml`。

4. **更新 CI 文档**
   - 将 `cargo help report future-incompat` 加入 CI 诊断步骤。

### 7.2 常见陷阱

| 陷阱 | 说明 |
|:---|:---|
| 假设 `pubtime` 一定存在 | 第三方 registry 或旧 lockfile 可能缺失该字段 |
| 运行时读取旧版 Cargo 设置的 `CARGO_BIN_EXE_*` | Rust < 1.96 的运行时不可用；需加 fallback |
| 在 `Cargo.toml` 中使用 TOML v1.1 后未验证 MSRV | 旧 Cargo 会解析失败 |
| 直接解析 `target/` 目录结构 | Build Dir Layout v2 会改变目录结构 |

---

> **对应练习**: [`exercises/src/cargo_196/`](../../exercises/src/cargo_196)
