# CLI Tools - 命令行工具

> **核心工具**: cargo 生态工具链、开发工具、质量保证工具  
> **适用场景**: 日常开发、CI/CD、代码质量、性能分析

---

## 📋 目录

- [CLI Tools - 命令行工具](#cli-tools---命令行工具)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [工具分类](#工具分类)
    - [安装管理](#安装管理)
  - [cargo 扩展](#cargo-扩展)
    - [cargo-edit - 依赖管理](#cargo-edit---依赖管理)
      - [添加依赖](#添加依赖)
      - [删除依赖](#删除依赖)
      - [升级依赖](#升级依赖)
    - [cargo-watch - 自动编译](#cargo-watch---自动编译)
      - [基础用法](#基础用法)
      - [高级用法](#高级用法)
    - [cargo-make - 任务运行](#cargo-make---任务运行)
      - [基础配置](#基础配置)
      - [高级配置](#高级配置)
    - [cargo-nextest - 测试运行](#cargo-nextest---测试运行)
      - [基础用法1](#基础用法1)
      - [高级功能](#高级功能)
  - [代码质量](#代码质量)
    - [cargo-clippy - 代码检查](#cargo-clippy---代码检查)
    - [cargo-fmt - 代码格式化](#cargo-fmt---代码格式化)
    - [cargo-audit - 安全审计](#cargo-audit---安全审计)
      - [基础用法2](#基础用法2)
      - [修复漏洞](#修复漏洞)
    - [cargo-deny - 依赖策略](#cargo-deny---依赖策略)
      - [配置文件 (`deny.toml`)](#配置文件-denytoml)
  - [开发工具](#开发工具)
    - [cargo-expand - 宏展开](#cargo-expand---宏展开)
      - [基础用法3](#基础用法3)
    - [cargo-tree - 依赖树](#cargo-tree---依赖树)
    - [cargo-outdated - 依赖检查](#cargo-outdated---依赖检查)
      - [基础用法4](#基础用法4)
    - [cargo-llvm-cov - 代码覆盖](#cargo-llvm-cov---代码覆盖)
      - [基础用法5](#基础用法5)
  - [性能分析](#性能分析)
    - [cargo-flamegraph - 火焰图](#cargo-flamegraph---火焰图)
      - [基础用法6](#基础用法6)
    - [cargo-bench - 基准测试](#cargo-bench---基准测试)
  - [发布工具](#发布工具)
    - [cargo-release - 版本发布](#cargo-release---版本发布)
      - [基础用法7](#基础用法7)
    - [cargo-dist - 分发构建](#cargo-dist---分发构建)
      - [基础用法8](#基础用法8)
  - [最佳实践](#最佳实践)
    - [1. 开发工作流](#1-开发工作流)
    - [2. CI/CD 集成](#2-cicd-集成)
    - [3. 定期维护](#3-定期维护)
    - [4. 工具组合](#4-工具组合)
    - [5. 性能分析流程](#5-性能分析流程)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 忘记更新工具](#️-陷阱1-忘记更新工具)
    - [⚠️ 陷阱2: 不配置 clippy](#️-陷阱2-不配置-clippy)
    - [⚠️ 陷阱3: 忽略安全审计](#️-陷阱3-忽略安全审计)
    - [⚠️ 陷阱4: 手动管理依赖](#️-陷阱4-手动管理依赖)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [工具仓库](#工具仓库)
    - [实用文章](#实用文章)
    - [相关文档](#相关文档)

---

## 概述

### 工具分类

**按功能分类**:

1. **依赖管理**: cargo-edit, cargo-upgrade, cargo-outdated
2. **开发效率**: cargo-watch, cargo-make, cargo-expand
3. **代码质量**: cargo-clippy, cargo-fmt, cargo-audit
4. **测试工具**: cargo-nextest, cargo-llvm-cov, cargo-tarpaulin
5. **性能分析**: cargo-flamegraph, cargo-bench, cargo-criterion
6. **发布工具**: cargo-release, cargo-dist, cargo-publish

**按使用频率分类**:

- **必备工具** (⭐⭐⭐⭐⭐): clippy, fmt, edit, watch
- **推荐工具** (⭐⭐⭐⭐): audit, expand, nextest
- **特定场景** (⭐⭐⭐): flamegraph, release, deny

### 安装管理

**批量安装推荐工具**:

```bash
# 必备工具
cargo install cargo-edit
cargo install cargo-watch
cargo install cargo-expand

# 质量工具
cargo install cargo-audit
cargo install cargo-deny
cargo install cargo-outdated

# 测试工具
cargo install cargo-nextest
cargo install cargo-llvm-cov

# 性能工具
cargo install flamegraph
```

**查看已安装工具**:

```bash
cargo install --list
```

**更新工具**:

```bash
cargo install-update -a  # 需先安装 cargo-update
```

---

## cargo 扩展

### cargo-edit - 依赖管理

**安装**:

```bash
cargo install cargo-edit
```

#### 添加依赖

```bash
# 基础用法
cargo add tokio

# 指定版本
cargo add tokio@1.35

# 添加 features
cargo add serde --features derive

# 添加 dev 依赖
cargo add --dev proptest

# 添加 build 依赖
cargo add --build cc

# 可选依赖
cargo add diesel --optional

# 从 git 添加
cargo add my-crate --git https://github.com/user/repo

# 从本地路径添加
cargo add my-crate --path ../my-crate
```

#### 删除依赖

```bash
# 删除依赖
cargo rm tokio

# 删除 dev 依赖
cargo rm --dev proptest
```

#### 升级依赖

```bash
# 升级所有依赖到最新兼容版本
cargo upgrade

# 升级到最新版本（可能破坏兼容性）
cargo upgrade --incompatible

# 只升级特定依赖
cargo upgrade tokio
```

**实战示例**:

```bash
# 快速添加 Web 项目依赖
cargo add axum
cargo add tokio --features full
cargo add serde --features derive
cargo add sqlx --features runtime-tokio-rustls,postgres
cargo add --dev reqwest
```

---

### cargo-watch - 自动编译

**安装**:

```bash
cargo install cargo-watch
```

#### 基础用法

```bash
# 自动检查（最快）
cargo watch -x check

# 自动测试
cargo watch -x test

# 自动运行
cargo watch -x run

# 自动构建
cargo watch -x build
```

#### 高级用法

```bash
# 链式命令（依次执行）
cargo watch -x check -x test -x run

# 监听特定文件
cargo watch -w src -x test

# 忽略特定文件
cargo watch -i '*.txt' -x test

# 清屏后执行
cargo watch -c -x test

# 延迟执行（防抖）
cargo watch --delay 2 -x test

# 执行 shell 命令
cargo watch -s 'cargo test && cargo run'
```

**实战示例 - Web 开发**:

```bash
# 自动重启 Web 服务器
cargo watch -x 'run --bin api-server'

# 测试 + 运行
cargo watch -x test -x 'run --bin api-server'
```

**实战示例 - TDD 开发**:

```bash
# 持续测试特定模块
cargo watch -x 'test user::tests'

# 详细测试输出
cargo watch -x 'test -- --nocapture'
```

---

### cargo-make - 任务运行

**安装**:

```bash
cargo install cargo-make
```

#### 基础配置

**Makefile.toml**:

```toml
[tasks.dev]
description = "开发模式"
command = "cargo"
args = ["run"]
watch = true

[tasks.build-release]
description = "发布构建"
command = "cargo"
args = ["build", "--release"]

[tasks.test-all]
description = "运行所有测试"
command = "cargo"
args = ["test", "--all-features"]

[tasks.clean-all]
description = "完全清理"
script = [
    "cargo clean",
    "rm -rf target/",
]
```

#### 高级配置

```toml
# 依赖任务
[tasks.ci]
description = "CI 流程"
dependencies = [
    "format-check",
    "clippy",
    "test-all",
]

[tasks.format-check]
command = "cargo"
args = ["fmt", "--check"]

[tasks.clippy]
command = "cargo"
args = ["clippy", "--all-targets", "--", "-D", "warnings"]

# 条件任务
[tasks.deploy]
description = "部署到生产"
condition = { env_set = ["DEPLOY_KEY"] }
script = [
    "cargo build --release",
    "./deploy.sh",
]

# 跨平台任务
[tasks.build-win]
condition = { platforms = ["windows"] }
command = "cargo"
args = ["build", "--target", "x86_64-pc-windows-msvc"]

[tasks.build-linux]
condition = { platforms = ["linux"] }
command = "cargo"
args = ["build", "--target", "x86_64-unknown-linux-gnu"]
```

**运行任务**:

```bash
# 运行单个任务
cargo make dev

# 运行 CI 任务
cargo make ci

# 列出所有任务
cargo make --list-all-steps

# 查看任务详情
cargo make --print-steps dev
```

---

### cargo-nextest - 测试运行

**安装**:

```bash
cargo install cargo-nextest --locked
```

#### 基础用法1

```bash
# 运行测试（比 cargo test 快 60%）
cargo nextest run

# 运行特定测试
cargo nextest run test_name

# 运行特定包
cargo nextest run -p my-package

# 显示输出
cargo nextest run --nocapture
```

#### 高级功能

```bash
# 并行度控制
cargo nextest run -j 4

# 重试失败测试
cargo nextest run --retries 3

# 只运行失败的测试
cargo nextest run --failed

# 按时间排序（识别慢测试）
cargo nextest run --final-status-level slow

# 测试覆盖率（配合 llvm-cov）
cargo llvm-cov nextest
```

**配置文件** (`.config/nextest.toml`):

```toml
[profile.default]
retries = 3
slow-timeout = { period = "60s", terminate-after = 2 }

[profile.ci]
retries = 5
fail-fast = true
```

---

## 代码质量

### cargo-clippy - 代码检查

**内置工具**（无需安装）:

```bash
# 基础检查
cargo clippy

# 检查所有目标
cargo clippy --all-targets

# 检查所有 features
cargo clippy --all-features

# 将警告视为错误
cargo clippy -- -D warnings

# 详细输出
cargo clippy -- -D clippy::all -D clippy::pedantic
```

**配置文件** (`clippy.toml`):

```toml
# 允许特定规则
allow-unwrap-in-tests = true

# 认知复杂度阈值
cognitive-complexity-threshold = 30

# 类型复杂度阈值
type-complexity-threshold = 250
```

---

### cargo-fmt - 代码格式化

**内置工具**:

```bash
# 格式化代码
cargo fmt

# 检查格式（CI 用）
cargo fmt -- --check

# 详细输出
cargo fmt -- --verbose
```

**配置文件** (`rustfmt.toml`):

```toml
edition = "2021"
max_width = 100
tab_spaces = 4
use_small_heuristics = "Max"
imports_granularity = "Crate"
group_imports = "StdExternalCrate"
```

---

### cargo-audit - 安全审计

**安装**:

```bash
cargo install cargo-audit
```

#### 基础用法2

```bash
# 检查安全漏洞
cargo audit

# 检查所有依赖（包括 dev）
cargo audit --all-features

# 生成 JSON 报告
cargo audit --json

# 忽略特定漏洞
cargo audit --ignore RUSTSEC-2020-0001
```

#### 修复漏洞

```bash
# 自动修复
cargo audit fix

# 查看可用更新
cargo audit fix --dry-run
```

**实战示例 - CI 集成**:

```yaml
# .github/workflows/security.yml
name: Security Audit
on:
  push:
  schedule:
    - cron: '0 0 * * *'  # 每天检查

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - run: cargo audit
```

---

### cargo-deny - 依赖策略

**安装**:

```bash
cargo install cargo-deny
```

#### 配置文件 (`deny.toml`)

```toml
[advisories]
db-path = "~/.cargo/advisory-db"
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]
deny = [
    "GPL-3.0",
]

[bans]
multiple-versions = "warn"
deny = [
    { name = "openssl" },  # 禁用 openssl
]

[sources]
unknown-registry = "deny"
unknown-git = "warn"
```

**运行检查**:

```bash
# 检查所有策略
cargo deny check

# 只检查许可证
cargo deny check licenses

# 只检查安全公告
cargo deny check advisories

# 只检查被禁用的依赖
cargo deny check bans
```

---

## 开发工具

### cargo-expand - 宏展开

**安装**:

```bash
cargo install cargo-expand
```

#### 基础用法3

```bash
# 展开所有宏
cargo expand

# 展开特定模块
cargo expand module::submodule

# 展开特定函数
cargo expand module::function

# 彩色输出
cargo expand --color always

# 展开测试
cargo expand --test test_name
```

**实战示例**:

```rust
// 原代码
#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
}

// 查看展开后的代码
// cargo expand
```

---

### cargo-tree - 依赖树

**内置工具**:

```bash
# 显示依赖树
cargo tree

# 显示特定包的依赖
cargo tree -p tokio

# 显示反向依赖（谁依赖了这个包）
cargo tree -i serde

# 去重显示
cargo tree --edges normal

# 只显示工作空间成员
cargo tree --workspace

# 显示重复依赖
cargo tree -d
```

---

### cargo-outdated - 依赖检查

**安装**:

```bash
cargo install cargo-outdated
```

#### 基础用法4

```bash
# 检查过时依赖
cargo outdated

# 详细输出
cargo outdated -v

# 只显示根依赖
cargo outdated --root-deps-only

# 检查工作空间
cargo outdated --workspace
```

---

### cargo-llvm-cov - 代码覆盖

**安装**:

```bash
cargo install cargo-llvm-cov
```

#### 基础用法5

```bash
# 生成覆盖率报告
cargo llvm-cov

# HTML 报告
cargo llvm-cov --html

# 打开浏览器查看
cargo llvm-cov --open

# 配合 nextest
cargo llvm-cov nextest

# 输出 lcov 格式（CI 用）
cargo llvm-cov --lcov --output-path lcov.info
```

---

## 性能分析

### cargo-flamegraph - 火焰图

**安装**:

```bash
cargo install flamegraph
```

#### 基础用法6

```bash
# 生成火焰图
cargo flamegraph

# 分析特定二进制
cargo flamegraph --bin my-app

# 采样频率
cargo flamegraph --freq 1000

# 输出文件名
cargo flamegraph -o my-profile.svg
```

---

### cargo-bench - 基准测试

**内置功能**:

```bash
# 运行基准测试
cargo bench

# 运行特定基准
cargo bench bench_name

# 保存结果
cargo bench -- --save-baseline my-baseline

# 对比结果
cargo bench -- --baseline my-baseline
```

---

## 发布工具

### cargo-release - 版本发布

**安装**:

```bash
cargo install cargo-release
```

#### 基础用法7

```bash
# 发布补丁版本（0.1.0 -> 0.1.1）
cargo release patch

# 发布小版本（0.1.0 -> 0.2.0）
cargo release minor

# 发布大版本（0.1.0 -> 1.0.0）
cargo release major

# 预发布版本
cargo release --pre-release alpha

# 干运行（不实际发布）
cargo release patch --dry-run
```

---

### cargo-dist - 分发构建

**安装**:

```bash
cargo install cargo-dist
```

#### 基础用法8

```bash
# 初始化配置
cargo dist init

# 构建分发包
cargo dist build

# 生成 CI 配置
cargo dist generate-ci github
```

---

## 最佳实践

### 1. 开发工作流

**描述**: 高效的日常开发流程。

```bash
# 开发时持续运行
cargo watch -x check -x test

# 提交前检查
cargo fmt && cargo clippy && cargo test

# 发布前完整检查
cargo make ci  # 使用 cargo-make 定义的 CI 任务
```

### 2. CI/CD 集成

**描述**: 在 CI 中使用工具。

```yaml
# .github/workflows/ci.yml
jobs:
  test:
    steps:
      - run: cargo fmt -- --check
      - run: cargo clippy -- -D warnings
      - run: cargo nextest run
      - run: cargo llvm-cov --lcov --output-path lcov.info
      - run: cargo audit
```

### 3. 定期维护

**描述**: 定期更新和审计。

```bash
# 每周一次
cargo outdated
cargo audit

# 每月一次
cargo upgrade --incompatible --dry-run
```

### 4. 工具组合

**描述**: 组合使用多个工具。

```bash
# 完整质量检查
cargo fmt --check && \
  cargo clippy --all-targets -- -D warnings && \
  cargo nextest run && \
  cargo audit && \
  cargo deny check
```

### 5. 性能分析流程

**描述**: 系统化的性能分析。

```bash
# 1. 基准测试
cargo bench --bench my_bench

# 2. 生成火焰图
cargo flamegraph --bin my-app

# 3. 分析瓶颈
# 查看 flamegraph.svg

# 4. 优化后对比
cargo bench -- --baseline before
```

---

## 常见陷阱

### ⚠️ 陷阱1: 忘记更新工具

**问题描述**: 使用过时的工具版本。

❌ **错误做法**:

```bash
# 安装后从不更新
cargo install cargo-audit  # 2020年安装
```

✅ **正确做法**:

```bash
# 定期更新
cargo install cargo-update
cargo install-update -a

# 或单独更新
cargo install cargo-audit --force
```

### ⚠️ 陷阱2: 不配置 clippy

**问题描述**: 使用默认配置，错过重要警告。

❌ **错误做法**:

```bash
cargo clippy  # 只显示基础警告
```

✅ **正确做法**:

```bash
# 使用严格规则
cargo clippy --all-targets -- -D warnings -D clippy::all

# 或配置 clippy.toml
```

### ⚠️ 陷阱3: 忽略安全审计

**问题描述**: 不定期检查安全漏洞。

❌ **错误做法**:

```bash
# 从不运行 audit
```

✅ **正确做法**:

```bash
# CI 中添加
cargo audit

# 或使用 GitHub Actions
uses: actions-rs/audit-check@v1
```

### ⚠️ 陷阱4: 手动管理依赖

**问题描述**: 手工编辑 Cargo.toml。

❌ **错误做法**:

```toml
# 手工添加依赖
[dependencies]
tokio = "1.35"  # 可能输错版本
```

✅ **正确做法**:

```bash
# 使用 cargo-edit
cargo add tokio  # 自动添加最新版本
```

---

## 参考资源

### 官方文档

- 📚 [Cargo Book](https://doc.rust-lang.org/cargo/)
- 📚 [Rustup Book](https://rust-lang.github.io/rustup/)
- 📚 [Clippy Documentation](https://doc.rust-lang.org/clippy/)

### 工具仓库

- 💻 [cargo-edit](https://github.com/killercup/cargo-edit)
- 💻 [cargo-watch](https://github.com/watchexec/cargo-watch)
- 💻 [cargo-nextest](https://github.com/nextest-rs/nextest)
- 💻 [cargo-deny](https://github.com/EmbarkStudios/cargo-deny)
- 💻 [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov)

### 实用文章

- 📖 [Awesome Rust Tools](https://github.com/rust-unofficial/awesome-rust#development-tools)
- 📖 [Rust Performance Book](https://nnethercote.github.io/perf-book/)

### 相关文档

- 🔗 [CLI 工具开发](../../03_application_dev/cli_tools/README.md)
- 🔗 [测试工具](../../03_application_dev/testing/README.md)
- 🔗 [日志系统](../logging/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
