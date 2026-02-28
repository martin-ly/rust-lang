# 📦 Cargo 速查卡 {#-cargo-速查卡}

> **快速参考** | [Cargo 官方文档](https://doc.rust-lang.org/cargo/) | [代码示例](../../../crates/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [📦 Cargo 速查卡 {#-cargo-速查卡}](#-cargo-速查卡--cargo-速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🆕 项目创建 {#-项目创建}](#-项目创建--项目创建)
    - [创建新项目](#创建新项目)
    - [项目结构](#项目结构)
  - [🔨 构建命令 {#-构建命令}](#-构建命令--构建命令)
    - [基本构建](#基本构建)
    - [指定目标](#指定目标)
    - [特性标志](#特性标志)
    - [并行和优化](#并行和优化)
  - [🧪 测试命令 {#-测试命令}](#-测试命令--测试命令)
    - [基本测试](#基本测试)
    - [测试选项](#测试选项)
    - [基准测试](#基准测试)
  - [📚 依赖管理 {#-依赖管理}](#-依赖管理--依赖管理)
    - [添加依赖](#添加依赖)
    - [更新依赖](#更新依赖)
    - [查看依赖](#查看依赖)
    - [依赖检查](#依赖检查)
  - [📤 发布命令 {#-发布命令}](#-发布命令--发布命令)
    - [发布准备](#发布准备)
    - [版本管理](#版本管理)
  - [🏢 工作空间 {#-工作空间}](#-工作空间--工作空间)
    - [工作空间命令](#工作空间命令)
    - [工作空间结构](#工作空间结构)
  - [⚙️ 配置文件 {#️-配置文件}](#️-配置文件-️-配置文件)
    - [Cargo.toml 结构](#cargotoml-结构)
    - [构建配置](#构建配置)
    - [特性配置](#特性配置)
  - [🛠️ 常用工具 {#️-常用工具}](#️-常用工具-️-常用工具)
    - [代码格式化](#代码格式化)
    - [代码检查](#代码检查)
    - [文档生成](#文档生成)
    - [代码覆盖率](#代码覆盖率)
    - [宏展开](#宏展开)
  - [🎯 常用别名 {#-常用别名}](#-常用别名--常用别名)
    - [配置别名](#配置别名)
    - [使用别名](#使用别名)
  - [📊 常用工作流 {#-常用工作流}](#-常用工作流--常用工作流)
    - [开发工作流](#开发工作流)
    - [CI/CD 工作流](#cicd-工作流)
    - [发布工作流](#发布工作流)
  - [🔍 故障排查 {#-故障排查}](#-故障排查--故障排查)
    - [清理和重建](#清理和重建)
    - [依赖问题](#依赖问题)
    - [构建问题](#构建问题)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 依赖版本冲突](#反例-1-依赖版本冲突)
    - [反例 2: 将 dev-dependencies 用于生产](#反例-2-将-dev-dependencies-用于生产)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 多平台库开发](#场景-1-多平台库开发)
    - [场景 2: 工作空间发布管理](#场景-2-工作空间发布管理)
    - [场景 3: 性能优化构建配置](#场景-3-性能优化构建配置)
  - [📐 形式化方法链接 {#-形式化方法链接}](#-形式化方法链接--形式化方法链接)
    - [理论基础](#理论基础)
    - [形式化定理](#形式化定理)
    - [相关速查卡](#相关速查卡)

---

## 🆕 项目创建 {#-项目创建}

### 创建新项目

```bash
# 创建二进制项目
cargo new my_project

# 创建库项目
cargo new --lib my_lib

# 在当前目录创建
cargo init

# 创建库项目（当前目录）
cargo init --lib
```

### 项目结构

```text
my_project/
├── Cargo.toml      # 项目配置
├── Cargo.lock      # 依赖锁定（自动生成）
└── src/
    └── main.rs     # 主文件（二进制）或 lib.rs（库）
```

---

## 🔨 构建命令 {#-构建命令}

### 基本构建

```bash
# 开发构建
cargo build

# 发布构建（优化）
cargo build --release

# 检查代码（不生成二进制）
cargo check

# 清理构建产物
cargo clean
```

### 指定目标

```bash
# 构建特定包
cargo build -p package_name

# 构建所有目标
cargo build --all-targets

# 构建二进制
cargo build --bin my_bin

# 构建示例
cargo build --example my_example

# 交叉编译
cargo build --target x86_64-unknown-linux-gnu
cargo build --target wasm32-unknown-unknown
```

### 特性标志

```bash
# 启用特定特性
cargo build --features "async,serde"

# 启用所有特性
cargo build --all-features

# 不使用默认特性
cargo build --no-default-features
```

### 并行和优化

```bash
# 指定并行任务数
cargo build -j 8

# 详细输出
cargo build --verbose
cargo build -vv  # 更详细

# 显示编译命令
cargo build --verbose
```

---

## 🧪 测试命令 {#-测试命令}

### 基本测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 运行匹配模式的测试
cargo test add

# 显示测试输出
cargo test -- --nocapture

# 单线程运行（调试用）
cargo test -- --test-threads=1
```

### 测试选项

```bash
# 运行被忽略的测试
cargo test -- --ignored

# 运行所有测试（包括被忽略的）
cargo test -- --include-ignored

# 只运行单元测试
cargo test --lib

# 只运行集成测试
cargo test --test integration_test

# 运行文档测试
cargo test --doc
```

### 基准测试

```bash
# 运行基准测试
cargo bench

# 运行特定基准测试
cargo bench --bench my_benchmark

# 运行特定测试
cargo bench --bench my_benchmark test_name
```

---

## 📚 依赖管理 {#-依赖管理}

### 添加依赖

```bash
# 添加依赖（编辑 Cargo.toml）
cargo add serde

# 添加带特性的依赖
cargo add serde --features derive

# 添加开发依赖
cargo add --dev criterion

# 添加构建依赖
cargo add --build serde_codegen

# 添加特定版本
cargo add serde@1.0
```

### 更新依赖

```bash
# 更新所有依赖
cargo update

# 更新特定依赖
cargo update -p serde

# 精确版本更新
cargo update -p serde --precise 1.0.100
```

### 查看依赖

```bash
# 查看依赖树
cargo tree

# 查看特定包的依赖
cargo tree -p package_name

# 显示重复依赖
cargo tree --duplicates

# 限制深度
cargo tree --depth 2

# 显示特性
cargo tree -f "{p} {f}"
```

### 依赖检查

```bash
# 检查过时依赖（需要 cargo-outdated）
cargo install cargo-outdated
cargo outdated

# 安全审计（需要 cargo-audit）
cargo install cargo-audit
cargo audit

# 自动修复安全问题
cargo audit fix
```

---

## 📤 发布命令 {#-发布命令}

### 发布准备

```bash
# 检查发布准备
cargo publish --dry-run

# 发布到 crates.io
cargo publish

# 发布特定包
cargo publish -p package_name

# 发布时允许脏工作目录
cargo publish --allow-dirty
```

### 版本管理

```bash
# 使用 cargo-release（推荐）
cargo install cargo-release

# 发布所有包
cargo release --workspace

# 预览发布
cargo release --workspace --dry-run
```

---

## 🏢 工作空间 {#-工作空间}

### 工作空间命令

```bash
# 构建所有成员
cargo build --workspace

# 构建特定成员
cargo build -p member1 -p member2

# 测试所有成员
cargo test --workspace

# 检查所有成员
cargo check --workspace
```

### 工作空间结构

```toml
# Cargo.toml（工作空间根）
[workspace]
members = [
    "crates/member1",
    "crates/member2",
]

[workspace.dependencies]
serde = "1.0"
tokio = { version = "1.0", features = ["full"] }
```

---

## ⚙️ 配置文件 {#️-配置文件}

### Cargo.toml 结构

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"
rust-version = "1.93"

[dependencies]
serde = "1.0"
tokio = { version = "1.0", features = ["full"] }

[dev-dependencies]
criterion = "0.5"

[build-dependencies]
serde_codegen = "1.0"

[features]
default = ["std"]
async = ["tokio"]
```

### 构建配置

```toml
[profile.dev]
opt-level = 0
debug = true
incremental = true

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true
panic = "abort"
```

### 特性配置

```toml
[features]
default = ["std", "async"]
std = []
async = ["tokio"]
serde = ["dep:serde"]
```

---

## 🛠️ 常用工具 {#️-常用工具}

### 代码格式化

```bash
# 格式化代码
cargo fmt

# 检查格式
cargo fmt -- --check

# 格式化所有文件
cargo fmt --all
```

### 代码检查

```bash
# 运行 Clippy
cargo clippy

# 所有目标
cargo clippy --all-targets

# 所有特性
cargo clippy --all-features

# 修复建议
cargo clippy --fix
```

### 文档生成

```bash
# 生成文档
cargo doc

# 打开文档
cargo doc --open

# 生成所有成员的文档
cargo doc --workspace

# 不构建依赖文档
cargo doc --no-deps
```

### 代码覆盖率

```bash
# 安装 tarpaulin
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --out Html

# 输出到终端
cargo tarpaulin --out Stdout

# 设置覆盖率阈值
cargo tarpaulin --fail-under 80
```

### 宏展开

```bash
# 安装 cargo-expand
cargo install cargo-expand

# 展开宏
cargo expand

# 展开特定项
cargo expand my_function
```

---

## 🎯 常用别名 {#-常用别名}

### 配置别名

```toml
# .cargo/config.toml
[alias]
# 测试别名
test-all = "test --all"
test-quick = "test --lib"

# 构建别名
build-release = "build --release"
build-all = "build --all"

# 检查别名
check-all = "check --all"

# Clippy 别名
clippy-all = "clippy --all-targets --all-features"
clippy-pedantic = "clippy --all -- -W clippy::pedantic"

# 格式化别名
fmt-check = "fmt --all -- --check"
```

### 使用别名

```bash
# 使用自定义别名
cargo test-all
cargo build-release
cargo clippy-all
```

---

## 📊 常用工作流 {#-常用工作流}

### 开发工作流

```bash
# 1. 创建项目
cargo new my_project
cd my_project

# 2. 添加依赖
cargo add serde --features derive

# 3. 开发循环
cargo check          # 快速检查
cargo test           # 运行测试
cargo clippy         # 代码检查
cargo fmt            # 格式化

# 4. 构建发布版本
cargo build --release
```

### CI/CD 工作流

```bash
# 检查
cargo check --all-targets

# 测试
cargo test --all-features

# 格式化检查
cargo fmt --all -- --check

# Clippy 检查
cargo clippy --all-targets --all-features -- -D warnings

# 构建
cargo build --release

# 文档 {#-相关文档}
cargo doc --no-deps
```

### 发布工作流

```bash
# 1. 更新版本
# 编辑 Cargo.toml version

# 2. 检查
cargo check --release
cargo test --release

# 3. 发布前检查
cargo publish --dry-run

# 4. 发布
cargo publish
```

---

## 🔍 故障排查 {#-故障排查}

### 清理和重建

```bash
# 清理构建缓存
cargo clean

# 清理特定包
cargo clean -p package_name

# 完全清理
rm -rf target/
cargo build
```

### 依赖问题

```bash
# 查看依赖冲突
cargo tree --duplicates

# 更新依赖
cargo update

# 检查依赖版本
cargo tree -p problematic_crate
```

### 构建问题

```bash
# 详细输出
cargo build -vv

# 检查特性
cargo check --features "feature1,feature2"

# 检查目标平台
cargo build --target <target>
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: 依赖版本冲突

**错误示例**:

```toml
[dependencies]
tokio = "1.0"   # crate A
other = "2.0"  # 内部依赖 tokio 1.5  ❌ 可能冲突
```

**原因**: 不同 crate 依赖同一库的不同版本，导致重复编译或行为不一致。

**修正**: 使用 `[workspace.dependencies]` 统一版本，或 `cargo tree` 检查。

---

### 反例 2: 将 dev-dependencies 用于生产

**错误示例**:

```toml
[dependencies]
tempfile = "3.0"  # 若仅测试用，不应放这里
```

**原因**: 生产构建会包含不需要的依赖。

**修正**: 测试专用依赖放 `[dev-dependencies]`。

---

## 📚 相关文档

- [工具链文档索引](../../06_toolchain/README.md)
- [Cargo 工作空间指南](../../06_toolchain/02_cargo_workspace_guide.md)
- [Cargo 包管理与工作空间索引（项目内）](../../../crates/c02_type_system/docs/cargo_package_management/00_INDEX.md)

## 🧩 相关示例代码 {#-相关示例代码}

这些示例可帮助你把 Cargo 的核心命令串成完整工作流：

- **Cargo 项目模板（文档示例）**：`crates/c02_type_system/docs/cargo_package_management/examples/`
  - [简单 CLI 项目](../../../crates/c02_type_system/docs/cargo_package_management/examples/01_simple_cli.md)
  - [带 features 的库](../../../crates/c02_type_system/docs/cargo_package_management/examples/02_library_with_features.md)
  - [Workspace 项目](../../../crates/c02_type_system/docs/cargo_package_management/examples/03_workspace_project.md)
- **运行 examples（真实 workspace 例子）**：
  - `cargo run -p c03_control_fn --example control_flow_example`
  - `cargo run -p c05_threads --example message_passing_demo`
  - `cargo run -p c08_algorithms --example sorting_algorithms_demo`
  - `cargo run -p c10_networks --example tcp_echo_server`
  - `cargo run -p c12_wasm --example 02_string_operations`

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Cargo 官方文档](https://doc.rust-lang.org/cargo/)
- [Cargo Book](https://doc.rust-lang.org/cargo/book/)
- [Cargo 参考手册](https://doc.rust-lang.org/cargo/reference/)

### 项目内部文档

- [Cargo 包管理完整文档](../../../crates/c02_type_system/docs/cargo_package_management/)
- [工具链文档](../../06_toolchain/README.md)
- [Cargo 工作空间指南](../../06_toolchain/02_cargo_workspace_guide.md)

## 🎯 使用场景 {#-使用场景}

### 场景 1: 多平台库开发

```toml
# Cargo.toml - 跨平台配置
[package]
name = "cross-platform-lib"
version = "0.1.0"
edition = "2024"

[dependencies]
# 通用依赖
cfg-if = "1.0"

[target.'cfg(windows)'.dependencies]
winapi = { version = "0.3", features = ["fileapi"] }

[target.'cfg(unix)'.dependencies]
libc = "0.2"

[target.'cfg(target_arch = "wasm32")'.dependencies]
wasm-bindgen = "0.2"
js-sys = "0.3"

[features]
default = ["std"]
std = []
no_std = ["alloc"]
alloc = []
```

### 场景 2: 工作空间发布管理

```toml
# Cargo.toml (workspace root)
[workspace]
members = ["crates/*"]
resolver = "3"

[workspace.package]
version = "0.1.0"
edition = "2024"
authors = ["Team <team@example.com>"]
license = "MIT OR Apache-2.0"
rust-version = "1.93"

[workspace.dependencies]
# 内部依赖
core-lib = { path = "crates/core-lib", version = "0.1.0" }
utils = { path = "crates/utils", version = "0.1.0" }

# 外部依赖
tokio = { version = "1.40", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }

# 开发依赖
criterion = "0.5"
```

```bash
# 发布流程
# 1. 更新版本
$ cargo set-version --workspace 0.2.0

# 2. 验证构建
$ cargo build --workspace --all-targets

# 3. 运行测试
$ cargo test --workspace

# 4. 检查发布
$ cargo publish --workspace --dry-run

# 5. 发布 (按依赖顺序)
$ cargo publish -p utils
$ cargo publish -p core-lib
$ cargo publish -p app
```

### 场景 3: 性能优化构建配置

```toml
# Cargo.toml - 性能优化
[package]
name = "high-perf-app"

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true

# 针对特定 CPU 优化
[profile.release-native]
inherits = "release"
rustflags = ["-C", "target-cpu=native"]

# 最小化二进制大小
[profile.size-optimized]
inherits = "release"
opt-level = "z"
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

```bash
# 构建优化版本
$ cargo build --profile release-native

# 构建最小化版本
$ cargo build --profile size-optimized

# 分析二进制大小
$ cargo bloat --release
```

---

## 📐 形式化方法链接 {#-形式化方法链接}

### 理论基础

| 概念 | 形式化文档 | 描述 |
| :--- | :--- | :--- |
| **类型系统** | [type_system_foundations](../../research_notes/type_theory/type_system_foundations.md) | 依赖版本解析的类型理论 |
| **类型构造** | [construction_capability](../../research_notes/type_theory/construction_capability.md) | 包组合的类型构造能力 |
| **Trait 系统** | [trait_system_formalization](../../research_notes/type_theory/trait_system_formalization.md) | 特征组合的兼容性 |

### 形式化定理

**定理 CARGO-T1（依赖解析正确性）**: 若 Cargo.toml 中的依赖约束可满足，则存在唯一的版本选择满足所有约束。

*证明*: 由 [construction_capability](../../research_notes/type_theory/construction_capability.md) 定理 TCON-T1，依赖版本选择作为类型构造问题，满足确定性判定。∎

---

### 相关速查卡

- [模块系统速查卡](./modules_cheatsheet.md) - Crate 和模块
- [测试速查卡](./testing_cheatsheet.md) - Cargo 测试命令
- [类型系统速查卡](./type_system.md) - 依赖类型管理
- [反模式速查卡](./ANTI_PATTERN_TEMPLATE.md) - Cargo 配置反模式

---

**最后更新**: 2026-02-20
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.1 更新完成**

🎯 **掌握 Cargo，高效管理项目！**
