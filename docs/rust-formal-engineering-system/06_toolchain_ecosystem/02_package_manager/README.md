# 包管理器理论

> **分级**: [B]
> **创建日期**: 2026-02-20
> **最后更新**: 2026-06-25（已按 Rust 1.96.0 复审）
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **概念说明**: Cargo 是 Rust 的包管理器和构建系统，负责依赖解析、版本管理、特性标志（feature flags）和 workspace 管理。形式化上，包管理涉及依赖图的语义版本约束求解和特性组合的完备性验证。
> 内容已整合至： 02_cargo_workspace_guide.md

[返回主索引](../../00_master_index.md) | [返回工具链索引](../README.md)

---

## Cargo 核心概念 {#cargo-核心概念}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 依赖管理 {#依赖管理-1}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"

[dependencies]
# 语义化版本 {#语义化版本}

> **Bloom 层级**: L5-L6 (分析/评价/创造)
serde = "1.0"           # >= 1.0.0, < 2.0.0
serde = "~1.0.150"      # >= 1.0.150, < 1.1.0
serde = "^1.0"          # >= 1.0.0, < 2.0.0
serde = "=1.0.150"      # 精确版本 1.0.150
serde = ">=1.0, <1.5"   # 范围

# 特性启用 {#特性启用}
serde = { version = "1.0", features = ["derive"] }
serde = { version = "1.0", default-features = false, features = ["alloc"] }

# 可选依赖 {#可选依赖}
tracing = { version = "0.1", optional = true }

# 平台特定依赖 {#平台特定依赖}
[target.'cfg(unix)'.dependencies]
nix = "0.27"

[target.'cfg(windows)'.dependencies]
windows-sys = "0.52"

# 开发依赖 {#开发依赖}
[dev-dependencies]
mockall = "0.12"
tokio-test = "0.4"

# 构建依赖 {#构建依赖}
[build-dependencies]
cc = "1.0"
```
### 工作空间 {#工作空间-1}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
# 根 Cargo.toml {#根-cargotoml}
[workspace]
members = ["crate-a", "crate-b", "crate-c"]
resolver = "2"

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.35", features = ["full"] }
anyhow = "1.0"

[workspace.package]
version = "0.1.0"
edition = "2024"
authors = ["Team"]
```
```toml
# crate-a/Cargo.toml {#crate-acargotoml}
[package]
name = "crate-a"
version.workspace = true
edition.workspace = true
authors.workspace = true

[dependencies]
serde = { workspace = true }
```
### 特性管理 {#特性管理}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```toml
[features]
# 默认特性 {#默认特性}
default = ["std", "derive"]

# 独立特性 {#独立特性}
std = []
alloc = []
serde = ["dep:serde"]
async = ["tokio", "tokio/rt"]

# 完整特性 {#完整特性}
full = ["std", "serde", "async"]

# 内部特性 {#内部特性}
__internal = []
```
### Cargo 命令 {#cargo-命令}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```bash
# 项目管理 {#项目管理}
cargo new project-name
cargo init
cargo new --lib lib-name

# 构建 {#构建}
cargo build
cargo build --release
cargo build --all-targets
cargo check          # 快速检查
cargo fix            # 自动修复

# 测试 {#测试}
cargo test
cargo test --doc
cargo test --lib
cargo test <filter>

# 依赖管理 {#依赖管理-1}
cargo add <crate>
cargo add --dev <crate>
cargo add --features <feature> <crate>
cargo update
cargo tree
cargo tree -d        # 显示重复依赖

# 发布 {#发布}
cargo publish --dry-run
cargo publish
cargo yank --version x.y.z

# 工作空间 {#工作空间-1}
cargo build --workspace
cargo test --workspace
cargo publish --workspace
```
### 语义版本规范 {#语义版本规范}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```rust
// 语义化版本: MAJOR.MINOR.PATCH
// MAJOR: 破坏性变更
// MINOR: 向后兼容的功能添加
// PATCH: 向后兼容的问题修复

// Cargo.toml 版本约束:
// "1.0.0"     = "^1.0.0"  (>=1.0.0, <2.0.0)
// "^1.0.0"    兼容 1.x.x
// "~1.0.0"    兼容 1.0.x
// ">=1.0.0"   1.0.0 及以上
// ">=1.0.0, <2.0.0"  范围
// "=1.0.0"    精确版本
// "*"         任何版本
```
### 自定义配置 {#自定义配置}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```toml
# .cargo/config.toml {#cargoconfigtoml}
[build]
target = "x86_64-unknown-linux-gnu"
rustflags = ["-C", "link-arg=-fuse-ld=lld"]

[profile.dev]
opt-level = 1
incremental = true

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"
strip = true

[registries.crates-io]
protocol = "sparse"

[net]
git-fetch-with-cli = true
retry = 3
```
### 虚拟工作空间示例 {#虚拟工作空间示例}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```toml
# 虚拟工作空间根 Cargo.toml {#虚拟工作空间根-cargotoml}
[workspace]
members = [
    "crates/core",
    "crates/utils",
    "crates/cli",
    "crates/api",
]
resolver = "2"

[workspace.package]
version = "1.0.0"
edition = "2024"
rust-version = "1.94"
authors = ["Your Name <you@example.com>"]
license = "MIT OR Apache-2.0"
repository = "https://github.com/username/project"

[workspace.dependencies]
# 核心依赖 {#核心依赖}
tokio = { version = "1.35", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
tracing = "0.1"

# 本地 crate {#本地-crate}
core = { path = "crates/core" }
utils = { path = "crates/utils" }
```
---

## 形式化方法 {#形式化方法}

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../research_notes/formal_methods/README.md](../../../../archive/research_notes_2026_06_25/formal_methods/README.md) |
| 类型系统形式化 | 类型理论数学定义 | [../../../research_notes/type_theory/10_type_system_foundations.md](../../../../archive/research_notes_2026_06_25/type_theory/10_type_system_foundations.md) |
| Send/Sync 形式化 | 线程安全形式化定义 | [../../../research_notes/formal_methods/10_send_sync_formalization.md](../../../../archive/research_notes_2026_06_25/formal_methods/10_send_sync_formalization.md) |
| 证明索引 | 形式化证明集合 | [../../../research_notes/10_proof_index.md](../../../../archive/research_notes_2026_06_25/10_proof_index.md) |

## 相关研究笔记 {#相关研究笔记}

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Cargo 工作空间指南 | 完整工作空间配置 | ../../../06_toolchain/02_cargo_workspace_guide.md |
| 研究方法论 | 研究方法指南 | [../../../research_notes/10_research_methodology.md](../../../../archive/research_notes_2026_06_25/10_research_methodology.md) |
| 最佳实践 | 工程最佳实践 | [../../../research_notes/10_best_practices.md](../../../../archive/research_notes_2026_06_25/10_best_practices.md) |
| 工具指南 | 验证工具使用 | [../../../research_notes/10_tools_guide.md](../../../../archive/research_notes_2026_06_25/10_tools_guide.md) |
| 质量检查清单 | 代码质量检查 | [../../../research_notes/10_quality_checklist.md](../../../../archive/research_notes_2026_06_25/10_quality_checklist.md) |

---

[返回主索引](../../00_master_index.md) |
[返回工具链索引](../README.md) |
[编译器理论](../01_compiler/README.md) |
[构建工具理论](../03_build_tools/README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-25（已按 Rust 1.96.0 复审）
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Wikipedia - Model Checking](https://en.wikipedia.org/wiki/Model_Checking)**
> **来源: [ACM - Formal Verification Survey](https://dl.acm.org/)**
> **来源: [IEEE - Formal Specification Standards](https://standards.ieee.org/)**
> **来源: [POPL - Automated Verification](https://www.sigplan.org/Conferences/POPL/)**
> **来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)**
> **来源: [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
