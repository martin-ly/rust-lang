# 代码分析（Code Analysis）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [📊 目录](#-目录)
- [🎯 目的](#-目的)
  - [核心价值](#核心价值)
- [📚 核心工具](#-核心工具)
  - [1. 静态分析（Static Analysis）](#1-静态分析static-analysis)
  - [2. 动态分析（Dynamic Analysis）](#2-动态分析dynamic-analysis)
  - [3. 安全分析（Security Analysis）](#3-安全分析security-analysis)
  - [4. 依赖分析（Dependency Analysis）](#4-依赖分析dependency-analysis)
- [💻 常用命令](#-常用命令)
  - [静态分析](#静态分析)
  - [动态分析](#动态分析)
  - [安全分析](#安全分析)
  - [依赖分析](#依赖分析)
- [🔗 相关条目](#-相关条目)
- [🧭 导航](#-导航)

## 🎯 目的

本模块统一静态/动态分析工具入口，支撑质量与安全保障。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **代码分析**: 专注于 Rust 代码分析最佳实践
- **最佳实践**: 基于 Rust 社区最新代码分析实践
- **完整覆盖**: 涵盖静态分析、动态分析、安全分析、依赖分析等核心主题
- **易于理解**: 提供详细的代码分析说明和代码示例

## 📚 核心工具

### 1. 静态分析（Static Analysis）

**推荐工具**: `clippy`, `cargo-udeps`, `cargo-deny`, `rust-analyzer`

- **代码检查**: `clippy`、代码风格检查
- **未使用依赖**: `cargo udeps`、依赖清理
- **依赖审计**: `cargo deny`、依赖安全检查
- **代码质量**: 代码质量分析、代码复杂度分析

**相关资源**:

- [Clippy 文档](https://rust-lang.github.io/rust-clippy/)
- [cargo-udeps 文档](https://docs.rs/cargo-udeps/)
- [cargo-deny 文档](https://docs.rs/cargo-deny/)
- [rust-analyzer 文档](https://rust-analyzer.github.io/)

### 2. 动态分析（Dynamic Analysis）

**推荐工具**: `miri`, `sanitizers`, `valgrind`, `perf`

- **MIRI 解释器**: `miri`、未定义行为检测
- **Sanitizers**: AddressSanitizer、ThreadSanitizer、LeakSanitizer
- **内存分析**: Valgrind、内存泄漏检测
- **性能分析**: perf、性能剖析

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [Sanitizers 文档](https://doc.rust-lang.org/nightly/unstable-book/language-features/sanitizer.html)
- [Valgrind 文档](https://valgrind.org/)
- [perf 文档](https://perf.wiki.kernel.org/)

### 3. 安全分析（Security Analysis）

**推荐工具**: `cargo-audit`, `cargo-geiger`, `cargo-deny`, `cargo-crev`

- **漏洞扫描**: `cargo audit`、依赖漏洞检测
- **不安全代码**: `cargo geiger`、unsafe 代码检测
- **依赖审计**: `cargo deny`、依赖安全检查
- **代码审查**: `cargo-crev`、代码审查工具

**相关资源**:

- [cargo-audit 文档](https://docs.rs/cargo-audit/)
- [cargo-geiger 文档](https://docs.rs/cargo-geiger/)
- [cargo-deny 文档](https://docs.rs/cargo-deny/)
- [cargo-crev 文档](https://github.com/crev-dev/cargo-crev)

### 4. 依赖分析（Dependency Analysis）

**推荐工具**: `cargo-tree`, `cargo-udeps`, `cargo-deny`, `cargo-outdated`

- **依赖树**: `cargo tree`、依赖关系可视化
- **未使用依赖**: `cargo udeps`、依赖清理
- **过期依赖**: `cargo outdated`、依赖更新检查
- **依赖审计**: `cargo deny`、依赖安全检查

**相关资源**:

- [cargo-tree 文档](https://docs.rs/cargo-tree/)
- [cargo-udeps 文档](https://docs.rs/cargo-udeps/)
- [cargo-outdated 文档](https://docs.rs/cargo-outdated/)
- [cargo-deny 文档](https://docs.rs/cargo-deny/)

## 💻 常用命令

### 静态分析

```bash
# Clippy 代码检查
cargo clippy -- -D warnings

# 未使用依赖检查
cargo udeps

# 依赖审计
cargo deny check
```

### 动态分析

```bash
# MIRI 解释器
cargo miri test

# Sanitizers
RUSTFLAGS="-Z sanitizer=address" cargo test

# 内存分析
valgrind --leak-check=full ./target/release/app
```

### 安全分析

```bash
# 漏洞扫描
cargo audit

# 不安全代码检测
cargo geiger

# 依赖审计
cargo deny check advisories
```

### 依赖分析

```bash
# 依赖树查看
cargo tree

# 过期依赖检查
cargo outdated

# 依赖清理
cargo udeps
```

---

## 🔗 相关条目

- **形式化工具**: [`../05_formal/00_index.md`](../05_formal/00_index.md)
- **调试**: [`../09_debugging/00_index.md`](../09_debugging/00_index.md)
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

## 🧭 导航

- **返回工具链**: [`../00_index.md`](../00_index.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
