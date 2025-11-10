# Miri 索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [Miri 索引](#miri-索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心功能](#-核心功能)
    - [1. 未定义行为检测（Undefined Behavior Detection）](#1-未定义行为检测undefined-behavior-detection)
    - [2. 借用规则检查（Borrow Checker）](#2-借用规则检查borrow-checker)
    - [3. 内存安全检查（Memory Safety）](#3-内存安全检查memory-safety)
    - [4. 并发安全检查（Concurrency Safety）](#4-并发安全检查concurrency-safety)
  - [💻 常用命令](#-常用命令)
    - [基础命令](#基础命令)
    - [高级选项](#高级选项)
  - [🚀 快速开始](#-快速开始)
  - [🔄 CI 集成建议](#-ci-集成建议)
    - [GitHub Actions](#github-actions)
    - [建议策略](#建议策略)
  - [✨ 最佳实践](#-最佳实践)
    - [开发流程](#开发流程)
    - [配置策略](#配置策略)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块使用 Miri 进行未定义行为检测与借用规则的运行时检查，提供全面的内存安全和并发安全检查。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **内存安全**: 专注于 Rust 内存安全检查最佳实践
- **最佳实践**: 基于 Rust 社区最新 Miri 实践
- **完整覆盖**: 涵盖未定义行为检测、借用规则检查、内存安全、并发安全等核心主题
- **易于理解**: 提供详细的 Miri 使用说明和代码示例

## 📚 核心功能

### 1. 未定义行为检测（Undefined Behavior Detection）

**推荐工具**: `miri`, `sanitizers`

- **未定义行为**: 未定义行为检测、UB 报告
- **内存访问**: 内存访问检查、越界访问检测
- **类型安全**: 类型安全检查、类型转换检查
- **指针安全**: 指针安全检查、悬垂指针检测（Rust 1.91 增强）

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [Miri 用户指南](https://github.com/rust-lang/miri/blob/master/docs/user-guide.md)
- [Sanitizers 文档](https://doc.rust-lang.org/nightly/unstable-book/language-features/sanitizer.html)

### 2. 借用规则检查（Borrow Checker）

**推荐工具**: `miri`, `rustc`

- **借用检查**: 借用规则检查、生命周期检查
- **数据竞争**: 数据竞争检测、并发安全检查
- **内存泄漏**: 内存泄漏检测、资源泄漏检测
- **借用冲突**: 借用冲突检测、借用规则违反

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)

### 3. 内存安全检查（Memory Safety）

**推荐工具**: `miri`, `valgrind`, `sanitizers`

- **内存安全**: 内存安全检查、内存错误检测
- **缓冲区溢出**: 缓冲区溢出检测、边界检查
- **内存泄漏**: 内存泄漏检测、资源泄漏检测
- **悬垂指针**: 悬垂指针检测（Rust 1.91 新增警告）

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [valgrind 文档](https://valgrind.org/)
- [Rust 1.91 悬空指针警告](../01_theoretical_foundations/02_memory_safety/03_dangling_pointer_warnings_rust_1_91.md)

### 4. 并发安全检查（Concurrency Safety）

**推荐工具**: `miri`, `sanitizers`, `loom`

- **数据竞争**: 数据竞争检测、并发安全检查
- **死锁检测**: 死锁检测、锁顺序检查
- **原子操作**: 原子操作检查、内存顺序检查
- **并发模型**: 并发模型验证、并发模式检查

**相关资源**:

- [Miri 文档](https://github.com/rust-lang/miri)
- [loom 文档](https://docs.rs/loom/)
- [ThreadSanitizer 文档](https://doc.rust-lang.org/nightly/unstable-book/language-features/sanitizer.html)

## 💻 常用命令

### 基础命令

```bash
# 运行测试
cargo +nightly miri test

# 单用例测试
cargo +nightly miri test -p <crate> <path::to::test>

# 环境变量配置
MIRIFLAGS=-Zmiri-strict-provenance cargo +nightly miri test
```

### 高级选项

```bash
# 启用严格来源检查
MIRIFLAGS=-Zmiri-strict-provenance cargo +nightly miri test

# 启用泄漏检查
MIRIFLAGS=-Zmiri-check-leaks cargo +nightly miri test

# 启用未初始化内存检查
MIRIFLAGS=-Zmiri-check-uninit cargo +nightly miri test
```

## 🚀 快速开始

```bash
# 安装 nightly 工具链
rustup toolchain install nightly

# 安装 Miri
cargo +nightly miri setup

# 运行 Miri 测试
cargo +nightly miri test -p c05_threads
```

## 🔄 CI 集成建议

### GitHub Actions

```yaml
name: Miri Check
on: [push, pull_request]
jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: nightly
          components: miri
      - name: Run Miri
        run: cargo +nightly miri test
```

### 建议策略

- **关键 crate**: 在关键 crate 的 CI job 增加可选矩阵项运行 Miri（减少总体时长）
- **Unsafe 代码**: 对含 unsafe 的路径按周跑 Miri，结果入库到工单系统
- **并发模块**: 对含 unsafe/并发细节的模块按阶段纳入 Miri 检查
- **问题记录**: 记录发现的问题与规避策略在对应 `00_index.md`

## ✨ 最佳实践

### 开发流程

- **提交前检查**: 使用 pre-commit hook 自动运行 Miri
- **代码审查**: 将 Miri 警告纳入代码审查标准
- **持续集成**: 在 CI 中运行 Miri 检查（可选，减少总体时长）
- **渐进式采用**: 逐步启用更严格的 Miri 检查

### 配置策略

- **项目初期**: 启用基础 Miri 检查
- **项目成熟**: 启用严格来源检查和泄漏检查
- **团队规范**: 统一 Miri 配置和检查策略
- **定期更新**: 保持 Miri 版本更新

---

## 🔗 相关索引

- **代码分析**: [`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md) - 动态分析工具
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md) - 质量保障标准
- **内存安全**: [`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md) - 内存安全理论

---

## 🧭 导航

- **返回工具链生态**: [`../00_index.md`](../00_index.md)
- **构建工具**: [`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
- **代码分析**: [`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**别名与规范说明**:

- 本页为 Miri 专题页，编号为 `03_miri`。与"03_build_tools"编号冲突已通过规范入口化处理：
  - 构建工具规范入口: [`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
  - Miri 在代码分析/运行时检查的综述入口: [`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
