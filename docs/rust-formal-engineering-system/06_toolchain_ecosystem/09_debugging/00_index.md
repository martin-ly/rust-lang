# 调试（Debugging）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [调试（Debugging）索引](#调试debugging索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心概念](#-核心概念)
    - [1. 调试策略（Debugging Strategy）](#1-调试策略debugging-strategy)
    - [2. 调试工具（Debugging Tools）](#2-调试工具debugging-tools)
    - [3. 调试技巧（Debugging Techniques）](#3-调试技巧debugging-techniques)
    - [4. 远程调试（Remote Debugging）](#4-远程调试remote-debugging)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c61_debugging/src/`](#cratesc61_debuggingsrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块介绍调试工具在 Rust 项目中的应用与实践，提供调试策略、调试工具、调试技巧的技术指导。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **调试工具**: 专注于 Rust 调试工具最佳实践
- **最佳实践**: 基于 Rust 社区最新调试实践
- **完整覆盖**: 涵盖调试策略、调试工具、调试技巧、远程调试等核心主题
- **易于理解**: 提供详细的调试说明和代码示例

## 📚 核心概念

### 1. 调试策略（Debugging Strategy）

**推荐工具**: `gdb`, `lldb`, `rust-gdb`, `rust-lldb`

- **断点调试**: 断点设置、条件断点、断点管理
- **日志调试**: 日志记录、日志分析、日志追踪
- **交互调试**: 交互式调试、REPL 调试
- **问题定位**: 问题定位、错误分析、堆栈跟踪

**相关资源**:

- [GDB 文档](https://www.gnu.org/software/gdb/)
- [LLDB 文档](https://lldb.llvm.org/)
- [rust-gdb 文档](https://github.com/rust-lang/rust-gdb)
- [rust-lldb 文档](https://github.com/rust-lang/rust-lldb)

### 2. 调试工具（Debugging Tools）

**推荐工具**: `gdb`, `lldb`, `perf`, `valgrind`, `miri`

- **调试器**: GDB、LLDB、CodeLLDB
- **分析器**: perf、valgrind、dhat
- **监控器**: 系统监控、应用监控、性能监控
- **内存分析**: 内存泄漏检测、内存错误分析

**相关资源**:

- [GDB 文档](https://www.gnu.org/software/gdb/)
- [LLDB 文档](https://lldb.llvm.org/)
- [perf 文档](https://perf.wiki.kernel.org/)
- [valgrind 文档](https://valgrind.org/)

### 3. 调试技巧（Debugging Techniques）

**推荐工具**: `tracing`, `log`, `env_logger`, `dbg!`

- **问题定位**: 问题定位、错误分析、性能调试
- **日志调试**: 日志记录、日志分析、日志追踪
- **断言调试**: 断言检查、条件检查、状态检查
- **性能调试**: 性能瓶颈、性能分析、性能优化

**相关资源**:

- [tracing 文档](https://docs.rs/tracing/)
- [log 文档](https://docs.rs/log/)
- [env_logger 文档](https://docs.rs/env_logger/)
- [Rust Book - Debugging](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html)

### 4. 远程调试（Remote Debugging）

**推荐工具**: `gdb`, `lldb`, `CodeLLDB`, `rust-gdb`

- **远程连接**: 远程调试连接、SSH 调试
- **远程执行**: 远程代码执行、远程断点
- **远程监控**: 远程监控、远程日志
- **容器调试**: 容器调试、Docker 调试

**相关资源**:

- [GDB 远程调试](https://sourceware.org/gdb/onlinedocs/gdb/Remote-Debugging.html)
- [LLDB 远程调试](https://lldb.llvm.org/use/remote.html)
- [CodeLLDB 文档](https://github.com/vadimcn/vscode-lldb)

## 💻 实践与样例

### 代码示例位置

- **调试工具**: [crates/c61_debugging](../../../crates/c61_debugging/)
- **工具链生态**: [`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

### 文件级清单（精选）

#### `crates/c61_debugging/src/`

- `debugging_strategy.rs` - 调试策略
- `debugging_tools.rs` - 调试工具
- `debugging_techniques.rs` - 调试技巧
- `remote_debugging.rs` - 远程调试
- `memory_debugging.rs` - 内存调试

### 快速开始示例

```bash
# GDB 调试
gdb ./target/debug/my_app

# LLDB 调试
lldb ./target/debug/my_app

# 日志调试
RUST_LOG=debug cargo run

# 断言调试
cargo test -- --nocapture
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- **工具链生态**: [`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)

---

## 🧭 导航

- **返回工具链生态**: [`../00_index.md`](../00_index.md)
- **IDE 集成**: [`../08_ide_integration/00_index.md`](../08_ide_integration/00_index.md)
- **监控**: [`../10_monitoring/00_index.md`](../10_monitoring/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
