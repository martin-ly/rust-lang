# 包管理器（Package Manager）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [包管理器（Package Manager）索引](#包管理器package-manager索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [Cargo 功能](#cargo-功能)
  - [💻 实际代码示例](#-实际代码示例)
  - [实践与示例（仓库内）](#实践与示例仓库内)
  - [设计建议](#设计建议)
  - [常见陷阱](#常见陷阱)
  - [参考资料](#参考资料)
  - [导航](#导航)

---

## 目的

- 介绍 Rust 包管理器 Cargo 的使用和最佳实践。
- 提供依赖管理和项目配置的指南。

---

## 核心概念

- **Cargo**: Rust 官方包管理器和构建工具
- **Cargo.toml**: 项目配置文件
- **Cargo.lock**: 依赖版本锁定文件
- **Workspace**: 多包项目管理
- **Feature**: 可选功能标志
- **Registry**: 包注册表（crates.io）

---

## Cargo 功能

- **依赖管理**: 版本解析和依赖图管理
- **构建系统**: 编译、测试、文档生成
- **工作空间**: 多 crate 项目管理
- **特性标志**: 条件编译和可选依赖
- **发布流程**: 打包和发布到 crates.io

---

## 💻 实际代码示例

将包管理器理论知识应用到实际代码中：

- **[工具链文档](../../../toolchain/02_cargo_workspace_guide.md)** - Cargo 工作空间指南
- **[项目根 Cargo.toml](../../../../../Cargo.toml)** - 工作空间配置示例

**学习路径**: 形式化理论 → 实际代码 → 验证理解

---

## 实践与示例（仓库内）

- Cargo 配置：参见项目根 `Cargo.toml` 和各 crate 的 `Cargo.toml`。
- 工作空间管理：参见项目根 `Cargo.workspace`。

---

## 设计建议

- 使用语义化版本控制。
- 合理使用特性标志。
- 利用工作空间管理多包项目。
- 定期更新依赖。

---

## 常见陷阱

- 依赖版本冲突。
- 特性标志使用不当。
- 工作空间配置错误。

---

## 参考资料

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [工具链文档](../../../toolchain/02_cargo_workspace_guide.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 编译器：[`../01_compiler/00_index.md`](../01_compiler/00_index.md)
- 构建工具：[`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
