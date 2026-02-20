# CLI 应用开发指南

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 文档定位

本指南为官方 **Command Line Book** 的补充与项目内导航，帮助在开发 Rust 命令行应用时快速定位到本项目的相关模块和示例。

---

## 官方 CLI Book 入口

| 资源 | URL | 说明 |
| :--- | :--- | :--- || **Command Line Book** | <https://rust-cli.github.io/book/> | 官方 CLI 应用开发教程 |
| **CLI Book 源码** | <https://github.com/rust-cli/book> | 贡献与反馈 |

---

## 本项目对应模块

| CLI 开发主题 | 官方 CLI Book | 本项目对应 |
| :--- | :--- | :--- || 参数解析 | clap、structopt | C03 控制流、[cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| 标准输入输出 | std::io | [C07 进程管理](../../crates/c07_process/) |
| 子进程与管道 | std::process | C07 [进程管理](../../crates/c07_process/docs/) |
| 文件系统 | std::fs | C03、C08 算法 |
| 错误处理 | anyhow、thiserror | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| 异步 CLI | tokio | [C06 异步](../../crates/c06_async/)、[async_patterns](../02_reference/quick_reference/async_patterns.md) |

---

## 推荐学习路径

1. **入门**: 通读 [Command Line Book](https://rust-cli.github.io/book/) 快速教程
2. **巩固**: 学习 C07 进程管理（std::process、std::io）
3. **进阶**: C03 错误处理 + [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md)
4. **高级**: C06 异步 + 高性能 CLI 工具开发

---

## 常用 crate 推荐

| 用途 | crate | 说明 |
| :--- | :--- | :--- || 参数解析 | clap | 最流行的 CLI 参数解析库 |
| 错误处理 | anyhow、thiserror | 生产级错误传播 |
| 终端交互 | crossterm、ratatui | TUI 应用 |
| 进度条 | indicatif | 进度显示 |

---

## 相关文档

- [C07 进程管理](../../crates/c07_process/docs/00_MASTER_INDEX.md)
- [故障排查指南](./TROUBLESHOOTING_GUIDE.md)
- [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md)
- [官方 Command Line Book](https://rust-cli.github.io/book/)
