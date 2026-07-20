# 调试工具（Debugging Tools）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [调试工具（Debugging Tools）索引](#调试工具debugging-tools索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [调试工具](#调试工具)
  - [💻 实际代码示例](#-实际代码示例)
  - [实践与示例（仓库内）](#实践与示例仓库内)
  - [设计建议](#设计建议)
  - [常见陷阱](#常见陷阱)
  - [参考资料](#参考资料)
  - [导航](#导航)

---

## 目的

- 介绍 Rust 调试工具的使用和最佳实践。
- 提供调试器、日志工具、错误追踪的指南。

---

## 核心概念

- **调试器**: GDB、LLDB 等调试器
- **日志工具**: 日志记录和查看
- **错误追踪**: 错误堆栈跟踪
- **内存调试**: 内存泄漏检测
- **并发调试**: 并发问题调试
- **远程调试**: 远程调试支持

---

## 调试工具

- **GDB**: GNU 调试器
- **LLDB**: LLVM 调试器
- **tracing**: 结构化日志库
- **log**: 日志宏库
- **backtrace**: 堆栈跟踪
- **miri**: 未定义行为检测器

---

## 💻 实际代码示例

将调试工具理论知识应用到实际代码中：

- **日志记录**: 使用 `log` 或 `tracing` 记录日志
- **调试器**: 使用 GDB 或 LLDB 调试程序

**学习路径**: 形式化理论 → 实际代码 → 验证理解

---

## 实践与示例（仓库内）

- 日志记录：在各 crate 中使用日志库。
- 调试器：使用调试器调试程序。

---

## 设计建议

- 使用结构化日志。
- 合理设置日志级别。
- 利用调试器定位问题。
- 使用 miri 检测未定义行为。

---

## 常见陷阱

- 日志级别设置不当。
- 忽略调试信息。
- 未使用调试器。

---

## 参考资料

- [Rust Book - Debugging](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html)
- [tracing Documentation](https://docs.rs/tracing/)
- [miri Documentation](https://github.com/rust-lang/miri)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- IDE集成：[`../08_ide_integration/00_index.md`](../08_ide_integration/00_index.md)
- 监控工具：[`../10_monitoring/00_index.md`](../10_monitoring/00_index.md)
