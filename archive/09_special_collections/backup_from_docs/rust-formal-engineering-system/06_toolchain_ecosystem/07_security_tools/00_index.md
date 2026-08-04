# 安全工具（Security Tools）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [安全工具（Security Tools）索引](#安全工具security-tools索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [安全工具](#安全工具)
  - [💻 实际代码示例](#-实际代码示例)
  - [实践与示例（仓库内）](#实践与示例仓库内)
  - [设计建议](#设计建议)
  - [常见陷阱](#常见陷阱)
  - [参考资料](#参考资料)
  - [导航](#导航)

---

## 目的

- 介绍 Rust 安全工具的使用和最佳实践。
- 提供安全扫描、漏洞检测、依赖审计的指南。

---

## 核心概念

- **安全扫描**: 扫描代码中的安全漏洞
- **漏洞检测**: 检测已知的安全漏洞
- **依赖审计**: 审计依赖的安全性
- **代码审计**: 人工审查代码安全性
- **威胁建模**: 识别和评估安全威胁

---

## 安全工具

- **cargo-audit**: 依赖安全审计
- **cargo-deny**: 依赖策略检查
- **cargo-geiger**: 不安全代码检测
- **cargo-crev**: 代码审查工具
- **rustsec**: Rust 安全咨询数据库

---

## 💻 实际代码示例

将安全工具理论知识应用到实际代码中：

- **依赖审计**: 运行 `cargo audit`
- **策略检查**: 运行 `cargo deny check`

**学习路径**: 形式化理论 → 实际代码 → 验证理解

---

## 实践与示例（仓库内）

- 依赖审计：运行 `cargo audit` 检查依赖安全。
- 策略检查：运行 `cargo deny check` 检查依赖策略。

---

## 设计建议

- 定期运行安全扫描。
- 及时更新依赖。
- 审查不安全代码使用。
- 建立安全策略。

---

## 常见陷阱

- 忽略安全警告。
- 依赖版本过旧。
- 不安全代码使用不当。

---

## 参考资料

- [cargo-audit Documentation](https://github.com/rustsec/rustsec/tree/main/cargo-audit)
- [cargo-deny Documentation](https://github.com/EmbarkStudios/cargo-deny)
- Rust 安全最佳实践

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 安全模式：[`../../03_design_patterns/08_security/00_index.md`](../../03_design_patterns/08_security/00_index.md)
