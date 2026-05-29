# Rust 所有权与可判定性 - Rust 1.94 索引

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **目录**: docs/rust-ownership-decidability/
> **总文件数**: 89+
> **核心主题**: 所有权系统、可判定性、形式化证明
> **Rust 版本**: 1.94.0+
> **梳理日期**: 2026-03-14
> **状态**: 🔄 **持续推进中**

---

## 📑 目录
>
- [Rust 所有权与可判定性 - Rust 1.94 索引](#rust-所有权与可判定性---rust-194-索引)
  - [📑 目录](#目录)
  - [📋 文档分类](#文档分类)
    - [核心完成报告 (20+ 文件)](#核心完成报告-20-文件)
    - [理论与证明 (15+ 文件)](#理论与证明-15-文件)
    - [实践指南 (10+ 文件)](#实践指南-10-文件)
    - [分析与审计 (20+ 文件)](#分析与审计-20-文件)
  - [🆕 Rust 1.94 相关更新](#rust-194-相关更新)
    - [所有权系统新特性](#所有权系统新特性)
  - [🎯 推进计划](#推进计划)
  - **最后更新**: 2026-03-14
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 📋 文档分类
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 核心完成报告 (20+ 文件)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- 100_PERCENT_COMPLETION_REPORT.md
- COMPLETION_100_PERCENT_SUMMARY.md
- FINAL_100_PERCENT_COMPLETION_*.md (10+ 变体)
- RUST_194_*_FINAL.md (10+ 变体)

### 理论与证明 (15+ 文件)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- UNIFIED_THEORETICAL_FRAMEWORK.md
- THEOREM_10_dependency_graph.md
- THEOREM_INTUITIONS.md
- 10_proof_strategies.md
- 10_formal_language_and_proofs.md (引用)

### 实践指南 (10+ 文件)

- ULTIMATE_COMPREHENSIVE_GUIDE.md
- INTERACTIVE_LEARNING_GUIDE.md
- 10_quick_reference_card.md
- READING_GUIDE.md

### 分析与审计 (20+ 文件)

- COMPREHENSIVE_COMPLETION_REPORT.md
- PROJECT_COMPREHENSIVE_AUDIT_REPORT.md
- AUDIT_REPORTS_INDEX.md
- CROSS_REFERENCE_VERIFICATION_*.md

---

## 🆕 Rust 1.94 相关更新

### 所有权系统新特性

| 特性 | 影响 | 文档位置 |
|------|------|----------|
| `array_windows` | 内存安全模式 | 待更新 |
| `ControlFlow` | 控制流证明 | 待更新 |
| `LazyCell/LazyLock` | 延迟初始化安全 | 待更新 |

---

## 🎯 推进计划

1. **批量更新核心报告** (20文件)
2. **更新理论文档** (15文件)
3. **创建统一索引** (本文件)

---

**最后更新**: 2026-03-14
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [rust-ownership-decidability 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
