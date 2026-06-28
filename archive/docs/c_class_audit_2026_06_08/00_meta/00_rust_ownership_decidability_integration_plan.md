# rust-ownership-decidability 与 research_notes 整合计划

> **分级**: [B]
> **Bloom 层级**: L2 (理解)

> **创建日期**: 2026-05-12
> **版本**: 1.0
> **状态**: 🟡 计划中
> **预计完成**: 阶段三（1-2 周内）

---

## 📑 目录

- [rust-ownership-decidability 与 research\_notes 整合计划](#rust-ownership-decidability-与-research_notes-整合计划)
  - [📑 目录](#-目录)
  - [1. 现状分析](#1-现状分析)
    - [1.1 `rust-ownership-decidability/` 概况](#11-rust-ownership-decidability-概况)
    - [1.2 `research_notes/` 概况](#12-research_notes-概况)
    - [1.3 重复与交叉](#13-重复与交叉)
  - [2. 整合策略](#2-整合策略)
    - [2.1 保留 `rust-ownership-decidability/` 作为独立体系](#21-保留-rust-ownership-decidability-作为独立体系)
    - [2.2 建立双向链接而非物理合并](#22-建立双向链接而非物理合并)
    - [2.3 版本号对齐](#23-版本号对齐)
    - [2.4 清理过时内容](#24-清理过时内容)
  - [3. 执行步骤](#3-执行步骤)
  - [4. 统一索引结构（建议）](#4-统一索引结构建议)
  - [5. 相关文档](#5-相关文档)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 现状分析
>
> **[来源: Rust Official Docs]**

### 1.1 `rust-ownership-decidability/` 概况

> **[来源: Wikipedia - Concurrency]**
>
> **[来源: Rust Official Docs]**

- **规模**: 642 个文件，11MB，600K+ 字
- **定位**: Rust 所有权系统的形式化语义分析与可判定性研究
- **核心内容**: 线性逻辑、核心概念、并发模式、验证工具、案例研究、比较研究
- **问题**: badge 标注 Rust 1.94，部分内容已过时（08-advanced-topics 中的 1.94 报告等）

### 1.2 `research_notes/` 概况
>
> **[来源: Rust Official Docs]**

- **规模**: 150+ 个文件
- **定位**: 通用研究笔记（形式化方法、类型理论、软件设计理论）
- **核心内容**: 所有权形式化、借用检查器证明、设计模式形式化、工作流引擎
- **问题**: 版本标注滞后（README 标 1.93.1+）

### 1.3 重复与交叉

| 主题 | `rust-ownership-decidability/` | `research_notes/` | 重复度 |
|------|-------------------------------|-------------------|--------|
| 所有权形式化 | `01-core-concepts/`, `formal-foundations/` | `formal_methods/10_ownership_model.md` | **高** |
| 借用检查器证明 | `formal-foundations/proofs/` | `formal_methods/10_borrow_checker_proof.md` | **高** |
| 设计模式形式化 | `11-design-patterns/` | `software_design_theory/01_design_patterns_formal/` | **中** |
| 并发形式化 | `12-concurrency-patterns/` | `formal_methods/concurrency_model.md` | **中** |
| 工作流形式化 | — | `software_design_theory/02_workflow/` | 独有 |
| 类型理论 | `01-core-concepts/` | `type_theory/` | **中** |

---

## 2. 整合策略

### 2.1 保留 `rust-ownership-decidability/` 作为独立体系

**理由**:

- 其内容深度和系统性远超 `research_notes/` 的对应部分
- 600K+ 字的内容迁移成本过高
- 有独立的完成报告和索引系统

### 2.2 建立双向链接而非物理合并

**操作**:

1. 在 `rust-ownership-decidability/README.md` 中添加 "Related Research Notes" 章节
2. 在 `research_notes/README.md` 中添加 "Ownership Decidability Deep Dive" 链接
3. 对重复主题，保留 `rust-ownership-decidability/` 为主要内容源，`research_notes/` 中改为精简概述 + 链接

### 2.3 版本号对齐

- 更新 `rust-ownership-decidability/README.md` badge 为 Rust 1.95+ ✅ 已完成
- 更新 `research_notes/README.md` 版本标注为 1.96.0+ ✅ 已完成
- 更新 `rust-ownership-decidability/` 中所有 `RUST_1.94_*` 文件引用，指向 1.95 对应文档

### 2.4 清理过时内容

- 将 `rust-ownership-decidability/08-advanced-topics/RUST_1.94_UPDATE_REPORT.md` 归档 ✅ 已完成
- 将 `rust-ownership-decidability/RUST_194_STDLIB_10_api_guide.md` 归档 ✅ 已完成
- 更新 `DEEP_DIVE_COMPLETION_REPORT.md` 中的版本目标

---

## 3. 执行步骤

| 步骤 | 操作 | 负责人 | 状态 |
|------|------|--------|------|
| 1 | 更新两个体系的 README 交叉引用 | 维护者 | 🟡 待执行 |
| 2 | 在 `research_notes/` 中对重复主题添加精简版 + 链接 | 维护者 | 🟡 待执行 |
| 3 | 更新 `rust-ownership-decidability/` 中所有 1.94 引用 | 维护者 | 🟡 待执行 |
| 4 | 创建统一的形式化内容索引 | 维护者 | 🟡 待执行 |
| 5 | 评审整合效果 | 项目维护团队 | 🟡 待执行 |

---

## 4. 统一索引结构（建议）

```
形式化内容总入口
├── 所有权与借用 (主: rust-ownership-decidability/)
│   ├── 核心概念
│   ├── 形式化证明
│   └── 验证工具
├── 类型理论 (主: research_notes/type_theory/)
│   ├── 基础理论
│   └── Trait 系统
├── 并发形式化 (主: rust-ownership-decidability/)
│   ├── 并发模式
│   └── 消息传递
├── 设计模式形式化 (主: research_notes/software_design_theory/)
│   ├── 23 种设计模式
│   └── 工作流引擎
└── 软件设计理论 (主: research_notes/software_design_theory/)
    ├── 分布式模式
    └── 容错模式
```

---

## 5. 相关文档

- `00_documentation_division_of_labor.md` — 文档体系分工协议
- `00_documentation_lifecycle.md` — 文档生命周期管理制度

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
