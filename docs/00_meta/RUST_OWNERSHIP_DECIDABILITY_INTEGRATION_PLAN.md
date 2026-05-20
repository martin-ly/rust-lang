# rust-ownership-decidability 与 research_notes 整合计划

> **创建日期**: 2026-05-12
> **版本**: 1.0
> **状态**: 🟡 计划中
> **预计完成**: 阶段三（1-2 周内）

---

## 1. 现状分析

### 1.1 `rust-ownership-decidability/` 概况

- **规模**: 642 个文件，11MB，600K+ 字
- **定位**: Rust 所有权系统的形式化语义分析与可判定性研究
- **核心内容**: 线性逻辑、核心概念、并发模式、验证工具、案例研究、比较研究
- **问题**: badge 标注 Rust 1.94，部分内容已过时（08-advanced-topics 中的 1.94 报告等）

### 1.2 `research_notes/` 概况

- **规模**: 150+ 个文件
- **定位**: 通用研究笔记（形式化方法、类型理论、软件设计理论）
- **核心内容**: 所有权形式化、借用检查器证明、设计模式形式化、工作流引擎
- **问题**: 版本标注滞后（README 标 1.93.1+）

### 1.3 重复与交叉

| 主题 | `rust-ownership-decidability/` | `research_notes/` | 重复度 |
|------|-------------------------------|-------------------|--------|
| 所有权形式化 | `01-core-concepts/`, `formal-foundations/` | `formal_methods/ownership_model.md` | **高** |
| 借用检查器证明 | `formal-foundations/proofs/` | `formal_methods/borrow_checker_proof.md` | **高** |
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
- 更新 `research_notes/README.md` 版本标注为 1.95.0+ ✅ 已完成
- 更新 `rust-ownership-decidability/` 中所有 `RUST_1.94_*` 文件引用，指向 1.95 对应文档

### 2.4 清理过时内容

- 将 `rust-ownership-decidability/08-advanced-topics/RUST_1.94_UPDATE_REPORT.md` 归档 ✅ 已完成
- 将 `rust-ownership-decidability/RUST_194_STDLIB_API_GUIDE.md` 归档 ✅ 已完成
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

- `DOCUMENTATION_DIVISION_OF_LABOR.md` — 文档体系分工协议
- `DOCUMENTATION_LIFECYCLE.md` — 文档生命周期管理制度

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
