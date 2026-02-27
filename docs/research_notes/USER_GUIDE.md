# 用户使用指南

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **状态**: ✅ 已完成

---

## 欢迎使用

Rust Formal Methods Research Notes 是一套全面的Rust形式化方法文档，涵盖所有权、借用、类型系统、并发等核心概念的深入解释和证明。

---

## 快速开始

### 根据目标选择入口

| 你的目标 | 推荐入口 | 预计时间 |
| :--- | :--- | :--- |
| 系统学习Rust形式化 | [00_COMPREHENSIVE_SUMMARY.md](00_COMPREHENSIVE_SUMMARY.md) | 40小时 |
| 解决特定问题 | [FAQ_COMPREHENSIVE.md](FAQ_COMPREHENSIVE.md) | 10分钟 |
| 准备面试 | [INTERVIEW_QUESTIONS_COLLECTION.md](INTERVIEW_QUESTIONS_COLLECTION.md) | 4小时 |
| 查阅速查 | [RUST_FORMAL_METHODS_CHEATSHEET.md](RUST_FORMAL_METHODS_CHEATSHEET.md) | 5分钟 |
| 理解设计模式 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | 20小时 |

---

## 学习路径

### 路径一：完整学习（推荐）

```
第1周：基础概念
├── 阅读 00_COMPREHENSIVE_SUMMARY.md
├── 学习 TUTORIAL_OWNERSHIP_SAFETY.md
├── 完成 TUTORIAL_BORROW_CHECKER.md
└── 练习 ownership_model.md 示例

第2周：类型系统
├── 学习 TUTORIAL_TYPE_SYSTEM.md
├── 阅读 type_system_foundations.md
├── 学习 trait_system_formalization.md
└── 完成 variance_theory.md 阅读

第3周：生命周期
├── 学习 TUTORIAL_LIFETIMES.md
├── 阅读 lifetime_formalization.md
└── 练习 LIFETIME_CHEATSHEET.md

第4周：并发与异步
├── 学习 TUTORIAL_CONCURRENCY_MODELS.md
├── 阅读 send_sync_formalization.md
├── 学习 async_state_machine.md
└── 阅读 pin_self_referential.md

第5-6周：设计模式
├── 阅读 software_design_theory/ 全部内容
└── 完成设计模式练习

第7-8周：形式化深入
├── 阅读 PROOF_INDEX.md
├── 学习 CORE_THEOREMS_FULL_PROOFS.md
└── 探索 COQ_FORMALIZATION_MATRIX.md
```

### 路径二：问题导向

```
问题：理解借用检查器错误
└── 路径：
    ├── 查阅 TUTORIAL_BORROW_CHECKER.md
    ├── 参考 CONCEPT_COMPARISON_TABLES.md
    ├── 阅读 borrow_checker_proof.md 相关章节
    └── 练习 COUNTER_EXAMPLES_COMPENDIUM.md 相关示例

问题：选择合适的并发原语
└── 路径：
    ├── 查阅 CONCURRENCY_CHEATSHEET.md
    ├── 参考 CONCURRENCY_SAFETY_MATRIX.md
    ├── 阅读 TUTORIAL_CONCURRENCY_MODELS.md
    └── 查看 send_sync_formalization.md

问题：设计模式选择
└── 路径：
    ├── 查阅 DESIGN_PATTERN_SELECTION_DECISION_TREE.md
    ├── 参考 DESIGN_PATTERNS_MATRIX.md
    ├── 阅读具体模式文档
    └── 查看 APPLICATION_TREES.md 应用场景
```

---

## 文档结构导航

### 核心形式化文档

| 文档 | 内容 | 难度 |
| :--- | :--- | :--- |
| [ownership_model.md](formal_methods/ownership_model.md) | 所有权系统完整形式化 | ⭐⭐⭐⭐⭐ |
| [borrow_checker_proof.md](formal_methods/borrow_checker_proof.md) | 借用检查器证明 | ⭐⭐⭐⭐⭐ |
| [lifetime_formalization.md](formal_methods/lifetime_formalization.md) | 生命周期形式化 | ⭐⭐⭐⭐ |
| [type_system_foundations.md](type_theory/type_system_foundations.md) | 类型系统基础 | ⭐⭐⭐⭐ |
| [async_state_machine.md](formal_methods/async_state_machine.md) | 异步状态机 | ⭐⭐⭐⭐ |

### 思维表征

| 类型 | 数量 | 用途 |
| :--- | :--- | :--- |
| 思维导图 | 15 | 概念可视化 |
| 矩阵 | 13 | 对比分析 |
| 决策树 | 10 | 选择指南 |
| 证明树 | 10 | 证明依赖 |
| 应用树 | 8 | 应用场景 |

### 实用资源

| 资源 | 用途 | 使用场景 |
| :--- | :--- | :--- |
| [PROOF_INDEX.md](PROOF_INDEX.md) | 定理索引 | 查找特定定理 |
| [CROSS_REFERENCE_INDEX.md](CROSS_REFERENCE_INDEX.md) | 交叉引用 | 导航相关文档 |
| [FAQ_COMPREHENSIVE.md](FAQ_COMPREHENSIVE.md) | 常见问题 | 快速答疑 |
| [RUST_FORMAL_METHODS_CHEATSHEET.md](RUST_FORMAL_METHODS_CHEATSHEET.md) | 速查 | 日常参考 |

---

## 使用技巧

### 搜索技巧

```bash
# 按主题搜索
grep -r "生命周期" docs/research_notes --include="*.md"

# 查找特定定理
grep -r "T-OW2" docs/research_notes --include="*.md"

# 查找代码示例
grep -r "```rust" docs/research_notes --include="*.md" -l
```

### 阅读建议

1. **首次阅读**
   - 从概述文档开始
   - 不必深究所有证明细节
   - 重点关注概念和示例

2. **深入研究**
   - 跟随证明树理解推导
   - 查看Rust示例代码
   - 对比形式化定义和实际代码

3. **问题驱动**
   - 先查FAQ和速查表
   - 定位相关教程
   - 深入核心形式化文档

---

## 常见问题

### Q: 如何快速找到特定概念的文档？

A: 使用 [CROSS_REFERENCE_INDEX.md](CROSS_REFERENCE_INDEX.md) 或搜索功能。

### Q: 形式化内容太难理解怎么办？

A: 建议路径：

1. 先读对应的教程（TUTORIAL_*.md）
2. 查看思维导图获得整体概念
3. 最后再读形式化定义

### Q: 文档是否保持更新？

A: 是的，项目维护团队会跟踪Rust版本更新，确保内容时效性。详见 [PROJECT_MAINTENANCE_GUIDE.md](PROJECT_MAINTENANCE_GUIDE.md)。

### Q: 如何贡献内容？

A: 请参考 [PROJECT_MAINTENANCE_GUIDE.md](PROJECT_MAINTENANCE_GUIDE.md) 中的贡献流程。

---

## 反馈与支持

| 方式 | 用途 | 响应时间 |
| :--- | :--- | :--- |
| GitHub Issues | 问题报告、内容建议 | 7天 |
| GitHub Discussions | 讨论、提问 | 14天 |
| Email | 私人反馈 | 14天 |

---

**祝您学习愉快！**

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 用户使用指南完成
