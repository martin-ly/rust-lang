# Tier 3: 技术参考层

> **定位**: 技术细节和参考文档
> **完成状态**: ✅ 100% (5篇核心文档 + 现有资源)
> **最后更新**: 2025-12-25

---

## 📚 核心技术参考 (NEW)

| 序号 | 文档 | 内容 | 行数 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| 1    | [01\_设计模式分类参考.md](01_design_pattern_categories_reference.md)      | GoF + 并发 + Rust特有模式完整分类      | ~900 | ✅   |
| 2    | [02\_模式实现对比.md](02_pattern_implementation_comparison.md)              | Trait vs 泛型、同步vs异步、性能对比    | ~650 | ✅   |
| 3    | [03_rust_190_feature_applications_reference.md](03_rust_190_feature_applications_reference.md) | async fn、GATs、let-else、RPITIT等特性 | ~750 | ✅   |
| 4    | [04\_模式性能评估参考.md](04_pattern_performance_evaluation_reference.md)      | 基准测试、性能数据、优化建议           | ~800 | ✅   |
| 5    | [05\_模式选择最佳实践.md](05_pattern_selection_best_practices.md)      | 决策树、场景驱动、反模式避免           | ~700 | ✅   |
| 6    | [06\_模式使用快速参考.md](06_pattern_quick_reference.md)      | 何时使用/避免、复杂度、线程安全性      | ~960 | ✅   |

**总计**: 6 篇核心文档，~4,760 行，400+ 代码示例

---

## 🗺️ 现有理论资源

| 资源                                                                              | 说明                                 |
| :--- | :--- |
| [00_MASTER_INDEX.md](../00_master_index.md)                                       | 完整索引                             |
| [FAQ.md](tier_01_foundations/04_faq.md)                                                               | 常见问题（完整版）                   |
| [Glossary.md](tier_01_foundations/03_glossary.md)                                                     | 术语表（完整版）                     |
| [Tier 1 基础层](../tier_01_foundations/README.md)                                          | 快速入门和基础参考                   |
| [Tier 1 术语表](../tier_01_foundations/03_glossary.md)                              | 核心术语快速参考                     |
| [Tier 1 常见问题](../tier_01_foundations/04_faq.md)                          | 新手常见问题解答                     |
| [OVERVIEW.md](../overview.md)                                                     | 概览                                 |
| [KNOWLEDGE_GRAPH.md](../knowledge_graph.md)                                       | 知识图谱                             |
| [MIND_MAP.md](../mind_map.md)                                                     | 思维导图                             |
| [RUST_192_DESIGN_PATTERN_IMPROVEMENTS.md](../rust_192_design_pattern_improvements.md)         | Rust 1.93.0导图（自 Rust 1.90 引入） |
| [RUST_190_COMPREHENSIVE_MINDMAP.md](../rust_190_comprehensive_mindmap.md)         | Rust 1.90导图（历史版本）            |
| [MULTIDIMENSIONAL_MATRIX_COMPARISON.md](../multidimensional_matrix_comparison.md) | 多维对比                             |

---

## 📖 学习路径

**推荐阅读顺序**:

1. 01\_设计模式分类参考 → 了解完整分类体系
2. 06\_模式使用快速参考 → 快速查找模式使用指南（⭐ 新增）
3. [03_Rust190特性应用参考](03_rust_190_feature_applications_reference.md) → 掌握现代Rust特性（自 Rust 1.90 引入）
4. 02\_模式实现对比 → 理解不同实现权衡
5. 04\_模式性能评估 → 性能基准与优化
6. 05\_模式选择最佳实践 → 实战决策指南

---

**返回**: [Tier 2](../tier_02_guides/README.md) | **下一步**: [Tier 4](../tier_04_advanced/README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
