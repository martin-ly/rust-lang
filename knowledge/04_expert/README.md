# 04 - 专家级主题

> **Rust 专家级知识：编译器内部、形式化验证、Unsafe 审计、Tree Borrows**

## 🎯 本模块学习目标

完成本模块后，你将能够：

- [ ] 理解 Rust 编译器的关键优化 passes 和 MIR 结构
- [ ] 使用 Miri 验证 unsafe 代码的内存安全
- [ ] 运用 Tree Borrows 模型分析别名规则
- [ ] 使用 Coq 进行 Rust 程序的形式化验证

## 📚 内容

| 文档 | 主题 | 难度 |
|------|------|------|
| [compiler_internals.md](compiler_internals.md) | 编译器内部机制 | ⭐⭐⭐⭐⭐ |
| [unsafe_audit.md](unsafe_audit.md) | Unsafe 代码审计方法论 | ⭐⭐⭐⭐⭐ |
| [miri/tree_borrows.md](miri/tree_borrows.md) | Tree Borrows 别名模型 | ⭐⭐⭐⭐⭐ |
| [academic/tree_borrows_authoritative_guide.md](academic/tree_borrows_authoritative_guide.md) | Tree Borrows 权威指南 | ⭐⭐⭐⭐⭐ |
| [academic/coq_formalization_guide.md](academic/coq_formalization_guide.md) | Coq 形式化验证实战 | ⭐⭐⭐⭐⭐ |

## ⏱️ 预计时间

- 编译器内部: 6-8 小时
- Unsafe 审计: 4-6 小时
- Tree Borrows: 4-6 小时
- 形式化验证: 8-10 小时
- **总计**: 约 22-30 小时

## 🎓 前置要求

- [03_advanced/](../03_advanced/) 的全部内容
- 对操作系统、编译原理有基本了解
- 形式化验证文档需要离散数学和逻辑基础

## ✅ 完成检查清单

- [ ] 能阅读和理解 rustc 的 MIR 输出
- [ ] 能使用 Miri 检测出 unsafe 代码中的 UB
- [ ] 能用 Tree Borrows 模型解释复杂借用场景
- [ ] 能在 Coq 中证明简单 Rust 程序的属性

## 🚀 下一步

- 深入 [safety_critical/](safety_critical/) 安全关键系统生态
- 返回 [05_reference/](../05_reference/) 查阅参考资料
- 探索 [06_ecosystem/](../06_ecosystem/) 实际项目开发

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09
