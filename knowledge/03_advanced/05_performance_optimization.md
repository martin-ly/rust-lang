# 性能优化

> **权威来源**: 本主题深度解释见 [concept/06_ecosystem/15_performance_optimization.md](../../concept/06_ecosystem/15_performance_optimization.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/05_performance_optimization.md](../../archive/knowledge/03_advanced/05_performance_optimization.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 先测量（cargo bench / flamegraph），再优化
2. 零成本抽象是目标：高层代码不劣于手写底层
3. 避免不必要克隆、分配与动态分发
4. 利用迭代器、切片和 `unsafe`（在必要时）提升局部性能

## 关键区分

| 优化层级 | 工具 | 影响 |
|---|---|---|
| 算法 | 复杂度分析 | 最大 |
| 数据结构 | 选择合适集合 | 大 |
| 微优化 | asm / cache | 小且风险高 |

## 常见陷阱

- 未测量就重写热点代码
- 过早使用 `unsafe` 替代安全抽象
- 忽略编译器优化与别名规则

---

**详细内容已迁移**：请点击上方 [concept/06_ecosystem/15_performance_optimization.md](../../concept/06_ecosystem/15_performance_optimization.md) 查看最新权威解释。
