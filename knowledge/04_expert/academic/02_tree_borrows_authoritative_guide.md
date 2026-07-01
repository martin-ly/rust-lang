# Tree Borrows 权威指南 / Tree Borrows Authoritative Guide

> **权威来源**: 本主题深度解释见 [concept/04_formal/36_tree_borrows_deep_dive.md](../../../concept/04_formal/36_tree_borrows_deep_dive.md)。
> **历史版本存档**: [archive/knowledge/04_expert/academic/02_tree_borrows_authoritative_guide.md](../../../archive/knowledge/04_expert/academic/02_tree_borrows_authoritative_guide.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. Tree Borrows 是 Rust 的别名模型，用于在 Miri 中判断指针访问是否合法。
2. 以树结构组织重新借用：父指针冻结时子指针仍可使用。
3. 每个引用有权限状态（Active/Frozen/Disabled/Reserved）随访问动态演化。
4. 比 Stacked Borrows 更宽容，支持更多合法 unsafe 模式。

## 关键区分

| 特性 | Stacked Borrows | Tree Borrows |
|---|---|---|
| 结构 | 栈 | 树 |
| 对重新借用 | 更严格 | 更灵活 |
| 默认启用 | 曾是 | 1.96+ 默认 |
| 适用 | 保守检测 | 工业级 unsafe |

## 常见陷阱

- 在 unsafe 中混用父子指针导致权限冲突。
- 用 Stacked Borrows 通过但 Tree Borrows 失败的代码仍可能有问题。
- 忽略 `Unique`/`Raw` 指针的权限差异。

---

**详细内容已迁移**：请点击上方 [concept/04_formal/36_tree_borrows_deep_dive.md](../../../concept/04_formal/36_tree_borrows_deep_dive.md) 查看最新权威解释。
