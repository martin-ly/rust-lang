# 借用检查器证明导读 / Borrow Checker Proof Guide

> **EN**: Borrow Checker Proof Guide
> **Summary**: 借用检查器证明导读 Borrow Checker Proof Guide. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/04_formal/28_borrow_checking_decidability.md](../../../concept/04_formal/28_borrow_checking_decidability.md)。
> **历史版本存档**: [archive/knowledge/04_expert/academic/04_borrow_checker_proof_guide.md](../../../archive/knowledge/04_expert/academic/04_borrow_checker_proof_guide.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 借用检查器通过流敏感的区域分析检测冲突借用
2. NLL 允许借用提前结束；Polonius 提供更精确的关系分析
3. 数据竞争自由与引用有效性是核心定理
4. Miri 在运行时验证别名规则（Stacked/Tree Borrows）

## 关键区分

| 组件 | 作用 | 阶段 |
|---|---|---|
| NLL | 非词法生命周期 | 编译期 |
| Polonius | 基于约束的借用检查 | 编译期 |
| Stacked/Tree Borrows | 别名模型 | 运行时检查 (Miri) |

## 常见陷阱

- 认为借用检查器就是别名模型
- 忽略 NLL 仍可能拒绝合法程序
- 在 unsafe 中假设 Miri 未报错即为合法

---

**详细内容已迁移**：请点击上方 [concept/04_formal/28_borrow_checking_decidability.md](../../../concept/04_formal/28_borrow_checking_decidability.md) 查看最新权威解释。
