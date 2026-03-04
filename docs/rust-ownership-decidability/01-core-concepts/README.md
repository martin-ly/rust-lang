# 01 - 核心概念

> **Rust所有权系统核心机制详解**

---

## 目录说明

本目录深入讲解Rust所有权系统的五大核心概念，从实践和理论两个维度进行形式化分析。

---

## 文档列表

| # | 文档 | 核心内容 | 定理数量 |
|:---:|:---|:---|:---:|
| 01-01 | [所有权规则](01-01-ownership-rules.md) | 所有权转移、Drop、RAII | 10+ |
| 01-02 | [借用系统](01-02-borrowing-system.md) | 共享借用vs可变借用 | 8+ |
| 01-03 | [生命周期](01-03-lifetimes.md) | 生命周期标注、省略规则 | 6+ |
| 01-04 | [运行时vs编译时](01-04-runtime-vs-compile-time.md) | 检查时机对比 | 5+ |
| 01-05 | [内部可变性](01-05-interior-mutability.md) | Cell/RefCell/Mutex | 8+ |

---

## 核心定理预览

```text
Thm OWNERSHIP-UNIQUENESS: 任意时刻，一个值只有一个所有者

Thm BORROW-XOR-MUT: 不能同时存在可变借用和不可变借用

Thm LIFETIME-SUBSET: 引用生命周期 ⊆ 被引用值生命周期
```

---

**维护者**: Rust Core Concepts Team
