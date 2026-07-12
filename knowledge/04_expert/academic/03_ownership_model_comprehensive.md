# 所有权模型综合指南 / Ownership Model Comprehensive Guide

> **EN**: Ownership Model Comprehensive Guide
> **Summary**: 所有权模型综合指南 Ownership Model Comprehensive Guide. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/04_formal/03_ownership_formal.md](../../../concept/04_formal/01_ownership_logic/02_ownership_formal.md)。
> **历史版本存档**: [archive/knowledge/04_expert/academic/03_ownership_model_comprehensive.md](../../../archive/knowledge/04_expert/academic/03_ownership_model_comprehensive.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 所有权是权限/资源模型：移动、复制、借用决定内存访问权
2. 可变/共享规则对应唯一性：`&mut T` 唯一，`&T` 可共享
3. 区域类型与生命周期约束引用的有效范围
4. 形式化模型（线性/仿射逻辑、分离逻辑）为借用检查器提供语义基础

## 关键区分

| 模型 | 视角 | 代表 |
|---|---|---|
| 操作语义 | 执行行为 | Rust 语言规范 |
| RustBelt/Iris | 分离逻辑 | POPL 2018 |
| Aeneas/LLBC | 函数式翻译 | ICFP 2022 |
| Tree Borrows | 别名模型 | PLDI 2025 |

## 常见陷阱

- 将借用检查器与别名模型混为一谈
- 忽略 unsafe 可绕过形式化保证
- 误用 `Pin` 破坏自引用不变式

---

**详细内容已迁移**：请点击上方 [concept/04_formal/03_ownership_formal.md](../../../concept/04_formal/01_ownership_logic/02_ownership_formal.md) 查看最新权威解释。
