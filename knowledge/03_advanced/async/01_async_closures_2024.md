# Rust 2024 Edition Async Closures 完整指南

> **EN**: Async Closures 2024
> **Summary**: Rust 2024 Edition Async Closures 完整指南 Async Closures 2024. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/24_async_closures.md](../../../concept/03_advanced/24_async_closures.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/async/01_async_closures_2024.md](../../../archive/knowledge/03_advanced/async/01_async_closures_2024.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. Rust 2024 允许 `async || { ... }` 形式的异步闭包
2. 捕获规则按闭包语义分析，而非 `async` 块整体
3. 需要关注取消安全与捕获生命周期
4. 迁移时替换 `async move ||` 等旧写法

## 关键区分

| 写法 | 版本 | 语义 |
|---|---|---|
| `async \|\| { ... }` | 2024 | 异步闭包 |
| `async move { ... }` | 旧版 | async 块捕获环境 |
| `\|\| async move { ... }` | 兼容 | 返回 Future 的闭包 |

## 常见陷阱

- 在 2024 前版本使用新语法导致编译错误
- 异步闭包捕获变量生命周期超过预期
- 未处理取消安全

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/24_async_closures.md](../../../concept/03_advanced/24_async_closures.md) 查看最新权威解释。
