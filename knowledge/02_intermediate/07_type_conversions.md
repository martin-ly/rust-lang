# Rust 类型转换 (Type Conversions)

> **EN**: Type Conversions
> **Summary**: Rust 类型转换 Type Conversions. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/01_foundation/02_type_system/14_coercion_and_casting.md](../../concept/01_foundation/02_type_system/14_coercion_and_casting.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/07_type_conversions.md](../../archive/knowledge/02_intermediate/07_type_conversions.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `as` 用于显式数值转换，可能截断或损失精度
2. `From/Into` 提供安全、可自定义的转换
3. `TryFrom/TryInto` 处理可能失败的转换
4. Deref 强制与引用转换发生在编译期

## 关键区分

| 方式 | 安全 | 失败处理 | 推荐度 |
|---|---|---|---|
| `From/Into` | 安全 | 不可失败 | 首选 |
| `TryFrom/TryInto` | 安全 | 返回 `Result` | 可能失败 |
| `as` | 可能溢出/截断 | 静默 | 谨慎使用 |

## 常见陷阱

- 浮点与整数 `as` 转换导致精度损失
- 忘记实现 `From` 导致 `?` 无法转换错误类型
- 混淆强制转换 (coercion) 与显式转换 (cast)

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/02_type_system/14_coercion_and_casting.md](../../concept/01_foundation/02_type_system/14_coercion_and_casting.md) 查看最新权威解释。
