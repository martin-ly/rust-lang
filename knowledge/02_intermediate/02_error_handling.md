# 错误处理 (Error Handling)

> **权威来源**: 本主题深度解释见 [concept/02_intermediate/04_error_handling.md](../../concept/02_intermediate/04_error_handling.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/02_error_handling.md](../../archive/knowledge/02_intermediate/02_error_handling.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 可恢复错误使用 `Result<T, E>`，不可恢复使用 `panic!`
2. `?` 运算符自动传播 `Result`/`Option`
3. `From` trait 支持错误类型自动转换
4. 自定义错误通常实现 `std::error::Error`

## 关键区分

| 场景 | 返回值 | 推荐方式 |
|---|---|---|
| 调用者能处理 | `Result<T, E>` | `?` / `match` |
| 程序状态不可恢复 | `panic!` | 断言/崩溃 |

## 常见陷阱

- 在 `main` 外滥用 `unwrap`
- 错误类型未实现 `From` 导致 `?` 不兼容
- 混淆 `Option` 与 `Result` 的语义

---

**详细内容已迁移**：请点击上方 [concept/02_intermediate/04_error_handling.md](../../concept/02_intermediate/04_error_handling.md) 查看最新权威解释。
