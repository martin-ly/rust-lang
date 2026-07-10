# 错误处理指南

> **EN**: Error Handling Guide
> **Summary**: Practical guide to Rust error handling with Option, Result, panic, custom error types, and the `?` operator. Migrated to the error handling authority.
>
> **适用 Rust 版本**: 1.97.0+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/01_foundation/08_error_handling/32_error_handling_basics.md](../../../../concept/01_foundation/08_error_handling/32_error_handling_basics.md)

---

## 主题列表

- 可恢复错误 vs 不可恢复错误
- `Option<T>` 与 `Result<T, E>` 基础
- `?` 操作符与错误传播
- `panic!`、`unwrap`、`expect` 的适用场景
- 自定义错误类型与 `std::error::Error`
- `From` / `Into` 错误转换
- `anyhow` vs `thiserror` 选型
