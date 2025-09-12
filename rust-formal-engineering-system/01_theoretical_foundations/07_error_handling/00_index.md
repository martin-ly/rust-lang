# 错误处理（Error Handling）索引

## 模型

- `Result<T, E>` 与 `Option<T>`：可恢复/不可恢复语义
- Panic 与不可恢复错误：边界与约束
- 错误分层：领域错误/技术错误/环境错误

## 策略与工具

- 错误类型设计：枚举化、细粒度 vs 聚合
- 错误传播：`?`、`thiserror`、`anyhow`
- 观测与SLO：错误率、重试、熔断

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
