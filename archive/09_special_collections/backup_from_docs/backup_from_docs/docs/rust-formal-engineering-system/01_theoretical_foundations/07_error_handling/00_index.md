# 错误处理（Error Handling）索引


## 📊 目录

- [模型](#模型)
- [策略与工具](#策略与工具)
- [实践与样例（Practice）](#实践与样例practice)
- [相关索引](#相关索引)
- [导航](#导航)


## 模型

- `Result<T, E>` 与 `Option<T>`：可恢复/不可恢复语义
- Panic 与不可恢复错误：边界与约束
- 错误分层：领域错误/技术错误/环境错误

## 策略与工具

- 错误类型设计：枚举化、细粒度 vs 聚合
- 错误传播：`?`、`thiserror`、`anyhow`
- 观测与SLO：错误率、重试、熔断

## 实践与样例（Practice）

- 错误处理基础：参见 [crates/c03_control_fn](../../../crates/c03_control_fn/)
- 网络错误处理：[crates/c10_networks](../../../crates/c10_networks/)
- 微服务错误处理：[crates/c13_microservice](../../../crates/c13_microservice/)

## 相关索引

- 类型系统（Result/Option 类型）：[`../01_type_system/00_index.md`](../01_type_system/00_index.md)
- 质量保障（错误测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 软件工程（错误策略）：[`../../05_software_engineering/00_index.md`](../../05_software_engineering/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
