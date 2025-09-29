# 理论基础（Theoretical Foundations）索引

## 目的

- 汇总 Rust 相关的理论支撑：类型系统、语义学、代数/范畴、并发语义等。
- 为实践模块提供可溯源的概念与形式化框架。

## 子模块

- 类型系统：[`./01_type_system/00_index.md`](./01_type_system/00_index.md)
- 内存安全：[`./02_memory_safety/00_index.md`](./02_memory_safety/00_index.md)
- 所有权与借用：[`./03_ownership_borrowing/00_index.md`](./03_ownership_borrowing/00_index.md)
- 并发模型：[`./04_concurrency_models/00_index.md`](./04_concurrency_models/00_index.md)
- Trait 系统：[`./05_trait_system/00_index.md`](./05_trait_system/00_index.md)
- 生命周期管理：[`./06_lifetime_management/00_index.md`](./06_lifetime_management/00_index.md)
- 错误处理：[`./07_error_handling/00_index.md`](./07_error_handling/00_index.md)
- 宏系统：[`./08_macro_system/00_index.md`](./08_macro_system/00_index.md)
- 形式化验证：[`./09_formal_verification/00_index.md`](./09_formal_verification/00_index.md)
- 数学基础：[`./10_mathematical_foundations/00_index.md`](./10_mathematical_foundations/00_index.md)

## 关键概念

- 类型与所有权：安全内存管理与别名控制的理论基础。
- 操作语义与类型化操作语义：行为与安全性质推导。
- 范畴/代数结构：抽象与组合的形式化工具。
- 错误语义：可恢复/不可恢复错误、效果系统关联。

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 编程范式：[`../02_programming_paradigms/`](../02_programming_paradigms/)
- 质量保障：[`../10_quality_assurance/`](../10_quality_assurance/)
- 返回项目根：[`../README.md`](../README.md)

## 配套示例（跨仓库）

- 泛型与抽象：工作区 [crates/c04_generic/](../../crates/c04_generic/)
- 控制流与函数式：[crates/c03_control_fn/](../../crates/c03_control_fn/)
- 并发与异步：[crates/c05_threads/](../../crates/c05_threads/)、[crates/c06_async/](../../crates/c06_async/)
- 分布式一致性与 SWIM：[crates/c20_distributed/](../../crates/c20_distributed/)

## 相关索引

- 编程范式（理论在实践中的应用）：[`../02_programming_paradigms/01_synchronous/00_index.md`](../02_programming_paradigms/01_synchronous/00_index.md) ・ [`../02_programming_paradigms/02_async/00_index.md`](../02_programming_paradigms/02_async/00_index.md)
- 质量保障（形式化验证工具）：[`../10_quality_assurance/00_index.md`](../10_quality_assurance/00_index.md)
- 研究议程（前沿理论方向）：[`../09_research_agenda/00_index.md`](../09_research_agenda/00_index.md)
