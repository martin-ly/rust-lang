# 宏系统（Macro System）索引

## 主题

- 宏种类：声明式宏（macro_rules!）、过程宏（派生、属性、函数样式）
- 展开与卫生：展开阶段、作用域、标识符卫生
- 设计建议：语义清晰、错误信息友好、最小可见性、避免过度魔法

## 工具与实践

- `proc-macro` crate 结构与测试策略
- `syn`/`quote` 解析与生成
- 错误定位与 `Span` 使用

## 实践与样例（Practice）

- 宏开发：参见 [crates/c04_generic](../../../crates/c04_generic/)
- 过程宏：[crates/c09_design_pattern](../../../crates/c09_design_pattern/)
- 代码生成：[crates/c03_control_fn](../../../crates/c03_control_fn/)

## 相关索引

- 类型系统（宏与类型系统交互）：[`../01_type_system/00_index.md`](../01_type_system/00_index.md)
- 工具链生态（宏工具）：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 质量保障（宏测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
