# 测试（Testing）索引


## 📊 目录

- [目的](#目的)
- [测试类型](#测试类型)
- [核心概念](#核心概念)
- [工具链](#工具链)
- [实践与示例](#实践与示例)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 建立完整的测试体系：单元测试、集成测试、端到端测试、属性测试。
- 提供测试最佳实践与工具链集成方案。

## 测试类型

- 单元测试：函数级测试，使用 `#[cfg(test)]` 模块
- 集成测试：模块间接口测试，位于 `tests/` 目录
- 端到端测试：完整业务流程测试
- 属性测试：基于属性的随机测试（proptest/quickcheck）
- 基准测试：性能回归测试（criterion）

## 核心概念

- 测试金字塔：单元测试为主，集成测试为辅，端到端测试最少
- 测试隔离：每个测试独立运行，不依赖外部状态
- 测试数据：使用工厂模式或构建器模式生成测试数据
- 模拟与存根：使用 mock 对象隔离外部依赖

## 工具链

- 内置测试：`cargo test`、`#[test]`、`#[cfg(test)]`
- 属性测试：`proptest`、`quickcheck`
- 基准测试：`criterion`、`cargo bench`
- 覆盖率：`cargo tarpaulin`、`grcov`

## 实践与示例

- 基础测试：参见 [crates/c03_control_fn](../../../crates/c03_control_fn/)
- 并发测试：[crates/c05_threads](../../../crates/c05_threads/)
- 异步测试：[crates/c06_async](../../../crates/c06_async/)
- 网络测试：[crates/c10_networks](../../../crates/c10_networks/)

## 相关索引

- 质量保障总览：[`../00_index.md`](../00_index.md)
- 验证工具：[`../04_validation/00_index.md`](../04_validation/00_index.md)
- 自动化：[`../08_automation/00_index.md`](../08_automation/00_index.md)

## 导航

- 返回质量保障：[`../00_index.md`](../00_index.md)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 软件工程：[`../../05_software_engineering/00_index.md`](../../05_software_engineering/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
