# 面向对象范式（Object-Oriented Paradigm）索引

## 目的

- 在 Rust 的所有权与 trait 体系下，说明对象建模与多态方式。

## 核心要点

- 面向接口：`trait` 定义行为，`impl` 提供实现
- 多态路径：泛型单态化 vs `dyn Trait` 动态分发（开销与适用场景）
- 继承替代：组合、`enum` 变体、委托、宏生成
- 对象安全：对象安全规则与设计取舍

## 实践与示例

- 设计模式：[crates/c09_design_pattern](../../../crates/c09_design_pattern/)
- 泛型与 trait：[crates/c04_generic](../../../crates/c04_generic/)
- 控制与函数：[crates/c03_control_fn](../../../crates/c03_control_fn/)

## 相关索引

- 理论基础（Trait 系统）：[`../../01_theoretical_foundations/05_trait_system/00_index.md`](../../01_theoretical_foundations/05_trait_system/00_index.md)
- 设计模式（面向对象模式）：[`../../03_design_patterns/00_index.md`](../../03_design_patterns/00_index.md)
- 质量保障（面向对象测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 函数式范式：[`../03_functional/00_index.md`](../03_functional/00_index.md)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
