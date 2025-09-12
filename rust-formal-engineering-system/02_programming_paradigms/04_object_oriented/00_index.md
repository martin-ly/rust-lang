# 面向对象范式（Object-Oriented Paradigm）索引

## 目的

- 在 Rust 的所有权与 trait 体系下，说明对象建模与多态方式。

## 核心要点

- 面向接口：`trait` 定义行为，`impl` 提供实现
- 多态路径：泛型单态化 vs `dyn Trait` 动态分发（开销与适用场景）
- 继承替代：组合、`enum` 变体、委托、宏生成
- 对象安全：对象安全规则与设计取舍

## 实践与示例

- 设计模式：`crates/c09_design_pattern/`
- 泛型与 trait：`crates/c04_generic/`
- 控制与函数：`crates/c03_control_fn/`

## 导航

- 返回范式总览：[`../`](../)
- 函数式范式：[`../03_functional/00_index.md`](../03_functional/00_index.md)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
