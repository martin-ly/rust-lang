# 函数式范式（Functional Paradigm）索引

## 目的

- 总结函数式编程在 Rust 中的落地方式与适用场景。
- 统一与命令式/面向对象范式的对照与协作边界。

## 术语

- 纯函数、副作用隔离、引用透明
- 不可变数据、代数数据类型（ADT）
- 高阶函数、组合子、迭代器链

## 核心概念

- 拥抱不可变：优先不可变结构，必要时局部可变（`RefCell`/`Cell`/`mut`）
- 代数数据类型：`enum` + 模式匹配建模业务状态机
- 组合优先：`Iterator`/`Option`/`Result` 组合器与零成本抽象

## 实践与示例

- 控制与函数：`crates/c03_control_fn/`
- 泛型与 trait：`crates/c04_generic/`
- 算法与迭代器：`crates/c08_algorithms/`

## 导航

- 返回范式总览：[`../`](../)
- 同步范式：[`../01_synchronous/00_index.md`](../01_synchronous/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 面向对象：[`../04_object_oriented/00_index.md`](../04_object_oriented/00_index.md)
