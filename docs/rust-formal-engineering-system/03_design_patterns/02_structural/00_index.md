# 结构型模式（Structural Patterns）索引


## 📊 目录

- [目的](#目的)
- [核心模式](#核心模式)
- [Rust 化要点](#rust-化要点)
- [术语（Terminology）](#术语terminology)
- [实践与样例（Practice）](#实践与样例practice)
  - [文件级清单（精选）](#文件级清单精选)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 介绍结构型设计模式在 Rust 中的实现与应用。
- 提供对象组合与结构设计的最佳实践。

## 核心模式

- 适配器模式（Adapter）：接口转换与兼容
- 装饰器模式（Decorator）：动态添加功能
- 外观模式（Facade）：简化复杂子系统接口
- 桥接模式（Bridge）：抽象与实现分离
- 组合模式（Composite）：树形结构处理
- 代理模式（Proxy）：控制对象访问
- 享元模式（Flyweight）：共享细粒度对象

## Rust 化要点

- 所有权与借用：通过 `&`/`&mut`/`Arc`/`Rc` 表达共享关系
- 枚举与模式匹配：使用 `enum` 替代继承层次
- 零成本抽象：`trait` + 泛型实现零成本抽象
- 不可变优先：通过不可变数据 + 构建者实现可维护性

## 术语（Terminology）

- 结构型模式（Structural Patterns）
- 适配器（Adapter）、装饰器（Decorator）
- 外观（Facade）、桥接（Bridge）
- 组合（Composite）、代理（Proxy）、享元（Flyweight）

## 实践与样例（Practice）

- 设计模式实现：参见 [crates/c09_design_pattern](../../../crates/c09_design_pattern/)
- 泛型与 trait：[crates/c04_generic](../../../crates/c04_generic/)
- 控制与函数：[crates/c03_control_fn](../../../crates/c03_control_fn/)

### 文件级清单（精选）

- `crates/c09_design_pattern/src/structural/`：
  - `adapter.rs`：适配器模式实现
  - `decorator.rs`：装饰器模式实现
  - `facade.rs`：外观模式实现
  - `bridge.rs`：桥接模式实现
  - `composite.rs`：组合模式实现
  - `proxy.rs`：代理模式实现
  - `flyweight.rs`：享元模式实现

## 相关索引

- 理论基础（类型系统）：[`../../01_theoretical_foundations/01_type_system/00_index.md`](../../01_theoretical_foundations/01_type_system/00_index.md)
- 编程范式（面向对象）：[`../../02_programming_paradigms/04_object_oriented/00_index.md`](../../02_programming_paradigms/04_object_oriented/00_index.md)
- 质量保障（模式测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 创建型模式：[`../01_creational/00_index.md`](../01_creational/00_index.md)
- 行为型模式：[`../03_behavioral/00_index.md`](../03_behavioral/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
