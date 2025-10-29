# 创建型模式（Creational Patterns）索引

## 📊 目录

- [创建型模式（Creational Patterns）索引](#创建型模式creational-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍创建型设计模式在 Rust 中的实现与应用。
- 提供对象创建的最佳实践与 Rust 化改造方案。

## 核心模式

- 单例模式（Singleton）：全局唯一实例，受限实现
- 工厂方法（Factory Method）：通过工厂函数创建对象
- 抽象工厂（Abstract Factory）：创建相关对象族
- 建造者模式（Builder）：分步构建复杂对象
- 原型模式（Prototype）：通过克隆创建对象

## Rust 化要点

- 所有权优先：通过所有权转移而非共享状态
- 零成本抽象：使用泛型与 trait 实现零成本抽象
- 类型安全：编译时保证类型正确性
- 不可变优先：优先使用不可变数据结构

## 术语（Terminology）

- 创建型模式（Creational Patterns）
- 工厂方法（Factory Method）、抽象工厂（Abstract Factory）
- 建造者（Builder）、原型（Prototype）
- 单例（Singleton）、全局状态（Global State）

## 实践与样例（Practice）

- 设计模式实现：参见 [crates/c09_design_pattern](../../../crates/c09_design_pattern/)
- 泛型与 trait：[crates/c04_generic](../../../crates/c04_generic/)
- 控制与函数：[crates/c03_control_fn](../../../crates/c03_control_fn/)

### 文件级清单（精选）

- `crates/c09_design_pattern/src/creational/`：
  - `singleton.rs`：单例模式的 Rust 实现
  - `factory_method.rs`：工厂方法模式
  - `abstract_factory.rs`：抽象工厂模式
  - `builder.rs`：建造者模式
  - `prototype.rs`：原型模式

## 相关索引

- 理论基础（Trait 系统）：[`../../01_theoretical_foundations/05_trait_system/00_index.md`](../../01_theoretical_foundations/05_trait_system/00_index.md)
- 编程范式（面向对象）：[`../../02_programming_paradigms/04_object_oriented/00_index.md`](../../02_programming_paradigms/04_object_oriented/00_index.md)
- 质量保障（模式测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 结构型模式：[`../02_structural/00_index.md`](../02_structural/00_index.md)
- 行为型模式：[`../03_behavioral/00_index.md`](../03_behavioral/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
