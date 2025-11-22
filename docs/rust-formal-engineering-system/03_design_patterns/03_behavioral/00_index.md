# 行为型模式（Behavioral Patterns）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [行为型模式（Behavioral Patterns）索引](#行为型模式behavioral-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

---

## 目的

- 介绍行为型设计模式在 Rust 中的实现与应用。
- 提供对象间通信与职责分配的最佳实践与 Rust 化改造方案。

---

## 核心模式

- **策略模式（Strategy）**: 定义算法族，使它们可以互换
- **观察者模式（Observer）**: 对象间一对多的依赖关系
- **命令模式（Command）**: 将请求封装为对象
- **状态模式（State）**: 允许对象在内部状态改变时改变行为
- **责任链模式（Chain of Responsibility）**: 将请求沿着处理者链传递
- **模板方法模式（Template Method）**: 定义算法骨架，子类实现步骤
- **访问者模式（Visitor）**: 在不改变元素类的前提下定义新操作
- **中介者模式（Mediator）**: 用一个中介对象封装一系列对象交互
- **备忘录模式（Memento）**: 在不破坏封装的前提下捕获对象状态
- **迭代器模式（Iterator）**: 提供顺序访问聚合对象元素的方法

---

## Rust 化要点

- **Trait 抽象**: 使用 Trait 定义行为接口
- **枚举状态**: 使用枚举实现状态机
- **闭包策略**: 使用闭包实现策略模式
- **迭代器**: 利用 Rust 内置迭代器

---

## 术语（Terminology）

- 行为型模式（Behavioral Patterns）
- 策略（Strategy）、观察者（Observer）、命令（Command）
- 状态（State）、责任链（Chain of Responsibility）
- 模板方法（Template Method）、访问者（Visitor）

---

## 📚 内容文档

- **[策略模式](./01_strategy_pattern.md)** - 策略模式详解和 Rust 实现 ✅
- **[观察者模式](./02_observer_pattern.md)** - 观察者模式详解和 Rust 实现 ✅

## 实践与样例（Practice）

### 文件级清单（精选）

- 参见 [`01_creational/`](../01_creational/) 目录下的相关示例
- 参见 [`crates/c09_design_pattern/`](../../../../crates/c09_design_pattern/) 目录

---

## 相关索引

- [创建型模式](../01_creational/00_index.md)
- [结构型模式](../02_structural/00_index.md)
- [设计模式总索引](../00_index.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 创建型模式：[`../01_creational/00_index.md`](../01_creational/00_index.md)
- 结构型模式：[`../02_structural/00_index.md`](../02_structural/00_index.md)
