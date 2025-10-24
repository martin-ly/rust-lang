# 行为型模式（Behavioral Patterns）索引


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

- 介绍行为型设计模式在 Rust 中的实现与应用。
- 提供对象间通信与职责分配的最佳实践。

## 核心模式

- 策略模式（Strategy）：算法族封装与切换
- 观察者模式（Observer）：发布-订阅机制
- 命令模式（Command）：请求封装为对象
- 职责链模式（Chain of Responsibility）：请求处理链
- 状态模式（State）：对象状态变化
- 访问者模式（Visitor）：操作与对象结构分离
- 解释器模式（Interpreter）：语言解释
- 备忘录模式（Memento）：状态保存与恢复
- 迭代器模式（Iterator）：集合遍历
- 中介者模式（Mediator）：对象间通信协调
- 模板方法模式（Template Method）：算法骨架定义

## Rust 化要点

- 枚举与模式匹配：使用 `enum` 替代状态机继承
- 闭包与函数指针：策略模式的函数式实现
- 迭代器：内置迭代器模式支持
- 所有权与借用：通过所有权系统管理对象生命周期

## 术语（Terminology）

- 行为型模式（Behavioral Patterns）
- 策略（Strategy）、观察者（Observer）
- 命令（Command）、职责链（Chain of Responsibility）
- 状态（State）、访问者（Visitor）
- 迭代器（Iterator）、中介者（Mediator）

## 实践与样例（Practice）

- 设计模式实现：参见 [crates/c09_design_pattern](../../../crates/c09_design_pattern/)
- 泛型与 trait：[crates/c04_generic](../../../crates/c04_generic/)
- 控制与函数：[crates/c03_control_fn](../../../crates/c03_control_fn/)

### 文件级清单（精选）

- `crates/c09_design_pattern/src/behavioral/`：
  - `strategy.rs`：策略模式实现
  - `observer.rs`：观察者模式实现
  - `command.rs`：命令模式实现
  - `chain_of_responsibility.rs`：职责链模式实现
  - `state.rs`：状态模式实现
  - `visitor.rs`：访问者模式实现
  - `iterator.rs`：迭代器模式实现
  - `mediator.rs`：中介者模式实现

## 相关索引

- 理论基础（类型系统）：[`../../01_theoretical_foundations/01_type_system/00_index.md`](../../01_theoretical_foundations/01_type_system/00_index.md)
- 编程范式（函数式）：[`../../02_programming_paradigms/03_functional/00_index.md`](../../02_programming_paradigms/03_functional/00_index.md)
- 质量保障（模式测试）：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 创建型模式：[`../01_creational/00_index.md`](../01_creational/00_index.md)
- 结构型模式：[`../02_structural/00_index.md`](../02_structural/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
