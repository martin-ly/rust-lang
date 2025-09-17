# 概览：设计模式（c09_design_pattern）

本模块系统整理结构型、创建型、行为型模式以及并发/异步/并行等现代范式在 Rust 的落地方式，并提供跨领域模式清单。

---

## 目录导航

- 顶层导航
  - 顶层说明：`README.md`
  - 章节导引：`09_design_patterns.md`
  - 版本对齐：`RUST_189_DESIGN_PATTERNS_ANALYSIS.md`

- 结构型（源码）
  - `src/structural/*/{define.rs, mod.rs}`（Adapter/Bridge/Composite/Decorator/Facade/Flyweight/Proxy）

- 创建型（源码）
  - `src/creational/*/{mod.rs, ...}`（Factory Method/Abstract Factory/Builder/Prototype/Singleton/Object Pool/Static Creation Method）

- 行为型（源码）
  - `src/behavioral/*/{define.rs, mod.rs}`（Strategy/Observer/Iterator/State/Command/Mediator/Memento/Interpreter/Visitor/Chain of Responsibility）

- 并发与并行（源码）
  - `src/concurrency/*`
  - `src/parallel/*`

- 领域专题（源码）
  - `web_framework_patterns.rs`、`database_patterns.rs`、`os_patterns.rs`、`game_engine_patterns.rs`

---

## 快速开始

1) 从 `09_design_patterns.md` 了解模块结构
2) 在 `src/structural/` 与 `src/behavioral/` 按模式逐个运行示例
3) 查阅 `tests/` 的集成测试以把握组合场景

---

## 待完善

- 增补“组合多个模式”的工程案例与评测
- 与 `c11_frameworks` 的框架性模式互链
