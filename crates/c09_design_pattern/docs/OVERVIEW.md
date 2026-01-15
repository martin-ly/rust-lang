# 概览：设计模式（c09_design_pattern）

本模块系统整理结构型、创建型、行为型模式以及并发/异步/并行等现代范式在 Rust 的落地方式，并提供跨领域模式清单。

**最后更新**: 2025-12-25
**适用版本**: Rust 1.92.0+ (Edition 2024)

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

1) 从 [Tier 1 基础层](./tier_01_foundations/) 开始学习
   - [项目概览](./tier_01_foundations/01_项目概览.md) - 快速了解设计模式
   - [主索引导航](./tier_01_foundations/02_主索引导航.md) - 找到适合你的学习路径
   - [术语表](./tier_01_foundations/03_术语表.md) - 核心术语速查
   - [常见问题](./tier_01_foundations/04_常见问题.md) - 解决常见疑问
2) 从 `09_design_patterns.md` 了解模块结构
3) 在 `src/structural/` 与 `src/behavioral/` 按模式逐个运行示例
4) 查阅 `tests/` 的集成测试以把握组合场景

---

## 待完善

- 增补“组合多个模式”的工程案例与评测
- 与 `c11_frameworks` 的框架性模式互链

### 组合模式工程案例（补全）

- ✅ **案例 A：Web 服务** (`src/pattern_combinations.rs`)
  - 组合：Facade + Builder + Strategy（路由策略）+ Circuit Breaker（并发模式）
  - 实现：`WebServerFacade`、`HttpRequestBuilder`、`RoutingStrategy`、`CircuitBreaker`
  - 测试：`tests/pattern_combinations_tests.rs`
  - 指标：QPS、错误率、熔断触发与半开恢复时间

- ✅ **案例 B：游戏引擎子系统** (`src/pattern_combinations.rs`)
  - 组合：Observer（事件总线）+ Command（输入映射）+ State（AI 状态机）
  - 实现：`GameEngine`、`EventBus`、`CommandMapper`、`AiStateManager`
  - 测试：`tests/pattern_combinations_tests.rs`
  - 指标：事件延迟、状态转换、资源占用

- ✅ **评测与测试**
  - 集成测试：验证模式组合的正确性
  - 并发安全测试：多线程环境下的正确性
  - 性能测试：吞吐量与延迟评估

### 互链

- 与 `c11_frameworks`：对齐 MVC/MVVM、依赖注入、插件化架构的模式清单
