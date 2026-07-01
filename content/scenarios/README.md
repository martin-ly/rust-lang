# Scenarios 目录

> **定位**: Rust 在**真实应用场景**中的能力映射：按领域划分的典型场景、技术选型、最佳实践与常见陷阱。
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **更新**: 随生态发展持续演进

---

## 目录结构

```text
content/scenarios/
├── README.md                              # 本文件
├── cli_tooling_scenarios.md               # CLI 工具开发场景
├── data_engineering_ml_scenarios.md       # 数据工程与机器学习场景
├── embedded_systems_scenarios.md          # 嵌入式系统场景
├── game_development_scenarios.md          # 游戏开发场景
├── systems_infrastructure_scenarios.md    # 系统基础设施场景
└── web_application_scenarios.md           # Web 应用场景
```
---

## 使用方式

每个场景文档通常包含：

1. **场景定义**：业务背景与技术约束
2. **Rust 优势**：为什么该场景适合 Rust
3. **核心技术栈**：常用 crate、工具链、架构模式
4. **典型架构**：模块划分与数据流
5. **最佳实践**：错误处理、测试、性能、安全
6. **常见陷阱**：新手易犯的错误与规避策略
7. **延伸阅读**：对应 `concept/` / `knowledge/` / `crates/` 中的深入内容

---

## 与主轨的关系

- `concept/` 回答 **"Rust 有什么机制"**。
- `knowledge/` 回答 **"如何学会 Rust"**。
- `content/scenarios/` 回答 **"在 X 场景下如何用 Rust 解决实际问题"**。
