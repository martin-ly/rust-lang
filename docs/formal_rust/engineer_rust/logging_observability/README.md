# 日志与可观测性（Logging & Observability）

## 1. 定义与软件工程对标

**日志与可观测性**用于记录系统运行状态、分析问题和提升可维护性。软件工程wiki认为，Logging/Observability是现代系统运维的基础。
**Logging & observability** means recording system state, analyzing issues, and improving maintainability. In software engineering, logging/observability is foundational for modern operations.

## 2. Rust 1.88 最新特性

- **tracing/metrics支持结构化日志与指标**
- **trait对象向上转型**：便于多日志后端适配。
- **LazyLock**：全局日志配置缓存。

## 3. 典型惯用法（Idioms）

- 使用log/tracing/metrics收集日志与指标
- 结合serde/json导出日志数据
- 利用trait抽象日志后端与适配器

## 4. 代码示例

```rust
use tracing::info;
info!("user_login", user_id = 42);
```

## 5. 软件工程概念对照

- **可追踪性（Traceability）**：结构化日志提升问题定位效率。
- **可维护性（Maintainability）**：集中日志管理便于维护。
- **自动化告警（Alerting）**：日志平台支持自动化响应。

## 6. FAQ

- Q: Rust日志系统的优势？
  A: 性能高、类型安全、生态丰富，适合高并发日志场景。

---
