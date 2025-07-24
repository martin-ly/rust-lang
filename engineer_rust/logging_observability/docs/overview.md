# 日志与可观测性（Logging & Observability）

## 1. 工程原理与定义（Principle & Definition）

日志与可观测性是指通过系统性采集、分析和关联日志、指标、追踪等数据，实现对系统内部状态的透明洞察。这体现了“可观测性三要素”与“系统透明性”哲学。Rust 以类型安全、tracing生态和metrics库支持严谨的可观测性工程。
Logging and observability refer to systematically collecting, analyzing, and correlating logs, metrics, and traces to achieve transparent insight into system internal states. This reflects the philosophy of the "three pillars of observability" and system transparency. Rust supports rigorous observability engineering via type safety, the tracing ecosystem, and metrics libraries.

## 2. Rust 1.88 新特性工程化应用

- tracing/metrics/log库：统一采集日志、指标与追踪。
- OpenTelemetry集成：标准化分布式可观测性。
- #[expect]属性：日志测试中的预期异常标注。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用tracing/metrics/log采集与分析运行时数据。
- 用OpenTelemetry实现分布式追踪。
- 用trait抽象可观测性接口，提升系统透明性。
- 用CI自动化测试日志与指标采集。

**最佳实践：**

- 抽象日志、指标与追踪接口，分离采集与分析逻辑。
- 用tracing/metrics统一可观测性数据流。
- 用OpenTelemetry提升分布式系统可观测性。
- 用自动化测试验证可观测性覆盖与准确性。

## 4. 常见问题 FAQ

- Q: Rust如何实现统一可观测性？
  A: 用tracing/metrics/log统一采集，OpenTelemetry标准化分布式追踪。
- Q: 如何保证日志与指标的准确性？
  A: 用类型系统约束数据结构，自动化测试验证采集与分析。
- Q: 如何做可观测性的自动化测试？
  A: 用CI集成日志与指标采集测试。

## 5. 参考与扩展阅读

- [tracing 日志与追踪](https://github.com/tokio-rs/tracing)
- [metrics 指标采集](https://metrics.rs/)
- [OpenTelemetry 分布式可观测性](https://opentelemetry.io/)
