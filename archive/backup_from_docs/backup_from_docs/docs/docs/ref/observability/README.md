# 可观测性总览（OTLP / OpenTelemetry）

本目录定义追踪、指标与日志三栈的统一规范与落地指南，遵循 OpenTelemetry 与 OTLP 语义约定，并面向本仓库网络/微服务/分布式示例统一对齐。

- Tracing：tracing + tracing-subscriber + opentelemetry-otlp
- Metrics：OpenTelemetry Metrics（可并行暴露 Prometheus）
- Logs：结构化 JSON，关联 trace/spanId，可导出 OTLP logs

详见：`tracing.md`、`metrics.md`、`logging.md`、`demo.md`。
