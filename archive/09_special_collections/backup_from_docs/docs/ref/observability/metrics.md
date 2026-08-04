# Metrics

- 使用 OpenTelemetry 指标；可桥接 Prometheus exporter
- 语义约定：HTTP/gRPC 客户端/服务端统一命名与属性
- 关键 SLI：延迟（p50/p95/p99）、错误率、饱和度、队列深度

命名/单位/属性遵循 OTel 语义规范；维护每个服务的指标目录与说明。
