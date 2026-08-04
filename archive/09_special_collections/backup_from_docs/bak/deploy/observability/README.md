# 观测性栈（Docker Compose）

包含：OpenTelemetry Collector、Grafana Tempo、Prometheus、Grafana。

使用：

- 启动：`scripts/observability/start-stack.ps1`
- 停止：`scripts/observability/stop-stack.ps1`

端口：

- OTLP gRPC: 4317
- OTLP HTTP: 4318
- Prometheus: 9090
- Grafana: 3000（admin/admin）
