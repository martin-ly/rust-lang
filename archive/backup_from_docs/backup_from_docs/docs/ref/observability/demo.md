# OTLP 本地演示

前置依赖：Docker（Jaeger/Tempo）、Prometheus、Grafana。

快速启动：

- 启动：`scripts/observability/start-stack.ps1`
- 停止：`scripts/observability/stop-stack.ps1`
- 访问：Grafana `http://localhost:3000`（admin/admin）、Prometheus `http://localhost:9090`

环境变量（示例服务）：

- OTEL_EXPORTER_OTLP_ENDPOINT=<http://localhost:4317（gRPC）或> <http://localhost:4318（HTTP）>
- OTEL_METRICS_EXPORTER=otlp
- OTEL_TRACES_SAMPLER=parentbased_always_on（dev）
- OTEL_SERVICE_NAME=example-service

验证：

1. 运行示例服务（如 `c13_microservice/examples/*observability_demo*`）
2. 造流量（curl/ab/hey）
3. 在 Grafana/Tempo/Prometheus 验证 traces/metrics/logs。
