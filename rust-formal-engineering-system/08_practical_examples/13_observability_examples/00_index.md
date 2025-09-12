# 可观测性示例（Observability Examples）索引

## 主题

- 指标：Prometheus 文本格式 `/metrics`
- 追踪：OpenTelemetry、Jaeger
- 剖析：pprof、火焰图

## 最小可运行示例

- `cargo run -p c13_microservice --example comprehensive_observability_demo`
- `OTEL_EXPORTER_OTLP_ENDPOINT=... cargo run -p c13_microservice --example comprehensive_observability_demo`

## 常见问题与排错

- 指标抓取不到：确认 `/metrics` 路由与防火墙；检查端口映射。
- tracing 无数据：核对 OTLP/Jaeger 端点与采样比例。
- pprof 导出失败：确认特性开关与生成的火焰图工具链。

## 运行

- 参见：`crates/c13_microservice/` 与 `crates/c10_networks/`
- 环境变量：`OTEL_EXPORTER_OTLP_ENDPOINT=...`

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
