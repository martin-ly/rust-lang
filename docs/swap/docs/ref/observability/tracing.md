# Tracing

- 传播：W3C TraceContext 与 Baggage
- 导出：OTLP gRPC/HTTP，支持环境变量配置
- 资源：service.name、service.version、deployment.environment
- 中间件：HTTP（axum/hyper）、gRPC（tonic）拦截器统一注入/传播
- 采样：parent-based，按环境配置比例/尾采样策略

Checklist：

- 在入口创建根 span 并向下游传播上下文
- 错误记录：设置状态与事件，避免在 attributes 中包含敏感信息
- 日志关联 trace_id/span_id，实现日志-追踪联动
