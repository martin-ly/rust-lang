# 作业与评测骨架

- c01-c02：所有权/借用/类型系统练习
  - 例：实现安全的切片分割函数、带生命周期约束的缓存结构
  - 运行：`scripts/ci/assignments/c01_ownership.ps1`、`scripts/ci/assignments/c02_type_system.ps1`
- c05-c06：并发/异步作业
  - 例：实现有界队列的背压策略；补充一个可能竞态的示例并用 Loom 捕获
  - 运行：`cargo test -p c05_threads`、`cargo test -p c06_async`
- c10-c13：网络/微服务作业
  - 例：为 REST/gRPC 接口补充契约测试；接入 OTLP 并输出自定义业务指标
  - 运行：`scripts/observability/start-stack.ps1` 后执行对应 crate 示例

统一评测：`scripts/ci/grade.ps1` 会执行 fmt、clippy、tests（nextest）等门禁；作业通过各模块脚本执行补充分科测试。
