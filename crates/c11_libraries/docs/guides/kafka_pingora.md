# Kafka 与 Pingora 现状

> 适用范围：Rust 1.89+；本文档说明 Kafka 与 Pingora 的当前实现状态，风格遵循 `../../c10_networks/docs/STYLE.md`。


## 📊 目录

- [Kafka MVP 路线图（建议）](#kafka-mvp-路线图建议)
  - [MVP 配置矩阵（建议）](#mvp-配置矩阵建议)
- [Kafka 环境与配置要点](#kafka-环境与配置要点)
  - [Windows 安装步骤（librdkafka）](#windows-安装步骤librdkafka)
- [Pingora MVP 路线图（建议）](#pingora-mvp-路线图建议)
- [常见问题与排查](#常见问题与排查)


- Kafka（`mq-kafka`）目前保留最小骨架，未接入生产者/消费者真实实现，原因：
  - `rdkafka` 的配置项与运行环境较为复杂（librdkafka 依赖、SASL/TLS、多分区与消费组、偏移管理等），后续将提供精简默认配置与可选高级参数。

- Pingora（`proxy-pingora`）目前提供占位 `start`，未接入完整路由/上游/过滤器：
  - Pingora 适合构建高性能代理/网关，后续将提供最小可用反向代理与可插拔中间件接口示例（超时/限流/重试/熔断/Tracing）。

如需优先支持以上两项，请告知目标能力与最小可用范围（MVP），我将按需排期实现。

---

## Kafka MVP 路线图（建议）

- 阶段 1：最小可用
  - 生产者：幂等生产（`enable.idempotence=true`），基础压缩，错误重试（指数退避）
  - 消费者：订阅主题/分区，自动位点提交（可配置），优雅关闭
  - 基础配置：`bootstrap.servers`、`group.id`、`security.protocol`（PLAINTEXT/TLS/SASL）

- 阶段 2：可靠性与安全
  - 事务性生产（与幂等配合），手动位点提交，Rebalance 回调
  - TLS/SASL（PLAIN/SCRAM），证书校验
  - 指标：投递延迟、重试次数、位点滞后

- 阶段 3：高级能力
  - 分区键路由/一致性哈希，批量发送与压缩策略
  - 死信队列（DLQ）、重试主题
  - 端到端可观测：主题/分区/位点 span

### MVP 配置矩阵（建议）

- 生产者（最小）：
  - `bootstrap.servers`
  - `enable.idempotence=true`
  - `compression.type=zstd`（按需）
  - `request.timeout.ms=30000`
- 消费者（最小）：
  - `bootstrap.servers`
  - `group.id`
  - `auto.offset.reset=earliest`
  - `enable.auto.commit=true`（或改手动）

## Kafka 环境与配置要点

- 依赖：`librdkafka`（需在系统可用），Windows/WSL 环境注意路径与动态链接库
- 安全：在公有云/生产环境优先开启 TLS/SASL；妥善管理证书与密钥
- 位点管理：至少一次语义下，消费者逻辑需幂等；手动提交时确保在处理成功后提交

### Windows 安装步骤（librdkafka）

1. 使用 vcpkg：
   - 安装 vcpkg 并集成：`.\u200bvcpkg integrate install`
   - 安装包：`vcpkg install librdkafka:x64-windows`
   - 将 vcpkg 的 `installed\x64-windows\bin` 加入 `PATH`
2. 或使用预编译包：
   - 设置环境变量 `RDKAFKA_LIB_DIR` 与 `RDKAFKA_INCLUDE_DIR`
   - 确保 `rdkafka.dll` 可被加载（加入 `PATH`）
3. WSL 推荐：`sudo apt-get install librdkafka-dev`

## Pingora MVP 路线图（建议）

- 阶段 1：最小反代
  - 监听地址、静态上游、基础超时（连接/请求/上游）

- 阶段 2：中间件与路由
  - 可插拔中间件：限流、重试、熔断、Tracing
  - 路由：基于前缀/Host/权重；健康检查

- 阶段 3：TLS 与安全
  - 终止 TLS（SNI）、上游 TLS、ACL
  - 指标：QPS/P95/P99、上游可用率

## 常见问题与排查

- Kafka 无法连接：
  - 检查 `bootstrap.servers` 可达性与安全配置；查看 broker 日志
  - Windows 下确认 `librdkafka` 安装与动态库路径（`PATH`）
- 消费无消息：
  - 检查 `group.id`、`auto.offset.reset`，以及主题/分区权限
- Pingora 502/超时：
  - 检查上游可达性与超时设置；查看 CPU 与连接数限制

> 当你提供明确的 MVP 需求（主题数/分区、SASL/TLS、位点策略、代理路由规则等），我将据此优先实现并提供端到端示例。
