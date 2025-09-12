# 消息队列示例（Messaging Examples）索引

## 主题

- Redis：发布/订阅、流（XADD/XREAD）
- RabbitMQ：队列、交换器、路由键
- 背压与重试：有界通道、确认、死信

## 最小可运行示例

- `REDIS_URL=... cargo run -p c13_microservice --example messaging_advanced_demo`
- `AMQP_URL=... cargo run -p c13_microservice --example messaging_advanced_demo`

## 常见问题与排错

- 连接不稳定：设置重试与指数退避；校验超时与心跳。
- 消息堆积：确认消费者速率与背压策略；设置死信队列。
- 序列化错误：统一使用 `serde` 与版本锁定，避免 schema 漂移。

## 运行

- 参见：`crates/c13_microservice/` 示例与 README
- 环境变量：`REDIS_URL=...`、`AMQP_URL=...`

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 微服务：[`../../../crates/c13_microservice`](../../../crates/c13_microservice/)
