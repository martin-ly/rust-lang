# 数据库示例（Database Examples）索引

## 主题

- ORM：SQLx、Diesel、SeaORM
- 连接池与超时：bb8、deadpool、sqlx 的池参数
- 迁移与版本：sqlx migrate、sea-orm-cli、diesel migration

## 最小可运行示例

- `DATABASE_URL=... cargo run -p c13_microservice --example grpc_service`
- `DATABASE_URL=... cargo test -p c13_microservice --features with-sqlx`

## 常见问题与排错

- 连接失败：检查防火墙/凭据；增大连接超时与重试次数。
- 迁移不一致：统一使用同一迁移工具与版本；在 CI 校验迁移历史。
- 连接池耗尽：增加池大小或优化查询；添加超时与熔断策略。

## 运行

- 参见：`crates/c13_microservice/` 示例与 README
- 环境变量：`DATABASE_URL=...`

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 微服务：[`../../../crates/c13_microservice`](../../../crates/c13_microservice/)
