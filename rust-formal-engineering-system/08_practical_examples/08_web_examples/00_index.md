# Web 示例（Web Examples）索引

## 框架

- Axum、Actix-Web、Warp、Tide

## 示例清单（摘取）

- 基础路由与中间件
- 表单与JSON处理
- WebSocket 回显与心跳
- 认证与授权（JWT/OAuth2）

## 最小可运行示例

- `cargo run -p c10_networks --example ws_echo_server`
- `cargo run -p c10_networks --example ws_echo_client`

## 常见问题与排错

- 端口被占用：修改示例端口或释放占用进程。
- CORS 问题：在中间件中显式允许来源与方法。
- WebSocket 断开：确认心跳机制与超时时间。

## 运行

- 参见：`crates/c13_microservice/README.md`
- 命令：`cargo run --example ws_echo_server` / `ws_echo_client` 等

## 导航

- 返回实践示例：[`../00_index.md`](../00_index.md)
- 微服务：[`../../crates/c13_microservice`](../../../crates/c13_microservice/)
