# 实践示例（Practical Examples）索引

## 目的

- 聚合示例入口与运行指引，形成可复制的最小可行方案（MVP）。

## 示例入口（仓库映射）

- 线程与同步：`crates/c05_threads/README.md`
- 异步与 Tokio：`crates/c06_async/README.md`
- 网络与协议：`crates/c10_networks/README.md`
- 微服务样板：`crates/c13_microservice/README.md`

### 子目录导航

- 异步示例：[`07_async_examples/00_index.md`](./07_async_examples/00_index.md)
- Web 示例：[`08_web_examples/00_index.md`](./08_web_examples/00_index.md)
- 系统示例：[`09_system_examples/00_index.md`](./09_system_examples/00_index.md)
- 嵌入式示例：[`10_embedded_examples/00_index.md`](./10_embedded_examples/00_index.md)
- 数据库示例：[`11_database_examples/00_index.md`](./11_database_examples/00_index.md)
- 消息队列示例：[`12_messaging_examples/00_index.md`](./12_messaging_examples/00_index.md)
- 可观测性示例：[`13_observability_examples/00_index.md`](./13_observability_examples/00_index.md)

## 示例矩阵（摘取）

- 并发/同步：scoped_threads、work_stealing、lockfree_ring_buffer
- 异步模式：select、JoinSet、背压、Semaphore 限流
- 网络：HTTP 客户端/服务端、WebSocket、UDP 回显、DNS 查询
- 微服务：Axum/Actix、gRPC、Volo、健康检查与指标

## 一键脚本说明

- Windows PowerShell 脚本：在相应 crate 的 `scripts/*.ps1` 目录（如 `c10_networks/scripts/`）
- Bash 脚本：`scripts/*.sh`（如 `c03_control_fn/build.sh`、`c04_generic/build.sh`）
- 可选使用 `just`：根目录 `justfile` 提供统一别名（如 `just dns-all`）

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 设计模式：[`../03_design_patterns/00_index.md`](../03_design_patterns/00_index.md)
- 工具链生态：[`../06_toolchain_ecosystem/00_index.md`](../06_toolchain_ecosystem/00_index.md)
