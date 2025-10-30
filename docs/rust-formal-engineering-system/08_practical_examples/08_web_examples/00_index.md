> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# Web 示例（Web Examples）索引

## 📊 目录

- [Web 示例（Web Examples）索引](#web-示例web-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [Web 框架](#web-框架)
    - [HTTP 服务](#http-服务)
    - [数据库集成](#数据库集成)
    - [认证与授权](#认证与授权)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 提供 Rust Web 开发的实用示例。
- 展示如何构建高性能的 Web 应用。

## 核心示例

### Web 框架

- Axum 框架示例
- Actix Web 示例
- Warp 框架示例
- Rocket 框架示例

### HTTP 服务

- REST API 实现
- GraphQL 服务
- WebSocket 服务
- 静态文件服务

### 数据库集成

- SQLite 集成示例
- PostgreSQL 集成示例
- MongoDB 集成示例
- Redis 集成示例

### 认证与授权

- JWT 认证示例
- OAuth 集成示例
- 会话管理示例
- 权限控制示例

## 实践与样例

- Web 示例：参见 [crates/c67_web_development](../../../crates/c67_web_development/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)
- 网络编程：[crates/c10_networks](../../../crates/c10_networks/)

### 文件级清单（精选）

- `crates/c67_web_development/src/`：
  - `web_frameworks.rs`：Web 框架示例
  - `http_services.rs`：HTTP 服务示例
  - `database_integration.rs`：数据库集成示例
  - `authentication.rs`：认证授权示例
- `crates/c13_microservice/src/`：
  - `web_microservice.rs`：Web 微服务示例
  - `api_gateway.rs`：API 网关示例
  - `service_mesh.rs`：服务网格示例

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 应用领域（云基础设施）：[`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 异步示例：[`../07_async_examples/00_index.md`](../07_async_examples/00_index.md)
- 系统示例：[`../09_system_examples/00_index.md`](../09_system_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
