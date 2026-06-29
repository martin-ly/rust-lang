# 错误处理与网络/Web 生态权威来源对齐矩阵

> **概念族**: 权威来源对齐 / 错误处理 / 网络 / Web
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [错误处理与网络/Web 生态权威来源对齐矩阵](#错误处理与网络web-生态权威来源对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、错误处理](#二错误处理)
  - [三、网络基础](#三网络基础)
  - [四、Web 框架](#四web-框架)
  - [五、Web 标准/协议](#五web-标准协议)
  - [六、与项目文档的映射](#六与项目文档的映射)
  - [七、未覆盖缺口](#七未覆盖缺口)
  - [相关概念](#相关概念)
  - [学术权威参考](#学术权威参考)

---

## 一、对齐说明

本文档将 `docs/research_notes/` 中的错误处理、网络基础与 Web 生态内容与国际化权威来源建立映射，覆盖：

- **错误处理**：从 `Result`/`Option`、`?` 操作符到库级错误抽象（`thiserror`、`anyhow`、`eyre`）。
- **网络基础**：tokio 异步 IO、`hyper` HTTP 实现、`tonic` gRPC 框架。
- **Web 框架与中间件**：`axum`、`actix-web`、`rocket`、`tower`、`tower-http`。
- **Web 标准/协议**：HTTP/1.1、HTTP/2、HTTP/3、WebSocket、OpenAPI。

对齐维度遵循本项目通用约定：概念定义、代码示例、版本特性、差异说明、反向追溯。

---

## 二、错误处理

| 概念/库 | 权威来源 | 项目文档 | 备注 |
|---------|----------|----------|------|
| `Result<T, E>` / `Option<T>` | [std::result](https://doc.rust-lang.org/std/result/) / [std::option](https://doc.rust-lang.org/std/option/) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | 可恢复错误与可选值 |
| `?` 操作符 | [Rust Reference - The question mark operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | 错误传播 |
| `std::error::Error` trait | [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html) | [10_std_library_alignment.md](10_std_library_alignment.md) | 错误对象抽象 |
| `panic!` / unwind | [Rust Reference - panic](https://doc.rust-lang.org/reference/runtime.html#the-panic-macro) / [Rust Book Ch 9.3](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html) | [10_rust_book_alignment.md](10_rust_book_alignment.md) §9 | 不可恢复错误 |
| `thiserror` | [docs.rs - thiserror](https://docs.rs/thiserror/) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | 库/库作者错误类型 |
| `anyhow` | [docs.rs - anyhow](https://docs.rs/anyhow/) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | 应用级错误传播 |
| `eyre` | [docs.rs - eyre](https://docs.rs/eyre/) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | 可定制报告链 |

---

## 三、网络基础

| 库/框架 | 权威来源 | 项目文档 | 备注 |
|---------|----------|----------|------|
| `tokio::net` | [Tokio Docs - tokio::net](https://docs.rs/tokio/latest/tokio/net/index.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | TCP/UDP 异步 IO |
| `hyper` | [hyper.rs](https://hyper.rs/) | [crates/c10_networks/](../../crates/c10_networks/README.md) / [software_design_theory/07_crate_architectures/08_hyper_architecture.md](software_design_theory/07_crate_architectures/08_hyper_architecture.md) | HTTP/1、HTTP/2 客户端/服务端 |
| `tonic` | [docs.rs - tonic](https://docs.rs/tonic/) | [crates/c10_networks/](../../crates/c10_networks/README.md) / [software_design_theory/07_crate_architectures/09_tonic_architecture.md](software_design_theory/07_crate_architectures/09_tonic_architecture.md) | gRPC over HTTP/2 |
| `mio` | [docs.rs - mio](https://docs.rs/mio/) | [software_design_theory/07_crate_architectures/21_mio_architecture.md](software_design_theory/07_crate_architectures/21_mio_architecture.md) | 跨平台 epoll/kqueue/IOCP |
| `h3` / `quinn` | [docs.rs - h3](https://docs.rs/h3/) / [docs.rs - quinn](https://docs.rs/quinn/) | [crates/c10_networks/](../../crates/c10_networks/README.md) | HTTP/3 + QUIC 实验/生产实现 |

---

## 四、Web 框架

| 框架/库 | 权威来源 | 项目文档 | 备注 |
|---------|----------|----------|------|
| `axum` | [docs.rs - axum](https://docs.rs/axum/) | [software_design_theory/07_crate_architectures/07_axum_architecture.md](software_design_theory/07_crate_architectures/07_axum_architecture.md) | 基于 Tower 的异步 Web 框架 |
| `actix-web` | [actix.rs](https://actix.rs/) | [software_design_theory/07_crate_architectures/12_actix_web_architecture.md](software_design_theory/07_crate_architectures/12_actix_web_architecture.md) | Actor 模型 Web 框架 |
| `rocket` | [rocket.rs](https://rocket.rs/) | [crates/c10_networks/](../../crates/c10_networks/README.md) | 类型驱动 Web 框架 |
| `tower` | [docs.rs - tower](https://docs.rs/tower/) | [software_design_theory/07_crate_architectures/02_tower_architecture.md](software_design_theory/07_crate_architectures/02_tower_architecture.md) | Service/Layer 中间件抽象 |
| `tower-http` | [docs.rs - tower-http](https://docs.rs/tower-http/) | [software_design_theory/07_crate_architectures/02_tower_architecture.md](software_design_theory/07_crate_architectures/02_tower_architecture.md) | HTTP 专用中间件集合 |

---

## 五、Web 标准/协议

| 标准/协议 | 权威来源 | 项目文档 | 备注 |
|-----------|----------|----------|------|
| HTTP/1.1 | [RFC 9112](https://www.rfc-editor.org/rfc/rfc9112.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | 报文格式与持久连接 |
| HTTP/2 | [RFC 9113](https://www.rfc-editor.org/rfc/rfc9113.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) / [software_design_theory/07_crate_architectures/08_hyper_architecture.md](software_design_theory/07_crate_architectures/08_hyper_architecture.md) | 二进制分帧、多路复用 |
| HTTP/3 | [RFC 9114](https://www.rfc-editor.org/rfc/rfc9114.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | 基于 QUIC 的无连接 HTTP |
| WebSocket | [RFC 6455](https://www.rfc-editor.org/rfc/rfc6455.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | 全双工通信 |
| OpenAPI | [OpenAPI Specification](https://spec.openapis.org/oas/latest.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | API 描述与代码生成 |

---

## 六、与项目文档的映射

| 项目文档 | 生态覆盖 | 权威来源 |
|----------|----------|----------|
| [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | Result、Option、`?`、panic、错误转换、thiserror/anyhow/eyre | Rust Book Ch 9、Rust Reference、std |
| [crates/c06_async/README.md](../../crates/c06_async/README.md) | 异步运行时、tokio 错误处理与任务管理 | Tokio Docs |
| [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | TCP/UDP、HTTP/1/2/3、WebSocket、gRPC、DNS、P2P | tokio::net、hyper、tonic、RFC 9112/9113/9114/6455 |
| [10_async_ecosystem_alignment.md](10_async_ecosystem_alignment.md) | tokio、hyper、axum、tonic 异步生态映射 | Tokio、hyper、axum、tonic 官方文档 |
| [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | axum、actix-web、hyper、tonic、tower 架构分析 | 官方文档与 crates.io 依赖分析 |
| [10_rust_book_alignment.md](10_rust_book_alignment.md) | Rust Book Ch 9 错误处理逐章映射 | The Rust Programming Language |
| [10_std_library_alignment.md](10_std_library_alignment.md) | `std::result`、`std::error::Error` 等核心 API | Rust Standard Library |
| [10_rust_reference_alignment.md](10_rust_reference_alignment.md) | panic、unwind、`?` 操作符等语言级语义 | Rust Reference |
| [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | API Guidelines 错误处理建议、错误类型设计 | Rust API Guidelines |
| [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) | Service Layer、Builder、Typestate 在 Web 框架中的应用 | Rust Design Patterns |

---

## 七、未覆盖缺口

1. `color-eyre` / `stable-eyre` 与错误报告可视化的专门对齐。
2. `reqwest` / `surf` 等高级 HTTP 客户端与 `hyper` 的选型矩阵。
3. `async-graphql` / `Juniper` 与 GraphQL 规范的对齐。
4. `tokio-tungstenite` / `fastwebsockets` 与 WebSocket RFC 的细粒度映射。
5. `utoipa` / `okapi` 等 OpenAPI 生成工具与 OpenAPI 3.1 规范的对齐。
6. HTTP/3 生产部署、QUIC 连接迁移与 0-RTT 的专项反例边界。

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Standard Library](https://doc.rust-lang.org/std/) | [Tokio](https://tokio.rs/) | [hyper](https://hyper.rs/) | [tonic](https://docs.rs/tonic/) | [axum](https://docs.rs/axum/) | [actix-web](https://actix.rs/) | [rocket](https://rocket.rs/) | [RFC 9112](https://www.rfc-editor.org/rfc/rfc9112.html) | [RFC 9113](https://www.rfc-editor.org/rfc/rfc9113.html) | [RFC 9114](https://www.rfc-editor.org/rfc/rfc9114.html) | [RFC 6455](https://www.rfc-editor.org/rfc/rfc6455.html) | [OpenAPI Specification](https://spec.openapis.org/oas/latest.html)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [错误处理速查卡](10_error_handling_cheatsheet.md)
- [异步生态权威来源对齐矩阵](10_async_ecosystem_alignment.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [Standard Library 对齐](10_std_library_alignment.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [社区最佳实践对齐](10_community_best_practices_alignment.md)
- [设计模式权威来源对齐](10_design_patterns_authoritative_alignment.md)
- [Crate 架构解构总索引](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
