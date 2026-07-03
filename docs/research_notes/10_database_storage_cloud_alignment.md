# 数据库、存储与云原生生态权威来源对齐矩阵 {#数据库存储与云原生生态权威来源对齐矩阵}

> **EN**: Database Storage Cloud Alignment
> **Summary**: 数据库、存储与云原生生态权威来源对齐矩阵 Database Storage Cloud Alignment.
> **概念族**: 权威来源对齐 / 数据库 / 存储 / 云原生
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [数据库、存储与云原生生态权威来源对齐矩阵 {#数据库存储与云原生生态权威来源对齐矩阵}](#数据库存储与云原生生态权威来源对齐矩阵-数据库存储与云原生生态权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、关系型数据库 {#二关系型数据库}](#二关系型数据库-二关系型数据库)
  - [三、KV / 缓存 / NoSQL {#三kv-缓存-nosql}](#三kv--缓存--nosql-三kv-缓存-nosql)
  - [四、消息队列 {#四消息队列}](#四消息队列-四消息队列)
  - [五、云原生与可观测性 {#五云原生与可观测性}](#五云原生与可观测性-五云原生与可观测性)
  - [六、容器 / Docker / Kubernetes 部署参考 {#六容器-docker-kubernetes-部署参考}](#六容器--docker--kubernetes-部署参考-六容器-docker-kubernetes-部署参考)
  - [七、与项目文档的映射 {#七与项目文档的映射}](#七与项目文档的映射-七与项目文档的映射)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的数据库、存储、分布式消息与云原生内容与 Rust 生态的权威来源建立映射。

覆盖范围：

- **关系型数据库**: ORM、查询构建器、原生驱动；
- **KV / 缓存 / NoSQL**: 内存缓存、嵌入式 KV、文档数据库；
- **消息队列**: Kafka、RabbitMQ、NATS 的 Rust 客户端；
- **云原生**: Kubernetes 客户端、可观测性（OpenTelemetry、Prometheus）、代理/服务网格；
- **部署参考**: Docker、Kubernetes、Helm 等容器化部署的权威文档。

对齐维度：概念定义、API 用法、版本兼容性、项目内部示例与架构文档的反向追溯。

---

## 二、关系型数据库 {#二关系型数据库}

| 库/框架 | 官方来源 | 项目文档 | 覆盖内容 |
|---------|----------|----------|----------|
| **Diesel** | [diesel.rs](https://diesel.rs/) / [docs.rs/diesel](https://docs.rs/diesel/) | [software_design_theory/07_crate_architectures/03_diesel_architecture.md](software_design_theory/07_crate_architectures/03_diesel_architecture.md) | 类型安全 ORM、Typestate 查询构建、后端抽象 |
| **SQLx** | [launchbadge/sqlx](https://github.com/launchbadge/sqlx) / [docs.rs/sqlx](https://docs.rs/sqlx/) | [software_design_theory/07_crate_architectures/09_sqlx_architecture.md](software_design_theory/07_crate_architectures/09_sqlx_architecture.md) / [15_sqlx_advanced_architecture.md](software_design_theory/07_crate_architectures/15_sqlx_advanced_architecture.md) | 编译期 SQL 验证、`query!` / `query_as!`、连接池 |
| **SeaORM** | [sea-ql.org/SeaORM](https://www.sea-ql.org/SeaORM/) / [docs.rs/sea-orm](https://docs.rs/sea-orm/) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | 异步 ORM、Entity/Relation、迁移 |
| **rusqlite** | [rusqlite/rusqlite](https://github.com/rusqlite/rusqlite) / [docs.rs/rusqlite](https://docs.rs/rusqlite/) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | SQLite 同步驱动、参数化查询、事务 |

---

## 三、KV / 缓存 / NoSQL {#三kv-缓存-nosql}

| 库/框架 | 官方来源 | 项目文档 | 覆盖内容 |
|---------|----------|----------|----------|
| **redis-rs** | [redis-rs/redis-rs](https://github.com/redis-rs/redis-rs) / [docs.rs/redis](https://docs.rs/redis/) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | Redis 客户端、连接池、Pub/Sub |
| **mini-redis** | [tokio-rs/mini-redis](https://github.com/tokio-rs/mini-redis) / [docs.rs/mini-redis](https://docs.rs/mini-redis/) | [crates/c06_async/README.md](../../crates/c06_async/README.md) | Tokio 官方教学实现、RESP 协议、异步网络 |
| **sled** | [spacejam/sled](https://github.com/spacejam/sled) / [docs.rs/sled](https://docs.rs/sled/) | — | 嵌入式 KV 存储、B-tree、MVCC 事务 |
| **mongodb-rust-driver** | [mongodb/mongo-rust-driver](https://github.com/mongodb/mongo-rust-driver) / [docs.rs/mongodb](https://docs.rs/mongodb/) | — | MongoDB 异步驱动、BSON、聚合管道 |

---

## 四、消息队列 {#四消息队列}

| 库/框架 | 官方来源 | 项目文档 | 覆盖内容 |
|---------|----------|----------|----------|
| **rdkafka** | [fede1024/rust-rdkafka](https://github.com/fede1024/rust-rdkafka) / [docs.rs/rdkafka](https://docs.rs/rdkafka/) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | Kafka 生产/消费、流处理、offset 管理 |
| **lapin** | [amqp-rs/lapin](https://github.com/amqp-rs/lapin) / [docs.rs/lapin](https://docs.rs/lapin/) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | RabbitMQ AMQP 客户端、异步通道、QoS |
| **nats-rs** | [nats-io/nats.rs](https://github.com/nats-io/nats.rs) / [docs.rs/nats](https://docs.rs/nats/) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | NATS 同步/异步客户端、Pub/Sub、JetStream |

---

## 五、云原生与可观测性 {#五云原生与可观测性}

| 库/框架 | 官方来源 | 项目文档 | 覆盖内容 |
|---------|----------|----------|----------|
| **kube-rs** | [kube.rs](https://kube.rs/) / [docs.rs/kube](https://docs.rs/kube/) | [k8s/deployment.yaml](../../k8s/deployment.yaml) / [k8s/service.yaml](../../k8s/service.yaml) | Kubernetes 类型安全客户端、Controller、CRD |
| **opentelemetry-rust** | [open-telemetry/opentelemetry-rust](https://github.com/open-telemetry/opentelemetry-rust) / [docs.rs/opentelemetry](https://docs.rs/opentelemetry/) | [software_design_theory/07_crate_architectures/18_tracing_architecture.md](software_design_theory/07_crate_architectures/18_tracing_architecture.md) | Trace/Metric/Log、Exporter、Context 传播 |
| **prometheus (client_rust)** | [prometheus/client_rust](https://github.com/prometheus/client_rust) / [docs.rs/prometheus](https://docs.rs/prometheus/) | [software_design_theory/07_crate_architectures/18_tracing_architecture.md](software_design_theory/07_crate_architectures/18_tracing_architecture.md) | Counter/Gauge/Histogram、注册表、文本导出 |
| **Envoy / Rust proxy** | [envoyproxy/envoy](https://github.com/envoyproxy/envoy) / [hyper.rs](https://hyper.rs/) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | 服务网格/代理层、HTTP 反向代理、中间件 |

---

## 六、容器 / Docker / Kubernetes 部署参考 {#六容器-docker-kubernetes-部署参考}

| 技术 | 权威来源 | 项目资源 | 说明 |
|------|----------|----------|------|
| **Docker** | [Docker Docs](https://docs.docker.com/) | — | 多阶段构建、镜像分层、非 root 容器 |
| **Kubernetes** | [Kubernetes Docs](https://kubernetes.io/docs/) | [k8s/configmap.yaml](../../k8s/configmap.yaml) / [deployment.yaml](../../k8s/deployment.yaml) / [service.yaml](../../k8s/service.yaml) | Deployment、Service、ConfigMap 模板 |
| **Helm** | [Helm Docs](https://helm.sh/docs/) | — | Chart 包管理、Values 注入、Release 升级 |
| **OCI / containerd** | [OCI Spec](https://opencontainers.org/) / [containerd](https://containerd.io/) | — | 镜像规范、运行时接口 |

> **说明**: `10_microservice_template.md` 目前尚未创建，相关微服务示例代码可参考 `examples/microservice_template.rs`。

---

## 七、与项目文档的映射 {#七与项目文档的映射}

| 项目文档 | 生态覆盖 | 权威来源 |
|----------|----------|----------|
| [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | Diesel、SQLx、SeaORM、rusqlite 架构解构 | 官方文档、docs.rs |
| [software_design_theory/07_crate_architectures/03_diesel_architecture.md](software_design_theory/07_crate_architectures/03_diesel_architecture.md) | Diesel ORM、Typestate 查询 | Diesel 官方 |
| [software_design_theory/07_crate_architectures/09_sqlx_architecture.md](software_design_theory/07_crate_architectures/09_sqlx_architecture.md) / [15_sqlx_advanced_architecture.md](software_design_theory/07_crate_architectures/15_sqlx_advanced_architecture.md) | SQLx 编译期验证与连接池 | SQLx 官方 |
| [crates/c10_networks/README.md](../../crates/c10_networks/README.md) | Redis、Kafka、RabbitMQ、NATS、代理层 | 各客户端官方文档 |
| [crates/c06_async/README.md](../../crates/c06_async/README.md) | mini-redis、异步网络模型 | Tokio/mini-redis |
| [software_design_theory/07_crate_architectures/18_tracing_architecture.md](software_design_theory/07_crate_architectures/18_tracing_architecture.md) | OpenTelemetry、Prometheus、Tracing | OTel/Prometheus 官方 |
| [10_distributed_pattern_matrix.md](10_distributed_pattern_matrix.md) | 消息队列、CQRS、Event Sourcing、Saga、Outbox | 分布式模式经典参考 |
| [k8s/deployment.yaml](../../k8s/deployment.yaml) / [service.yaml](../../k8s/service.yaml) | Kubernetes 部署模板 | Kubernetes 官方 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. **SeaORM** 与 **rusqlite** 的专项架构解构文档尚未建立。
2. **Redis Cluster**、**Sentinel** 模式与 Rust 客户端的完整映射。
3. **Kafka Streams**、**RabbitMQ 死信队列**、**NATS JetStream** 的 Rust 实践案例。
4. **MongoDB** 聚合管道、Change Streams、事务在 Rust 驱动中的边界示例。
5. **sled** 的事务隔离级别、崩溃恢复与性能权衡。
6. **kube-rs** Controller / Operator 模式的完整实战示例与反例。
7. **OpenTelemetry** Collector、Baggage、Propagator 与 Rust 服务的端到端示例。
8. **Prometheus Service Discovery**、**Alertmanager** 与 Rust 生态的集成。
9. **Helm Chart** 与 **Kustomize** 配置未在项目仓库中落地。
10. **Envoy WASM/Rust 扩展** 与 **Linkerd/服务网格** 的对齐内容。

> **权威来源**: [Diesel](https://diesel.rs/) | [SQLx](https://github.com/launchbadge/sqlx) | [SeaORM](https://www.sea-ql.org/SeaORM/) | [rusqlite](https://github.com/rusqlite/rusqlite) | [redis-rs](https://github.com/redis-rs/redis-rs) | [mini-redis](https://github.com/tokio-rs/mini-redis) | [sled](https://github.com/spacejam/sled) | [mongodb-rust-driver](https://github.com/mongodb/mongo-rust-driver) | [rust-rdkafka](https://github.com/fede1024/rust-rdkafka) | [lapin](https://github.com/amqp-rs/lapin) | [nats.rs](https://github.com/nats-io/nats.rs) | [kube-rs](https://kube.rs/) | [opentelemetry-rust](https://github.com/open-telemetry/opentelemetry-rust) | [prometheus/client_rust](https://github.com/prometheus/client_rust) | [Envoy](https://github.com/envoyproxy/envoy) | [Kubernetes](https://kubernetes.io/docs/) | [Docker](https://docs.docker.com/)
> **官方来源**: [Rust Standard Library](https://doc.rust-lang.org/std/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [异步生态权威来源对齐](10_async_ecosystem_alignment.md)
- [分布式模式特性矩阵](10_distributed_pattern_matrix.md)
- [Rust 工业级 Crate 架构解构总索引](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md)
- [知识图谱索引](10_knowledge_graph_index.md)
- [研究笔记完整索引](INDEX.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
