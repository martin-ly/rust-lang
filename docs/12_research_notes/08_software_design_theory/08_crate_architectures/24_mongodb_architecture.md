> **Canonical 说明**: 本文件专注 **mongodb-rust-driver 的 BSON 模型与异步（Async）连接池架构**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [数据库访问](../../../../concept/06_ecosystem/06_data_and_distributed/02_database_access.md)
> - [数据库系统](../../../../concept/06_ecosystem/06_data_and_distributed/04_database_systems.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。
> **⚠️ 历史文档提示**：
>
> 本文档反映 mongodb-rust-driver 3.x 在 Rust 1.96+ 生态下的设计状态。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / mongodb
>
> **层级**: L3-L5

---

# mongodb-rust-driver Crate 架构解构 {#mongodb-rust-driver-crate-架构解构}

> **EN**: Mongodb Architecture
> **Summary**: mongodb-rust-driver Crate 架构解构 Mongodb Architecture.
>
> **最后更新**: 2026-06-29
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L3-L5
> **知识领域**: 文档数据库、NoSQL、异步（Async） IO、分布式存储
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 1. 引言：Rust MongoDB 客户端的生态定位 {#1-引言rust-mongodb-客户端的生态定位}

>
> **[来源: [mongodb-rust-driver crates.io](https://crates.io/crates/mongodb)]**

`mongodb` crate 是 MongoDB 官方维护的 Rust 驱动，基于 Tokio 异步运行时（Runtime），使用 `bson` crate 处理 MongoDB 的原生 BSON 数据模型。它为 Rust 应用提供了从单机到副本集、分片集群的统一访问抽象，是 Rust 生态中构建文档型数据持久化层的首选客户端。

> [mongodb-rust-driver docs.rs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

与关系型 SQL 客户端不同，`mongodb-rust-driver` 的设计哲学是**"BSON 原生、类型可选、异步优先"**：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **数据模型** | `bson::Document` 与 serde 派生类型双轨 | 快速原型可用动态文档，生产代码可用强类型模型 |
| **核心抽象** | `Client` → `Database` → `Collection<T>` 三级层次 | 与 MongoDB 命名空间一一对应，语义清晰 |
| **运行时（Runtime）** | 纯 Tokio 异步 API，可选 `sync` feature | 与 Rust 异步生态对齐，同步场景可启用 feature |
| **类型安全** | `Serialize`/`Deserialize` 边界 + 泛型（Generics） `Collection<T>` | 编译期保证文档结构与 Rust 类型匹配 |
| **连接管理** | 内置连接池 + Server 选择器 + 拓扑监控 | 无需外部池即可支撑高并发 |

> [mongodb-rust-driver GitHub Repository](https://github.com/mongodb/mongo-rust-driver)(<https://github.com/mongodb/mongo-rust-driver>)

```rust,ignore
use mongodb::{Client, bson::doc};

let client = Client::with_uri_str("mongodb://127.0.0.1:27017").await?;
let db = client.database("rust_learning");
let coll = db.collection::<mongodb::bson::Document>("items");

coll.insert_one(doc! { "name": "rust", "score": 95 }).await?;
```

> [来源: mongodb-rust-driver Examples](https://github.com/mongodb/mongo-rust-driver/tree/main/tests)

---

## 2. 核心 API 架构 {#2-核心-api-架构}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 三层命名空间：Client / Database / Collection {#21-三层命名空间client-database-collection}

```mermaid
graph TD
    CLIENT[Client<br/>集群连接 + 连接池 + 拓扑监控]
    CLIENT -->|database(name)| DB[Database<br/>数据库级操作]
    DB -->|collection::<T>(name)| COLL[Collection<T><br/>CRUD / 索引 / 聚合 / 变更流]
    COLL -->|watch| CS[ChangeStream<br/>变更流]
    COLL -->|aggregate| CURSOR[Cursor<T><br/>聚合/查询结果游标]
    COLL -->|create_index| INDEX[IndexModel<br/>索引定义]
    CLIENT -->|start_session| SESSION[ClientSession<br/>事务会话]
```

> [mongodb-rust-driver Client Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

| 类型 | 职责 | 共享能力 |
|:--|:--|:--|
| `Client` | 维护连接池、拓扑监控、服务器选择器 | `Clone` 后共享同一个连接池 |
| `Database` | 执行数据库级命令（如 `drop_database`） | 由 `Client` 派生，可 `Clone` |
| `Collection<T>` | CRUD、聚合、索引、变更流 | 内部使用 `Arc`，可安全跨任务共享 |

> [mongodb-rust-driver Collection Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

### 2.2 CRUD 操作：BSON 与强类型模型 {#22-crud-操作bson-与强类型模型}

`Collection<T>` 通过 serde 支持两种使用方式：

```rust,ignore
use mongodb::bson::doc;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Item {
    name: String,
    score: i32,
}

let typed_coll = db.collection::<Item>("items");
typed_coll.insert_one(Item { name: "rust".into(), score: 95 }).await?;

// 动态 BSON 文档路径
let doc_coll = db.collection::<mongodb::bson::Document>("items");
let found = doc_coll.find_one(doc! { "name": "rust" }).await?;
```

> [来源: mongodb-rust-driver CRUD Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)

**关键设计**：`insert_one`/`find_one`/`update_one`/`delete_one` 等方法将 BSON 的动态性约束在 `Document` 类型与 serde 序列化边界内，业务层可获得静态类型保证。

### 2.3 聚合管道（Aggregation Pipeline） {#23-聚合管道aggregation-pipeline}

聚合通过 `Vec<Document>` 描述管道阶段，返回 `Cursor<T>` 实现流式消费：

```rust,ignore
use futures::stream::TryStreamExt;

let pipeline = vec![
    doc! { "$match": { "status": "active" } },
    doc! { "$group": { "_id": "$category", "total": { "$sum": "$amount" } } },
    doc! { "$sort": { "total": -1 } },
];

let mut cursor = coll.aggregate(pipeline).await?;
while let Some(doc) = cursor.try_next().await? {
    println!("{:?}", doc);
}
```

> [mongodb-rust-driver Aggregate Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

`Cursor` 同时实现 `Stream<Item = Result<T>>` 与 `advance()`/`deserialize_current()` 手动模式，兼容 `futures::StreamExt`/`TryStreamExt` 组合子。

### 2.4 索引：类型安全的 `IndexModel` {#24-索引类型安全的-indexmodel}

```rust,ignore
use mongodb::{IndexModel, options::IndexOptions};

let index = IndexModel::builder()
    .keys(doc! { "name": 1 })
    .options(IndexOptions::builder().unique(true).build())
    .build();

coll.create_index(index).await?;
```

> [来源: mongodb-rust-driver Index Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)

索引模型使用 builder 模式避免字段缺失，并通过 `IndexOptions` 控制唯一性、TTL、部分索引等高级行为。

### 2.5 变更流（Change Streams） {#25-变更流change-streams}

变更流基于 MongoDB Oplog，提供副本集/分片集群上的事件订阅：

```rust,ignore
let mut change_stream = coll.watch().await?;
while let Some(event) = change_stream.next_if_any().await? {
    println!("op={:?}, doc={:?}", event.operation_type, event.full_document);
}
```

> [mongodb-rust-driver ChangeStream Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

`ChangeStream` 内置断点续传：通过 `resume_token()` 获取恢复令牌，可在故障后使用 `resume_after`/`start_after` 选项重建流。

### 2.6 事务与会话 {#26-事务与会话}

多文档事务通过 `ClientSession` 显式管理：

```rust,ignore
let mut session = client.start_session().await?;
session.start_transaction().await?;

// 操作必须传入 session 才会纳入事务
coll.insert_one(doc! { "x": 1 }).session(&mut session).await?;
coll.delete_one(doc! { "y": 2 }).session(&mut session).await?;

session.commit_transaction().await?;
```

> [来源: mongodb-rust-driver Transaction Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)

**重要边界**：事务需要副本集或分片集群；单节点 `mongod` 不支持多文档事务。

### 2.7 连接池与客户端选项 {#27-连接池与客户端选项}

`ClientOptions` 控制连接池大小、读写关注、TLS、超时等关键参数：

```rust,ignore
use mongodb::options::{ClientOptions, ServerApi, ServerApiVersion};

let mut opts = ClientOptions::parse("mongodb://127.0.0.1:27017").await?;
opts.max_pool_size = Some(64);
opts.server_api = Some(ServerApi::builder().version(ServerApiVersion::V1).build());

let client = Client::with_options(opts)?;
```

> [mongodb-rust-driver ClientOptions Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

连接池内置于 `Client`，默认大小与 MongoDB 官方驱动推荐值一致；通过 `Clone` 共享 `Client` 即可获得池复用，无需额外引入第三方池 crate。

---

## 3. 类型系统利用 {#3-类型系统利用}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 维度 | API | 类型系统（Type System）价值 |
|:--|:--|:--|
| **集合类型参数** | `Collection<T>` | `T: Serialize + DeserializeOwned + Send + Sync`，编译期保证文档-类型映射 |
| **BSON 宏（Macro）** | `bson::doc!` | 在编译期构造 `Document`，避免运行时字符串拼接 |
| **Options Builder** | `ClientOptions::builder()` / `IndexModel::builder()` | Typestate 模式避免非法配置状态 |
| **Session 传递** | `.session(&mut session)` | 通过显式参数将操作绑定到事务边界，避免隐式上下文 |
| **错误类型** | `mongodb::error::Error` / `Result<T>` | 所有 IO 与协议错误必须在调用点处理 |

> [mongodb-rust-driver Error Docs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)(<https://docs.rs/mongodb/latest/mongodb/struct.Collection.html>)

---

## 4. 反例边界 {#4-反例边界}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 未处理 `Document` / `Bson` 类型转换失败 | 运行时序列化错误、字段缺失 | 对动态文档使用 `Option<T>` 或显式模式校验；优先使用 serde 强类型模型 |
| 连接泄漏（未复用 `Client`） | 每个请求新建连接，耗尽文件描述符 | `Clone` 同一个 `Client` 或 `Collection`，依赖内置连接池 |
| 索引误用（如单节点使用唯一索引忽略 `_id` 规则） | 写冲突、性能退化 | 理解 MongoDB 索引语义，使用 `IndexOptions` 精确控制 |
| 在异步上下文阻塞等待驱动 Future | 线程阻塞、吞吐量崩溃 | 始终 `await` 驱动返回的 Future；超时通过 `tokio::time::timeout` 作用于 `JoinHandle` 而非直接包裹驱动 Future |
| 忽略事务拓扑要求 | 单节点 `mongod` 调用事务返回错误 | 仅在副本集/分片集群启用事务 |
| 变更流未处理 resume token | 故障后丢失事件 | 定期读取 `change_stream.resume_token()` 并在重建流时使用 |
| 未配置读写关注 | 数据一致性（Coherence）问题 | 根据业务需求显式设置 `ReadConcern`/`WriteConcern` |

> [MongoDB 官方文档](https://www.mongodb.com/docs/)(<https://www.mongodb.com/docs/>)

**特别警示**：mongodb-rust-driver 官方文档明确警告，**不要直接对驱动返回的 Future 使用 `tokio::time::timeout` 后丢弃**，因为这会让驱动内部状态不一致。正确做法是将驱动操作 `spawn` 到任务中，再对 `JoinHandle` 做超时。

---

## 5. 代码示例锚点 {#5-代码示例锚点}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| 基本 CRUD | [`crates/c10_networks/examples/mongodb_basic_crud.rs`](../../../../crates/c10_networks/examples/mongodb_basic_crud.rs) | Client/Database/Collection、插入/查询/更新/删除/索引 |
| 聚合与变更流 | [`crates/c10_networks/examples/mongodb_aggregation_change_streams.rs`](../../../../crates/c10_networks/examples/mongodb_aggregation_change_streams.rs) | Aggregation Pipeline、Change Stream 骨架 |

> [c10_networks Crate](https://github.com/rust-lang/rust)(../../../../crates/c10_networks/README.md)

---

## 6. 相关架构与延伸阅读 {#6-相关架构与延伸阅读}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Tokio 异步运行时架构](06_tokio_architecture.md)
- [redis-rs 缓存/消息架构](23_redis_architecture.md)
- [SQLx 数据库工具架构](09_sqlx_architecture.md)
- [异步编程模型](../../../../concept/03_advanced/01_async/01_async.md)
- [分布式模式](../../../../concept/03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md)
- [数据库与存储生态权威来源对齐](../../01_alignment_matrices/19_database_storage_cloud_alignment.md)

---

## 权威来源索引 {#权威来源索引}

> **[来源: [mongodb-rust-driver crates.io](https://crates.io/crates/mongodb)]**
> **[来源: [mongodb-rust-driver docs.rs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)]**
> **[来源: [mongodb-rust-driver GitHub](https://github.com/mongodb/mongo-rust-driver)]**
> **[来源: [MongoDB 官方文档](https://www.mongodb.com/docs/)]**
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
> **权威来源**: [mongodb-rust-driver crates.io](https://crates.io/crates/mongodb), [mongodb-rust-driver docs.rs](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html), [MongoDB 官方文档](https://www.mongodb.com/docs/)
>
> **权威来源对齐变更日志**: 2026-06-29 创建 mongodb 生态专题，对齐 mongodb-rust-driver 3.x 官方文档与 MongoDB 官方参考

---

## 权威来源参考 {#权威来源参考}

> **P0（官方/必读）**:
>
> - [来源: [mongodb-rust-driver Documentation](https://docs.rs/mongodb/latest/mongodb/struct.Collection.html)]
> - [来源: [mongodb-rust-driver crates.io](https://crates.io/crates/mongodb)]
> - [来源: [MongoDB 官方文档](https://www.mongodb.com/docs/)]
> - [来源: [MongoDB BSON 规范](https://bsonspec.org/)]
> **P1（学术论文/演讲）**:
>
> - [来源: [MongoDB: The Definitive Guide (O'Reilly)](https://www.oreilly.com/library/view/mongodb-the-definitive/9781491954461/)] — 文档数据库模型与分布式一致性
> - [来源: [Conflict-free Replicated Data Types](https://hal.inria.fr/file/index/docid/555588/filename/techreport.pdf)] — 与变更流/最终一致性相关的理论基础
> **P2（仓库/社区文章）**:
>
> - [来源: [mongodb-rust-driver GitHub Repository](https://github.com/mongodb/mongo-rust-driver)]
> - [来源: [MongoDB Developer Center](https://www.mongodb.com/developer/)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneasverif.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
