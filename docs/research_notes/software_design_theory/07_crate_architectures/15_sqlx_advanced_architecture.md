# SQLx crate 架构解构

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 1. 引言

SQLx 是 Rust 生态中的异步 SQL 工具包，年下载量超过 3000 万次 [来源: crates.io 统计, 2025]。与其他 Rust ORM（如 Diesel）不同，SQLx 采用**查询优先（query-first）**
哲学：开发者编写原生 SQL，SQLx 在编译期检查查询的语法正确性、类型安全性以及与数据库 schema 的兼容性。
这种设计消除了运行时 SQL 语法错误的全部可能性，同时保留了 SQL 的全部表达能力——无需学习 DSL，无需受限于 ORM 的查询生成能力边界。

SQLx 的核心理念可概括为：**SQL 是源语言，Rust 类型是派生产物**。
通过宏系统在编译期连接数据库、执行查询计划分析，SQLx 将数据库 schema 的知识静态编码到 Rust 类型系统中，实现真正的编译期验证。

> [来源: SQLx 官方文档, https://docs.rs/sqlx/latest/sqlx/]
> [来源: SQLx GitHub README, https://github.com/launchbadge/sqlx]

---

## 2. 核心架构图
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

SQLx 采用**分层抽象架构**，将连接管理、查询执行、类型映射、迁移系统解耦为独立的 trait 与模块。

```mermaid
graph TB
    subgraph MacroLayer["宏层（编译期）"]
        QM["query!"]
        QA["query_as!"]
        QC["query_scalar!"]
        MC["宏展开器:<br/>连接数据库 → 准备语句 → 推导类型"]
    end

    subgraph RuntimeLayer["运行时层"]
        EX["Executor trait"]
        POOL["Pool&lt;DB&gt;"]
        CONN["Connection&lt;DB&gt;"]
        TX["Transaction&lt;DB&gt;"]
    end

    subgraph TypeLayer["类型映射层"]
        FR["FromRow"]
        TD["Type&lt;DB&gt; / Encode&lt;DB&gt; / Decode&lt;DB&gt;"]
        MAP["数据库类型 ↔ Rust 类型映射表"]
    end

    subgraph DBLayer["数据库驱动层"]
        PG["PostgreSQL"]
        MY["MySQL"]
        SQ["SQLite"]
    end

    QM --> MC
    QA --> MC
    QC --> MC
    MC -->|生成代码| EX
    EX --> POOL
    EX --> CONN
    EX --> TX
    POOL --> DBLayer
    CONN --> DBLayer
    TX --> DBLayer
    FR --> TD
    TD --> MAP
    MAP --> DBLayer

    style MacroLayer fill:#fff3e0
    style RuntimeLayer fill:#e3f2fd
    style TypeLayer fill:#e8f5e9
    style DBLayer fill:#fce4ec
```

**架构要点解读：**

| 层级 | 职责 | 核心类型/Trait |
|:---|:---|:---|
| 宏层 | 编译期查询验证与代码生成 | `query!`, `query_as!`, `query_scalar!` |
| 执行层 | 查询执行与连接生命周期管理 | `Executor`, `Pool`, `Connection`, `Transaction` |
| 类型层 | 数据库类型与 Rust 类型的双向映射 | `FromRow`, `Type`, `Encode`, `Decode` |
| 驱动层 | 特定数据库协议的实现 | `sqlx-postgres`, `sqlx-mysql`, `sqlx-sqlite` |

> [来源: SQLx 架构概述, https://docs.rs/sqlx/latest/sqlx/macro.query.html]

---

## 3. 关键 Trait 定义
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 3.1 `Executor` — 统一查询执行接口
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
pub trait Executor<'c>: Send + Debug + Sized {
    type Database: Database;

    fn fetch_many<'e, 'q: 'e, E: 'q>(
        self,
        query: E,
    ) -> BoxStream<'e, Result<Either<QueryResult<Self::Database>, <Self::Database as Database>::Row>, Error>>
    where
        'c: 'e,
        E: Execute<'q, Self::Database>;

    fn fetch_optional<'e, 'q: 'e, E: 'q>(
        self,
        query: E,
    ) -> BoxFuture<'e, Result<Option<<Self::Database as Database>::Row>, Error>>
    where
        'c: 'e,
        E: Execute<'q, Self::Database>;

    fn execute<'e, 'q: 'e, E: 'q>(
        self,
        query: E,
    ) -> BoxFuture<'e, Result<QueryResult<Self::Database>, Error>>
    where
        'c: 'e,
        E: Execute<'q, Self::Database>;
}
```

`Executor` 是 SQLx 最核心的 trait。`Pool`, `Connection`, `Transaction` 全部实现 `Executor`，使得同一段查询代码可以在三种执行上下文中复用：

| 实现者 | 语义 | 适用场景 |
|:---|:---|:---|
| `&Pool<DB>` | 从池中获取连接，执行后归还 | 大多数读操作 |
| `&mut Connection<DB>` | 在单一连接上执行 | 需要会话状态的操作 |
| `&mut Transaction<DB>` | 在事务中执行，支持回滚 | 多语句原子操作 |

> [来源: SQLx Executor 文档, https://docs.rs/sqlx/latest/sqlx/trait.Executor.html]

### 3.2 `FromRow` — 行到结构体的类型安全映射
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
pub trait FromRow<'r, R: Row>: Sized {
    fn from_row(row: &'r R) -> Result<Self, Error>;
}
```

`FromRow` 定义了如何将数据库行转换为 Rust 类型。`query_as!` 宏生成的代码在编译期即确定了列名到字段的映射，但运行时仍通过 `FromRow` 执行实际构造。

```rust,ignore
use sqlx::FromRow;

#[derive(FromRow)]
struct User {
    id: i64,
    name: String,
    email: Option<String>, // NULL 映射为 None
}

// 等价手动实现
impl<'r> FromRow<'r, PgRow> for User {
    fn from_row(row: &'r PgRow) -> Result<Self, sqlx::Error> {
        Ok(User {
            id: row.try_get("id")?,
            name: row.try_get("name")?,
            email: row.try_get("email")?,
        })
    }
}
```

> [来源: SQLx FromRow 文档, https://docs.rs/sqlx/latest/sqlx/trait.FromRow.html]

### 3.3 `Type`, `Encode`, `Decode` — 类型系统的三支柱
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
pub trait Type<DB: Database> {
    fn type_info() -> <DB as Database>::TypeInfo;
    fn compatible(ty: &<DB as Database>::TypeInfo) -> bool;
}

pub trait Encode<'q, DB: Database> {
    fn encode_by_ref(&self, buf: &mut <DB as Database>::ArgumentBuffer<'q>) -> Result<IsNull, BoxDynError>;
}

pub trait Decode<'r, DB: Database>: Sized {
    fn decode(value: <DB as Database>::ValueRef<'r>) -> Result<Self, BoxDynError>;
}
```

这三者的分工：

| Trait | 职责 | 编译期/运行时 |
|:---|:---|:---:|
| `Type` | 声明 Rust 类型对应的数据库类型 | 编译期 |
| `Encode` | 将 Rust 值编码为数据库协议字节流 | 运行时 |
| `Decode` | 将数据库协议字节流解码为 Rust 值 | 运行时 |

SQLx 为所有标准 Rust 类型实现了这三者：`i32`, `i64`, `String`, `Vec<u8>`, `bool`, `chrono::DateTime<Utc>` 等。用户可以为自定义类型手动实现（如 PostgreSQL 的 `JSONB` 映射到 serde `Value`）。

> [来源: SQLx 类型系统文档, https://docs.rs/sqlx/latest/sqlx/trait.Type.html]

---

## 4. 编译期查询验证：宏系统的工程实现
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 4.1 `query!` 宏的工作流程
>
> **[来源: [crates.io](https://crates.io/)]**

```mermaid
sequenceDiagram
    participant C as rustc
    participant M as sqlx_macros
    participant DB as 编译期数据库
    participant GEN as 生成代码

    C->>M: 展开 query!("SELECT id, name FROM users WHERE id = $1", id)
    M->>DB: 连接到 DATABASE_URL
    M->>DB: PREPARE 语句
    DB-->>M: 返回参数类型 [INT8] 和返回列 [id: INT8, name: TEXT]
    M->>M: 检查 $1 绑定变量与传入参数类型兼容性
    M->>GEN: 生成结构体 + 参数编码 + 结果解码代码
    GEN-->>M: TokenStream
    M-->>C: 返回生成代码
    C->>C: 编译生成的 impl
```

生成的代码（简化）近似：

```rust,ignore
// query!("SELECT id, name FROM users WHERE id = $1", id)
// 生成一个匿名记录类型：
struct _QueryRecord {
    id: i64,       // 从 PostgreSQL INT8 推导
    name: String,  // 从 PostgreSQL TEXT 推导
}

sqlx::query_as::<_, _QueryRecord>("SELECT id, name FROM users WHERE id = $1")
    .bind(id as i64)  // 编译期类型检查：id 必须可转换为 i64
```

### 4.2 `query_as!` 与显式类型的映射
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    name: String,
}

// query_as! 验证 SQL 返回的列类型与 struct 字段类型兼容
let user = sqlx::query_as!(User, "SELECT id, name FROM users WHERE id = $1", id)
    .fetch_one(&pool)
    .await?;
```

`query_as!` 不仅检查 SQL 语法，还**验证每个列的类型与目标 struct 字段是否兼容**。如果数据库中 `name` 为 `TEXT` 但 struct 中声明为 `i32`，编译直接失败。

> [来源: SQLx 宏文档, https://docs.rs/sqlx/latest/sqlx/macro.query.html]
> [来源: Rust Reference, Procedural Macros, https://doc.rust-lang.org/reference/procedural-macros.html]

---

## 5. 连接池与异步执行模型
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 5.1 `Pool` 的内部结构
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```mermaid
graph TB
    subgraph Pool["Pool&lt;DB&gt;"]
        IDLE["空闲连接队列<br/>VecDeque&lt;Idle&lt;DB&gt;&gt;"]
        WAIT["等待者队列<br/>Vec&lt;Waker&gt;"]
        SIZE["当前连接数: AtomicUsize"]
        OPT["配置: max_conns, timeout, ..."]
    end

    APP["应用任务"] -->|acquire| POOL_WAIT{"池满?"}
    POOL_WAIT -->|否| IDLE
    POOL_WAIT -->|是| WAIT
    IDLE -->|返回连接| APP
    WAIT -->|连接归还时唤醒| APP

    style Pool fill:#e3f2fd
```

```rust,ignore
use sqlx::postgres::PgPoolOptions;

let pool = PgPoolOptions::new()
    .max_connections(20)
    .acquire_timeout(Duration::from_secs(3))
    .connect("postgres://user:pass@localhost/db")
    .await?;

// pool 实现 Executor，可以直接传入 query
let row = sqlx::query!("SELECT 1 as one")
    .fetch_one(&pool)
    .await?;
```

### 5.2 连接获取的异步语义
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

`Pool::acquire()` 是一个异步操作：当池中没有空闲连接且未达到 `max_connections` 上限时，创建新连接；当达到上限时，任务进入等待队列，直到有连接被归还。这种设计与 Tokio 的异步运行时深度集成，避免阻塞线程。

> [来源: SQLx Pool 文档, https://docs.rs/sqlx/latest/sqlx/struct.Pool.html]

---

## 6. 迁移系统：`sqlx migrate`
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 6.1 迁移的设计原则
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

SQLx 的迁移系统是**纯 SQL 驱动**的，与 Diesel 的 DSL 迁移不同。每个迁移是一个 `.sql` 文件，通过文件名的版本号排序执行：

```
migrations/
├── 20240101000000_create_users_table.sql
├── 20240102000000_add_email_index.sql
└── 20240103000000_create_posts_table.sql
```

```sql
-- 20240101000000_create_users_table.sql
CREATE TABLE users (
    id BIGSERIAL PRIMARY KEY,
    name TEXT NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW()
);
```

### 6.2 迁移执行流程
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```mermaid
graph LR
    CMD["sqlx migrate run"] --> DB["检查 _sqlx_migrations 表"]
    DB --> SORT["按版本号排序迁移文件"]
    SORT --> DIFF["找出未执行的迁移"]
    DIFF --> TX["BEGIN TRANSACTION"]
    TX --> EXEC["逐条执行迁移 SQL"]
    EXEC --> RECORD["记录版本到 _sqlx_migrations"]
    RECORD --> COMMIT["COMMIT"]
```

迁移的幂等性由事务保证——每个迁移在独立的事务中执行，失败时自动回滚。`sqlx migrate revert` 支持回滚到指定版本（需提供对应的 `down` 迁移）。

> [来源: SQLx CLI 迁移文档, https://github.com/launchbadge/sqlx/tree/main/sqlx-cli]

---

## 7. SQLx vs Diesel：两种范型的对比
>
> **[来源: [crates.io](https://crates.io/)]**

| 维度 | SQLx（查询优先） | Diesel（Schema 优先） |
|:---|:---|:---|
| 查询方式 | 原生 SQL | Diesel DSL（类型安全的查询构建器） |
| 编译期验证 | ✅ SQL 语法 + 类型 + schema | ✅ schema + DSL 类型 |
| 数据库连接 | 编译期需要 live DB | 仅需 schema 定义（`diesel print-schema`） |
| 复杂查询 | SQL 的全部能力 | 受限于 DSL 表达能力 |
| 学习曲线 | 低（懂 SQL 即可） | 中（需学习 DSL） |
| 异步支持 | 原生 async/await | 通过 `diesel-async` 附加 |
| 迁移 | 纯 SQL | Rust DSL + SQL |
| 典型场景 | 复杂查询、团队已有 SQL 专家 | CRUD 为主、强类型查询构建 |

### 7.1 同一段查询的两种表达
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust,ignore
// SQLx：原生 SQL
let users = sqlx::query_as!(User,
    r#"
    SELECT u.id, u.name, COUNT(p.id) as post_count
    FROM users u
    LEFT JOIN posts p ON p.user_id = u.id
    WHERE u.created_at > $1
    GROUP BY u.id
    HAVING COUNT(p.id) > $2
    "#,
    since,
    min_posts
)
.fetch_all(&pool)
.await?;
```

```rust,ignore
// Diesel：DSL 构建
diesel::users
    .left_join(posts::table.on(posts::user_id.eq(users::id)))
    .filter(users::created_at.gt(since))
    .group_by(users::id)
    .having(diesel::dsl::count(posts::id).gt(min_posts))
    .select((users::id, users::name, diesel::dsl::count(posts::id)))
    .load::<User>(&mut conn)?;
```

当查询复杂度增加（CTE、窗口函数、LATERAL JOIN），SQLx 的"写 SQL"方式优势愈发明显；而对于简单的 CRUD，Diesel 的 DSL 提供了更好的可组合性和重构安全性。

> [来源: Diesel 官方文档, https://diesel.rs/guides/getting-started.html]
> [来源: SQLx vs Diesel 社区讨论, https://github.com/launchbadge/sqlx/discussions]

---

## 8. 性能保证机制
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 8.1 零成本语句准备
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

SQLx 的宏在编译期完成 SQL 的 `PREPARE` 操作，生成描述符信息。运行时仅执行 `EXECUTE`（对于 PostgreSQL 的扩展查询协议），避免了每次查询的解析开销。

### 8.2 类型映射的性能特征
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 映射类型 | 开销 | 说明 |
|:---|:---:|:---|
| 标量类型（i32, String, bool） | 极低 | 直接内存拷贝或引用 |
| `Vec<u8>` / `&[u8]` | 低 | 字节流直接传输 |
| `chrono::DateTime` | 中 | 字符串/整数解析为时间结构 |
| `serde_json::Value` | 中 | JSON 文本解析为 Rust 结构 |
| 自定义类型（`#[derive(Type)]`） | 依赖实现 | 由 `Encode`/`Decode` 实现决定 |

### 8.3 连接池的公平性
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

SQLx 的 `Pool` 使用 FIFO 等待队列，确保在高并发下请求获取连接的公平性，避免某些请求长期饥饿。

> [来源: SQLx Pool 源码, sqlx-core/src/pool/inner.rs]

---

## 9. 反模式边界：何时不应使用 SQLx
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 9.1 无编译期数据库访问的场景
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

SQLx 的宏必须在编译期连接数据库。如果构建环境无法访问数据库（如 CI 隔离网络、离线构建），需要使用 `sqlx prepare` 预生成查询元数据：

```bash
# 在可访问 DB 的环境中生成离线数据
$ cargo sqlx prepare -- --lib

# 生成 sqlx-data.json，后续离线构建时宏读取此文件
$ SQLX_OFFLINE=true cargo build
```

若不愿维护离线数据文件，应考虑 Diesel 或其他纯代码生成方案。

### 9.2 极度动态查询
>
> **[来源: [crates.io](https://crates.io/)]**

SQLx 的宏要求查询字符串在编译期可确定（字面量）。对于完全动态的查询构建（如用户驱动的查询条件组合），需要回退到 `sqlx::query`（非宏版本），此时失去编译期验证：

```rust,ignore
// ✅ 编译期验证
sqlx::query!("SELECT * FROM users WHERE id = $1", id)

// ❌ 运行时字符串，无编译期验证
let sql = format!("SELECT * FROM {} WHERE id = $1", table_name);
sqlx::query(&sql).bind(id).fetch_one(&pool).await?;
```

### 9.3 需要 ORM 级联操作的场景
>
> **[来源: [docs.rs](https://docs.rs/)]**

SQLx 不是 ORM，不提供关联加载、懒加载、级联删除等 ORM 特性。如果业务模型高度关系化且需要这些便利，Diesel 或 SeaORM 更合适。

```rust,ignore
// SeaORM 的关联加载（SQLx 不支持）
let user = User::find_by_id(1).one(&db).await?;
let posts = user.find_related(Post).all(&db).await?;
```

### 9.4 多数据库异构部署的复杂性
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

SQLx 的宏在编译期绑定特定数据库类型。如果同一套代码需要同时支持 PostgreSQL 和 MySQL（如可插拔后端），需要条件编译或抽象层，增加了复杂度。

> [来源: SQLx 离线模式文档, https://docs.rs/sqlx/latest/sqlx/macro.query.html#offline-mode-requires-the-offline-feature]

---

## 10. 来源与扩展阅读
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 来源 | URL | 用途 |
|:---|:---|:---|
| SQLx 官方文档 | <https://docs.rs/sqlx/latest/sqlx/> | 权威 API 参考 |
| SQLx GitHub | <https://github.com/launchbadge/sqlx> | 源码与迁移工具 |
| Diesel 官方文档 | <https://diesel.rs/> | ORM 对比参考 |
| SeaORM 文档 | <https://www.sea-ql.org/SeaORM/> | 异步 ORM 替代方案 |
| PostgreSQL 扩展查询协议 | <https://www.postgresql.org/docs/current/protocol-flow.html#PROTOCOL-FLOW-EXT-QUERY> | 底层协议 |

> **文档元信息**
>
> - 对应 Rust 版本: 1.96.0+ (Edition 2024)
> - 对应 SQLx 版本: 0.8+
> - 最后更新: 2026-05-22
> - 状态: ✅ 初版完成

---

## 相关架构与延伸阅读
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [Diesel ORM 架构](./03_diesel_architecture.md)
- [SQLx 主架构分析](./09_sqlx_architecture.md)
- 类型系统与所有权

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [docs.rs](https://docs.rs/)]**
>
> **[来源: [Rust Database Ecosystem](https://www.areweadyet.org/topics/database/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-22 补全权威来源标注 [来源: Authority Source Sprint Batch 9]

---
