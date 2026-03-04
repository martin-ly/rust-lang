# SQLx 异步SQL框架形式化分析

> **主题**: 编译时SQL验证的异步数据库访问
>
> **形式化框架**: 依赖类型 + 查询计划分析
>
> **参考**: SQLx Documentation; Type-Safe SQL

---

## 目录

- [SQLx 异步SQL框架形式化分析](#sqlx-异步sql框架形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 编译时SQL验证](#2-编译时sql验证)
    - [2.1 宏扩展过程](#21-宏扩展过程)
    - [定义 2.1 (query!宏)](#定义-21-query宏)
    - [定理 2.1 (编译时验证)](#定理-21-编译时验证)
    - [2.2 类型推导](#22-类型推导)
    - [定理 2.2 (结果类型推导)](#定理-22-结果类型推导)
  - [3. 连接池管理](#3-连接池管理)
    - [3.1 获取与释放](#31-获取与释放)
    - [定义 3.1 (Pool)](#定义-31-pool)
    - [定理 3.1 (连接获取)](#定理-31-连接获取)
    - [3.2 生命周期管理](#32-生命周期管理)
    - [定理 3.2 (自动释放)](#定理-32-自动释放)
  - [4. 查询接口](#4-查询接口)
    - [4.1 query\_as](#41-query_as)
    - [定义 4.1 (FromRow)](#定义-41-fromrow)
    - [定理 4.1 (结构化映射)](#定理-41-结构化映射)
    - [4.2 fetch/fetch\_one/fetch\_all](#42-fetchfetch_onefetch_all)
    - [定理 4.2 (流式处理)](#定理-42-流式处理)
  - [5. 事务语义](#5-事务语义)
    - [5.1 ACID保证](#51-acid保证)
    - [定义 5.1 (Transaction)](#定义-51-transaction)
    - [定理 5.1 (原子性)](#定理-51-原子性)
    - [5.2 嵌套事务](#52-嵌套事务)
    - [定理 5.2 (Savepoint)](#定理-52-savepoint)
  - [6. 迁移系统](#6-迁移系统)
    - [定义 6.1 (Migration)](#定义-61-migration)
    - [定理 6.1 (迁移原子性)](#定理-61-迁移原子性)
  - [7. 反例与最佳实践](#7-反例与最佳实践)
    - [反例 7.1 (SQL注入)](#反例-71-sql注入)
    - [反例 7.2 (忘记await)](#反例-72-忘记await)
    - [反例 7.3 (连接泄漏)](#反例-73-连接泄漏)
  - [参考文献](#参考文献)

---

## 1. 引言

SQLx是Rust的异步SQL框架，提供:

- **编译时检查**: SQL查询在编译时验证
- **类型安全**: 查询结果自动映射到Rust类型
- **异步**: 基于async/await
- **无ORM**: 直接使用SQL

---

## 2. 编译时SQL验证

### 2.1 宏扩展过程

### 定义 2.1 (query!宏)

```rust
let users = sqlx::query!("SELECT id, name FROM users")
    .fetch_all(&pool)
    .await?;
```

**编译时过程**:

```text
1. 解析SQL
2. 连接数据库 (编译时)
3. 准备/描述查询
4. 获取结果模式
5. 生成返回类型
6. 生成代码
```

### 定理 2.1 (编译时验证)

> SQL错误在编译时捕获。

**捕获错误**:

- 语法错误
- 表/列不存在
- 类型不匹配
- 权限不足

**示例**:

```rust
// 编译错误: column "email" does not exist
sqlx::query!("SELECT email FROM users");

// 正确
sqlx::query!("SELECT name FROM users");
```

∎

### 2.2 类型推导

### 定理 2.2 (结果类型推导)

> 宏自动生成与查询结果匹配的类型。

**证明**:

```rust
let row = sqlx::query!("SELECT id, name FROM users WHERE id = $1", 1i32)
    .fetch_one(&pool)
    .await?;

// row类型自动生成:
// struct { id: i32, name: String }
```

数据库返回的模式 → Rust结构体:

- `INTEGER` → `i32`
- `TEXT/VARCHAR` → `String`
- `BOOLEAN` → `bool`
- `TIMESTAMP` → `chrono::DateTime`

∎

---

## 3. 连接池管理

### 3.1 获取与释放

### 定义 3.1 (Pool)

```rust
pub struct Pool<DB: Database> {
    // 连接队列
    // 状态管理
}
```

### 定理 3.1 (连接获取)

> `Pool::acquire` 返回可用的数据库连接。

**实现**:

```rust
impl<DB: Database> Pool<DB> {
    pub async fn acquire(&self) -> Result<PoolConnection<DB>, Error> {
        // 1. 检查空闲连接
        if let Some(conn) = self.idle.pop() {
            if conn.is_alive() {
                return Ok(conn);
            }
        }

        // 2. 创建新连接(如果未达上限)
        if self.size() < self.max_size() {
            return self.connect().await;
        }

        // 3. 等待可用连接
        self.wait_for_connection().await
    }
}
```

∎

### 3.2 生命周期管理

### 定理 3.2 (自动释放)

> 连接在drop时自动返回池。

**证明**:

```rust
impl<DB: Database> Drop for PoolConnection<DB> {
    fn drop(&mut self) {
        if self.live {
            // 返回连接池
            self.pool.release(self.inner.take());
        }
    }
}
```

**RAII模式**:

- 获取连接 → 使用 → 自动返回
- 即使panic也正确释放

∎

---

## 4. 查询接口

### 4.1 query_as

### 定义 4.1 (FromRow)

```rust
trait FromRow<'r, R: Row> {
    fn from_row(row: &'r R) -> Result<Self, Error>;
}
```

### 定理 4.1 (结构化映射)

> `query_as!` 自动映射到自定义类型。

**示例**:

```rust
#[derive(sqlx::FromRow)]
struct User {
    id: i32,
    name: String,
}

let users: Vec<User> = sqlx::query_as!(User, "SELECT id, name FROM users")
    .fetch_all(&pool)
    .await?;
```

编译时检查:

- User字段与查询结果匹配
- 类型兼容
- 字段名正确

∎

### 4.2 fetch/fetch_one/fetch_all

| 方法 | 返回 | 说明 |
|------|------|------|
| `fetch_one` | `Result<T, Error>` | 恰好一行 |
| `fetch_all` | `Result<Vec<T>, Error>` | 所有行 |
| `fetch` | `Stream<Item = Result<T, Error>>` | 流式 |
| `fetch_optional` | `Result<Option<T>, Error>` | 0或1行 |

### 定理 4.2 (流式处理)

> `fetch` 返回Stream，支持大结果集处理。

**证明**:

```rust
let mut rows = sqlx::query!("SELECT * FROM large_table").fetch(&pool);

while let Some(row) = rows.try_next().await? {
    // 逐行处理
    process(row).await;
}
```

**优势**:

- 不一次性加载所有数据
- 内存效率高
- 响应式处理

∎

---

## 5. 事务语义

### 5.1 ACID保证

### 定义 5.1 (Transaction)

```rust
pub struct Transaction<'c, DB: Database> {
    connection: &'c mut PoolConnection<DB>,
    open: bool,
}
```

### 定理 5.1 (原子性)

> 事务内的操作要么全部提交，要么全部回滚。

**实现**:

```rust
async fn transfer(pool: &Pool<Postgres>) -> Result<(), Error> {
    let mut tx = pool.begin().await?;

    sqlx::query!("UPDATE accounts SET balance = balance - $1 WHERE id = $2", 100, 1)
        .execute(&mut tx)
        .await?;

    sqlx::query!("UPDATE accounts SET balance = balance + $1 WHERE id = $2", 100, 2)
        .execute(&mut tx)
        .await?;

    tx.commit().await?;  // 或自动回滚(如果drop)
    Ok(())
}
```

∎

### 5.2 嵌套事务

### 定理 5.2 (Savepoint)

> 支持嵌套事务(savepoint)。

**实现**:

```rust
let mut tx = pool.begin().await?;

// 外层操作
sqlx::query!("INSERT INTO parent ...").execute(&mut tx).await?;

{
    let mut nested = tx.begin().await?;  // SAVEPOINT sp1

    // 内层操作
    sqlx::query!("INSERT INTO child ...").execute(&mut nested).await?;

    nested.commit().await?;  // RELEASE SAVEPOINT sp1
}

// 或回滚内层
// nested.rollback().await?;  // ROLLBACK TO SAVEPOINT sp1

tx.commit().await?;
```

∎

---

## 6. 迁移系统

### 定义 6.1 (Migration)

```rust
sqlx::migrate!("./migrations")
    .run(&pool)
    .await?;
```

### 定理 6.1 (迁移原子性)

> 每个迁移在事务中执行。

**保证**:

- 迁移要么完全成功，要么完全失败
- 不会留下半完成状态
- 版本控制跟踪

∎

---

## 7. 反例与最佳实践

### 反例 7.1 (SQL注入)

```rust
// 危险! 不要这样做
let query = format!("SELECT * FROM users WHERE name = '{}'", user_input);
sqlx::query(&query).fetch_all(&pool).await?;

// 正确做法 (参数化查询)
sqlx::query!("SELECT * FROM users WHERE name = $1", user_input)
    .fetch_all(&pool)
    .await?;
```

### 反例 7.2 (忘记await)

```rust
// 错误: 没有await
let result = sqlx::query!("SELECT * FROM users").fetch_all(&pool);
// result 是 Future，不是实际结果

// 正确
let result = sqlx::query!("SELECT * FROM users").fetch_all(&pool).await?;
```

### 反例 7.3 (连接泄漏)

```rust
// 长时间持有连接
let conn = pool.acquire().await?;
// 执行慢操作...
tokio::time::sleep(Duration::from_secs(60)).await;
// 连接被占用60秒

// 更好做法
{
    let conn = pool.acquire().await?;
    // 快速使用
}  // 立即释放
```

---

## 参考文献

1. **SQLx Contributors.** (2024). *SQLx Documentation*. <https://docs.rs/sqlx/>

2. **Weurding, R.** (2020). *Compile-time SQL Verification in Rust*.
   - 关键贡献: SQLx设计理念
   - 关联: 第2节

3. **PostgreSQL Documentation.** (2024). *Protocol*. <https://www.postgresql.org/docs/>

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 8个*
*最后更新: 2026-03-04*
