# SQL 数据库高级实战补充

## 连接管理详解

### PostgreSQL 连接池

```rust
use tokio_postgres::{NoTls, Config};
use deadpool_postgres::{Config as PoolConfig, Runtime, Pool, Manager, ManagerConfig};

async fn create_postgres_pool() -> anyhow::Result<Pool> {
    let mut cfg = Config::new();
    cfg.host("localhost");
    cfg.port(5432);
    cfg.user("postgres");
    cfg.password("mypassword");
    cfg.dbname("mydb");
    
    let mgr_config = ManagerConfig {
        recycling_method: deadpool_postgres::RecyclingMethod::Fast,
    };
    
    let mgr = Manager::from_config(cfg, NoTls, mgr_config);
    
    let pool = Pool::builder(mgr)
        .max_size(16)  // 最大连接数
        .build()?;
    
    Ok(pool)
}

// 使用连接池
async fn use_pool(pool: &Pool) -> anyhow::Result<()> {
    let client = pool.get().await?;
    
    let rows = client
        .query("SELECT id, name FROM users WHERE id = $1", &[&1i32])
        .await?;
    
    for row in rows {
        let id: i32 = row.get(0);
        let name: String = row.get(1);
        println!("User: {} - {}", id, name);
    }
    
    Ok(())
}
```

---

### MySQL 连接池

```rust
use sqlx::mysql::{MySqlPoolOptions, MySqlPool};

async fn create_mysql_pool() -> anyhow::Result<MySqlPool> {
    let pool = MySqlPoolOptions::new()
        .max_connections(16)
        .min_connections(2)
        .acquire_timeout(std::time::Duration::from_secs(5))
        .idle_timeout(std::time::Duration::from_secs(600))
        .max_lifetime(std::time::Duration::from_secs(1800))
        .connect("mysql://root:mypassword@localhost/mydb")
        .await?;
    
    Ok(pool)
}

// 使用连接池
async fn use_mysql_pool(pool: &MySqlPool) -> anyhow::Result<()> {
    let row: (i32, String) = sqlx::query_as("SELECT id, name FROM users WHERE id = ?")
        .bind(1)
        .fetch_one(pool)
        .await?;
    
    println!("User: {} - {}", row.0, row.1);
    
    Ok(())
}
```

---

## CRUD 操作完整示例

### 创建 (CREATE)

```rust
use tokio_postgres::Client;

#[derive(Debug)]
struct User {
    id: i32,
    name: String,
    email: String,
    created_at: chrono::DateTime<chrono::Utc>,
}

async fn create_user(client: &Client, name: &str, email: &str) -> anyhow::Result<User> {
    let row = client
        .query_one(
            "INSERT INTO users (name, email, created_at) VALUES ($1, $2, NOW()) RETURNING id, name, email, created_at",
            &[&name, &email],
        )
        .await?;
    
    Ok(User {
        id: row.get(0),
        name: row.get(1),
        email: row.get(2),
        created_at: row.get(3),
    })
}
```

---

### 读取 (READ)

```rust
async fn get_user_by_id(client: &Client, user_id: i32) -> anyhow::Result<Option<User>> {
    let rows = client
        .query("SELECT id, name, email, created_at FROM users WHERE id = $1", &[&user_id])
        .await?;
    
    if rows.is_empty() {
        return Ok(None);
    }
    
    let row = &rows[0];
    Ok(Some(User {
        id: row.get(0),
        name: row.get(1),
        email: row.get(2),
        created_at: row.get(3),
    }))
}

async fn list_users(client: &Client, limit: i64, offset: i64) -> anyhow::Result<Vec<User>> {
    let rows = client
        .query(
            "SELECT id, name, email, created_at FROM users ORDER BY id LIMIT $1 OFFSET $2",
            &[&limit, &offset],
        )
        .await?;
    
    let users = rows
        .iter()
        .map(|row| User {
            id: row.get(0),
            name: row.get(1),
            email: row.get(2),
            created_at: row.get(3),
        })
        .collect();
    
    Ok(users)
}
```

---

### 更新 (UPDATE)

```rust
async fn update_user(client: &Client, user_id: i32, name: &str, email: &str) -> anyhow::Result<u64> {
    let rows_affected = client
        .execute(
            "UPDATE users SET name = $1, email = $2, updated_at = NOW() WHERE id = $3",
            &[&name, &email, &user_id],
        )
        .await?;
    
    Ok(rows_affected)
}
```

---

### 删除 (DELETE)

```rust
async fn delete_user(client: &Client, user_id: i32) -> anyhow::Result<bool> {
    let rows_affected = client
        .execute("DELETE FROM users WHERE id = $1", &[&user_id])
        .await?;
    
    Ok(rows_affected > 0)
}

// 软删除
async fn soft_delete_user(client: &Client, user_id: i32) -> anyhow::Result<()> {
    client
        .execute("UPDATE users SET deleted_at = NOW() WHERE id = $1", &[&user_id])
        .await?;
    
    Ok(())
}
```

---

## 事务管理详解

### 基础事务

```rust
use tokio_postgres::Transaction;

async fn transfer_money(
    client: &mut Client,
    from_user: i32,
    to_user: i32,
    amount: f64,
) -> anyhow::Result<()> {
    // 开始事务
    let transaction = client.transaction().await?;
    
    // 检查余额
    let row = transaction
        .query_one("SELECT balance FROM accounts WHERE user_id = $1 FOR UPDATE", &[&from_user])
        .await?;
    let balance: f64 = row.get(0);
    
    if balance < amount {
        return Err(anyhow::anyhow!("余额不足"));
    }
    
    // 扣款
    transaction
        .execute(
            "UPDATE accounts SET balance = balance - $1 WHERE user_id = $2",
            &[&amount, &from_user],
        )
        .await?;
    
    // 入账
    transaction
        .execute(
            "UPDATE accounts SET balance = balance + $1 WHERE user_id = $2",
            &[&amount, &to_user],
        )
        .await?;
    
    // 提交事务
    transaction.commit().await?;
    
    Ok(())
}
```

---

### 事务隔离级别

```rust
use tokio_postgres::IsolationLevel;

async fn read_committed_transaction(client: &mut Client) -> anyhow::Result<()> {
    let mut transaction = client.transaction().await?;
    transaction.set_isolation_level(IsolationLevel::ReadCommitted).await?;
    
    // 执行查询...
    
    transaction.commit().await?;
    Ok(())
}

async fn serializable_transaction(client: &mut Client) -> anyhow::Result<()> {
    let mut transaction = client.transaction().await?;
    transaction.set_isolation_level(IsolationLevel::Serializable).await?;
    
    // 执行查询...
    
    transaction.commit().await?;
    Ok(())
}
```

---

### 事务重试（乐观锁）

```rust
use std::time::Duration;

async fn optimistic_update(client: &mut Client, user_id: i32, new_value: i32) -> anyhow::Result<()> {
    const MAX_RETRIES: usize = 3;
    
    for attempt in 0..MAX_RETRIES {
        let transaction = client.transaction().await?;
        
        // 读取当前版本
        let row = transaction
            .query_one("SELECT value, version FROM data WHERE user_id = $1", &[&user_id])
            .await?;
        let current_version: i32 = row.get(1);
        
        // 尝试更新（乐观锁）
        let rows_affected = transaction
            .execute(
                "UPDATE data SET value = $1, version = version + 1 WHERE user_id = $2 AND version = $3",
                &[&new_value, &user_id, &current_version],
            )
            .await?;
        
        if rows_affected > 0 {
            transaction.commit().await?;
            return Ok(());
        }
        
        // 版本冲突，回滚并重试
        transaction.rollback().await?;
        
        if attempt < MAX_RETRIES - 1 {
            tokio::time::sleep(Duration::from_millis(100 * (attempt as u64 + 1))).await;
        }
    }
    
    Err(anyhow::anyhow!("达到最大重试次数"))
}
```

---

## 查询构建

### 动态查询构建

```rust
struct QueryBuilder {
    sql: String,
    conditions: Vec<String>,
    params: Vec<String>,
}

impl QueryBuilder {
    fn new(base_sql: &str) -> Self {
        Self {
            sql: base_sql.to_string(),
            conditions: Vec::new(),
            params: Vec::new(),
        }
    }
    
    fn add_condition(&mut self, condition: &str, param: String) {
        self.conditions.push(condition.to_string());
        self.params.push(param);
    }
    
    fn build(&self) -> (String, &[String]) {
        let mut sql = self.sql.clone();
        if !self.conditions.is_empty() {
            sql.push_str(" WHERE ");
            sql.push_str(&self.conditions.join(" AND "));
        }
        (sql, &self.params)
    }
}

async fn search_users(
    client: &Client,
    name: Option<&str>,
    email: Option<&str>,
    min_age: Option<i32>,
) -> anyhow::Result<Vec<User>> {
    let mut builder = QueryBuilder::new("SELECT id, name, email, created_at FROM users");
    let mut param_idx = 1;
    
    if let Some(n) = name {
        builder.add_condition(&format!("name LIKE ${}", param_idx), format!("%{}%", n));
        param_idx += 1;
    }
    
    if let Some(e) = email {
        builder.add_condition(&format!("email = ${}", param_idx), e.to_string());
        param_idx += 1;
    }
    
    if let Some(age) = min_age {
        builder.add_condition(&format!("age >= ${}", param_idx), age.to_string());
    }
    
    let (sql, params) = builder.build();
    
    // 注意：这里需要将 params 转换为 tokio_postgres 接受的类型
    // 实际使用中可能需要更复杂的处理
    
    let rows = client.query(&sql, &[]).await?;  // 简化示例
    
    let users = rows
        .iter()
        .map(|row| User {
            id: row.get(0),
            name: row.get(1),
            email: row.get(2),
            created_at: row.get(3),
        })
        .collect();
    
    Ok(users)
}
```

---

## 类型映射详解

### 基础类型映射

```rust
use tokio_postgres::types::Type;

async fn type_mapping_examples(client: &Client) -> anyhow::Result<()> {
    // 整数类型
    let smallint: i16 = 123;
    let integer: i32 = 123456;
    let bigint: i64 = 123456789;
    
    // 浮点类型
    let real: f32 = 123.45;
    let double: f64 = 123.456789;
    
    // 字符串类型
    let text: String = "Hello".to_string();
    let varchar: String = "World".to_string();
    
    // 布尔类型
    let boolean: bool = true;
    
    // 日期时间类型
    let timestamp: chrono::DateTime<chrono::Utc> = chrono::Utc::now();
    let date: chrono::NaiveDate = chrono::Local::now().date_naive();
    
    // 二进制类型
    let bytea: Vec<u8> = vec![1, 2, 3, 4];
    
    // JSON 类型
    let json_data = serde_json::json!({
        "key": "value",
        "nested": {
            "field": 123
        }
    });
    
    client
        .execute(
            "INSERT INTO type_examples (
                smallint_col, integer_col, bigint_col, 
                real_col, double_col,
                text_col, varchar_col,
                boolean_col,
                timestamp_col, date_col,
                bytea_col, json_col
            ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)",
            &[
                &smallint, &integer, &bigint,
                &real, &double,
                &text, &varchar,
                &boolean,
                &timestamp, &date,
                &bytea, &json_data,
            ],
        )
        .await?;
    
    Ok(())
}
```

---

### 自定义类型

```rust
use postgres_types::{ToSql, FromSql};

#[derive(Debug, ToSql, FromSql)]
#[postgres(name = "user_status")]
enum UserStatus {
    #[postgres(name = "active")]
    Active,
    #[postgres(name = "inactive")]
    Inactive,
    #[postgres(name = "banned")]
    Banned,
}

async fn use_custom_type(client: &Client) -> anyhow::Result<()> {
    // 插入自定义类型
    client
        .execute(
            "INSERT INTO users (name, status) VALUES ($1, $2)",
            &[&"Alice", &UserStatus::Active],
        )
        .await?;
    
    // 查询自定义类型
    let rows = client
        .query("SELECT name, status FROM users WHERE id = $1", &[&1i32])
        .await?;
    
    for row in rows {
        let name: String = row.get(0);
        let status: UserStatus = row.get(1);
        println!("User {} status: {:?}", name, status);
    }
    
    Ok(())
}
```

---

## 性能优化

### 批量插入

```rust
async fn batch_insert_users(client: &Client, users: Vec<(String, String)>) -> anyhow::Result<()> {
    // 方法1：使用 COPY
    let stmt = "COPY users (name, email) FROM STDIN WITH (FORMAT CSV)";
    let sink = client.copy_in(stmt).await?;
    
    // 注意：实际使用需要 BinaryCopyInWriter 或其他方式
    
    // 方法2：批量 INSERT（更通用）
    if users.is_empty() {
        return Ok(());
    }
    
    const BATCH_SIZE: usize = 1000;
    for chunk in users.chunks(BATCH_SIZE) {
        let mut query = String::from("INSERT INTO users (name, email) VALUES ");
        let mut params: Vec<&(dyn ToSql + Sync)> = Vec::new();
        
        for (i, (name, email)) in chunk.iter().enumerate() {
            if i > 0 {
                query.push_str(", ");
            }
            query.push_str(&format!("(${}, ${})", i * 2 + 1, i * 2 + 2));
            params.push(name);
            params.push(email);
        }
        
        client.execute(&query, &params).await?;
    }
    
    Ok(())
}
```

---

### 索引优化

```sql
-- 创建索引
CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_users_created_at ON users(created_at);

-- 复合索引
CREATE INDEX idx_users_status_created ON users(status, created_at);

-- 部分索引
CREATE INDEX idx_active_users ON users(email) WHERE status = 'active';

-- 全文检索索引
CREATE INDEX idx_users_name_fulltext ON users USING GIN(to_tsvector('english', name));

-- 查看索引使用情况
EXPLAIN ANALYZE SELECT * FROM users WHERE email = 'alice@example.com';
```

---

### 查询优化

```rust
// ❌ N+1 查询问题
async fn bad_n_plus_one(client: &Client) -> anyhow::Result<()> {
    let users = client.query("SELECT id, name FROM users", &[]).await?;
    
    for user in users {
        let user_id: i32 = user.get(0);
        // 每个用户都查询一次订单
        let _orders = client
            .query("SELECT * FROM orders WHERE user_id = $1", &[&user_id])
            .await?;
    }
    
    Ok(())
}

// ✅ JOIN 优化
async fn good_join_query(client: &Client) -> anyhow::Result<()> {
    let rows = client
        .query(
            "SELECT u.id, u.name, o.id, o.total 
             FROM users u
             LEFT JOIN orders o ON u.id = o.user_id",
            &[],
        )
        .await?;
    
    // 处理结果...
    
    Ok(())
}

// ✅ 使用 IN 子查询
async fn good_in_query(client: &Client) -> anyhow::Result<()> {
    let users = client.query("SELECT id, name FROM users", &[]).await?;
    let user_ids: Vec<i32> = users.iter().map(|row| row.get(0)).collect();
    
    // 一次查询获取所有订单
    let orders = client
        .query("SELECT * FROM orders WHERE user_id = ANY($1)", &[&user_ids])
        .await?;
    
    Ok(())
}
```

---

## 安全最佳实践

### SQL 注入防护

```rust
// ❌ 危险：字符串拼接
async fn unsafe_query(client: &Client, user_input: &str) -> anyhow::Result<()> {
    let query = format!("SELECT * FROM users WHERE name = '{}'", user_input);
    // 如果 user_input = "'; DROP TABLE users; --"，将导致灾难！
    let _rows = client.query(&query, &[]).await?;
    Ok(())
}

// ✅ 安全：参数化查询
async fn safe_query(client: &Client, user_input: &str) -> anyhow::Result<()> {
    let rows = client
        .query("SELECT * FROM users WHERE name = $1", &[&user_input])
        .await?;
    Ok(())
}
```

---

### 密码加密存储

```rust
use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};

async fn register_user(client: &Client, email: &str, password: &str) -> anyhow::Result<i32> {
    // 加密密码
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    let password_hash = argon2
        .hash_password(password.as_bytes(), &salt)?
        .to_string();
    
    // 存储加密后的密码
    let row = client
        .query_one(
            "INSERT INTO users (email, password_hash) VALUES ($1, $2) RETURNING id",
            &[&email, &password_hash],
        )
        .await?;
    
    Ok(row.get(0))
}

async fn verify_login(client: &Client, email: &str, password: &str) -> anyhow::Result<bool> {
    let row = client
        .query_one(
            "SELECT password_hash FROM users WHERE email = $1",
            &[&email],
        )
        .await?;
    
    let stored_hash: String = row.get(0);
    let parsed_hash = PasswordHash::new(&stored_hash)?;
    
    Ok(Argon2::default()
        .verify_password(password.as_bytes(), &parsed_hash)
        .is_ok())
}
```

---

## 数据库迁移

### 使用 SQLx 迁移

```bash
# 安装 sqlx-cli
cargo install sqlx-cli

# 创建迁移
sqlx migrate add create_users_table

# 运行迁移
sqlx migrate run --database-url postgres://user:pass@localhost/mydb

# 回滚迁移
sqlx migrate revert --database-url postgres://user:pass@localhost/mydb
```

**迁移文件示例** (`migrations/20250101000000_create_users_table.sql`):

```sql
-- Add migration script here
CREATE TABLE users (
    id SERIAL PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    created_at TIMESTAMP NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMP NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);
```

---

### 代码中应用迁移

```rust
use sqlx::postgres::PgPool;

async fn run_migrations(pool: &PgPool) -> anyhow::Result<()> {
    sqlx::migrate!("./migrations")
        .run(pool)
        .await?;
    
    Ok(())
}
```

---

## 生产环境部署

### 连接池配置

```rust
async fn production_pool_config() -> anyhow::Result<PgPool> {
    let pool = PgPoolOptions::new()
        // 连接数配置
        .max_connections(20)  // 最大连接数
        .min_connections(5)   // 最小连接数
        
        // 超时配置
        .acquire_timeout(Duration::from_secs(5))
        .idle_timeout(Duration::from_secs(600))  // 空闲10分钟
        .max_lifetime(Duration::from_secs(1800))  // 最长30分钟
        
        // 连接测试
        .test_before_acquire(true)
        
        .connect("postgres://user:pass@localhost/mydb")
        .await?;
    
    Ok(pool)
}
```

---

### 健康检查

```rust
async fn health_check(pool: &PgPool) -> anyhow::Result<bool> {
    match sqlx::query("SELECT 1")
        .fetch_one(pool)
        .await
    {
        Ok(_) => Ok(true),
        Err(e) => {
            eprintln!("数据库健康检查失败: {}", e);
            Ok(false)
        }
    }
}
```

---

### 优雅关闭

```rust
async fn graceful_shutdown(pool: PgPool) {
    println!("关闭数据库连接池...");
    pool.close().await;
    println!("数据库连接池已关闭");
}
```

---

## 监控与故障排查

### 慢查询监控

```sql
-- PostgreSQL 慢查询日志配置
ALTER SYSTEM SET log_min_duration_statement = 1000;  -- 记录超过1秒的查询
ALTER SYSTEM SET log_statement = 'all';  -- 记录所有语句

-- 查看慢查询
SELECT query, calls, total_time, mean_time
FROM pg_stat_statements
ORDER BY mean_time DESC
LIMIT 10;
```

---

### 连接数监控

```sql
-- 查看当前连接数
SELECT count(*) FROM pg_stat_activity;

-- 查看每个数据库的连接数
SELECT datname, count(*) 
FROM pg_stat_activity 
GROUP BY datname;

-- 查看最大连接数
SHOW max_connections;
```

---

## 总结

本指南涵盖了 SQL 数据库在 Rust 中的完整应用：

### 核心功能

- ✅ PostgreSQL、MySQL、SQLite 三大数据库
- ✅ 连接池管理
- ✅ CRUD 操作
- ✅ 事务管理
- ✅ 查询构建
- ✅ 类型映射

### 生产实践

- ✅ 性能优化（索引、批量操作、查询优化）
- ✅ 安全最佳实践（SQL注入防护、密码加密）
- ✅ 数据库迁移
- ✅ 监控与故障排查

### 高级特性

- ✅ 事务隔离级别
- ✅ 乐观锁
- ✅ 自定义类型
- ✅ 健康检查
- ✅ 优雅关闭

---

**相关资源**:

- [PostgreSQL 官方文档](https://www.postgresql.org/docs/)
- [MySQL 官方文档](https://dev.mysql.com/doc/)
- [SQLite 官方文档](https://www.sqlite.org/docs.html)
- [tokio-postgres](https://docs.rs/tokio-postgres/)
- [SQLx](https://docs.rs/sqlx/)

---

**更新日期**: 2025-10-24  
**文档版本**: 1.0  
**反馈**: 如有问题或建议，欢迎提 Issue
