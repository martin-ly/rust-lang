# C11 开发库: 常见问题解答 (FAQ)

> **文档定位**: 开发库实践中的常见问题快速解答  
> **使用方式**: 遇到问题时快速查找解决方案和最佳实践  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 问题解答

---

## 📋 问题索引

**快速跳转**:

- [数据库集成](#数据库集成)
- [Redis缓存](#redis缓存)
- [消息队列](#消息队列)
- [连接管理](#连接管理)
- [性能优化](#性能优化)
- [错误处理](#错误处理)

---

## 数据库集成

### Q1: 如何选择合适的数据库驱动？

**A**: 根据需求选择异步或同步驱动：

**PostgreSQL**:

- ✅ `tokio-postgres`: 原生异步，性能最优
- `sqlx`: 编译时SQL检查
- `diesel`: ORM，适合复杂查询

**MySQL**:

- ✅ `mysql_async`: 异步驱动
- `sqlx`: 跨数据库支持

**SQLite**:

- `rusqlite`: 同步，适合嵌入式
- ✅ `sqlx`: 异步支持

**相关**: [sql.md](./sql.md)

---

### Q2: 如何正确管理数据库连接池？

**A**: 使用连接池避免连接耗尽：

```rust
use tokio_postgres::Config;
use deadpool_postgres::{Manager, Pool};

async fn create_pool() -> Result<Pool> {
    let config = Config::new()
        .host("localhost")
        .user("postgres")
        .password("password")
        .dbname("mydb")
        .parse()?;
    
    let manager = Manager::new(config, tokio_postgres::NoTls);
    let pool = Pool::builder(manager)
        .max_size(16)               // 最大连接数
        .build()?;
    
    Ok(pool)
}
```

**最佳实践**:

- 设置合理的池大小（CPU核心数 * 2-4）
- 配置超时避免阻塞
- 监控连接池状态

**相关**: [sql.md](./sql.md)

---

## Redis缓存

### Q3: Redis连接池如何配置？

**A**: 使用 `bb8-redis` 或 `deadpool-redis`：

```rust
use redis::aio::ConnectionManager;
use redis::Client;

async fn create_redis_pool() -> Result<ConnectionManager> {
    let client = Client::open("redis://127.0.0.1/")?;
    let manager = ConnectionManager::new(client).await?;
    Ok(manager)
}
```

**连接池配置**:

```rust
use deadpool_redis::{Config, Runtime};

let cfg = Config::from_url("redis://127.0.0.1/");
let pool = cfg.create_pool(Some(Runtime::Tokio1))?;
```

**相关**: [redis.md](./redis.md)

---

### Q4: 如何实现Redis分布式锁？

**A**: 使用 SET NX EX 命令：

```rust
use redis::AsyncCommands;

async fn acquire_lock(
    conn: &mut ConnectionManager,
    key: &str,
    value: &str,
    ttl_seconds: usize
) -> Result<bool> {
    let result: bool = conn
        .set_options(key, value, |opts| {
            opts.with_expiration(redis::SetExpiry::EX(ttl_seconds))
                .conditional_set(redis::ExistenceCheck::NX)
        })
        .await?;
    
    Ok(result)
}

async fn release_lock(conn: &mut ConnectionManager, key: &str, value: &str) -> Result<bool> {
    let script = r"
        if redis.call('get', KEYS[1]) == ARGV[1] then
            return redis.call('del', KEYS[1])
        else
            return 0
        end
    ";
    
    let result: i32 = redis::Script::new(script)
        .key(key)
        .arg(value)
        .invoke_async(conn)
        .await?;
    
    Ok(result == 1)
}
```

**相关**: [redis.md](./redis.md)

---

## 消息队列

### Q5: 如何选择合适的消息队列？

**A**: 根据场景选择：

| 场景 | 推荐 | 原因 |
|------|------|------|
| 高吞吐量、持久化 | Kafka | 分布式日志、大规模数据 |
| 低延迟、简单 | NATS | 微服务通信 |
| IoT、嵌入式 | MQTT | 轻量级、QoS支持 |

**决策表**:

```text
需要消息持久化？
├─ 是 → Kafka
└─ 否 → NATS/MQTT
    ├─ IoT设备 → MQTT
    └─ 微服务 → NATS
```

**相关**: [mq.md](./mq.md), [kafka_pingora.md](./kafka_pingora.md)

---

### Q6: Kafka生产者如何保证消息可靠性？

**A**: 配置 acks 和重试：

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::ClientConfig;

fn create_producer() -> Result<FutureProducer> {
    ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .set("acks", "all")                // 等待所有副本确认
        .set("retries", "10")              // 重试次数
        .set("enable.idempotence", "true") // 幂等性
        .create()
        .map_err(|e| e.into())
}
```

**可靠性级别**:

- `acks=0`: 不等待确认（最快）
- `acks=1`: 等待leader确认
- `acks=all`: 等待所有副本确认（最可靠）

**相关**: [kafka_pingora.md](./kafka_pingora.md)

---

## 连接管理

### Q7: 如何处理连接断开和重连？

**A**: 实现自动重连逻辑：

```rust
use tokio::time::{sleep, Duration};

async fn with_retry<F, T, E>(mut f: F, max_retries: usize) -> Result<T, E>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
{
    for attempt in 1..=max_retries {
        match f().await {
            Ok(result) => return Ok(result),
            Err(e) if attempt < max_retries => {
                eprintln!("Attempt {} failed, retrying...", attempt);
                sleep(Duration::from_secs(2u64.pow(attempt as u32))).await; // 指数退避
            }
            Err(e) => return Err(e),
        }
    }
    unreachable!()
}
```

**Redis重连示例**:

```rust
use redis::aio::ConnectionManager;

// ConnectionManager 自动重连
let manager = ConnectionManager::new(client).await?;
```

**相关**: 各中间件文档

---

## 性能优化

### Q8: 如何批量操作提升性能？

**A**: 使用批量API和Pipeline：

**Redis Pipeline**:

```rust
use redis::pipe;

async fn batch_set(conn: &mut ConnectionManager, data: Vec<(String, String)>) -> Result<()> {
    let mut pipe = pipe();
    for (key, value) in data {
        pipe.set(&key, &value);
    }
    pipe.query_async(conn).await?;
    Ok(())
}
```

**PostgreSQL批量插入**:

```rust
let stmt = client.prepare("INSERT INTO users (name, age) VALUES ($1, $2)").await?;
for (name, age) in users {
    client.execute(&stmt, &[&name, &age]).await?;
}
```

**性能提升**: 可达 10-100倍

**相关**: [redis.md](./redis.md), [sql.md](./sql.md)

---

## 错误处理

### Q9: 如何优雅地处理中间件错误？

**A**: 使用统一的错误类型：

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MiddlewareError {
    #[error("Database error: {0}")]
    Database(#[from] tokio_postgres::Error),
    
    #[error("Redis error: {0}")]
    Redis(#[from] redis::RedisError),
    
    #[error("Kafka error: {0}")]
    Kafka(String),
    
    #[error("Connection timeout")]
    Timeout,
}
```

**使用示例**:

```rust
async fn get_user(pool: &Pool, id: i32) -> Result<User, MiddlewareError> {
    let client = pool.get().await?;
    let row = client.query_one("SELECT * FROM users WHERE id = $1", &[&id]).await?;
    Ok(User::from_row(row))
}
```

**相关**: 各模块错误处理

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [README](./README.md) - 项目概述
- [Glossary](./Glossary.md) - 术语表
- [sql.md](./sql.md) - SQL数据库
- [redis.md](./redis.md) - Redis缓存
- [mq.md](./mq.md) - 消息队列

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [源码实现](../src/)
