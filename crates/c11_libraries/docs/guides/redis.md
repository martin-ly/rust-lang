# Redis（kv-redis）

> 适用范围：Rust 1.89+；示例需启用特性 `kv-redis`，风格遵循 `../../c10_networks/docs/STYLE.md`。

## 📊 目录

- [Redis（kv-redis）](#rediskv-redis)
  - [📊 目录](#-目录)
  - [Redis 核心概念](#redis-核心概念)
    - [Redis 的优势](#redis-的优势)
  - [快速开始](#快速开始)
    - [环境准备](#环境准备)
    - [基础操作](#基础操作)
  - [数据类型详解](#数据类型详解)
    - [String (字符串)](#string-字符串)
    - [Hash (哈希表)](#hash-哈希表)
    - [List (列表)](#list-列表)
    - [Set (集合)](#set-集合)
    - [Sorted Set (有序集合)](#sorted-set-有序集合)
  - [连接与连接池](#连接与连接池)
    - [单连接 vs 连接池](#单连接-vs-连接池)
    - [连接配置](#连接配置)
    - [TLS/SSL 连接](#tlsssl-连接)
  - [超时与重试](#超时与重试)
    - [示例：对 GET 使用退避重试](#示例对-get-使用退避重试)
  - [批量与管道（MGET/MSET/PIPELINE）](#批量与管道mgetmsetpipeline)
    - [内存优化与大 Key 治理](#内存优化与大-key-治理)
  - [Lua 脚本（原子性）](#lua-脚本原子性)
    - [分布式锁（示例）](#分布式锁示例)
  - [发布/订阅（Pub/Sub）](#发布订阅pubsub)
    - [连接池调优建议](#连接池调优建议)
  - [错误处理与可观测性](#错误处理与可观测性)
    - [运行与验证](#运行与验证)
  - [常见问题（FAQ）](#常见问题faq)
  - [Redis 生产环境实践补充](#redis-生产环境实践补充)
  - [持久化与高可用](#持久化与高可用)
    - [RDB vs AOF](#rdb-vs-aof)
    - [Redis Sentinel (哨兵)](#redis-sentinel-哨兵)
    - [Redis Cluster (集群)](#redis-cluster-集群)
  - [性能优化](#性能优化)
    - [内存优化](#内存优化)
    - [命令优化](#命令优化)
  - [生产环境实践](#生产环境实践)
    - [缓存策略](#缓存策略)
    - [缓存穿透、击穿、雪崩](#缓存穿透击穿雪崩)

---

## Redis 核心概念

### Redis 的优势

1. **极高性能**:
   - 纯内存操作，读写速度极快 (10万+ QPS)
   - 单线程模型，避免锁竞争
   - 高效的数据结构实现

2. **丰富的数据类型**:
   - String, Hash, List, Set, Sorted Set
   - Bitmap, HyperLogLog, Geo
   - Stream (Redis 5.0+)

3. **多种应用场景**:
   - 缓存（最常用）
   - 会话存储
   - 分布式锁
   - 消息队列
   - 实时排行榜
   - 限流

---

## 快速开始

### 环境准备

**启动 Redis**:

```bash
# Docker 启动 Redis
docker run -d --name redis -p 6379:6379 redis:7-alpine

# 或使用 docker-compose
cat > docker-compose.yml << EOF
version: '3.8'
services:
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    command: redis-server --appendonly yes
volumes:
  redis-data:
EOF

docker-compose up -d
```

**依赖配置**:

```toml
[dependencies]
redis = { version = "0.24", features = ["tokio-comp", "connection-manager"] }
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
anyhow = "1"
```

---

### 基础操作

**连接 Redis**:

```rust
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 连接 Redis
    let client = redis::Client::open("redis://127.0.0.1:6379/")?;
    let mut con = client.get_async_connection().await?;
    
    // 基础操作
    con.set("key", "value").await?;
    let value: String = con.get("key").await?;
    println!("获取值: {}", value);
    
    // 设置过期时间
    con.set_ex("temp_key", "temp_value", 60).await?;  // 60秒过期
    
    // 删除键
    con.del("key").await?;
    
    Ok(())
}
```

**检查键是否存在**:

```rust
use redis::AsyncCommands;

async fn key_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // 设置键
    con.set("user:1000", "John").await?;
    
    // 检查键是否存在
    let exists: bool = con.exists("user:1000").await?;
    println!("键存在: {}", exists);
    
    // 获取键的类型
    let key_type: String = con.key_type("user:1000").await?;
    println!("键类型: {}", key_type);
    
    // 获取键的 TTL
    let ttl: i64 = con.ttl("user:1000").await?;
    println!("TTL: {} 秒", ttl);  // -1 表示永不过期
    
    // 设置过期时间
    con.expire("user:1000", 3600).await?;  // 1小时
    
    // 重命名键
    con.rename("user:1000", "user:1001").await?;
    
    Ok(())
}
```

---

## 数据类型详解

### String (字符串)

**基础字符串操作**:

```rust
use redis::AsyncCommands;

async fn string_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // SET 和 GET
    con.set("name", "Alice").await?;
    let name: String = con.get("name").await?;
    
    // SETNX (只在键不存在时设置)
    let set: bool = con.set_nx("counter", 0).await?;
    println!("设置成功: {}", set);
    
    // SETEX (设置并指定过期时间)
    con.set_ex("session:abc123", "user_data", 3600).await?;
    
    // MGET 和 MSET (批量操作)
    con.mset(&[("key1", "value1"), ("key2", "value2")]).await?;
    let values: Vec<String> = con.mget(&["key1", "key2"]).await?;
    
    // INCR 和 DECR (原子递增/递减)
    let count: i64 = con.incr("counter", 1).await?;
    let count: i64 = con.decr("counter", 1).await?;
    
    // INCRBY 和 DECRBY (指定增量)
    let count: i64 = con.incr("counter", 10).await?;
    
    // APPEND (追加字符串)
    let len: i64 = con.append("name", " Smith").await?;
    
    // GETRANGE (获取子字符串)
    let substr: String = con.getrange("name", 0, 4).await?;
    
    Ok(())
}
```

**计数器应用**:

```rust
async fn counter_example(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // 页面访问计数
    let views: i64 = con.incr("page:home:views", 1).await?;
    println!("页面访问次数: {}", views);
    
    // 用户积分
    con.incrby("user:1000:score", 100).await?;
    
    // 限流：每分钟最多100次请求
    let key = format!("rate_limit:user:1000:{}", chrono::Utc::now().minute());
    let count: i64 = con.incr(&key, 1).await?;
    con.expire(&key, 60).await?;
    
    if count > 100 {
        println!("请求被限流");
    }
    
    Ok(())
}
```

---

### Hash (哈希表)

**Hash 操作**:

```rust
use redis::AsyncCommands;

async fn hash_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // HSET 和 HGET
    con.hset("user:1000", "name", "Alice").await?;
    con.hset("user:1000", "age", 30).await?;
    let name: String = con.hget("user:1000", "name").await?;
    
    // HMSET (批量设置)
    con.hset_multiple(
        "user:1001",
        &[("name", "Bob"), ("email", "bob@example.com"), ("role", "admin")]
    ).await?;
    
    // HGETALL (获取所有字段)
    let user: std::collections::HashMap<String, String> = 
        con.hgetall("user:1000").await?;
    
    // HINCRBY (字段递增)
    let age: i64 = con.hincr("user:1000", "age", 1).await?;
    
    // HEXISTS (检查字段是否存在)
    let exists: bool = con.hexists("user:1000", "name").await?;
    
    // HDEL (删除字段)
    con.hdel("user:1000", "age").await?;
    
    // HKEYS 和 HVALS
    let keys: Vec<String> = con.hkeys("user:1000").await?;
    let values: Vec<String> = con.hvals("user:1000").await?;
    
    // HLEN (字段数量)
    let len: i64 = con.hlen("user:1000").await?;
    
    Ok(())
}
```

**用户信息存储**:

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
struct User {
    id: u64,
    name: String,
    email: String,
    created_at: String,
}

async fn user_storage_example(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    let user = User {
        id: 1000,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        created_at: chrono::Utc::now().to_rfc3339(),
    };
    
    // 存储用户信息（使用 Hash）
    let key = format!("user:{}", user.id);
    con.hset(&key, "name", &user.name).await?;
    con.hset(&key, "email", &user.email).await?;
    con.hset(&key, "created_at", &user.created_at).await?;
    
    // 获取用户信息
    let name: String = con.hget(&key, "name").await?;
    let email: String = con.hget(&key, "email").await?;
    
    println!("用户: {} <{}>", name, email);
    
    Ok(())
}
```

---

### List (列表)

**List 操作**:

```rust
use redis::AsyncCommands;

async fn list_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // LPUSH 和 RPUSH (左/右插入)
    con.lpush("messages", "msg1").await?;
    con.rpush("messages", "msg2").await?;
    
    // LPOP 和 RPOP (左/右弹出)
    let msg: Option<String> = con.lpop("messages", None).await?;
    
    // LRANGE (获取范围)
    let messages: Vec<String> = con.lrange("messages", 0, -1).await?;  // 获取所有
    
    // LLEN (列表长度)
    let len: i64 = con.llen("messages").await?;
    
    // LINDEX (获取指定索引元素)
    let msg: String = con.lindex("messages", 0).await?;
    
    // LTRIM (修剪列表)
    con.ltrim("messages", 0, 99).await?;  // 只保留前100条
    
    // BLPOP (阻塞式弹出)
    let result: Option<(String, String)> = con.blpop("queue", 5.0).await?;
    
    Ok(())
}
```

**消息队列应用**:

```rust
async fn message_queue_example() -> anyhow::Result<()> {
    let client = redis::Client::open("redis://127.0.0.1:6379/")?;
    
    // 生产者
    tokio::spawn({
        let client = client.clone();
        async move {
            let mut con = client.get_async_connection().await.unwrap();
            for i in 0..10 {
                let message = format!("Task {}", i);
                con.rpush::<_, _, ()>("task_queue", &message).await.unwrap();
                println!("生产: {}", message);
                tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
            }
        }
    });
    
    // 消费者
    let mut con = client.get_async_connection().await?;
    loop {
        match con.blpop::<_, Option<(String, String)>>("task_queue", 2.0).await? {
            Some((_, task)) => {
                println!("消费: {}", task);
                // 处理任务...
            }
            None => {
                println!("队列为空，等待新任务...");
            }
        }
    }
}
```

---

### Set (集合)

**Set 操作**:

```rust
use redis::AsyncCommands;

async fn set_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // SADD (添加成员)
    con.sadd("tags", "rust").await?;
    con.sadd("tags", "redis").await?;
    
    // SISMEMBER (检查成员是否存在)
    let is_member: bool = con.sismember("tags", "rust").await?;
    
    // SMEMBERS (获取所有成员)
    let members: Vec<String> = con.smembers("tags").await?;
    
    // SCARD (集合大小)
    let count: i64 = con.scard("tags").await?;
    
    // SREM (删除成员)
    con.srem("tags", "redis").await?;
    
    // SPOP (随机弹出)
    let random: Option<String> = con.spop("tags", None).await?;
    
    // SRANDMEMBER (随机获取，不删除)
    let random: Option<String> = con.srandmember("tags", None).await?;
    
    // 集合运算
    con.sadd("set1", &["a", "b", "c"]).await?;
    con.sadd("set2", &["b", "c", "d"]).await?;
    
    // SINTER (交集)
    let intersection: Vec<String> = con.sinter(&["set1", "set2"]).await?;
    
    // SUNION (并集)
    let union: Vec<String> = con.sunion(&["set1", "set2"]).await?;
    
    // SDIFF (差集)
    let diff: Vec<String> = con.sdiff(&["set1", "set2"]).await?;
    
    Ok(())
}
```

**标签系统应用**:

```rust
async fn tag_system_example(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // 为文章添加标签
    con.sadd("article:1000:tags", &["rust", "redis", "backend"]).await?;
    con.sadd("article:1001:tags", &["rust", "async", "tokio"]).await?;
    
    // 获取文章标签
    let tags: Vec<String> = con.smembers("article:1000:tags").await?;
    println!("文章标签: {:?}", tags);
    
    // 找到同时包含 "rust" 和 "redis" 标签的文章
    con.sadd("tag:rust:articles", 1000).await?;
    con.sadd("tag:redis:articles", 1000).await?;
    con.sadd("tag:rust:articles", 1001).await?;
    
    let articles: Vec<i64> = con.sinter(&["tag:rust:articles", "tag:redis:articles"]).await?;
    println!("同时包含 rust 和 redis 标签的文章: {:?}", articles);
    
    Ok(())
}
```

---

### Sorted Set (有序集合)

**Sorted Set 操作**:

```rust
use redis::AsyncCommands;

async fn zset_operations(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // ZADD (添加成员和分数)
    con.zadd("leaderboard", "Alice", 100).await?;
    con.zadd("leaderboard", "Bob", 85).await?;
    con.zadd("leaderboard", "Charlie", 95).await?;
    
    // ZSCORE (获取分数)
    let score: f64 = con.zscore("leaderboard", "Alice").await?;
    
    // ZRANK (获取排名，从0开始)
    let rank: Option<i64> = con.zrank("leaderboard", "Alice").await?;
    
    // ZINCRBY (增加分数)
    let new_score: f64 = con.zincr("leaderboard", "Bob", 10.0).await?;
    
    // ZRANGE (按排名获取，升序)
    let top3: Vec<String> = con.zrange("leaderboard", 0, 2).await?;
    
    // ZREVRANGE (按排名获取，降序)
    let top3: Vec<(String, f64)> = con.zrevrange_withscores("leaderboard", 0, 2).await?;
    
    // ZRANGEBYSCORE (按分数范围获取)
    let players: Vec<String> = con.zrangebyscore("leaderboard", 90, 100).await?;
    
    // ZCOUNT (统计分数范围内的成员数)
    let count: i64 = con.zcount("leaderboard", 90, 100).await?;
    
    // ZREM (删除成员)
    con.zrem("leaderboard", "Bob").await?;
    
    // ZCARD (集合大小)
    let size: i64 = con.zcard("leaderboard").await?;
    
    Ok(())
}
```

**排行榜应用**:

```rust
async fn leaderboard_example(con: &mut redis::aio::Connection) -> anyhow::Result<()> {
    // 更新玩家分数
    async fn update_score(con: &mut redis::aio::Connection, player: &str, score: f64) -> anyhow::Result<()> {
        con.zadd("game:leaderboard", player, score).await?;
        Ok(())
    }
    
    // 批量更新
    let players = vec![
        ("Alice", 1500.0),
        ("Bob", 1200.0),
        ("Charlie", 1800.0),
        ("David", 1350.0),
        ("Eve", 1650.0),
    ];
    
    for (player, score) in players {
        update_score(con, player, score).await?;
    }
    
    // 获取前10名
    let top10: Vec<(String, f64)> = con
        .zrevrange_withscores("game:leaderboard", 0, 9)
        .await?;
    
    println!("排行榜前10名:");
    for (rank, (player, score)) in top10.iter().enumerate() {
        println!("{}. {} - {:.0} 分", rank + 1, player, score);
    }
    
    // 获取某个玩家的排名
    let rank: Option<i64> = con.zrevrank("game:leaderboard", "Alice").await?;
    if let Some(rank) = rank {
        println!("Alice 的排名: {}", rank + 1);
    }
    
    // 获取某个分数段的玩家数量
    let count: i64 = con.zcount("game:leaderboard", 1500, 2000).await?;
    println!("1500-2000分的玩家数: {}", count);
    
    Ok(())
}
```

---

## 连接与连接池

### 单连接 vs 连接池

**单连接**:

```rust
use redis::Client;

async fn single_connection_example() -> anyhow::Result<()> {
    let client = Client::open("redis://127.0.0.1:6379/")?;
    let mut con = client.get_async_connection().await?;
    
    // 使用连接
    con.set("key", "value").await?;
    let value: String = con.get("key").await?;
    
    Ok(())
}
```

**连接池（推荐用于生产）**:

```rust
use redis::Client;
use redis::aio::ConnectionManager;

async fn connection_pool_example() -> anyhow::Result<()> {
    let client = Client::open("redis://127.0.0.1:6379/")?;
    
    // ConnectionManager 自动管理连接池
    let manager = ConnectionManager::new(client).await?;
    
    // 可以克隆并在多个任务中使用
    let manager_clone = manager.clone();
    
    tokio::spawn(async move {
        let mut con = manager_clone;
        con.set::<_, _, ()>("key1", "value1").await.unwrap();
    });
    
    // 主任务
    let mut con = manager;
    con.set("key2", "value2").await?;
    
    Ok(())
}
```

---

### 连接配置

**完整连接配置**:

```rust
use redis::{Client, RedisConnectionInfo, ConnectionAddr, ConnectionInfo};

async fn advanced_connection_config() -> anyhow::Result<()> {
    let conn_info = ConnectionInfo {
        addr: ConnectionAddr::Tcp("127.0.0.1".to_string(), 6379),
        redis: RedisConnectionInfo {
            db: 0,  // 数据库编号
            username: None,  // 用户名（Redis 6+）
            password: Some("your_password".to_string()),  // 密码
        },
    };
    
    let client = Client::open(conn_info)?;
    let mut con = client.get_async_connection().await?;
    
    // 测试连接
    redis::cmd("PING").query_async(&mut con).await?;
    
    Ok(())
}
```

**超时配置**:

```rust
use redis::Client;
use std::time::Duration;

async fn timeout_config() -> anyhow::Result<()> {
    let client = Client::open("redis://127.0.0.1:6379/")?
        .set_connection_timeout(Duration::from_secs(5))?  // 连接超时
        .set_response_timeout(Duration::from_secs(3))?;   // 响应超时
    
    let mut con = client.get_async_connection().await?;
    
    Ok(())
}
```

---

### TLS/SSL 连接

```rust
#[cfg(feature = "tls")]
async fn tls_connection() -> anyhow::Result<()> {
    use redis::Client;
    
    // 使用 rediss:// 协议启用 TLS
    let client = Client::open("rediss://127.0.0.1:6380/")?;
    let mut con = client.get_async_connection().await?;
    
    con.set("secure_key", "secure_value").await?;
    
    Ok(())
}
```

---

## 超时与重试

- 连接/命令超时：通过配置项设置
- 重试：仅对幂等读操作使用 `util::retry_async`，避免对写操作造成重复副作用

### 示例：对 GET 使用退避重试

```rust
# async fn get_with_retry(store: &c12_middlewares::redis_client::RedisStore) -> anyhow::Result<()> {
use c12_middlewares::util::retry_async;
let val = retry_async(|| store.get("k"), 3, 50).await?; // 最多 3 次，初始退避 50ms
let _ = val;
Ok(())
}
```

## 批量与管道（MGET/MSET/PIPELINE）

- MSET/MGET：统一接口 `mset/mget` 提升吞吐
- Pipeline：合并多条写命令，减少 RTT（以实现为准）

```rust
# async fn batch(store: &c12_middlewares::redis_client::RedisStore) -> anyhow::Result<()> {
let pairs: &[(&str, &[u8])] = &[("k1", b"v1"), ("k2", b"v2")];
store.mset(pairs).await?;
let values = store.mget(&["k1", "k2"]).await?;
assert_eq!(values.len(), 2);
Ok(())
}
```

### 内存优化与大 Key 治理

- 避免存储超大 value；必要时拆分为分片键 `key:part:n`
- 设置合理 TTL，定期清理冷数据；避免阻塞性命令（如对大集合的 KEYS）
- 使用压缩（应用层）对长文本/JSON 做压缩后存储

## Lua 脚本（原子性）

- 使用 Lua 在服务端执行原子逻辑，避免竞态
- 典型用例：限流、计数、比较并设置

```rust
# async fn lua_example(store: &c12_middlewares::redis_client::RedisStore) -> anyhow::Result<()> {
let script = r#"
local c = redis.call('INCR', KEYS[1])
if c == 1 then
  redis.call('EXPIRE', KEYS[1], ARGV[1])
end
return c
"#;
let keys = ["rate:ip:1.2.3.4"];
let args = ["60"]; // 60 秒窗口
let cnt = store.eval(script, &keys, &args).await?;
let _ = cnt; // 根据实现返回类型处理
Ok(())
}
```

### 分布式锁（示例）

```rust
# async fn dist_lock_example(store: &c12_middlewares::redis_client::RedisStore) -> anyhow::Result<()> {
use rand::Rng;
let key = "lock:resource";
let token: u64 = rand::thread_rng().gen();
let ttl_secs = 5;

// 加锁（SET NX PX）
let ok = store.set_nx_px(key, &token.to_be_bytes(), ttl_secs * 1000).await?;
if !ok { return Ok(()); }

// 关键区...

// 仅当 token 匹配时解锁（Lua 保证原子性）
let script = r#"
if redis.call('GET', KEYS[1]) == ARGV[1] then
  return redis.call('DEL', KEYS[1])
else
  return 0
end
"#;
let _ = store.eval(script, &[key], &[&token.to_string()]).await?;
Ok(())
}
```

## 发布/订阅（Pub/Sub）

- 适合简单广播；对可达性/持久化有要求时使用 MQ（如 NATS/Kafka）

```rust
# async fn pubsub() -> anyhow::Result<()> {
#[cfg(feature = "kv-redis")]
{
    let store = c12_middlewares::redis_client::RedisStore::connect("redis://127.0.0.1:6379").await?;
    let mut sub = store.subscribe("topic").await?;
    store.publish("topic", b"hello").await?;
    let _msg = sub.next_message().await?;
}
Ok(())
}
```

### 连接池调优建议

- 起步：`min=1, max=16`；观察等待队列与后端 CPU 来调优
- 将长耗时命令隔离到独立池/客户端，避免阻塞其他请求

## 错误处理与可观测性

- 错误统一到 `c12_middlewares::Error::Redis`
- 启用 `obs` 特性自动生成 tracing span，关键操作可见

```rust
# fn handle(result: Result<(), c12_middlewares::Error>) {
match result {
    Ok(_) => {}
    Err(c12_middlewares::Error::Redis(e)) => eprintln!("Redis 错误: {}", e),
    Err(e) => eprintln!("其他错误: {}", e),
}
}
```

### 运行与验证

```powershell
# 本地快速起服务（Docker）
docker run -p 6379:6379 --name redis -d redis:7

# 运行示例（需启用 kv-redis 与 tokio）
cargo run --example basic_usage --features kv-redis,tokio,obs
```

## 常见问题（FAQ）

- Q: 连接经常超时？
  - A: 增大连接/命令超时；检查网络与 CPU 饱和；合理设置池大小。
- Q: 如何实现分布式锁？
  - A: 使用 `SET key val NX PX ttl` 与 Lua 校验/解锁；或采用 Redlock（注意 CAP 取舍）。
- Q: 如何提升批量写入性能？
  - A: 使用 pipeline、MSET；减少单次 value 体积；避免阻塞命令。
- Q: 是否支持二进制值？
  - A: 接口以 `&[u8]` 表示 value，支持二进制。

## Redis 生产环境实践补充

## 持久化与高可用

### RDB vs AOF

**RDB (Redis Database)**:

- 定期快照
- 文件小，恢复快
- 可能丢失最后一次快照后的数据

```bash
# redis.conf 配置
save 900 1      # 900秒内至少1个key变化
save 300 10     # 300秒内至少10个key变化
save 60 10000   # 60秒内至少10000个key变化
```

**AOF (Append Only File)**:

- 记录每个写命令
- 更安全，最多丢1秒数据
- 文件较大，恢复较慢

```bash
# redis.conf 配置
appendonly yes
appendfsync everysec  # 每秒同步一次
# appendfsync always  # 每次写命令都同步（最安全但最慢）
# appendfsync no      # 由操作系统决定（最快但可能丢数据）
```

---

### Redis Sentinel (哨兵)

**高可用架构**: 主从复制 + 自动故障转移

```rust
use redis::Client;

async fn sentinel_connection() -> anyhow::Result<()> {
    // 连接到 Sentinel
    let client = Client::open(vec![
        "redis://sentinel1:26379/",
        "redis://sentinel2:26379/",
        "redis://sentinel3:26379/",
    ])?;
    
    let mut con = client.get_async_connection().await?;
    con.set("key", "value").await?;
    
    Ok(())
}
```

---

### Redis Cluster (集群)

**集群连接**:

```rust
use redis::cluster::ClusterClient;
use redis::cluster::ClusterClientBuilder;

async fn cluster_connection() -> anyhow::Result<()> {
    let nodes = vec![
        "redis://127.0.0.1:7000/",
        "redis://127.0.0.1:7001/",
        "redis://127.0.0.1:7002/",
    ];
    
    let client = ClusterClient::builder(nodes)
        .read_from_replicas()  // 从副本读取
        .build()?;
    
    let mut con = client.get_async_connection().await?;
    con.set("key", "value").await?;
    
    Ok(())
}
```

---

## 性能优化

### 内存优化

**1. 使用合适的数据结构**:

```rust
// ❌ 不好：存储 JSON 字符串
con.set("user:1000", r#"{"name":"Alice","age":30,"email":"alice@example.com"}"#).await?;

// ✅ 好：使用 Hash
con.hset_multiple("user:1000", &[
    ("name", "Alice"),
    ("age", "30"),
    ("email", "alice@example.com"),
]).await?;
```

**2. 压缩大值**:

```rust
use flate2::write::GzEncoder;
use flate2::Compression;
use std::io::Write;

async fn compress_and_store(con: &mut redis::aio::Connection, key: &str, data: &str) -> anyhow::Result<()> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data.as_bytes())?;
    let compressed = encoder.finish()?;
    
    con.set(key, compressed).await?;
    
    Ok(())
}
```

**3. 设置过期时间**:

```rust
// 避免内存泄漏
con.set_ex("session:abc123", "user_data", 3600).await?;  // 1小时过期
```

---

### 命令优化

**避免使用的命令**:

```rust
// ❌ KEYS: 会阻塞服务器
let keys: Vec<String> = redis::cmd("KEYS").arg("user:*").query_async(con).await?;

// ✅ SCAN: 渐进式迭代
let mut cursor = 0;
loop {
    let (new_cursor, keys): (u64, Vec<String>) = redis::cmd("SCAN")
        .arg(cursor)
        .arg("MATCH").arg("user:*")
        .arg("COUNT").arg(100)
        .query_async(con).await?;
    
    // 处理 keys...
    
    cursor = new_cursor;
    if cursor == 0 {
        break;
    }
}
```

---

## 生产环境实践

### 缓存策略

**Cache-Aside (旁路缓存)**:

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
struct User {
    id: u64,
    name: String,
    email: String,
}

async fn cache_aside_get_user(
    con: &mut redis::aio::Connection,
    db: &Database,  // 假设的数据库连接
    user_id: u64,
) -> anyhow::Result<User> {
    let cache_key = format!("user:{}", user_id);
    
    // 1. 先查缓存
    if let Some(cached): Option<String> = con.get(&cache_key).await? {
        return Ok(serde_json::from_str(&cached)?);
    }
    
    // 2. 缓存未命中，查数据库
    let user = db.get_user(user_id).await?;
    
    // 3. 写入缓存
    let json = serde_json::to_string(&user)?;
    con.set_ex(&cache_key, json, 3600).await?;  // 1小时
    
    Ok(user)
}
```

---

### 缓存穿透、击穿、雪崩

**1. 缓存穿透（查询不存在的数据）**:

```rust
// 解决方案：缓存空值
async fn get_with_null_cache(con: &mut redis::aio::Connection, key: &str) -> anyhow::Result<Option<String>> {
    // 检查缓存
    if let Some(cached) = con.get::<_, Option<String>>(key).await? {
        if cached == "NULL" {
            return Ok(None);  // 缓存的空值
        }
        return Ok(Some(cached));
    }
    
    // 查询数据库
    let value = query_database(key).await?;
    
    match value {
        Some(v) => {
            con.set_ex(key, &v, 3600).await?;
            Ok(Some(v))
        }
        None => {
            // 缓存空值，防止穿透
            con.set_ex(key, "NULL", 300).await?;  // 短时间过期
            Ok(None)
        }
    }
}
```

**2. 缓存击穿（热点数据过期）**:

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

pub struct HotKeyCache {
    redis: redis::aio::ConnectionManager,
    loading: Arc<Mutex<std::collections::HashSet<String>>>,
}

impl HotKeyCache {
    pub async fn get(&self, key: &str) -> anyhow::Result<Option<String>> {
        let mut con = self.redis.clone();
        
        // 检查缓存
        if let Some(cached) = con.get::<_, Option<String>>(key).await? {
            return Ok(Some(cached));
        }
        
        // 使用互斥锁防止缓存击穿
        let mut loading = self.loading.lock().await;
        if loading.contains(key) {
            drop(loading);
            // 等待其他线程加载完成
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            return self.get(key).await;
        }
        
        loading.insert(key.to_string());
        drop(loading);
        
        // 加载数据
        let value = query_database(key).await?;
        
        if let Some(ref v) = value {
            con.set_ex(key, v, 3600).await?;
        }
        
        // 清理加载标记
        self.loading.lock().await.remove(key);
        
        Ok(value)
    }
}
```

**3. 缓存雪崩（大量key同时过期）**:

```rust
use rand::Rng;

// 解决方案：给过期时间加随机值
async fn set_with_random_ttl(con: &mut redis::aio::Connection, key: &str, value: &str) -> anyhow::Result<()> {
    let base_ttl = 3600;  // 1小时
    let random_offset = rand::thread_rng().gen_range(0..300);  // 0-5分钟随机偏移
    let ttl = base_ttl + random_offset;
    
    con.set_ex(key, value, ttl).await?;
    
    Ok(())
}

// 辅助函数
async fn query_database(_key: &str) -> anyhow::Result<Option<String>> {
    Ok(Some("database_value".to_string()))
}

struct Database;
impl Database {
    async fn get_user(&self,_id: u64) -> anyhow::Result<User> {
        Ok(User {
            id: _id,
            name: "Alice".to_string(),
            email: "<alice@example.com>".to_string(),
        })
    }
}
```
