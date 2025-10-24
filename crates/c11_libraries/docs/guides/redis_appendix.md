# Redis 生产环境实践补充

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
```

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
