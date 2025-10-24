# Redis（kv-redis）

> 适用范围：Rust 1.89+；示例需启用特性 `kv-redis`，风格遵循 `../../c10_networks/docs/STYLE.md`。


## 📊 目录

- [快速开始](#快速开始)
- [连接与连接池](#连接与连接池)
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


启用：`--features kv-redis`

接口：`kv::KeyValueStore`

## 快速开始

```rust
use c12_middlewares::kv::KeyValueStore;

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "kv-redis")]
{
    let store = c12_middlewares::redis_client::RedisStore::connect(
        "redis://127.0.0.1:6379"
    ).await?;
    store.set("k", b"v").await?;
    let v = store.get("k").await?;
    assert!(v.is_some());
}
Ok(())
}
```

## 连接与连接池

- 默认提供简单连接；生产建议使用 `connect_with(config)` 启用池化
- 池大小：根据并发与阻塞操作时间估算，起始 `min=1, max=16`，再按指标调整

```rust
use c12_middlewares::config::RedisConfig;

# async fn connect_with_pool() -> anyhow::Result<()> {
#[cfg(feature = "kv-redis")]
{
    let cfg = RedisConfig::new("redis://127.0.0.1:6379")
        .with_pool_min_max(1, 16)
        .with_connect_timeout_ms(2_000)
        .with_cmd_timeout_ms(1_000);
    let store = c12_middlewares::redis_client::RedisStore::connect_with(cfg).await?;
    let _ = store.ping().await?;
}
Ok(())
}
```

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
