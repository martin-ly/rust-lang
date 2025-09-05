# Redis（kv-redis）

启用：`--features kv-redis`

接口：`kv::KeyValueStore`

示例：

```rust
use c12_middlewares::kv::KeyValueStore;

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "kv-redis")]
{
    let store = c12_middlewares::redis_client::RedisStore::connect("redis://127.0.0.1:6379").await?;
    store.set("k", b"v").await?;
    let v = store.get("k").await?;
    assert!(v.is_some());
}
Ok(())
}
```
