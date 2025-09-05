# Pingora（proxy-pingora）

启用：`--features proxy-pingora`

示例：

```rust
# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "proxy-pingora")]
{
    c12_middlewares::pingora_proxy::PingoraProxy::start("127.0.0.1:8080").await?;
}
Ok(())
}
```
