# Pingora（proxy-pingora）

> 适用范围：Rust 1.89+；示例需启用特性 `proxy-pingora`，风格遵循 `../../c10_networks/docs/STYLE.md`。

启用：`--features proxy-pingora`

## 最小可用示例

```rust
# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "proxy-pingora")]
{
    c12_middlewares::pingora_proxy::PingoraProxy::start("127.0.0.1:8080").await?;
}
Ok(())
}
```

## 反向代理与上游路由（规划）

- 静态上游：将 `/` 路由至固定上游 `http://127.0.0.1:9000`
- 动态路由：基于前缀/Host/权重选择上游
- 健康检查：主动探测/熔断与半开

接口形态（草案，可执行原型将保持该形态的子集一致）：

```rust
# async fn proxy_route() -> anyhow::Result<()> {
#[cfg(feature = "proxy-pingora")]
{
    use c12_middlewares::pingora_proxy::{PingoraProxy, Route, Upstream};
    let routes = vec![
        Route::prefix("/", Upstream::new("http://127.0.0.1:9000")),
    ];
    PingoraProxy::with_routes("0.0.0.0:8080", routes)
        .with_timeouts(5_000, 10_000)
        .start()
        .await?;
}
Ok(())
}
```

## 可插拔中间件（规划）

- 超时：连接/请求/上游响应超时
- 限流：令牌桶/漏桶
- 重试：可配置幂等方法、指数退避
- 熔断：失败率/慢调用比例阈值
- Tracing：启用 `obs` 自动注入 span

示意用法：

```rust
# async fn proxy_mw() -> anyhow::Result<()> {
#[cfg(feature = "proxy-pingora")]
{
    use c12_middlewares::pingora_proxy::{PingoraProxy, middleware};
    let proxy = PingoraProxy::builder("0.0.0.0:8080")
        .middleware(middleware::timeout(5_000))
        .middleware(middleware::rate_limit(10_000, 1_000))
        .middleware(middleware::retry(2))
        .middleware(middleware::circuit_breaker(50, 10_000))
        .build();
    proxy.start().await?;
}
Ok(())
}
```

### 典型路由场景

- 前缀路由：`/api` → `http://127.0.0.1:9000`，`/static` → `http://127.0.0.1:9001`
- Host 路由：`api.example.com` → 上游 A，`cdn.example.com` → 上游 B
- 权重与健康检查：按权重进行上游选择，失败熔断并半开恢复

### 超时/重试/熔断建议

- 连接/请求/上游响应分别设置上限，避免级联超时
- 重试仅用于幂等方法（GET/HEAD），并采用指数退避
- 熔断基于失败率与慢调用比例，设置观测窗口

## TLS 与安全（草案）

- 终止 TLS：加载证书/私钥，支持 SNI
- 上游 TLS：双向 TLS、证书校验
- 访问控制：基于 IP/CIDR/路径的 ACL

### 本地验证

```powershell
# 启动一个本地上游（例如简单 http 服务，示意）
# 例如使用 Python: python -m http.server 9000

# 启动 Pingora 反代（示例接口草案）
cargo run -p c12_middlewares --example pingora_demo --features proxy-pingora,tokio,obs
```

## 运维建议（现可落地）

- 使用 SO_REUSEPORT、合理的线程数与内核参数
- 配置超时/重试的上限，避免级联故障
- 监控：QPS、P95/P99 延迟、上游可用率、熔断状态

> 当前为文档规划与接口草图，具体以 `pingora_proxy` 模块实现为准；如需优先支持，请在 `kafka_pingora.md` 所述 MVP 范围内给出需求。
