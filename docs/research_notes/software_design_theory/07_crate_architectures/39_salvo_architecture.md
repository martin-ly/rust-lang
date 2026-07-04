> **Canonical 说明**: 本文件专注 **Salvo Web 框架的 Router / Handler / FlowCtrl 中间件架构**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [Web 框架生态](../../../../concept/06_ecosystem/27_web_frameworks.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。
> **Rust 版本**: 1.96.1+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / salvo
>
> **层级**: L3-L5

---

# Salvo Crate 架构解构 {#salvo-crate-架构解构}

> **EN**: Salvo Architecture
> **Summary**: Salvo Crate 架构解构 Salvo Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5 (应用/分析/评价)
>
> **知识领域**: Web 框架、HTTP 服务、路由组合、中间件、异步 IO
>
> **对应 Rust 版本**: 1.96.1+ (salvo 0.93.0+)

---

## 1. 引言：Salvo 在 Rust Web 生态中的定位 {#1-引言salvo-在-rust-web-生态中的定位}

> **[来源: [Salvo 官方文档](https://salvo.rs/)]**

`Salvo` 是 Rust 生态中快速发展的**现代 Web 框架**，设计目标是提供接近 Axum 的模块化能力，同时内置更多生产级特性（CORS、JWT、OpenAPI、静态文件、反向代理等）。它基于 Tokio 异步运行时与 Hyper HTTP 协议实现构建，采用宏驱动的 Handler 抽象，使业务代码保持简洁。

> [来源: [salvo crates.io](https://crates.io/crates/salvo)]

与一线框架相比，Salvo 的核心取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **Handler 抽象** | `#[handler]` 宏 + 普通异步函数 | 低样板代码，自动适配 Service trait |
| **路由模型** | `Router` 树 + 路径参数 `<name>` | 声明式组合，支持嵌套与通配 |
| **中间件** | `Handler` 即中间件，`hoop` 链式挂载 | 与业务 handler 使用同一抽象 |
| **内置特性** | CORS / JWT / OpenAPI / 静态文件 / 压缩 | 减少额外依赖，开箱即用 |
| **运行时绑定** | 默认 Tokio，强依赖 Hyper | 与主流 async 生态一致 |

> [来源: [salvo GitHub Repository](https://github.com/salvo-rs/salvo)]

```rust,ignore
use salvo::prelude::*;

#[handler]
async fn hello() -> &'static str {
    "Hello, Salvo!"
}

#[tokio::main]
async fn main() {
    let router = Router::new().get(hello);
    let acceptor = TcpListener::new("127.0.0.1:5800").bind().await;
    Server::new(acceptor).serve(router).await;
}
```

> [来源: [salvo examples](https://github.com/salvo-rs/salvo/tree/main/examples)]

---

## 2. 核心 API 架构 {#2-核心-api-架构}

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 2.1 Router → Handler 请求管线 {#21-router-handler-请求管线}

```mermaid
graph LR
    TCP[TCP Listener] --> HTTP[Hyper HTTP Parser]
    HTTP --> ROUTER[Salvo Router]
    ROUTER --> |path match| METHOD[Method Router]
    METHOD --> HANDLER[#[handler] async fn]
    HANDLER --> |Response| HTTP
```

Salvo 的请求生命周期分为四层：

1. **网络层**：`TcpListener` 接受连接，Hyper 负责 HTTP/1.1 与 HTTP/2 解析。
2. **路由层**：`Router` 使用内部 trie 树进行路径匹配，支持 `<param>` 路径参数与 `**` 通配。
3. **处理层**：`#[handler]` 宏将普通异步函数转换为满足 `Handler` trait 的组件。
4. **响应层**：返回值通过 `Scribe` / `Writer` trait 写入 HTTP Response body。

> [来源: [salvo::routing 文档](https://docs.rs/salvo/latest/salvo/routing/index.html)]

### 2.2 `#[handler]` 宏与零成本抽象 {#22-handler-宏与零成本抽象}

`#[handler]` 是 Salvo 类型系统的核心杠杆。它在编译期为函数生成 `Handler` trait 实现，避免手写 `Service` boilerplate：

```rust,ignore
#[handler]
async fn create_user(
    req: &mut Request,
    res: &mut Response,
) {
    let user: User = req.parse_json().await.unwrap();
    res.render(Json(user));
}
```

> [来源: [salvo::handler 文档](https://docs.rs/salvo/latest/salvo/handler/index.html)]

被修饰的函数可以按需声明 `&mut Request`、`&mut Response`、`&mut FlowCtrl`、`Depot` 等参数，宏在编译期生成对应的 trait 调用，无动态分发开销。

### 2.3 路径参数与提取器 {#23-路径参数与提取器}

Salvo 的路径参数通过 `Request::param::<T>(name)` 提取，`T` 需实现 `FromStr`：

```rust,ignore
#[handler]
async fn greet(req: &mut Request) -> String {
    let name = req.param::<String>("name").unwrap_or_else(|| "World".into());
    format!("Hello, {name}!")
}

let router = Router::with_path("greet/<name>").get(greet);
```

> [来源: [salvo::extract 文档](https://docs.rs/salvo/latest/salvo/extract/index.html)]

对于 JSON/Query/Form，Salvo 提供 `req.parse_json::<T>()`、`req.query::<T>(name)` 等便捷方法，将 HTTP 协议的动态性限制在类型转换层。

### 2.4 中间件：Handler 即中间件 {#24-中间件handler-即中间件}

Salvo 没有独立的 Middleware trait，任何 `Handler` 都可以作为中间件通过 `hoop` 挂载：

```rust,ignore
#[handler]
async fn logger(req: &mut Request, depot: &mut Depot, res: &mut Response, ctrl: &mut FlowCtrl) {
    tracing::info!("{} {}", req.method(), req.uri());
    ctrl.call_next(req, depot, res).await;
}

let router = Router::new().hoop(logger).get(hello);
```

> [来源: [salvo::routing::Router::hoop](https://docs.rs/salvo/latest/salvo/routing/struct.Router.html#method.hoop)]

这种设计消除了中间件与 handler 之间的抽象鸿沟，代价是 `FlowCtrl` 的调用顺序需要开发者显式管理。

---

## 3. 与 axum / actix-web 对比 {#3-与-axum-actix-web-对比}

> **[来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]**

| 维度 | Salvo | Axum | Actix-web |
|:--|:--|:--|:--|
| **底层协议** | Hyper | Hyper | 自研 HTTP / Tokio |
| **Handler 抽象** | `#[handler]` 宏 | `Handler<T, S>` trait + 变参泛型 | `Handler<Args>` trait |
| **提取器** | `Request::param` / `parse_json` | `FromRequest` / `FromRequestParts` | `FromRequest` |
| **中间件模型** | Handler 即中间件 (`hoop`) | Tower `Service` + `Layer` | `Transform` trait |
| **路由注册** | `Router::with_path` / `push` | `Router::route` / `nest` / `merge` | `App::service` / `route` |
| **内置特性** | 丰富（CORS/JWT/OpenAPI/静态文件） | 精简，依赖 tower-http | 丰富（WebSocket/Static/CORS） |
| **运行时** | Tokio | Tokio | Tokio + Actix actor |
| **学习曲线** | 中（宏 + 约定） | 中高（需理解 Tower） | 中（Actor 模型背景） |

> [来源: [axum 文档](https://docs.rs/axum/latest/axum/)] · [actix-web 文档](https://actix.rs/docs/)

**关键差异**：

- **Salvo vs Axum**：两者都基于 Hyper，但 Salvo 通过 `#[handler]` 宏隐藏了 Tower `Service` 的复杂性，更适合希望快速搭建生产服务的团队；Axum 则提供更纯粹的函数式组合和更大的中间件生态。
- **Salvo vs Actix-web**：Actix-web 保留 Actor 模型与 `Arbiter` 运行时抽象，Salvo 完全采用 async/await + Tokio，没有 Actor 状态隔离的概念，状态共享更直接。

---

## 4. 反例边界 {#4-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| `#[handler]` 函数返回类型未实现 `Scribe` | 编译错误：类型无法写入 Response | 返回 `&str` / `String` / `Json<T>` / `StatusError` |
| 路径参数名与 `<name>` 不匹配 | 运行时 `param` 返回 `None` | 保持 handler 中 `req.param("name")` 与路由声明一致 |
| 在 handler 中读取 body 后再次读取 | 第二次读取为空或 panic | 提前 `parse_json` 并复用结果 |
| 中间件忘记调用 `ctrl.call_next` | 请求被截断，后续 handler 不执行 | 在需要继续处理时显式调用 `FlowCtrl::call_next` |
| 错误地将 `Depot` 当作全局可变状态 | 并发下出现数据竞争 | 使用 `Arc<RwLock<T>>` 或数据库等线程安全抽象 |
| 开启 HTTPS 但未配置证书 | 运行时 panic | 使用 `RustlsConfig` / `NativeTlsConfig` 正确加载证书 |

> [来源: [salvo::writing 文档](https://docs.rs/salvo/latest/salvo/writing/index.html)]

---

## 5. 代码示例锚点 {#5-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| Salvo 路由与路径参数 | [`crates/c06_async/examples/salvo_web_routing.rs`](../../../../crates/c06_async/examples/salvo_web_routing.rs) | `Router` 注册、`#[handler]`、路径参数提取 |

> [来源: [c06_async Crate](https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c06_async)]

---

## 6. 相关概念 {#6-相关概念}

- [00_crate_architecture_master_index.md](00_crate_architecture_master_index.md) — Rust 工业级 Crate 架构总索引
- [07_axum_architecture.md](07_axum_architecture.md) — Axum Web 框架架构
- [12_actix_web_architecture.md](12_actix_web_architecture.md) — Actix-web 框架架构
- [41_askama_architecture.md](41_askama_architecture.md) — Askama 模板引擎架构
- [42_maud_architecture.md](42_maud_architecture.md) — Maud 模板宏架构
- [concept L3: 异步编程](../../../../concept/03_advanced/01_async/02_async.md)
- [concept L6: Web 框架与中间件](../../../../06_ecosystem)

---

> **权威来源**: [Salvo 官方文档](https://salvo.rs/) · [salvo docs.rs](https://docs.rs/salvo/latest/salvo/) · [salvo GitHub](https://github.com/salvo-rs/salvo) · [Hyper 文档](https://docs.rs/hyper/latest/hyper/) · [Tokio 文档](https://docs.rs/tokio/latest/tokio/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.1+ (Edition 2024)
> **最后更新**: 2026-06-29
> **状态**: ✅ 已完成

---

## 权威来源参考 {#权威来源参考}

### P0 — 核心官方文档 {#p0-核心官方文档}

> - [来源: [salvo docs.rs](https://docs.rs/salvo/latest/salvo/)]
> - [来源: [Salvo 官方站点](https://salvo.rs/)]
> - [来源: [salvo crates.io](https://crates.io/crates/salvo)]

### P1 — 标准与生态文档 {#p1-标准与生态文档}

> - [来源: [Hyper 文档](https://docs.rs/hyper/latest/hyper/)]
> - [来源: [Tower Service trait](https://docs.rs/tower-service/latest/tower_service/trait.Service.html)]
> - [来源: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)]

### P2 — 仓库与社区文章 {#p2-仓库与社区文章}

> - [来源: [salvo GitHub Repository](https://github.com/salvo-rs/salvo)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]
> - [来源: [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->]

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneas-verification.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
