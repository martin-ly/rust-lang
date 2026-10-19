# Rust gRPC / RPC 生态（canonical 缺口闭环页）

> **EN**: Rust gRPC & RPC Ecosystem (canonical gap-closure page)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `network-programming` 分类（15,176 crates）中 gRPC/RPC 子域的 canonical 页：tonic 0.14.6 事实标准（0.14 系服务端直接建于 axum 0.8 + hyper 1 + h2 0.4 之上的收敛事实）、prost 0.14.4 protobuf 代码生成、tonic-web/tonic-reflection 配套，附 capnp/tarpc 替代路线裁决与 `grpc` 长尾撞名陷阱。本页补齐 W9 缺口扫描登记的「13 页顺带提及、0 专页」缺口（2026-10-19）。
> **受众**: [入门→进阶]
> **内容分级**: [专题级]
> **定位**: W9 建页队列①（提及数最高）——全库 13 页顺带提及 tonic/gRPC 而无专页（01_distributed_systems、03_serde_patterns、01_async 等），本页为闭环裁决产物。
> **版本事实基线**: crates.io API 2026-10-19 实查；rustc 1.99.1。
> **前置概念**: [网络协议](07_network_protocols.md) · [分布式系统](01_distributed_systems.md) · [异步 I/O](../../03_advanced/01_async/01_async.md) · [Rust vs Go：gRPC 原生语言对比（L5）](../../05_comparative/01_systems_languages/03_rust_vs_go.md)
> **权威来源**: [tonic docs.rs](https://docs.rs/tonic/) · [prost docs.rs](https://docs.rs/prost/) · [gRPC 官方仓库](https://github.com/grpc/grpc) · [crates.io network-programming 分类](https://crates.io/categories/network-programming) · [std::net — TCP/传输层 std 锚点](https://doc.rust-lang.org/std/net/)（P0：gRPC=HTTP/2 over TCP 的 std 传输语义基线，2026-10-20 核验）

---

## 一、版图与实查锚点（crates.io 2026-10-19）

| crate | 版本（实查） | 累计下载 | 近期下载 | 判读 |
|:---|:---|---:|---:|:---|
| **tonic** | **0.14.6**（2026-05-07） | 4.32 亿 | 9,749 万 | 事实标准（Rust gRPC 默认答案） |
| **prost** | **0.14.4**（2026-06-07） | 6.46 亿 | 1.48 亿 | protobuf 代码生成事实标准 |
| h2 | 0.4.20（2026-10-06） | 8.95 亿 | 1.95 亿 | HTTP/2 底层（tonic 的直接依赖） |
| hyper | 1.12.0（2026-10-06） | 10.2 亿 | — | HTTP 栈（tonic 0.14 的直接依赖） |
| axum | 0.8.9（2026-04-14） | 5.29 亿 | 1.35 亿 | tonic 0.14 服务端承载层（依赖实拆确认） |
| tonic-web | 0.14.6 | 1,907 万 | 487 万 | 浏览器 gRPC-Web 转译 |
| tonic-reflection | 0.14.6 | 6,753 万 | 1,320 万 | gRPC 反射服务 |
| **etcd-client** | **0.21.1**（2026-10-19 当天更新） | 1,028 万 | 316 万 | tonic 之上的生产级客户端实证 |
| capnp | 0.27.2（2026-09-08） | 1,542 万 | 253 万 | Cap'n Proto 替代路线代表 |
| tarpc | 0.38.0（2026-08-12） | 1,026 万 | 139 万 | Rust-to-Rust RPC 替代（Google 出品） |
| `grpc` | 0.9.0（2026-05-28） | 104 万 | 2.9 万 | 长尾撞名者，非 canonical |

## 二、架构裁决：tonic 0.14 的「栈收敛」是本生态最重要的近期事实

对 tonic 0.14.6 的依赖清单实拆（crates.io API）显示其 normal 依赖含 `hyper ^1`、`h2 ^0.4`、`axum ^0.8`、`tower-service/tower-layer`、`tokio-stream`、`tower ^0.5`、`rustls-native-certs`/`webpki-roots`/`zstd`——即 **tonic 0.14 的服务端已直接构建在 axum/hyper 的 HTTP 栈之上**，不再是早年自带独立 tower 传输层的设计。工程含义：

1. gRPC 服务与 REST 服务（axum）现在共享同一个 hyper/tower 中间件生态——拦截器、超时（hyper-timeout）、TLS 配置完全同构；
2. 判读旧资料时必须注意：讲「tonic 的 Tower 服务模型」的旧文对应 0.9/0.10 时代架构，0.14 后服务端语义已并入 axum 路由模型；
3. 客户端栈仍是 tonic 自带 channel + `tower::balance` 负载均衡组合（见[分布式系统页](01_distributed_systems.md)）。

## 三、路线裁决：gRPC 之外选什么

- **默认选型 = tonic + prost**：`.proto` 即跨语言事实源，prost 生成纯 Rust 消息类型（与 `protobuf` crate 的运行时反射路线相反，prost 是 AOT 代码生成——无运行时、无反射、可 `no_std` 边缘）。
- **Cap'n Proto（capnp 0.27.2）**：零拷贝 + 能力安全模型，适合对延迟极敏感且两端都是 Rust 的内部 RPC；代价是生态与工具链远小于 gRPC。
- **tarpc 0.38.0**：纯 Rust-to-Rust 场景（无跨语言需求）的最简形态——trait 即服务定义，无需 schema 语言。
- **边界裁决**：WebSocket/实时推送归[WebSocket 页](06_websocket_realtime_communication.md)，服务发现与负载均衡语义归[分布式系统页](01_distributed_systems.md)，本页只裁 RPC 框架与序列化契约层。

## 四、Rust gRPC vs Go gRPC（选型对照）

Go 是 gRPC 的「原生公民」（grpc-go 官方维护）；Rust 侧 tonic 是社区实现但下载量（tonic 4.32 亿 + prost 6.46 亿）证明其在 Rust 微服务栈中已是默认件。Rust 侧相对优势：prost 生成类型的编译期完备性、tower 中间件的可组合性；相对劣势：无官方 grpc-rust 绑定（grpc 官方只提供 C-core，`grpc` crate 的 grpc-rs 绑定是长尾）、Google 侧对 Rust 的支持主要经由 tonic 生态间接完成。

## 五、反例与陷阱

1. **`grpc` crate 撞名陷阱**：检索 "rust grpc" 首先命中的 `grpc`（104 万累计下载）是 grpc-rs C 绑定长尾，非生产主流——判读必须先查 recent_downloads（2.9 万 vs tonic 9,749 万）。
2. **gRPC-Web ≠ tonic-web 全解**：浏览器端 gRPC 受 CORS/H2 限制，tonic-web 是转译代理方案而非任意浏览器可直连 gRPC。
3. **旧 Tower 架构叙述腐烂**：2023 年前的「tonic 基于 Tower transport」表述对 0.14 已不成立（服务端并入 axum/hyper），引用旧教程需核对版本线。

## 国际权威参考 / International Authority References

- [tonic GitHub（hyperium/tonic）](https://github.com/hyperium/tonic) · [prost GitHub](https://github.com/tokio-rs/prost)
- [gRPC 官方文档](https://grpc.io/docs/) · [gRPC-Web 规范](https://github.com/grpc/grpc-web)
- [Cap'n Proto 官网](https://capnproto.org/) · [tarpc（Google/tarpc）](https://github.com/google/tarpc)
