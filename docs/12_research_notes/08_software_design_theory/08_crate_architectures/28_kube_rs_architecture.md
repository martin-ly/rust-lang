> **Canonical 说明**: 本文件专注 **kube-rs Kubernetes 客户端、Controller 与 CRD 派生架构**。
>
> 若只需要使用指南与生态定位，请优先参考：
>
> - [云原生](../../../../concept/06_ecosystem/04_web_and_networking/02_cloud_native.md)
> - [微服务模式](../../../../concept/06_ecosystem/03_design_patterns/05_microservice_patterns.md)
>
> 本文件保留架构级深度内容，与上述使用指南形成互补。
> **⚠️ 历史文档提示**：
>
> 本文档涉及的 Kubernetes 生态以 `kube-rs` crate 为主。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **概念族**: Crate 架构 / kube-rs
>
> **层级**: L3-L5

---

# kube-rs Crate 架构解构 {#kube-rs-crate-架构解构}

> **EN**: Kube Rs Architecture
> **Summary**: kube-rs Crate 架构解构 Kube Rs Architecture.
> **最后更新**: 2026-06-29
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L3-L5
>
> **知识领域**: 云原生、Kubernetes、分布式系统、控制器模式、异步（Async） IO
>
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 1. 引言：kube-rs 的生态定位 {#1-引言kube-rs-的生态定位}

> **[来源: [kube-rs crates.io](https://crates.io/crates/kube)]**

`kube-rs` 是 Rust 生态中对接 **Kubernetes** 的工业级客户端，提供类型安全的 API 访问、资源监听与控制器运行时（Runtime）。它适用于构建 Kubernetes Operator、集群自动化工具、GitOps 控制器、CI/CD 触发器与可观测性 Agent 等场景。

> [来源: [kube-rs docs.rs](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]

与官方 Go client 相比，`kube-rs` 的核心取舍是：

| 维度 | 设计选择 | 工程价值 |
|:--|:--|:--|
| **API 模型** | `Api<K>` 泛型（Generics）封装 REST 路径 | 编译期保证资源类型与 API Group/Version 匹配 |
| **运行时（Runtime）** | 基于 Tokio 的异步（Async） watcher / controller | 与 Rust 异步生态天然集成，支持背压与超时 |
| **CRD 支持** | `#[derive(CustomResource)]` 派生宏（Macro） | 将 Kubernetes CRD 静态化为 Rust struct |
| **类型生成** | 依赖 `k8s-openapi` 生成核心资源类型 | 随 Kubernetes 版本更新，避免手工维护 |

> [来源: [kube-rs GitHub Repository](https://github.com/kube-rs/kube)]

```rust,ignore
use k8s_openapi::api::core::v1::Pod;
use kube::{api::ListParams, Api, Client};

let client = Client::try_default().await?;
let pods: Api<Pod> = Api::namespaced(client, "default");
let list = pods.list(&ListParams::default().limit(10)).await?;
```

> [来源: [kube-rs Client Examples](https://github.com/kube-rs/kube/tree/main/examples)]

---

## 2. 核心概念 {#2-核心概念}

> **[来源: [Kubernetes 官方文档](https://kubernetes.io/docs/home/)]**

`kube-rs` 的编程模型围绕以下核心概念展开：`Client`、`Api`、`Resource`、`Controller`、`Informer`、`watcher` 与 CRD 派生。

### 2.1 Client / Api / Resource {#21-client-api-resource}

- `Client`：封装与 kube-apiserver 的 HTTP/2 连接、认证与配置发现。
- `Api<K>`：针对具体 Kubernetes 资源类型的类型化接口，`K` 必须实现 `Resource` trait。
- `Resource`：由 `kube::Resource` 定义，提供 API Group、Version、Kind、Plural 等元数据。

```rust,ignore
use k8s_openapi::api::core::v1::Pod;
use kube::{Api, Client};

let client = Client::try_default().await?;
let pods: Api<Pod> = Api::namespaced(client, "default");
```

> [来源: [kube docs.rs – Api](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]

### 2.2 Controller / Controller::new {#22-controller-controllernew}

`kube::runtime::Controller` 实现了 Kubernetes 的 **Controller 模式**：监听一个或多个资源类型，对事件进行 reconcile（调谐）。

```rust,ignore
use kube::runtime::Controller;
use kube::runtime::watcher;

Controller::new(pods_api, watcher::Config::default())
    .run(reconcile, error_policy, context)
    .for_each(|res| async move {
        if let Err(e) = res {
            eprintln!("reconcile failed: {e}");
        }
    })
    .await;
```

> [来源: [kube-rs Controller Guide](https://kube.rs/controllers/intro/)]

### 2.3 Informer 与 watcher {#23-informer-与-watcher}

- `watcher`：低阶 API，返回 `Stream<Item = Result<Event<K>, watcher::Error>>`，适合自定义处理逻辑。
- `Informer`（旧称）已被 `watcher` + `Controller` 组合取代。

```rust,ignore
use futures::StreamExt;
use kube::runtime::{watcher, WatchStreamExt};
use std::pin::pin;

let stream = watcher(pods, watcher::Config::default()).applied_objects();
let mut stream = pin!(stream);
while let Some(pod) = stream.next().await {
    // 处理 Applied 事件
}
```

> [来源: [kube docs.rs – watcher](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]

### 2.4 CRD 派生 {#24-crd-派生}

通过 `#[derive(CustomResource)]` 将 Rust struct 映射为 Kubernetes CRD：

```rust,ignore
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Serialize, Deserialize};

#[derive(CustomResource, Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[kube(group = "example.com", version = "v1", kind = "MyApp")]
struct MyAppSpec {
    replicas: i32,
}
```

> [来源: [kube-rs CRD Guide](https://kube.rs/)]

---

## 3. kube-rs 与 k8s-openapi 的关系 {#3-kube-rs-与-k8s-openapi-的关系}

> **[来源: [k8s-openapi docs.rs](https://docs.rs/k8s-openapi/latest/k8s_openapi/)]**

| 职责 | crate | 说明 |
|:--|:--|:--|
| 核心类型定义 | `k8s-openapi` | 提供 `Pod`、`Deployment`、`Service` 等 Kubernetes API 的 Rust 类型 |
| 运行时客户端 | `kube` | 提供 `Client`、`Api`、`Controller`、`watcher` 等高级抽象 |
| 特征绑定 | `kube::Resource` | `k8s-openapi` 中的类型通过 `kube` 实现 `Resource`，从而可用于 `Api<K>` |

`k8s-openapi` 的 `latest` feature 会锁定到当前最新的 Kubernetes 稳定版本。生产环境中应显式选择目标集群版本，以避免字段不兼容。

> [来源: [k8s-openapi GitHub](https://github.com/Arnavion/k8s-openapi)]

---

## 4. 反例边界 {#4-反例边界}

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 反例 | 错误表现 | 正确做法 |
|:--|:--|:--|
| 未处理 watcher 错误 | 网络闪断后静默丢失事件，状态与集群不一致 | 使用 `watcher::Config::default().streaming_lists(true)`，并对 `Err` 分支做指数退避重连 |
| 未使用 `owner_reference` | 删除 CR 时，由该 CR 创建的子资源泄漏 | reconcile 时通过 `controller_owner_reference` 设置 ownerRef |
| CRD 版本管理混乱 | `v1alpha1` 与 `v1` 字段冲突，导致反序列化失败 | 显式声明 `version`，使用 `serde` `default` 与 `apiextensions.k8s.io` 版本转换策略 |
| 集群外运行依赖 `KUBECONFIG` | 在容器内无 kubeconfig 时启动失败 | 集群内使用 `Client::incluster()`，集群外使用 `Client::try_default()` 并校验 |
| watcher 无超时/取消 | 控制循环无法优雅关闭 | 使用 `tokio::select!` 或 `CancellationToken` 管理生命周期（Lifetimes） |
| 对同一资源高频 list | 给 apiserver 造成过大压力 | 使用 watcher 增量监听，必要时结合 local cache（`reflector`） |

> [来源: [Kubernetes API Concepts](https://kubernetes.io/docs/reference/using-api/api-concepts/)]

---

## 5. 类型系统利用 {#5-类型系统利用}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

`kube-rs` 通过类型系统（Type System）将 Kubernetes 的资源语义静态化：

| 维度 | API | 类型系统价值 |
|:--|:--|:--|
| 资源类型区分 | `Api<Pod>` vs `Api<Deployment>` | 编译期防止将 Pod 接口用于 Deployment |
| 命名空间/集群作用域 | `Api::namespaced` vs `Api::all` | 在类型层面区分 namespaced 与 cluster-scoped 资源 |
| CRD 安全 | `#[derive(CustomResource)]` | 宏生成 `Resource` 实现，保证 Group/Version/Kind 一致 |
| 异步 trait | `Controller::run` 返回 Stream/Future | `Send + 'static` 保证跨任务安全 |

> [来源: [kube docs.rs – Resource](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]

---

## 6. 代码示例锚点 {#6-代码示例锚点}

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 示例 | 文件 | 说明 |
|:--|:--|:--|
| 查询 Pod 列表 | [`crates/c10_networks/examples/kube_list_pods.rs`](../../../../crates/c10_networks/examples/kube_list_pods.rs) | 使用 `Client::try_default` 与 `Api::list` 查询命名空间 Pod |
| 监听 Pod 变更事件 | [`crates/c10_networks/examples/kube_watch_pods.rs`](../../../../crates/c10_networks/examples/kube_watch_pods.rs) | 使用 `watcher` 与 `applied_objects` 监听 Pod 事件 |

> [来源: [c10_networks Crate](../../../../crates/c10_networks)]

---

## 7. 相关架构与延伸阅读 {#7-相关架构与延伸阅读}

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [Tokio 异步运行时架构](06_tokio_architecture.md)
- [Tracing 可观测性架构](19_tracing_architecture.md)
- [异步编程模型](../../../../concept/03_advanced/01_async/01_async.md)
- [分布式模式](../../../../concept/03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md)
- [Kafka / rdkafka 架构](27_kafka_architecture.md) — 消息队列与事件驱动对比

---

## 权威来源索引 {#权威来源索引}

> **[来源: [kube-rs crates.io](https://crates.io/crates/kube)]**
>
> **[来源: [kube-rs docs.rs](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]**
>
> **[来源: [kube-rs GitHub](https://github.com/kube-rs/kube)]**
>
> **[来源: [k8s-openapi docs.rs](https://docs.rs/k8s-openapi/latest/k8s_openapi/)]**
>
> **[来源: [Kubernetes 官方文档](https://kubernetes.io/docs/home/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **权威来源**: [kube-rs docs.rs](https://docs.rs/kube/latest/kube/runtime/watcher/index.html), [kube-rs crates.io](https://crates.io/crates/kube), [Kubernetes 官方文档](https://kubernetes.io/docs/home/)
>
> **权威来源对齐变更日志**: 2026-06-29 创建 kube-rs 生态专题，对齐 kube-rs 官方文档与 Kubernetes 官方文档

---

## 权威来源参考 {#权威来源参考}

> **P0（官方/必读）**:
>
> - [来源: [kube-rs Documentation](https://docs.rs/kube/latest/kube/runtime/watcher/index.html)]
> - [来源: [kube-rs crates.io](https://crates.io/crates/kube)]
> - [来源: [Kubernetes 官方文档](https://kubernetes.io/docs/home/)]
> - [来源: [k8s-openapi Documentation](https://docs.rs/k8s-openapi/latest/k8s_openapi/)]
> **P1（学术论文/演讲）**:
>
> - [来源: [Borg, Omega, and Kubernetes – ACM Queue](https://queue.acm.org/detail.cfm?id=2898444)] — Google 集群管理系统演进
> - [来源: [Large-scale cluster management at Google with Borg](https://research.google/pubs/large-scale-cluster-management-at-google-with-borg/)] — 分布式调度与控制器模式
> **P2（仓库/社区文章）**:
>
> - [来源: [kube-rs GitHub Repository](https://github.com/kube-rs/kube)]
> - [来源: [kube.rs Guides](https://kube.rs/)]
> - [来源: [This Week in Rust](https://this-week-in-rust.org/)]

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneasverif.github.io/)
- [Oxide](https://arxiv.org/abs/1903.00982)
