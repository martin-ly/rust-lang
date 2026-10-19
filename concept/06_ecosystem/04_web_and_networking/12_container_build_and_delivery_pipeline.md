> **内容分级**: [综述级]
> **代码状态**: ✅ 含可编译示例（依赖 tokio/axum 的块使用 `ignore` 标注）
> **定理链**: N/A — 工程实践综述页，不涉及形式化定理链

# Kubernetes 上的 Rust 服务：容器化构建与交付流水线

> **EN**: Container Build and Delivery Pipeline for Rust Services on Kubernetes
> **Summary**: Build-side and runtime-side engineering for shipping Rust services to Kubernetes: multi-stage Dockerfiles, cargo-chef dependency caching, musl static linking, distroless images, probe contracts, cgroup-aware resource limits, and graceful shutdown with tokio signal handling.

> **Rust 版本**: 1.99.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页（Rust 服务**容器化构建与交付流水线**的 canonical 页。Kubernetes 运行时部署语义——ConfigMap/Secret 配置注入、Deployment/Service/HPA、kube-rs Operator、Sidecar、QoS 等级——的权威页见 [Rust 服务与 Kubernetes](11_kubernetes_rust.md)，本页不重复其正文，只互补构建侧与生命周期契约侧）。
> **受众**: [进阶]
> **A/S/P 标记**: **P+S+A** — Procedure + Structure + Application
> **双维定位**: P×App — 把 Rust 服务从源码构建为可交付容器镜像，并在 Kubernetes 上正确运行
> **定位**: 系统梳理 Rust 服务交付到 Kubernetes 的完整流水线：源码 → 依赖缓存 → 静态链接 → 最小运行时镜像 → 探针契约 → 资源约束 → 优雅停机。建立「构建侧」与「运行侧」两段式决策框架，与既有 K8s 部署实践页互补。
> **前置概念**: [云原生生态](02_cloud_native.md) · [Rust 服务与 Kubernetes](11_kubernetes_rust.md) · [Tokio 运行时内部机制](10_tokio_runtime_internals.md) · [交叉编译](../05_systems_and_embedded/02_cross_compilation.md)
> **后置概念**: [云原生与 Serverless 模式](../14_enterprise_architecture/12_cloud_native_and_serverless_patterns.md) · [可观测性与 SRE 模式](../14_enterprise_architecture/09_observability_and_sre_patterns.md)
> **来源**: [Kubernetes Pod Lifecycle](https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/) · [Configure Liveness/Readiness/Startup Probes](https://kubernetes.io/docs/tasks/configure-pod-container/configure-liveness-readiness-startup-probes/) · [Manage Resources for Containers](https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/) · [Rust musl 目标平台支持](https://doc.rust-lang.org/rustc/platform-support/x86_64-unknown-linux-musl.html) · [cargo-chef](https://github.com/LukeMathWalker/cargo-chef) · [Google Distroless](https://github.com/GoogleContainerTools/distroless) · [tokio::signal](https://docs.rs/tokio/latest/tokio/signal/index.html)

---

## 📑 目录

- [Kubernetes 上的 Rust 服务：容器化构建与交付流水线](#kubernetes-上的-rust-服务容器化构建与交付流水线)
  - [📑 目录](#-目录)
  - [一、Canonical 边界与本页分工](#一canonical-边界与本页分工)
  - [二、容器化构建流水线](#二容器化构建流水线)
    - [2.1 多阶段构建的层缓存语义](#21-多阶段构建的层缓存语义)
    - [2.2 cargo-chef：依赖层与源码层解耦](#22-cargo-chef依赖层与源码层解耦)
    - [2.3 musl 与静态链接：从 glibc 耦合到 scratch 镜像](#23-musl-与静态链接从-glibc-耦合到-scratch-镜像)
    - [2.4 distroless 镜像族选型](#24-distroless-镜像族选型)
    - [2.5 参考 Dockerfile：cargo-chef + musl + distroless 全链路](#25-参考-dockerfilecargo-chef--musl--distroless-全链路)
  - [三、Kubernetes 运行时契约](#三kubernetes-运行时契约)
    - [3.1 探针契约：startup / readiness / liveness](#31-探针契约startup--readiness--liveness)
    - [3.2 资源限制与 cgroup 感知](#32-资源限制与-cgroup-感知)
    - [3.3 优雅停机与 tokio 信号处理](#33-优雅停机与-tokio-信号处理)
  - [四、反例与边界](#四反例与边界)
  - [五、决策树：构建与镜像选型](#五决策树构建与镜像选型)
  - [六、常见陷阱](#六常见陷阱)
  - [七、来源与延伸阅读](#七来源与延伸阅读)
  - [相关概念](#相关概念)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)
  - [国际化权威来源补充（International Authority Sources）](#国际化权威来源补充international-authority-sources)

---

## 一、Canonical 边界与本页分工

知识库中 Kubernetes × Rust 主题已有两个权威页，本页是它们的**构建侧互补页**，三者分工如下：

| 页面 | 视角 | 覆盖内容 | 本页关系 |
|---|---|---|---|
| [Rust 服务与 Kubernetes](11_kubernetes_rust.md) | 运行时部署实践（L4-L6） | ConfigMap/Secret、Deployment/Service/HPA、kube-rs Operator、Sidecar、QoS | 本页**不重复**其配置管理与部署模式正文 |
| [云原生与 Serverless 模式](../14_enterprise_architecture/12_cloud_native_and_serverless_patterns.md) | 企业架构模式（L5-L6） | 云原生模式语义矩阵、Serverless、服务网格 | 本页提供模式落地时的构建工序 |
| **本页** | 构建与交付流水线（L4-L5） | 多阶段 Dockerfile、cargo-chef、musl/静态链接、distroless、探针实现、cgroup 感知、tokio 信号处理 | canonical：容器化构建工序与生命周期实现 |

> **判定依据**: AGENTS.md §2 Canonical 规则。F 轨道缺口（`reports/F_TRACK_PLAN_2026-10-13.md` §20）指已删除的 `knowledge/06_ecosystem/deployment/01_kubernetes_deployment_guide.md` 部署指南——其「构建工序」维度在 `concept/` 无 canonical 承接，本页即该缺口的互补补齐；「部署语义」维度已由 `11_kubernetes_rust.md` 覆盖，不重复建页。

交付流水线全景：

```text
源码 (Cargo.toml/Cargo.lock/src)
  │  cargo-chef prepare → recipe.json          # 依赖清单快照
  │  cargo-chef cook   → 依赖预编译缓存层        # 源码变更不击穿依赖层
  ▼
builder 阶段: cargo build --release [--target *-musl]
  │  产物: 单一自包含二进制（Rust 无运行时依赖）
  ▼
runtime 阶段: distroless/cc | scratch | slim
  │  USER nonroot · 无 shell · 无包管理器
  ▼
Kubernetes: 镜像 → Pod → 探针门控 → 流量 → SIGTERM 排空 → 退出
```

---

## 二、容器化构建流水线

### 2.1 多阶段构建的层缓存语义

Docker 层缓存以「指令 + 输入内容哈希」为键。Rust 项目的关键矛盾：**编译依赖耗时最长，却最容易因无关源码改动而失效**。解法是重排 COPY 顺序，把「依赖清单」与「源码」拆成两个缓存层：

```dockerfile
# 反例顺序（每次改一行代码都全量重编译）:
# COPY . .
# RUN cargo build --release

# 正确顺序（依赖清单未变 → 依赖编译层命中缓存）:
FROM rust:1.99-slim-bookworm AS builder
WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo 'fn main() {}' > src/main.rs
RUN cargo build --release          # 依赖全部编译进 target/ 缓存层
RUN rm -rf src                    # 删除 dummy 源码
COPY src ./src
RUN cargo build --release          # 只有本地 crate 重新编译
```

> **关键洞察**: dummy `main.rs` 技巧的语义是让 `cargo build` 在「只有依赖、没有真实源码」的输入下先跑一遍，把依赖编译产物固化进镜像层；第二次 build 只对本地 crate 增量编译。该技巧对 workspace 多 crate 项目需要为每个本地 crate 造 dummy，维护成本高——这正是 cargo-chef 出现的动机。[来源: [cargo-chef README](https://github.com/LukeMathWalker/cargo-chef)]

### 2.2 cargo-chef：依赖层与源码层解耦

[cargo-chef](https://github.com/LukeMathWalker/cargo-chef) 把「依赖图」显式化为可缓存的 recipe 文件，替代 dummy 技巧：

```dockerfile
FROM rust:1.99-slim-bookworm AS chef
RUN cargo install cargo-chef
WORKDIR /app

FROM chef AS planner
COPY Cargo.toml Cargo.lock ./
RUN cargo chef prepare --recipe-path recipe.json   # 只含依赖清单，不含源码

FROM chef AS builder
COPY --from=planner /app/recipe.json recipe.json
RUN cargo chef cook --release --recipe-path recipe.json  # 预编译全部依赖
COPY . .
RUN cargo build --release                            # 本地 crate 增量编译
```

| 阶段 | 输入 | 缓存失效条件 |
|---|---|---|
| `prepare` | `Cargo.toml` + `Cargo.lock` | 依赖清单变更 |
| `cook` | `recipe.json` | 依赖版本/feature 变更 |
| `build` | 全量源码 | 仅本地源码变更 |

> **边界说明**: `cook` 只缓存第三方依赖。若本地 workspace 内多个 crate 相互依赖，`COPY . .` 后仍会重编译本地 crate 图；对超大 workspace 可配合 `sccache` 或 CI 级 `cargo build` 缓存进一步压缩。[来源: [cargo-chef](https://github.com/LukeMathWalker/cargo-chef)]

### 2.3 musl 与静态链接：从 glibc 耦合到 scratch 镜像

glibc 动态链接的二进制对运行时镜像的 glibc 版本有隐式要求（builder 与 runtime 的 glibc 不一致会产生符号版本错误）。musl 目标把这一耦合彻底消除：

```dockerfile
FROM rust:1.99-slim-bookworm AS builder
RUN apt-get update && apt-get install -y musl-tools
RUN rustup target add x86_64-unknown-linux-musl
WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN cargo chef prepare --recipe-path recipe.json
RUN cargo chef cook --release --target x86_64-unknown-linux-musl --recipe-path recipe.json
COPY . .
RUN cargo build --release --target x86_64-unknown-linux-musl

FROM scratch
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/my-service /my-service
COPY --from=builder /usr/share/ca-certificates /usr/share/ca-certificates
ENTRYPOINT ["/my-service"]
```

要点：

1. **静态链接产物**放入 `scratch`（空镜像）后，镜像只含二进制与显式拷贝的文件，体积可压到 10-20 MB，攻击面为零个可执行工具。
2. **TLS 根证书必须显式拷贝**：`scratch` 没有 `/etc/ssl`，`reqwest`/`rustls` 加载系统信任库会失败。
3. **musl 的破坏边界**：依赖链中若含需要 glibc 的 C 库（部分 vendored OpenSSL、某些 DNS 解析路径），musl 目标可能链接失败或行为退化；此时退回 `distroless/cc`（见 2.4）。
4. Rust 1.99.0 起 x86_64 默认 PIE 化、`riscv64-unknown-linux-musl` 进入 Tier 2，musl 谱系的平台覆盖继续扩大。[来源: [Rust musl 平台支持](https://doc.rust-lang.org/rustc/platform-support/x86_64-unknown-linux-musl.html) · [Rust 1.99.0 Release Notes](https://releases.rs/docs/1.99.0/)]

### 2.4 distroless 镜像族选型

[Google Distroless](https://github.com/GoogleContainerTools/distroless) 提供「只有运行时依赖、没有包管理器与 shell」的镜像族：

| 镜像 | 内容 | 适用 Rust 场景 |
|---|---|---|
| `gcr.io/distroless/static` | 仅 CA 证书 + `/tmp` | musl 静态二进制（首选） |
| `gcr.io/distroless/cc` | + libstdc++/gcc 运行时 | glibc 动态链接、含 C 依赖 |
| `gcr.io/distroless/base` | + glibc | 需要 glibc 的 C 扩展依赖 |
| `gcr.io/distroless/cc-debian12` | 上述 Debian 12 变体 | 与 `rust:1.99-slim-bookworm` 构建层对齐 |

```dockerfile
FROM gcr.io/distroless/cc-debian12 AS runtime
COPY --from=builder /app/target/release/my-service /usr/local/bin/my-service
USER nonroot:nonroot
EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/my-service"]
```

> **工程价值**: `USER nonroot:nonroot` 配合 Kubernetes 的 `securityContext.runAsNonRoot: true` 形成双层防线；distroless 无 shell 意味着 `kubectl exec` 排障不可用，排障需改用 [ephemeral debug 容器](https://kubernetes.io/docs/tasks/debug/debug-application/debug-running-pod/)。

### 2.5 参考 Dockerfile：cargo-chef + musl + distroless 全链路

生产推荐的组合（依赖缓存 + 静态链接 + 最小运行时 + 非 root）：

```dockerfile
# syntax=docker/dockerfile:1
FROM rust:1.99-slim-bookworm AS chef
RUN cargo install cargo-chef
WORKDIR /app

FROM chef AS planner
COPY Cargo.toml Cargo.lock ./
RUN cargo chef prepare --recipe-path recipe.json

FROM chef AS builder
COPY --from=planner /app/recipe.json recipe.json
RUN rustup target add x86_64-unknown-linux-musl \
    && apt-get update && apt-get install -y musl-tools
RUN cargo chef cook --release --target x86_64-unknown-linux-musl --recipe-path recipe.json
COPY . .
RUN cargo build --release --target x86_64-unknown-linux-musl

FROM gcr.io/distroless/static-debian12:nonroot AS runtime
COPY --from=builder /app/target/x86_64-unknown-linux-musl/release/my-service /usr/local/bin/my-service
EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/my-service"]
```

> **关键洞察**: `:nonroot` 标签变体已内置非 root 用户与 UID，无需再写 `USER` 指令；`static` 族与 musl 二进制组合时，最终镜像不含任何 libc——扫描器视角的攻击面只剩一个 ELF 文件。

---

## 三、Kubernetes 运行时契约

### 3.1 探针契约：startup / readiness / liveness

三类探针职责互斥，Rust 服务应暴露**两个独立端点**而非一个：

```yaml
startupProbe:        # 启动门控：通过前屏蔽 liveness/readiness 失败
  httpGet: { path: /healthz/live, port: 8080 }
  failureThreshold: 30
  periodSeconds: 2
readinessProbe:      # 流量门控：失败 → 从 Service endpoints 摘除
  httpGet: { path: /healthz/ready, port: 8080 }
  periodSeconds: 5
livenessProbe:       # 存活门控：失败 → 容器重启
  httpGet: { path: /healthz/live, port: 8080 }
  periodSeconds: 10
```

Rust 侧实现（axum，`ignore` 依赖块）：

```rust ignore
use std::sync::atomic::{AtomicBool, Ordering};
use axum::{routing::get, Router, http::StatusCode};

static READY: AtomicBool = AtomicBool::new(true);

async fn live() -> StatusCode {
    // 只回答「事件循环还在转」：不查数据库、不查下游
    StatusCode::OK
}

async fn ready() -> StatusCode {
    // 停机排空期间翻转为 false，让 kube-proxy 先摘流量再退出进程
    if READY.load(Ordering::Acquire) { StatusCode::OK } else { StatusCode::SERVICE_UNAVAILABLE }
}

fn router() -> Router {
    Router::new().route("/healthz/live", get(live)).route("/healthz/ready", get(ready))
}
```

> **契约要点**: `livenessProbe` 检查下游依赖是反模式（见第四节反例 2）——下游故障时重启整个服务只会放大故障；`readinessProbe` 才是表达「暂时不能接流量」的正确通道。探针端点处理函数不得进入任何可能阻塞的共享状态，否则探针超时会被误判为死锁。[来源: [Kubernetes 探针文档](https://kubernetes.io/docs/tasks/configure-pod-container/configure-liveness-readiness-startup-probes/)]

### 3.2 资源限制与 cgroup 感知

```yaml
resources:
  requests: { cpu: 250m, memory: 128Mi }   # 调度依据
  limits:   { cpu: "1",  memory: 256Mi }   # 硬上限：超限 → OOMKill / CPU 节流
```

Rust 服务特有的两个感知点：

1. **`std::thread::available_parallelism()` 尊重 cgroup 配额**——tokio 多线程运行时默认按它决定 worker 线程数，因此 `limits.cpu` 会直接影响运行时并行度：

```rust
// 容器内实测：limits.cpu=1 时返回 1（Linux cgroup v1/v2 均生效）
let workers = std::thread::available_parallelism()
    .map(|n| n.get())
    .unwrap_or(1);
println!("runtime worker threads: {workers}");
```

2. **内存 limit 覆盖整个进程足迹**（二进制 + 堆 + mmap），Rust 无 GC 但分配器（glibc malloc / mimalloc）有自己的 arena；`requests.memory` 应按「稳态 RSS + 峰值余量」设定，而不是按堆分配器上限设定，否则突发分配直接触发 OOMKill（exit 137）。[来源: [Manage Resources for Containers](https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/)]

> **边界说明**: CPU limit 触发的是 cgroup 节流（throttling）而非进程终止——表现为尾延迟锯齿波。对尾延迟敏感的服务，常见做法是只设 `requests.cpu` 不设 `limits.cpu`（QoS 从 Guaranteed 降为 Burstable），用尾延迟指标而非 OOM 指标做权衡。

### 3.3 优雅停机与 tokio 信号处理

Kubernetes 终止序列：`SIGTERM` → 等待 `terminationGracePeriodSeconds`（默认 30s）→ `SIGKILL`。同时 readiness 失败与端点摘除**与容器终止并发进行**——进程必须自己完成「摘流量 → 排空在途请求 → 退出」三步：

```rust ignore
use tokio::signal::unix::{signal, SignalKind};

async fn shutdown_signal() {
    let terminate = async {
        signal(SignalKind::terminate()).expect("install SIGTERM handler")
            .recv().await;
    };
    let interrupt = async {
        signal(SignalKind::interrupt()).expect("install SIGINT handler")
            .recv().await;
    };
    tokio::select! {
        _ = terminate => {},
        _ = interrupt => {},
    }
    // 与 3.1 的 readiness 端点联动：先摘流量，再排空
    READY.store(false, Ordering::Release);
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, router())
        .with_graceful_shutdown(shutdown_signal())
        .await?;
    Ok(())
}
```

时序约束（三条必须同时成立的算术）：

```text
探针摘除时间 (readiness periodSeconds × 失败检出)
  + 在途请求排空时间 (最长请求耗时)
  + 资源清理时间 (连接池 flush、指标上报)
  ≤ terminationGracePeriodSeconds
```

> **关键洞察**: `tokio::signal` 的 handler 与 `signal-hook`、`ctrlc` 等第三方信号库**不能混用**——同一信号只能注册一次，重复注册会导致其中一个库收不到信号。选定 `tokio::signal` 后，全进程的信号处理都应经由它。[来源: [tokio::signal 文档](https://docs.rs/tokio/latest/tokio/signal/index.html) · [Kubernetes Pod 终止语义](https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#pod-termination)]

---

## 四、反例与边界

### 反例 1：cargo-chef cook 后不锁 `Cargo.lock`

`Cargo.lock` 未提交进仓库时，`prepare` 生成的 recipe 每次解析出不同版本，`cook` 缓存层永远失效，且构建不可复现。**正确做法**：`Cargo.lock` 必须入库，recipe 缓存命中以 lock 文件哈希为界。

### 反例 2：livenessProbe 检查下游依赖

`/healthz/live` 里查询数据库连接池：数据库抖动 30 秒 → 全部副本 liveness 失败 → 集群级重启风暴 → 数据库承受重连洪峰。liveness 只应回答「进程事件循环存活」；下游健康属于 readiness 与独立监控的职责。

### 反例 3：scratch 镜像遗漏 CA 证书

musl 静态二进制放入 `scratch` 后服务启动正常，但首个 HTTPS 出站请求失败（`invalid peer certificate: UnknownIssuer`）——信任库不存在。必须在 Dockerfile 显式 `COPY` CA 证书，或改用 `distroless/static`（自带证书）。

### 反例 4：`terminationGracePeriodSeconds` 与排空窗口错配

grace period 设 10s，但服务最长流式请求 25s：SIGTERM 后排空未完成即被 SIGKILL，客户端看到连接重置。排空窗口必须按 P99 请求耗时反推 grace period，而不是取默认值。

### 边界极限

- **musl 边界**：依赖含 glibc-only C 库（部分 vendored OpenSSL 配置）时 musl 目标不可用，退回 `distroless/cc` 并接受 libc 层存在。
- **distroless 边界**：无 shell 使 `kubectl exec` 排障失效；调试需 ephemeral 容器或构建期注入 `strace` 类工具后移除。
- **镜像体积边界**：`strip` + `panic = "abort"` + LTO 可再压 20-40% 体积，代价是 panic 回溯信息丢失——与 `crash-loop 快速失败` 的可观测性权衡需显式记录。

---

## 五、决策树：构建与镜像选型

```text
需要出站 TLS？
├─ 是 → 依赖链含 glibc-only C 库？
│        ├─ 是 → rust:slim 构建 + distroless/cc-debian12 运行（glibc 对齐）
│        └─ 否 → musl 静态构建 + distroless/static:nonroot（显式 CA）
└─ 否（纯内网服务）→ musl 静态构建 + scratch（最小攻击面）

构建耗时 > 5 分钟？
├─ 是 → cargo-chef（依赖层缓存）+ CI 层 sccache
└─ 否 → 两段 COPY + dummy main.rs 技巧即可

排障频率高（开发/预发环境）？
├─ 是 → distroless/base + 独立 debug 镜像变体
└─ 否 → distroless/static 或 scratch（生产）
```

---

## 六、常见陷阱

| # | 陷阱 | 症状 | 修正 |
|---|---|---|---|
| 1 | builder/runtime glibc 版本错配 | `GLIBC_2.xx not found` 启动崩溃 | 构建与运行层同源 Debian，或 musl 静态化 |
| 2 | `COPY . .` 排在依赖编译前 | 每次提交全量重编译 | 依赖清单先 COPY，或用 cargo-chef |
| 3 | 信号库混用（tokio::signal + signal-hook） | SIGTERM 丢失、被 SIGKILL | 全进程统一走 `tokio::signal` |
| 4 | readiness 端点复用 liveness 端点 | 停机时流量未摘除即断连 | 两个端点 + 停机时 readiness 翻转 503 |
| 5 | `limits.cpu` 引发节流尾延迟 | p99 锯齿波 | 尾延迟敏感服务只设 requests.cpu |
| 6 | scratch 无 CA 证书 | TLS 握手 UnknownIssuer | 显式 COPY 证书或用 distroless/static |
| 7 | 探针端点进入可阻塞共享状态 | 探针超时 → 误重启 | 探针 handler 无锁、无 IO |

---

## 七、来源与延伸阅读

- [Kubernetes Pod Lifecycle 与终止语义](https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/) — SIGTERM/SIGKILL、grace period、端点摘除并发语义
- [Configure Liveness, Readiness and Startup Probes](https://kubernetes.io/docs/tasks/configure-pod-container/configure-liveness-readiness-startup-probes/) — 三类探针职责与参数
- [Manage Resources for Containers](https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/) — requests/limits 与 QoS
- [Rust `x86_64-unknown-linux-musl` 平台支持](https://doc.rust-lang.org/rustc/platform-support/x86_64-unknown-linux-musl.html) — musl 目标官方定位
- [Rust 1.99.0 Release Notes](https://releases.rs/docs/1.99.0/) — PIE 默认化、riscv64-musl Tier 2（本页版本基线）
- [cargo-chef](https://github.com/LukeMathWalker/cargo-chef) — 依赖缓存 recipe 模型
- [Google Distroless](https://github.com/GoogleContainerTools/distroless) — 镜像族与 nonroot 变体
- [tokio::signal](https://docs.rs/tokio/latest/tokio/signal/index.html) — Unix 信号与 tokio 运行时的集成契约

---

## 相关概念

- [Rust 服务与 Kubernetes](11_kubernetes_rust.md) — 运行时部署语义 canonical（ConfigMap/Secret、HPA、Operator、Sidecar、QoS）
- [云原生生态](02_cloud_native.md) — 生态概览入口
- [Tokio 运行时内部机制](10_tokio_runtime_internals.md) — worker 线程与并行度语义
- [交叉编译](../05_systems_and_embedded/02_cross_compilation.md) — musl 目标与 target 机制
- [云原生与 Serverless 模式](../14_enterprise_architecture/12_cloud_native_and_serverless_patterns.md) — 架构模式层
- [微服务架构模式](../../05_comparative/05_idioms_patterns_architecture/04_architecture/03_microservices.md) — L5 架构对比层：容器化交付的微服务语境
- [可观测性与 SRE 模式](../14_enterprise_architecture/09_observability_and_sre_patterns.md) — 探针之外的信号面

---

## 🧭 思维导图（Mindmap）

```text
Kubernetes 上的 Rust 服务：容器化构建与交付流水线
├── 构建流水线
│   ├── 层缓存语义
│   │   ├── 依赖清单先 COPY
│   │   └── dummy main.rs 技巧
│   ├── cargo-chef
│   │   ├── prepare → recipe.json
│   │   └── cook → 依赖预编译层
│   ├── musl 静态链接
│   │   ├── scratch 镜像
│   │   ├── CA 证书显式拷贝
│   │   └── glibc-only C 库边界
│   └── distroless 族
│       ├── static / cc / base
│       └── nonroot 变体
├── 运行时契约
│   ├── 探针
│   │   ├── startup / readiness / liveness
│   │   └── 停机时 readiness 翻转
│   ├── 资源
│   │   ├── available_parallelism ↔ cgroup
│   │   └── OOMKill / CPU 节流
│   └── 优雅停机
│       ├── SIGTERM → grace period → SIGKILL
│       ├── tokio::signal 单一信号入口
│       └── 排空窗口算术
└── 决策框架
    ├── 镜像选型树
    └── 体积 vs 可观测性权衡
```

> **认知功能**: 本 mindmap 从本页章节结构提炼，一级分支对应「构建 / 运行 / 决策」三段式，可作为交付评审时的快速检查索引。

## 国际化权威来源补充（International Authority Sources）

- <https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/>
- <https://kubernetes.io/docs/tasks/configure-pod-container/configure-liveness-readiness-startup-probes/>
- <https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/>
- <https://doc.rust-lang.org/rustc/platform-support/x86_64-unknown-linux-musl.html>
- <https://doc.rust-lang.org/cargo/reference/profiles.html>
- <https://github.com/LukeMathWalker/cargo-chef>
- <https://github.com/GoogleContainerTools/distroless>
- 学术锚（2026-10-20 arXiv API 实核）：[The Promise and Reality of Continuous Integration Caching: An Empirical Study of Travis CI Builds (Ghaleb, da Costa, Zou)](https://arxiv.org/abs/2601.19146)（2026-01-27 提交，v2）——CI 缓存收益/失效/污染的实证量化，佐证本页「依赖层缓存（cargo-chef recipe）有收益但有失效陷阱」的工程判读口径；口径限于 CI 缓存现象学，Rust 容器专属结论仍以本页 crates.io/Docker 实查为准。
