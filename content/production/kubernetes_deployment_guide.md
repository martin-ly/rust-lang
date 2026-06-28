# Rust 服务 Kubernetes 部署指南

> **定位**: 生产环境容器化部署
> **适用**: Rust 微服务、API 服务、Web 应用
> **工具链**: Docker, Kubernetes, Helm (可选)

---

## 📋 目录

- [Rust 服务 Kubernetes 部署指南](.#rust-服务-kubernetes-部署指南)
  - [📋 目录](.#-目录)
  - [🎯 部署策略概览](.#-部署策略概览)
  - [📦 容器化](.#-容器化)
    - [1. 多阶段 Dockerfile](.#1-多阶段-dockerfile)
    - [2. 镜像优化](.#2-镜像优化)
  - [☸️ Kubernetes 资源配置](.#️-kubernetes-资源配置)
    - [1. Deployment](.#1-deployment)
    - [2. Service](.#2-service)
    - [3. ConfigMap / Secret](.#3-configmap--secret)
    - [4. HorizontalPodAutoscaler](.#4-horizontalpodautoscaler)
  - [🔒 安全最佳实践](.#-安全最佳实践)
  - [📊 监控与可观测性](.#-监控与可观测性)
  - [🔗 参考资源](.#-参考资源)

---

## 🎯 部署策略概览

```text
本地开发 → Docker 构建 → 镜像仓库 → Kubernetes 部署
    │            │              │              │
    ▼            ▼              ▼              ▼
cargo run   多阶段构建      GHCR/DockerHub   Helm/Raw YAML
```

**Rust 容器化优势**:

- 静态链接二进制 → 最小镜像 (scratch/distroless)
- 无 GC → 可预测的内存使用，适合资源限制
- 编译期安全 → 减少运行时崩溃和重启

---

## 📦 容器化

### 1. 多阶段 Dockerfile

```dockerfile
# 阶段 1: 构建
FROM rust:1.95-slim AS builder
WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN cargo build --release

# 阶段 2: 最小运行镜像
FROM gcr.io/distroless/cc-debian12:nonroot
COPY --from=builder /app/target/release/myapp /usr/local/bin/myapp
EXPOSE 8080
USER nonroot:nonroot
ENTRYPOINT ["/usr/local/bin/myapp"]
```

**镜像大小对比**:

| 基础镜像 | 大小 | 适用场景 |
|---------|------|---------|
| `rust:1.95` | ~1.5GB | 仅构建 |
| `debian:slim` | ~80MB | 需要 shell/debug |
| `alpine` | ~15MB | 需要 musl 静态链接 |
| `distroless/cc` | ~25MB | **推荐**: 最小攻击面 |
| `scratch` | ~5MB | 纯静态二进制 |

### 2. 镜像优化

```dockerfile
# 使用 cargo-chef 缓存依赖层
FROM lukemathwalker/cargo-chef:latest-rust-1.95 AS chef
WORKDIR /app

FROM chef AS planner
COPY . .
RUN cargo chef prepare --recipe-path recipe.json

FROM chef AS builder
COPY --from=planner /app/recipe.json recipe.json
# 仅依赖层 — 缓存友好
RUN cargo chef cook --release --recipe-path recipe.json
COPY . .
RUN cargo build --release
```

---

## ☸️ Kubernetes 资源配置

### 1. Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-api
  labels:
    app: rust-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-api
  template:
    metadata:
      labels:
        app: rust-api
    spec:
      securityContext:
        runAsNonRoot: true
        runAsUser: 65532
        seccompProfile:
          type: RuntimeDefault
      containers:
        - name: api
          image: ghcr.io/myorg/rust-api:1.95.0
          ports:
            - containerPort: 8080
              name: http
          resources:
            requests:
              memory: "64Mi"
              cpu: "100m"
            limits:
              memory: "256Mi"
              cpu: "500m"
          livenessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /ready
              port: 8080
            initialDelaySeconds: 2
            periodSeconds: 5
          securityContext:
            allowPrivilegeEscalation: false
            readOnlyRootFilesystem: true
            capabilities:
              drop:
                - ALL
```

### 2. Service

```yaml
apiVersion: v1
kind: Service
metadata:
  name: rust-api
spec:
  selector:
    app: rust-api
  ports:
    - port: 80
      targetPort: 8080
  type: ClusterIP
---
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: rust-api
  annotations:
    nginx.ingress.kubernetes.io/rate-limit: "100"
spec:
  rules:
    - host: api.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: rust-api
                port:
                  number: 80
```

### 3. ConfigMap / Secret

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: rust-api-config
data:
  RUST_LOG: "info,tower_http=debug"
  SERVER_WORKERS: "4"
---
apiVersion: v1
kind: Secret
metadata:
  name: rust-api-secrets
type: Opaque
stringData:
  DATABASE_URL: "postgres://user:pass@db:5432/app"
  JWT_SECRET: "replace-me-in-production"
```

### 4. HorizontalPodAutoscaler

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: rust-api-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: rust-api
  minReplicas: 3
  maxReplicas: 20
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 30
      policies:
        - type: Percent
          value: 100
          periodSeconds: 15
```

---

## 🔒 安全最佳实践

| 层级 | 措施 | 说明 |
|------|------|------|
| 镜像 | Distroless + nonroot | 最小攻击面 |
| 容器 | readOnlyRootFilesystem | 防止运行时篡改 |
| 容器 | drop ALL capabilities | 最小权限 |
| Pod | runAsNonRoot | 禁止 root |
| Pod | seccomp RuntimeDefault | 系统调用过滤 |
| 网络 | NetworkPolicy | 东西向流量限制 |
| 供应链 | cosign 签名 | 镜像验证 |

---

## 📊 监控与可观测性

```rust
// 使用 tracing + opentelemetry 集成
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_telemetry() {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(opentelemetry::global::tracer("rust-api"))
        .init();
}
```

**推荐工具栈**:

- **指标**: Prometheus + `metrics` crate
- **追踪**: Jaeger/Tempo + OpenTelemetry
- **日志**: `tracing` + fluent-bit/vector
- **告警**: Prometheus Alertmanager

---

## 🔗 参考资源

- [项目 K8s 配置](../../k8s)
- [Rust on Kubernetes Best Practices](https://www.shuttle.rs/blog/2024/03/28/rust-on-kubernetes)
- [Distroless Images](https://github.com/GoogleContainerTools/distroless)
- [cargo-chef](https://github.com/LukeMathWalker/cargo-chef)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
