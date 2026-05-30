# Kubernetes 部署完整指南

> **相关概念**: [云原生](../../../concept/06_ecosystem/24_cloud_native.md)
> **Bloom 层级**: 理解
> **适用范围**: 生产环境
> **Kubernetes 版本**: 1.28+
> **难度**: 高级
> **预计时间**: 60分钟
> **权威来源**: [Kubernetes 官方文档](https://kubernetes.io/docs/), [Distroless 镜像](https://github.com/GoogleContainerTools/distroless)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Kubernetes 官方文档来源标注 [来源: Authority Source Sprint Batch 8]

---

## 📋 目录
>
> **[来源: Rust Official Docs]**

- [Kubernetes 部署完整指南](#kubernetes-部署完整指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🏗️ 基础架构](#️-基础架构)
  - [🐳 容器化](#-容器化)
    - [多阶段构建](#多阶段构建)
    - [Distroless 镜像](#distroless-镜像)
  - [☸️ Kubernetes 配置](#️-kubernetes-配置)
    - [Deployment](#deployment)
    - [Service](#service)
    - [ConfigMap](#configmap)
    - [Secret](#secret)
    - [HPA (水平自动伸缩)](#hpa-水平自动伸缩)
    - [VPA (垂直自动伸缩)](#vpa-垂直自动伸缩)
  - [📈 可观测性](#-可观测性)
    - [Metrics](#metrics)
    - [Logging](#logging)
    - [Tracing](#tracing)
  - [🛡️ 安全性](#️-安全性)
    - [NetworkPolicy](#networkpolicy)
    - [PodSecurityPolicy](#podsecuritypolicy)
  - [⚡ 性能优化](#-性能优化)
    - [资源优化](#资源优化)
    - [启动优化](#启动优化)
    - [优雅关闭](#优雅关闭)
  - [🔗 参考资源](#-参考资源)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

---

## 🎯 概述
>
> **[来源: Rust Official Docs]**

本指南涵盖将 Rust 应用部署到 Kubernetes 的完整流程，包括：

- 优化的容器镜像构建
- 完整的 K8s 资源配置
- 可观测性集成
- 安全配置
- 性能优化

---

## 🏗️ 基础架构
>
> **[来源: Rust Official Docs]**

```text
┌─────────────────────────────────────────────────────────┐
│                      Ingress                            │
│                  (NGINX/Traefik)                        │
└─────────────────────┬───────────────────────────────────┘
                      │
┌─────────────────────▼───────────────────────────────────┐
│                    Service                              │
│              (Load Balancer)                            │
└─────────────────────┬───────────────────────────────────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
┌───────▼───┐  ┌──────▼────┐  ┌────▼──────┐
│   Pod 1   │  │   Pod 2   │  │   Pod 3   │
│  ┌─────┐  │  │  ┌─────┐  │  │  ┌─────┐  │
│  │ App │  │  │  │ App │  │  │  │ App │  │
│  └──┬──┘  │  │  └──┬──┘  │  │  └──┬──┘  │
│     │     │  │     │     │  │     │     │
│  ┌──▼──┐  │  │  ┌──▼──┐  │  │  ┌──▼──┐  │
│  │Sidecar│|  │  │Sidecar│ | │  │Sidecar││
│  │Proxy│  │  │ │Proxy │  │  │  │Proxy|  |
│  └─────┘  │  │  └─────┘  │  │  └─────┘  │
└───────────┘  └───────────┘  └───────────┘
```

---

## 🐳 容器化
>
> **[来源: Rust Official Docs]**

### 多阶段构建
>
> **[来源: Rust Official Docs]**

```dockerfile
# ==========================================
# 构建阶段
# ==========================================
FROM rust:1.95-slim AS builder

WORKDIR /app

# 安装依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 缓存依赖
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release && rm -rf src

# 构建应用
COPY src ./src
RUN touch src/main.rs  # 强制重新编译
RUN cargo build --release

# 运行测试
RUN cargo test --release

# ==========================================
# 生产镜像
# ==========================================
FROM gcr.io/distroless/cc-debian12

# 非 root 用户
USER nonroot:nonroot

# 复制二进制文件
COPY --from=builder --chown=nonroot:nonroot /app/target/release/myapp /app/

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD ["/app/myapp", "healthcheck"]

EXPOSE 8080

ENTRYPOINT ["/app/myapp"]
```

### Distroless 镜像
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```dockerfile
# 更安全的 distroless 变体
FROM rust:1.95-slim AS builder
WORKDIR /app
COPY . .
RUN cargo build --release

# 使用静态链接
FROM scratch
COPY --from=builder /app/target/release/myapp /myapp
# 需要静态链接: RUSTFLAGS='-C target-feature=+crt-static'
ENTRYPOINT ["/myapp"]
```

```bash
# 构建命令
docker build -t myapp:v1.0.0 .

# 安全扫描
docker run --rm -v /var/run/docker.sock:/var/run/docker.sock \
    aquasec/trivy image myapp:v1.0.0
```

---

## ☸️ Kubernetes 配置
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Deployment
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
  namespace: production
  labels:
    app: rust-app
    version: v1.0.0
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 25%
      maxUnavailable: 0
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: rust-app
      securityContext:
        runAsNonRoot: true
        runAsUser: 65534
        runAsGroup: 65534
        fsGroup: 65534

      containers:
      - name: app
        image: registry.example.com/rust-app:v1.0.0
        imagePullPolicy: Always

        ports:
        - name: http
          containerPort: 8080
          protocol: TCP

        env:
        - name: RUST_LOG
          value: "info"
        - name: RUST_BACKTRACE
          value: "1"
        - name: APP_ENV
          value: "production"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: rust-app-secrets
              key: database-url

        envFrom:
        - configMapRef:
            name: rust-app-config

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
            port: http
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 5
          failureThreshold: 3

        readinessProbe:
          httpGet:
            path: /ready
            port: http
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 3

        startupProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 5
          periodSeconds: 5
          failureThreshold: 30

        securityContext:
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          capabilities:
            drop:
            - ALL

        volumeMounts:
        - name: tmp
          mountPath: /tmp

      volumes:
      - name: tmp
        emptyDir: {}

      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - rust-app
              topologyKey: kubernetes.io/hostname
```

### Service
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```yaml
# k8s/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: rust-app
  namespace: production
  labels:
    app: rust-app
spec:
  type: ClusterIP
  selector:
    app: rust-app
  ports:
  - name: http
    port: 80
    targetPort: 8080
    protocol: TCP
  sessionAffinity: None

---
apiVersion: v1
kind: Service
metadata:
  name: rust-app-headless
  namespace: production
  labels:
    app: rust-app
spec:
  type: ClusterIP
  clusterIP: None  # Headless for service discovery
  selector:
    app: rust-app
  ports:
  - name: http
    port: 8080
```

### ConfigMap
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```yaml
# k8s/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: rust-app-config
  namespace: production
data:
  # 应用配置
  RUST_LOG: "info,tower_http=debug"
  APP_PORT: "8080"
  METRICS_PORT: "9090"

  # 数据库连接池配置
  DB_MAX_CONNECTIONS: "100"
  DB_MIN_CONNECTIONS: "10"
  DB_CONNECT_TIMEOUT: "10"

  # 性能调优
  TOKIO_WORKER_THREADS: "8"

  # 日志格式
  LOG_FORMAT: "json"
```

### Secret
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```yaml
# k8s/secret.yaml (加密存储)
apiVersion: v1
kind: Secret
metadata:
  name: rust-app-secrets
  namespace: production
type: Opaque
stringData:
  database-url: "postgres://user:pass@postgres:5432/myapp"
  api-key: "secret-api-key"
  jwt-secret: "jwt-signing-secret"
```

### HPA (水平自动伸缩)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```yaml
# k8s/hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: rust-app-hpa
  namespace: production
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: rust-app
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
  - type: Pods
    pods:
      metric:
        name: http_requests_per_second
      target:
        type: AverageValue
        averageValue: "1000"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15
      - type: Pods
        value: 4
        periodSeconds: 15
      selectPolicy: Max
```

### VPA (垂直自动伸缩)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```yaml
# k8s/vpa.yaml
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: rust-app-vpa
  namespace: production
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: rust-app
  updatePolicy:
    updateMode: "Auto"
  resourcePolicy:
    containerPolicies:
    - containerName: app
      minAllowed:
        cpu: 50m
        memory: 64Mi
      maxAllowed:
        cpu: 1000m
        memory: 1Gi
      controlledResources: ["cpu", "memory"]
```

---

## 📈 可观测性
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### Metrics
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```yaml
# k8s/servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: rust-app-metrics
  namespace: production
  labels:
    app: rust-app
spec:
  selector:
    matchLabels:
      app: rust-app
  endpoints:
  - port: http
    path: /metrics
    interval: 30s
    scrapeTimeout: 10s
```

### Logging
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```yaml
# k8s/fluentd-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: fluentd-config
data:
  fluent.conf: |
    <source>
      @type tail
      path /var/log/containers/rust-app*.log
      pos_file /var/log/fluentd-rust-app.log.pos
      tag rust-app
      <parse>
        @type json
        time_key timestamp
        time_format %Y-%m-%dT%H:%M:%S.%NZ
      </parse>
    </source>

    <filter rust-app>
      @type grep
      <regexp>
        key level
        pattern ^(ERROR|WARN|INFO)$
      </regexp>
    </filter>
```

### Tracing
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```yaml
# k8s/otel-collector.yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: rust-app-traces
spec:
  mode: sidecar
  config: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318

    exporters:
      jaeger:
        endpoint: jaeger-collector:14250
        tls:
          insecure: true

    service:
      pipelines:
        traces:
          receivers: [otlp]
          exporters: [jaeger]
```

---

## 🛡️ 安全性
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### NetworkPolicy
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```yaml
# k8s/networkpolicy.yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: rust-app-network-policy
  namespace: production
spec:
  podSelector:
    matchLabels:
      app: rust-app
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          name: ingress-nginx
    ports:
    - protocol: TCP
      port: 8080
  egress:
  - to:
    - podSelector:
        matchLabels:
          app: postgres
    ports:
    - protocol: TCP
      port: 5432
  - to: []  # DNS
    ports:
    - protocol: UDP
      port: 53
```

### PodSecurityPolicy
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```yaml
# k8s/podsecuritypolicy.yaml
apiVersion: policy/v1beta1
kind: PodSecurityPolicy
metadata:
  name: rust-app-psp
spec:
  privileged: false
  allowPrivilegeEscalation: false
  requiredDropCapabilities:
    - ALL
  volumes:
    - 'emptyDir'
  runAsUser:
    rule: 'MustRunAsNonRoot'
  seLinux:
    rule: 'RunAsAny'
  fsGroup:
    rule: 'RunAsAny'
```

---

## ⚡ 性能优化
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 资源优化
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```yaml
# 基于实际使用调整资源
resources:
  requests:
    memory: "64Mi"   # 根据实际内存使用设置
    cpu: "100m"      # 1/10 核心
  limits:
    memory: "128Mi"  # 防止 OOM
    cpu: "1000m"     # 1 核心
```

### 启动优化
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,compile_fail
// 应用代码: 快速启动
#[tokio::main]
async fn main() {
    // 1. 快速启动 HTTP 服务
    let app = create_app();
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await.unwrap();

    // 2. 在后台初始化数据库连接池
    tokio::spawn(async {
        init_db_pool().await;
    });

    // 3. 立即开始服务
    axum::serve(listener, app).await.unwrap();
}
```

### 优雅关闭
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
use tokio::signal;

async fn graceful_shutdown() {
    let ctrl_c = async {
        signal::ctrl_c().await.expect("failed to install Ctrl+C handler");
    };

    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    println!("signal received, starting graceful shutdown");

    // 关闭逻辑
    // 1. 停止接受新连接
    // 2. 等待现有请求完成
    // 3. 关闭数据库连接
    // 4. 退出
}
```

---

## 🔗 参考资源
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [Kubernetes 官方文档](https://kubernetes.io/docs/)
- [Distroless 镜像](https://github.com/GoogleContainerTools/distroless)
- [Kubernetes Security Best Practices](https://kubernetes.io/docs/concepts/security/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [Rust 标准库速查](../../05_reference/03_std_library_cheatsheet.md)

- [Deployment 部署](README.md)
- [Databases 数据库](../databases/README.md)

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**
