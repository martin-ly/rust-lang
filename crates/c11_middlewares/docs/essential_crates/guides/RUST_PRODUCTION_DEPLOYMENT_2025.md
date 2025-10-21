# Rust 生产部署完全指南 (2025版)

> 从开发到生产：Rust 应用的完整部署流程、最佳实践与故障排查

## 📋 目录

- [Rust 生产部署完全指南 (2025版)](#rust-生产部署完全指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心目标](#核心目标)
    - [技术栈选择](#技术栈选择)
  - [部署架构设计](#部署架构设计)
    - [1. 单体应用架构](#1-单体应用架构)
    - [2. 微服务架构](#2-微服务架构)
  - [容器化部署](#容器化部署)
    - [1. 多阶段 Dockerfile (生产优化)](#1-多阶段-dockerfile-生产优化)
    - [2. Docker Compose (本地开发)](#2-docker-compose-本地开发)
  - [Kubernetes 部署](#kubernetes-部署)
    - [1. 完整的 K8s 清单](#1-完整的-k8s-清单)
    - [2. 部署命令](#2-部署命令)
  - [CI/CD 流水线](#cicd-流水线)
    - [GitHub Actions 完整配置](#github-actions-完整配置)
  - [配置管理](#配置管理)
    - [1. 分层配置系统](#1-分层配置系统)
    - [2. Rust 配置加载代码](#2-rust-配置加载代码)
  - [日志与监控](#日志与监控)
    - [1. 结构化日志 (tracing)](#1-结构化日志-tracing)
    - [2. Prometheus 监控](#2-prometheus-监控)
    - [3. Grafana 仪表板](#3-grafana-仪表板)
  - [性能优化](#性能优化)
    - [1. 编译优化](#1-编译优化)
    - [2. 运行时优化](#2-运行时优化)
  - [安全加固](#安全加固)
    - [1. HTTPS/TLS 配置](#1-httpstls-配置)
    - [2. 安全头部](#2-安全头部)
    - [3. 速率限制](#3-速率限制)
  - [灾难恢复](#灾难恢复)
    - [1. 数据库备份](#1-数据库备份)
    - [2. 恢复流程](#2-恢复流程)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
      - [问题1: Pod 无法启动](#问题1-pod-无法启动)
      - [问题2: 性能下降](#问题2-性能下降)
      - [问题3: 内存泄漏](#问题3-内存泄漏)
  - [最佳实践](#最佳实践)
    - [✅ 推荐做法](#-推荐做法)
  - [常见陷阱](#常见陷阱)
    - [❌ 避免的错误](#-避免的错误)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [工具](#工具)
    - [监控生态](#监控生态)
    - [最佳实践1](#最佳实践1)
  - [总结](#总结)

---

## 概述

### 核心目标

**生产部署的关键要素：**

- ✅ **可靠性**：高可用、故障恢复
- ✅ **可观测性**：日志、指标、追踪
- ✅ **可扩展性**：水平扩展、负载均衡
- ✅ **安全性**：加密、认证、授权
- ✅ **可维护性**：配置管理、版本控制

### 技术栈选择

```toml
[dependencies]
# Web 框架
axum = "0.7"
tower = "0.4"
tower-http = "0.5"

# 配置管理
config = "0.14"
dotenvy = "0.15"

# 日志与追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
opentelemetry = "0.24"
opentelemetry-jaeger = "0.23"

# 监控
prometheus = "0.13"
metrics = "0.23"
metrics-exporter-prometheus = "0.15"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "migrate"] }

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 异步运行时
tokio = { version = "1.40", features = ["full"] }

# 安全
rustls = "0.23"
jsonwebtoken = "9.3"
argon2 = "0.5"
```

---

## 部署架构设计

### 1. 单体应用架构

```text
┌─────────────────────────────────────────┐
│          Load Balancer (Nginx)          │
│              (443 HTTPS)                │
└─────────────────┬───────────────────────┘
                  │
     ┌────────────┼────────────┐
     │            │            │
     ▼            ▼            ▼
┌─────────┐  ┌─────────┐  ┌─────────┐
│  App 1  │  │  App 2  │  │  App 3  │
│ (Rust)  │  │ (Rust)  │  │ (Rust)  │
└────┬────┘  └────┬────┘  └────┬────┘
     │            │            │
     └────────────┼────────────┘
                  │
                  ▼
          ┌───────────────┐
          │   PostgreSQL  │
          │  (Primary)    │
          └───────┬───────┘
                  │
          ┌───────▼───────┐
          │   PostgreSQL  │
          │   (Replica)   │
          └───────────────┘
```

**适用场景**：

- 中小型应用
- 单一数据库
- 团队规模 < 20人

### 2. 微服务架构

```text
                    ┌────────────────┐
                    │  API Gateway   │
                    │    (Axum)      │
                    └────────┬───────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
   ┌─────────┐          ┌─────────┐         ┌─────────┐
   │  User   │          │  Order  │         │ Payment │
   │ Service │          │ Service │         │ Service │
   └────┬────┘          └────┬────┘         └────┬────┘
        │                    │                    │
        ▼                    ▼                    ▼
   ┌─────────┐          ┌─────────┐         ┌─────────┐
   │  DB-1   │          │  DB-2   │         │  DB-3   │
   └─────────┘          └─────────┘         └─────────┘
                             │
                             ▼
                    ┌────────────────┐
                    │  Message Queue │
                    │    (Kafka)     │
                    └────────────────┘
```

**适用场景**：

- 大型复杂应用
- 团队规模 > 50人
- 需要独立扩展

---

## 容器化部署

### 1. 多阶段 Dockerfile (生产优化)

```dockerfile
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 阶段1: 构建器 (Builder)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
FROM rust:1.83-slim as builder

# 安装必要的系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 创建工作目录
WORKDIR /app

# 复制依赖文件 (利用 Docker 缓存)
COPY Cargo.toml Cargo.lock ./

# 预构建依赖 (优化构建速度)
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src
COPY migrations ./migrations

# 构建应用 (启用 LTO 和优化)
ENV CARGO_PROFILE_RELEASE_LTO=true
ENV CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
RUN cargo build --release

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 阶段2: 运行时 (Runtime)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非 root 用户
RUN useradd -m -u 1000 appuser

WORKDIR /app

# 从构建器复制二进制文件
COPY --from=builder /app/target/release/myapp /app/myapp
COPY --from=builder /app/migrations /app/migrations

# 设置权限
RUN chown -R appuser:appuser /app
USER appuser

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD ["/app/myapp", "health"]

# 暴露端口
EXPOSE 8080

# 启动应用
CMD ["/app/myapp"]
```

**优化效果**：

- ✅ 最终镜像大小：**~80MB** (相比 2GB+ 的完整 Rust 镜像)
- ✅ 构建时间：首次 5-10分钟，后续 30秒-2分钟
- ✅ 启动时间：< 1秒

### 2. Docker Compose (本地开发)

```yaml
version: '3.8'

services:
  # 应用服务
  app:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgres://user:pass@db:5432/myapp
      - RUST_LOG=info
      - JAEGER_AGENT_HOST=jaeger
    depends_on:
      - db
      - redis
      - jaeger
    networks:
      - app-network
    restart: unless-stopped

  # PostgreSQL 数据库
  db:
    image: postgres:16-alpine
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=pass
      - POSTGRES_DB=myapp
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    networks:
      - app-network
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user"]
      interval: 10s
      timeout: 5s
      retries: 5

  # Redis 缓存
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    networks:
      - app-network
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 3s
      retries: 5

  # Jaeger 追踪
  jaeger:
    image: jaegertracing/all-in-one:1.51
    ports:
      - "16686:16686"  # UI
      - "6831:6831/udp"  # Agent
    networks:
      - app-network

  # Prometheus 监控
  prometheus:
    image: prom/prometheus:v2.48.0
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus_data:/prometheus
    ports:
      - "9090:9090"
    networks:
      - app-network

volumes:
  postgres_data:
  prometheus_data:

networks:
  app-network:
    driver: bridge
```

---

## Kubernetes 部署

### 1. 完整的 K8s 清单

**Namespace:**

```yaml
apiVersion: v1
kind: Namespace
metadata:
  name: myapp-prod
  labels:
    env: production
```

**ConfigMap:**

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: myapp-config
  namespace: myapp-prod
data:
  APP_NAME: "MyApp"
  RUST_LOG: "info"
  PORT: "8080"
```

**Secret:**

```yaml
apiVersion: v1
kind: Secret
metadata:
  name: myapp-secrets
  namespace: myapp-prod
type: Opaque
stringData:
  DATABASE_URL: "postgres://user:password@db:5432/myapp"
  JWT_SECRET: "your-super-secret-key"
```

**Deployment:**

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: myapp
  namespace: myapp-prod
  labels:
    app: myapp
    version: v1.0.0
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: myapp
  template:
    metadata:
      labels:
        app: myapp
        version: v1.0.0
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      # 使用非 root 用户
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        fsGroup: 1000

      # 容器配置
      containers:
      - name: myapp
        image: myregistry.com/myapp:v1.0.0
        imagePullPolicy: IfNotPresent
        
        ports:
        - name: http
          containerPort: 8080
          protocol: TCP
        
        # 环境变量
        envFrom:
        - configMapRef:
            name: myapp-config
        - secretRef:
            name: myapp-secrets
        
        # 资源限制
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 500m
            memory: 512Mi
        
        # 健康检查
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 10
          timeoutSeconds: 3
          failureThreshold: 3
        
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
          timeoutSeconds: 2
          failureThreshold: 3
        
        # 启动探针 (避免慢启动被杀死)
        startupProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 0
          periodSeconds: 5
          timeoutSeconds: 3
          failureThreshold: 30
        
        # 卷挂载
        volumeMounts:
        - name: config
          mountPath: /app/config
          readOnly: true
      
      # 卷定义
      volumes:
      - name: config
        configMap:
          name: myapp-config
      
      # Pod 反亲和性 (分散到不同节点)
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
                  - myapp
              topologyKey: kubernetes.io/hostname
```

**Service:**

```yaml
apiVersion: v1
kind: Service
metadata:
  name: myapp
  namespace: myapp-prod
  labels:
    app: myapp
spec:
  type: ClusterIP
  selector:
    app: myapp
  ports:
  - name: http
    port: 80
    targetPort: 8080
    protocol: TCP
```

**HorizontalPodAutoscaler:**

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: myapp-hpa
  namespace: myapp-prod
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: myapp
  minReplicas: 3
  maxReplicas: 10
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
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15
```

**Ingress (HTTPS):**

```yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: myapp-ingress
  namespace: myapp-prod
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/force-ssl-redirect: "true"
    nginx.ingress.kubernetes.io/rate-limit: "100"
spec:
  ingressClassName: nginx
  tls:
  - hosts:
    - api.myapp.com
    secretName: myapp-tls
  rules:
  - host: api.myapp.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: myapp
            port:
              number: 80
```

### 2. 部署命令

```bash
# 1. 应用所有配置
kubectl apply -f k8s/namespace.yaml
kubectl apply -f k8s/configmap.yaml
kubectl apply -f k8s/secret.yaml
kubectl apply -f k8s/deployment.yaml
kubectl apply -f k8s/service.yaml
kubectl apply -f k8s/hpa.yaml
kubectl apply -f k8s/ingress.yaml

# 2. 查看部署状态
kubectl get all -n myapp-prod
kubectl get pods -n myapp-prod -w

# 3. 查看日志
kubectl logs -f deployment/myapp -n myapp-prod

# 4. 滚动更新
kubectl set image deployment/myapp myapp=myregistry.com/myapp:v1.1.0 -n myapp-prod
kubectl rollout status deployment/myapp -n myapp-prod

# 5. 回滚
kubectl rollout undo deployment/myapp -n myapp-prod
```

---

## CI/CD 流水线

### GitHub Actions 完整配置

```yaml
name: CI/CD Pipeline

on:
  push:
    branches: [main, develop]
    tags: ['v*']
  pull_request:
    branches: [main, develop]

env:
  CARGO_TERM_COLOR: always
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  # 阶段1: 代码质量检查
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  check:
    name: Code Quality
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy
      
      - name: Cache
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/bin/
            ~/.cargo/registry/index/
            ~/.cargo/registry/cache/
            ~/.cargo/git/db/
            target/
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Format Check
        run: cargo fmt --all -- --check
      
      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings
      
      - name: Security Audit
        run: |
          cargo install cargo-audit
          cargo audit

  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  # 阶段2: 测试
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  test:
    name: Test Suite
    runs-on: ubuntu-latest
    needs: check
    
    services:
      postgres:
        image: postgres:16-alpine
        env:
          POSTGRES_USER: test
          POSTGRES_PASSWORD: test
          POSTGRES_DB: testdb
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Cache
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/bin/
            ~/.cargo/registry/index/
            ~/.cargo/registry/cache/
            ~/.cargo/git/db/
            target/
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Run Tests
        run: cargo test --all-features --workspace
        env:
          DATABASE_URL: postgres://test:test@localhost:5432/testdb
      
      - name: Code Coverage
        run: |
          cargo install cargo-llvm-cov
          cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info
      
      - name: Upload Coverage
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
          fail_ci_if_error: true

  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  # 阶段3: 构建镜像
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  build:
    name: Build Docker Image
    runs-on: ubuntu-latest
    needs: test
    if: github.event_name == 'push'
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3
      
      - name: Login to Registry
        uses: docker/login-action@v3
        with:
          registry: ${{ env.REGISTRY }}
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}
      
      - name: Extract Metadata
        id: meta
        uses: docker/metadata-action@v5
        with:
          images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
          tags: |
            type=ref,event=branch
            type=semver,pattern={{version}}
            type=semver,pattern={{major}}.{{minor}}
            type=sha,prefix={{branch}}-
      
      - name: Build and Push
        uses: docker/build-push-action@v5
        with:
          context: .
          push: true
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=registry,ref=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:buildcache
          cache-to: type=registry,ref=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:buildcache,mode=max

  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  # 阶段4: 部署到生产环境
  # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  deploy:
    name: Deploy to Production
    runs-on: ubuntu-latest
    needs: build
    if: startsWith(github.ref, 'refs/tags/v')
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Configure kubectl
        uses: azure/k8s-set-context@v3
        with:
          method: kubeconfig
          kubeconfig: ${{ secrets.KUBE_CONFIG }}
      
      - name: Deploy to K8s
        run: |
          kubectl set image deployment/myapp \
            myapp=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.ref_name }} \
            -n myapp-prod
          
          kubectl rollout status deployment/myapp -n myapp-prod
      
      - name: Run Smoke Tests
        run: |
          kubectl run smoke-test --rm -i --restart=Never --image=curlimages/curl:latest \
            -- curl -f https://api.myapp.com/health
      
      - name: Notify Slack
        uses: 8398a7/action-slack@v3
        with:
          status: ${{ job.status }}
          text: 'Deployment completed: ${{ github.ref_name }}'
          webhook_url: ${{ secrets.SLACK_WEBHOOK }}
        if: always()
```

---

## 配置管理

### 1. 分层配置系统

**配置结构：**

```text
config/
├── default.toml        # 默认配置
├── development.toml    # 开发环境
├── staging.toml        # 预发布环境
└── production.toml     # 生产环境
```

**default.toml:**

```toml
[server]
host = "0.0.0.0"
port = 8080
workers = 4

[database]
max_connections = 10
min_connections = 2
timeout = 30

[cache]
ttl = 3600
max_size = 1000

[logging]
level = "info"
format = "json"
```

**production.toml:**

```toml
[server]
workers = 16

[database]
max_connections = 50
min_connections = 10
timeout = 60

[logging]
level = "warn"
```

### 2. Rust 配置加载代码

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;
use std::env;

#[derive(Debug, Deserialize)]
pub struct Settings {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub cache: CacheConfig,
    pub logging: LoggingConfig,
}

#[derive(Debug, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
}

#[derive(Debug, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
    pub timeout: u64,
}

##derive(Debug, Deserialize)]
pub struct CacheConfig {
    pub ttl: u64,
    pub max_size: usize,
}

#[derive(Debug, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String,
}

impl Settings {
    pub fn new() -> Result<Self, ConfigError> {
        // 1. 获取运行环境
        let env = env::var("APP_ENV").unwrap_or_else(|_| "development".into());
        
        // 2. 构建配置
        let config = Config::builder()
            // 默认配置
            .add_source(File::with_name("config/default"))
            // 环境特定配置
            .add_source(File::with_name(&format!("config/{}", env)).required(false))
            // 本地配置 (不提交到 Git)
            .add_source(File::with_name("config/local").required(false))
            // 环境变量覆盖 (APP__SERVER__PORT=8080)
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?;
        
        // 3. 反序列化
        config.try_deserialize()
    }
}

// 使用示例
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let settings = Settings::new()?;
    
    println!("Server: {}:{}", settings.server.host, settings.server.port);
    println!("Database: {}", settings.database.url);
    
    Ok(())
}
```

**环境变量优先级：**

```bash
# 1. 文件配置 (最低优先级)
config/default.toml → config/production.toml

# 2. 本地文件 (开发者个人配置)
config/local.toml

# 3. 环境变量 (最高优先级)
export APP__SERVER__PORT=9000
export APP__DATABASE__MAX_CONNECTIONS=100
```

---

## 日志与监控

### 1. 结构化日志 (tracing)

```rust
use tracing::{info, error, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

// 初始化日志
pub fn init_logging() {
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(
            tracing_subscriber::fmt::layer()
                .json() // 生产环境使用 JSON
                .with_target(true)
                .with_current_span(true)
                .with_thread_ids(true)
        )
        .init();
}

// 使用 #[instrument] 自动记录函数调用
#[instrument(skip(db), fields(user_id = %user_id))]
async fn get_user(db: &PgPool, user_id: i64) -> Result<User, Error> {
    info!("Fetching user");
    
    let user = sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", user_id)
        .fetch_one(db)
        .await
        .map_err(|e| {
            error!("Failed to fetch user: {:?}", e);
            Error::DatabaseError(e)
        })?;
    
    info!(username = %user.username, "User found");
    Ok(user)
}
```

**JSON 日志输出示例：**

```json
{
  "timestamp": "2025-10-20T12:34:56.789Z",
  "level": "INFO",
  "target": "myapp::handlers",
  "span": {
    "user_id": 123,
    "name": "get_user"
  },
  "fields": {
    "message": "User found",
    "username": "alice"
  },
  "thread_id": "tokio-runtime-worker-1"
}
```

### 2. Prometheus 监控

```rust
use axum::{
    routing::get,
    Router,
};
use metrics::{counter, histogram, gauge};
use metrics_exporter_prometheus::{Matcher, PrometheusBuilder, PrometheusHandle};
use std::time::Instant;

// 初始化 Prometheus
fn setup_metrics() -> PrometheusHandle {
    PrometheusBuilder::new()
        .set_buckets_for_metric(
            Matcher::Full("http_request_duration_seconds".to_string()),
            &[0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0],
        )
        .unwrap()
        .install_recorder()
        .unwrap()
}

// 中间件：记录请求指标
async fn metrics_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let path = req.uri().path().to_string();
    
    // 请求计数
    counter!("http_requests_total", "method" => method.as_str(), "path" => &path).increment(1);
    
    // 执行请求
    let response = next.run(req).await;
    
    // 记录延迟
    let latency = start.elapsed().as_secs_f64();
    histogram!("http_request_duration_seconds", "method" => method.as_str(), "path" => &path).record(latency);
    
    // 记录状态码
    let status = response.status().as_u16().to_string();
    counter!("http_responses_total", "status" => &status).increment(1);
    
    response
}

// 业务指标
async fn process_order(order: Order) -> Result<(), Error> {
    // 活跃订单数
    gauge!("active_orders").increment(1.0);
    
    // 处理逻辑
    let result = do_process(order).await;
    
    gauge!("active_orders").decrement(1.0);
    
    if result.is_ok() {
        counter!("orders_processed_total", "status" => "success").increment(1);
    } else {
        counter!("orders_processed_total", "status" => "error").increment(1);
    }
    
    result
}

// /metrics 端点
async fn metrics_handler(handle: PrometheusHandle) -> String {
    handle.render()
}

#[tokio::main]
async fn main() {
    let prometheus_handle = setup_metrics();
    
    let app = Router::new()
        .route("/metrics", get(move || metrics_handler(prometheus_handle.clone())))
        .layer(axum::middleware::from_fn(metrics_middleware));
    
    // ...
}
```

**Prometheus 配置 (prometheus.yml):**

```yaml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'myapp'
    static_configs:
      - targets: ['myapp:8080']
    metrics_path: '/metrics'
```

### 3. Grafana 仪表板

**关键指标：**

1. **请求速率 (RPS)**

   ```promql
   rate(http_requests_total[5m])
   ```

2. **错误率**

   ```promql
   rate(http_responses_total{status=~"5.."}[5m]) /
   rate(http_responses_total[5m])
   ```

3. **P50/P95/P99 延迟**

   ```promql
   histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))
   ```

4. **数据库连接池**

   ```promql
   db_connections_active
   db_connections_idle
   ```

---

## 性能优化

### 1. 编译优化

**Cargo.toml:**

```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
strip = true
```

**效果对比：**

| 配置 | 二进制大小 | 启动时间 | QPS |
|------|------------|----------|-----|
| **默认 debug** | 120MB | 500ms | 5,000 |
| **release** | 15MB | 200ms | 15,000 |
| **release + LTO** | 12MB | 150ms | 18,000 |
| **release + LTO + strip** | **8MB** | **100ms** | **20,000** |

### 2. 运行时优化

**Tokio 调优：**

```rust
#[tokio::main(flavor = "multi_thread", worker_threads = 16)]
async fn main() {
    // 使用 16 个工作线程
}

// 或者使用环境变量
TOKIO_WORKER_THREADS=16 ./myapp
```

**数据库连接池调优：**

```rust
let pool = PgPoolOptions::new()
    .max_connections(50)          // 最大连接数
    .min_connections(10)          // 最小连接数
    .acquire_timeout(Duration::from_secs(30))
    .idle_timeout(Duration::from_secs(600))
    .max_lifetime(Duration::from_secs(1800))
    .connect(&database_url)
    .await?;
```

**内存优化：**

```rust
// 使用 jemalloc (更好的内存分配器)
#[global_allocator]
static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;

// 或使用 mimalloc
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
```

---

## 安全加固

### 1. HTTPS/TLS 配置

**Axum + rustls:**

```rust
use axum_server::tls_rustls::RustlsConfig;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }));
    
    // TLS 配置
    let config = RustlsConfig::from_pem_file(
        "cert.pem",
        "key.pem",
    )
    .await?;
    
    let addr = SocketAddr::from(([0, 0, 0, 0], 443));
    
    axum_server::bind_rustls(addr, config)
        .serve(app.into_make_service())
        .await?;
    
    Ok(())
}
```

### 2. 安全头部

```rust
use tower_http::set_header::SetResponseHeaderLayer;
use http::header;

let app = Router::new()
    .route("/", get(handler))
    .layer(SetResponseHeaderLayer::if_not_present(
        header::STRICT_TRANSPORT_SECURITY,
        HeaderValue::from_static("max-age=31536000; includeSubDomains"),
    ))
    .layer(SetResponseHeaderLayer::if_not_present(
        header::X_CONTENT_TYPE_OPTIONS,
        HeaderValue::from_static("nosniff"),
    ))
    .layer(SetResponseHeaderLayer::if_not_present(
        header::X_FRAME_OPTIONS,
        HeaderValue::from_static("DENY"),
    ))
    .layer(SetResponseHeaderLayer::if_not_present(
        HeaderValue::from_static("Content-Security-Policy"),
        HeaderValue::from_static("default-src 'self'"),
    ));
```

### 3. 速率限制

```rust
use tower_governor::{Governor, GovernorConfigBuilder};

#[tokio::main]
async fn main() {
    // 每分钟 60 个请求
    let governor_conf = Box::new(
        GovernorConfigBuilder::default()
            .per_second(1)
            .burst_size(5)
            .finish()
            .unwrap(),
    );
    
    let app = Router::new()
        .route("/api/v1/users", get(list_users))
        .layer(Governor::new(&governor_conf));
    
    // ...
}
```

---

## 灾难恢复

### 1. 数据库备份

**自动备份脚本 (backup.sh):**

```bash
#!/bin/bash

# 配置
DB_HOST="localhost"
DB_PORT="5432"
DB_NAME="myapp"
DB_USER="postgres"
BACKUP_DIR="/backups"
RETENTION_DAYS=7

# 创建备份
BACKUP_FILE="$BACKUP_DIR/myapp_$(date +%Y%m%d_%H%M%S).sql.gz"
pg_dump -h $DB_HOST -p $DB_PORT -U $DB_USER $DB_NAME | gzip > $BACKUP_FILE

# 上传到 S3
aws s3 cp $BACKUP_FILE s3://my-backups/postgres/

# 清理旧备份
find $BACKUP_DIR -name "*.sql.gz" -mtime +$RETENTION_DAYS -delete

echo "Backup completed: $BACKUP_FILE"
```

**Kubernetes CronJob:**

```yaml
apiVersion: batch/v1
kind: CronJob
metadata:
  name: db-backup
  namespace: myapp-prod
spec:
  schedule: "0 2 * * *"  # 每天凌晨 2:00
  jobTemplate:
    spec:
      template:
        spec:
          containers:
          - name: backup
            image: postgres:16-alpine
            command:
            - /bin/sh
            - -c
            - |
              pg_dump -h $DB_HOST -U $DB_USER $DB_NAME | gzip > /tmp/backup.sql.gz
              aws s3 cp /tmp/backup.sql.gz s3://my-backups/postgres/backup_$(date +%Y%m%d).sql.gz
            env:
            - name: DB_HOST
              value: "postgres.myapp-prod.svc.cluster.local"
            - name: DB_USER
              value: "postgres"
            - name: DB_NAME
              value: "myapp"
            - name: PGPASSWORD
              valueFrom:
                secretKeyRef:
                  name: db-secrets
                  key: password
          restartPolicy: OnFailure
```

### 2. 恢复流程

**从备份恢复：**

```bash
# 1. 下载备份
aws s3 cp s3://my-backups/postgres/backup_20251020.sql.gz /tmp/

# 2. 恢复数据库
gunzip < /tmp/backup_20251020.sql.gz | psql -h localhost -U postgres -d myapp

# 3. 验证数据
psql -h localhost -U postgres -d myapp -c "SELECT COUNT(*) FROM users;"
```

---

## 故障排查

### 1. 常见问题

#### 问题1: Pod 无法启动

**症状：**

```bash
kubectl get pods -n myapp-prod
NAME                     READY   STATUS             RESTARTS   AGE
myapp-7d9f8b5c4-abc123   0/1     CrashLoopBackOff   5          5m
```

**排查步骤：**

```bash
# 1. 查看 Pod 日志
kubectl logs myapp-7d9f8b5c4-abc123 -n myapp-prod

# 2. 查看事件
kubectl describe pod myapp-7d9f8b5c4-abc123 -n myapp-prod

# 3. 进入容器调试
kubectl exec -it myapp-7d9f8b5c4-abc123 -n myapp-prod -- /bin/sh
```

**常见原因：**

- ❌ 配置错误 (环境变量、Secret)
- ❌ 健康检查失败
- ❌ 资源不足 (OOMKilled)
- ❌ 镜像拉取失败

#### 问题2: 性能下降

**症状：** P99 延迟从 100ms 增加到 5秒

**排查步骤：**

```bash
# 1. 查看监控指标
# - CPU/内存使用率
# - 请求速率
# - 数据库连接池

# 2. 查看慢查询日志
# 在 Grafana 中查询：
histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))

# 3. 数据库慢查询
SELECT query, mean_exec_time, calls
FROM pg_stat_statements
ORDER BY mean_exec_time DESC
LIMIT 10;
```

**常见原因：**

- ❌ 数据库连接池耗尽
- ❌ N+1 查询问题
- ❌ 缺少数据库索引
- ❌ 内存泄漏

#### 问题3: 内存泄漏

**排查工具：**

```bash
# 1. 查看内存使用情况
kubectl top pods -n myapp-prod

# 2. 使用 valgrind (本地)
valgrind --leak-check=full ./myapp

# 3. 使用 heaptrack
heaptrack ./myapp
heaptrack_gui heaptrack.myapp.12345.gz
```

---

## 最佳实践

### ✅ 推荐做法

1. **使用多阶段 Dockerfile**

   ```dockerfile
   # ✅ 最小化镜像大小
   FROM rust:1.83 as builder
   FROM debian:bookworm-slim
   ```

2. **启用所有健康检查**

   ```yaml
   # ✅ liveness + readiness + startup
   livenessProbe: ...
   readinessProbe: ...
   startupProbe: ...
   ```

3. **使用结构化日志**

   ```rust
   // ✅ JSON 格式，便于查询
   tracing_subscriber::fmt::layer().json()
   ```

4. **配置资源限制**

   ```yaml
   # ✅ 防止资源耗尽
   resources:
     requests: { cpu: 100m, memory: 128Mi }
     limits: { cpu: 500m, memory: 512Mi }
   ```

5. **实施速率限制**

   ```rust
   // ✅ 防止滥用
   .layer(Governor::new(&governor_conf))
   ```

6. **定期备份数据**

   ```yaml
   # ✅ 每天自动备份
   schedule: "0 2 * * *"
   ```

7. **使用 Secrets 管理敏感信息**

   ```yaml
   # ✅ 不在代码中硬编码
   envFrom:
   - secretRef:
       name: myapp-secrets
   ```

8. **启用 HTTPS/TLS**

   ```rust
   // ✅ 加密传输
   RustlsConfig::from_pem_file("cert.pem", "key.pem")
   ```

9. **实施 CI/CD 自动化**

   ```yaml
   # ✅ 自动测试 + 自动部署
   on: push: branches: [main]
   ```

10. **监控所有关键指标**

    ```promql
    # ✅ RPS, 错误率, 延迟, 资源使用
    rate(http_requests_total[5m])
    ```

---

## 常见陷阱

### ❌ 避免的错误

1. **使用 debug 镜像部署**

   ```dockerfile
   # ❌ 120MB, 慢
   FROM rust:1.83
   
   # ✅ 8MB, 快
   FROM debian:bookworm-slim
   ```

2. **没有健康检查**

   ```yaml
   # ❌ 无法检测服务状态
   # (没有 livenessProbe/readinessProbe)
   
   # ✅ 自动重启失败的 Pod
   livenessProbe: { httpGet: { path: /health, port: 8080 } }
   ```

3. **硬编码配置**

   ```rust
   // ❌ 无法动态修改
   let db_url = "postgres://localhost/myapp";
   
   // ✅ 从环境变量读取
   let db_url = env::var("DATABASE_URL")?;
   ```

4. **忽略错误日志**

   ```rust
   // ❌ 错误被吞掉
   let _ = process().await;
   
   // ✅ 记录错误
   if let Err(e) = process().await {
       error!("Process failed: {:?}", e);
   }
   ```

5. **没有资源限制**

   ```yaml
   # ❌ 可能占满节点资源
   # (没有 resources.limits)
   
   # ✅ 限制资源使用
   resources:
     limits: { cpu: 500m, memory: 512Mi }
   ```

6. **没有备份策略**

   ```bash
   # ❌ 数据丢失无法恢复
   
   # ✅ 定期自动备份
   0 2 * * * /scripts/backup.sh
   ```

7. **使用 HTTP 而非 HTTPS**

   ```rust
   // ❌ 明文传输，不安全
   .bind("0.0.0.0:80")
   
   // ✅ HTTPS 加密
   axum_server::bind_rustls(addr, tls_config)
   ```

8. **没有监控告警**

   ```yaml
   # ❌ 故障时无人知晓
   
   # ✅ 设置告警规则
   - alert: HighErrorRate
     expr: rate(http_responses_total{status=~"5.."}[5m]) > 0.05
   ```

9. **忽略安全审计**

   ```bash
   # ❌ 使用有漏洞的依赖
   
   # ✅ 定期审计
   cargo audit
   cargo deny check advisories
   ```

10. **没有滚动更新策略**

    ```yaml
    # ❌ 停机部署
    type: Recreate
    
    # ✅ 零停机部署
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 0
      maxSurge: 1
    ```

---

## 参考资源

### 官方文档

- [Kubernetes 官方文档](https://kubernetes.io/docs/)
- [Docker 官方文档](https://docs.docker.com/)
- [Tokio 文档](https://tokio.rs/)
- [Axum 文档](https://docs.rs/axum/)

### 工具

- [Helm](https://helm.sh/) - Kubernetes 包管理器
- [Kustomize](https://kustomize.io/) - K8s 配置管理
- [Tilt](https://tilt.dev/) - 本地 K8s 开发
- [Skaffold](https://skaffold.dev/) - CI/CD 工具

### 监控生态

- [Prometheus](https://prometheus.io/) - 指标监控
- [Grafana](https://grafana.com/) - 可视化
- [Jaeger](https://www.jaegertracing.io/) - 分布式追踪
- [Loki](https://grafana.com/oss/loki/) - 日志聚合

### 最佳实践1

- [12-Factor App](https://12factor.net/) - 现代应用构建原则
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Google SRE Book](https://sre.google/sre-book/table-of-contents/)

---

## 总结

生产部署的**关键成功要素**：

1. ✅ **容器化**：使用多阶段 Dockerfile，镜像 < 100MB
2. ✅ **编排**：Kubernetes + HPA 自动扩展
3. ✅ **CI/CD**：GitHub Actions 全自动部署
4. ✅ **配置**：分层配置 + 环境变量
5. ✅ **监控**：Prometheus + Grafana + Jaeger
6. ✅ **日志**：结构化 JSON 日志
7. ✅ **安全**：HTTPS + 速率限制 + 审计
8. ✅ **备份**：每日自动备份 + S3
9. ✅ **性能**：LTO + PGO + 连接池调优
10. ✅ **故障恢复**：健康检查 + 滚动更新 + 回滚

**下一步**：

- 实施蓝绿部署
- 添加 Canary 发布
- 集成 Service Mesh (Istio)
- 实施 Chaos Engineering

🚀 **现在你已经掌握了 Rust 生产部署的完整知识体系！**
