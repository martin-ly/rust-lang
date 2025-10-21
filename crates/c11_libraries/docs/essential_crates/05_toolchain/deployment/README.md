# Deployment - 部署工具

## 📋 目录

- [Deployment - 部署工具](#deployment---部署工具)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [容器化](#容器化)
    - [Dockerfile](#dockerfile)
    - [优化的 Dockerfile](#优化的-dockerfile)
  - [发布工具](#发布工具)
    - [cargo-dist](#cargo-dist)
    - [cargo-release](#cargo-release)
  - [Kubernetes](#kubernetes)
    - [部署配置](#部署配置)
  - [参考资源](#参考资源)

---

## 概述

Rust 应用的部署工具和最佳实践。

---

## 容器化

### Dockerfile

```dockerfile
# 多阶段构建
FROM rust:1.75 as builder
WORKDIR /app

COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

# 最小运行时镜像
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-app /usr/local/bin/

CMD ["my-app"]
```

### 优化的 Dockerfile

```dockerfile
FROM rust:1.75 as builder
WORKDIR /app

# 缓存依赖
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# 构建应用
COPY src ./src
RUN touch src/main.rs
RUN cargo build --release

FROM gcr.io/distroless/cc-debian12
COPY --from=builder /app/target/release/my-app /
CMD ["/my-app"]
```

---

## 发布工具

### cargo-dist

```bash
# 安装
cargo install cargo-dist

# 初始化
cargo dist init

# 构建发布包
cargo dist build

# 生成发布计划
cargo dist plan
```

### cargo-release

```bash
# 安装
cargo install cargo-release

# 发布新版本
cargo release patch  # 0.1.0 -> 0.1.1
cargo release minor  # 0.1.0 -> 0.2.0
cargo release major  # 0.1.0 -> 1.0.0
```

---

## Kubernetes

### 部署配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: rust-app
        image: myregistry/rust-app:latest
        ports:
        - containerPort: 8080
        resources:
          requests:
            memory: "64Mi"
            cpu: "250m"
          limits:
            memory: "128Mi"
            cpu: "500m"
```

---

## 参考资源

- [cargo-dist 文档](https://opensource.axo.dev/cargo-dist/)
- [Docker 最佳实践](https://docs.docker.com/develop/dev-best-practices/)
