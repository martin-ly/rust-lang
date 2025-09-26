# 🦀 CI/CD自动化配置

**创建时间**: 2025年9月25日
**版本**: 1.0.0

---

## 📋 目录

- [🦀 CI/CD自动化配置](#-cicd自动化配置)
  - [📋 目录](#-目录)
  - [🎯 CI/CD概述](#-cicd概述)
  - [🔧 GitHub Actions配置](#-github-actions配置)
  - [🚀 部署配置](#-部署配置)
  - [📊 监控配置](#-监控配置)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 CI/CD概述

### 自动化目标

1. **持续集成**: 自动构建和测试
2. **持续部署**: 自动部署和发布
3. **质量保证**: 自动质量检查
4. **监控告警**: 自动监控和告警

---

## 🔧 GitHub Actions配置

### 主工作流

```yaml
# .github/workflows/main.yml
name: Main CI/CD Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always

jobs:
  build:
    name: Build
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
        override: true

    - name: Build
      run: cargo build --release

    - name: Upload artifacts
      uses: actions/upload-artifact@v3
      with:
        name: build-artifacts
        path: target/

  test:
    name: Test
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        override: true

    - name: Run tests
      run: cargo test --all

    - name: Run coverage
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Html

  quality:
    name: Quality Check
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
        override: true

    - name: Check formatting
      run: cargo fmt -- --check

    - name: Run clippy
      run: cargo clippy --all -- -D warnings

    - name: Security audit
      run: |
        cargo install cargo-audit
        cargo audit

  deploy:
    name: Deploy
    runs-on: ubuntu-latest
    needs: [build, test, quality]
    if: github.ref == 'refs/heads/main'

    steps:
    - uses: actions/checkout@v3

    - name: Deploy to production
      run: echo "Deploying to production..."
```

### 发布工作流

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    name: Create Release
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        override: true

    - name: Build release
      run: cargo build --release

    - name: Create release
      uses: actions/create-release@v1
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
      with:
        tag_name: ${{ github.ref }}
        release_name: Release ${{ github.ref }}
        body: |
          Release ${{ github.ref }}

          Changes:
          - Bug fixes
          - Performance improvements
          - New features
        draft: false
        prerelease: false
```

---

## 🚀 部署配置

### Docker配置

```dockerfile
# Dockerfile
FROM rust:1.70-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN cargo build --release

COPY src ./src
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates
COPY --from=builder /app/target/release/my_app /usr/local/bin/my_app
EXPOSE 8080
CMD ["my_app"]
```

### 部署脚本

```bash
#!/bin/bash
# scripts/deploy.sh

set -e

echo "Starting deployment..."

# 构建镜像
docker build -t my-app:latest .

# 推送镜像
docker push my-app:latest

# 部署到K8s
kubectl set image deployment/my-app my-app=my-app:latest

# 等待部署完成
kubectl rollout status deployment/my-app

echo "Deployment completed!"
```

---

## 📊 监控配置

### Prometheus配置

```yaml
# monitoring/prometheus.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'my-app'
    static_configs:
      - targets: ['localhost:8080']
    metrics_path: '/metrics'
    scrape_interval: 5s
```

### 告警规则

```yaml
# monitoring/alerts.yml
groups:
  - name: my-app
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.1
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
```

---

## 📝 最佳实践

### 自动化原则

1. **简单性**: 保持配置简单
2. **可靠性**: 确保流程稳定
3. **可维护性**: 易于维护
4. **监控性**: 提供监控

### 检查清单

- [ ] CI/CD配置完整
- [ ] 测试覆盖全面
- [ ] 质量检查完善
- [ ] 部署流程可靠
- [ ] 监控配置有效

---

-**遵循这些CI/CD自动化配置，您将能够建立高效、可靠的持续集成和部署流程！🦀**-
