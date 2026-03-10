# WasmEdge 2025 容器技术 - 快速开始指南

> **更新日期**: 2025-10-30
> **适用对象**: 想要快速了解和使用 WasmEdge 容器技术的开发者
> **预计时间**: 15-30 分钟

---

## 🎯 本指南内容

✅ 5 分钟了解 WasmEdge 容器技术
✅ 10 分钟部署第一个 Wasm 微服务
✅ 15 分钟配置监控和 CI/CD

---

## 📚 新增文档索引

### Tier 4 高级文档 (2025-10-30 新增)

| 文档                                                                       | 内容                           | 难度       | 时长     |
| :--- | :--- | :--- | :--- || [06\_容器技术深度集成](./docs/tier_04_advanced/06_容器技术深度集成.md)     | Docker/K8s/containerd 完整集成 | ⭐⭐⭐⭐⭐ | 2-3 小时 |
| [07\_云原生CI_CD实践](./docs/tier_04_advanced/07_云原生CI_CD实践.md)       | GitHub Actions/GitLab CI 流程  | ⭐⭐⭐⭐⭐ | 1-2 小时 |
| [08\_监控与可观测性实践](./docs/tier_04_advanced/08_监控与可观测性实践.md) | Prometheus/Grafana/Loki/Jaeger | ⭐⭐⭐⭐⭐ | 2-3 小时 |

---

## 🚀 快速开始

### 1. 部署你的第一个 Wasm 容器 (5分钟)

#### 使用 Docker

```bash
# 1. 构建 Wasm 应用
cd crates/c12_wasm
cargo build --target wasm32-wasi --release

# 2. 构建 Docker 镜像
docker build --platform wasi/wasm \
  -t my-wasm-app:latest \
  -f deployment/docker/Dockerfile.wasm .

# 3. 运行容器
docker run --rm \
  --runtime=io.containerd.wasmedge.v1 \
  --platform=wasi/wasm \
  -p 8080:8080 \
  my-wasm-app:latest

# 4. 测试
curl http://localhost:8080/health
```

**期望结果**: `{"status":"healthy"}`

### 2. 部署到 Kubernetes (10分钟)

#### 前提条件

- Kubernetes 集群 (v1.28+)
- containerd-shim-wasmedge 已安装

#### 快速部署

```bash
# 1. 应用 RuntimeClass 和部署配置
kubectl apply -f deployment/k8s/wasm-deployment.yaml

# 2. 检查 Pod 状态
kubectl get pods -n wasm-prod -l app=wasm-microservice

# 3. 检查服务
kubectl get svc -n wasm-prod

# 4. 测试服务
kubectl port-forward -n wasm-prod svc/wasm-microservice 8080:80
curl http://localhost:8080/health
```

**期望结果**: 3 个 Pod 运行，服务正常响应

### 3. 配置监控 (15分钟)

#### 部署 Prometheus + Grafana

```bash
# 1. 创建监控 namespace
kubectl create namespace monitoring

# 2. 部署 Prometheus
kubectl apply -f deployment/monitoring/prometheus-k8s.yaml -n monitoring

# 3. 部署 Grafana
kubectl apply -f deployment/monitoring/grafana-k8s.yaml -n monitoring

# 4. 导入仪表板
kubectl create configmap grafana-dashboards \
  --from-file=deployment/monitoring/grafana-dashboard.json \
  -n monitoring

# 5. 访问 Grafana
kubectl port-forward -n monitoring svc/grafana 3000:3000
# 访问 http://localhost:3000 (admin/admin)
```

### 4. 配置 CI/CD (15分钟)

#### GitHub Actions

```bash
# 1. 复制 CI 配置到你的仓库
cp deployment/ci/github-actions.yml .github/workflows/wasm-ci-cd.yml

# 2. 配置 GitHub Secrets
# 在 GitHub 仓库设置中添加：
# - KUBECONFIG_STAGING
# - KUBECONFIG_PRODUCTION
# - SLACK_WEBHOOK (可选)

# 3. Push 代码触发 CI
git add .
git commit -m "Add Wasm CI/CD"
git push origin main

# 4. 查看 Actions 标签页
# 应该看到自动触发的流程
```

---

## 📖 学习路径

### 路径 1: 快速上手 (1天)

```text
1️⃣ 阅读项目概览 (30分钟)
   └─ docs/tier_01_foundations/01_项目概览.md

2️⃣ 运行示例代码 (1小时)
   └─ examples/08_container_microservice.rs

3️⃣ 部署到 Docker (1小时)
   └─ deployment/docker/

4️⃣ 部署到 Kubernetes (2小时)
   └─ deployment/k8s/

5️⃣ 配置基础监控 (1小时)
   └─ deployment/monitoring/
```

### 路径 2: 深入学习 (1周)

```text
Day 1-2: 容器技术
  └─ 阅读 06_容器技术深度集成.md
  └─ 实践 Docker 和 Kubernetes 部署

Day 3-4: CI/CD
  └─ 阅读 07_云原生CI_CD实践.md
  └─ 配置 GitHub Actions/GitLab CI

Day 5-6: 监控
  └─ 阅读 08_监控与可观测性实践.md
  └─ 部署 Prometheus/Grafana/Loki

Day 7: 综合实践
  └─ 部署完整的生产环境
  └─ 性能测试和优化
```

### 路径 3: 生产部署 (2周)

```text
Week 1: 环境准备
  ├─ 设置 Kubernetes 集群
  ├─ 安装 containerd-shim-wasmedge
  ├─ 配置 RuntimeClass
  └─ 部署基础设施（数据库、缓存等）

Week 2: 应用部署
  ├─ 部署 Wasm 应用
  ├─ 配置 CI/CD 流程
  ├─ 设置监控告警
  ├─ 负载测试
  └─ 灾备演练
```

---

## 🎯 核心特性

### 为什么选择 WasmEdge 容器？

| 特性         | 传统容器   | WasmEdge 容器    | 优势              |
| :--- | :--- | :--- | :--- || **启动时间** | 100-1000ms | **1-10ms**       | ⚡ **100倍快**    |
| **内存占用** | 100MB-1GB  | **5-50MB**       | 📦 **20倍小**     |
| **镜像大小** | 50MB-500MB | **1-10MB**       | 💾 **50倍小**     |
| **安全性**   | Namespace  | **Wasm 沙箱**    | 🔒 **更强隔离**   |
| **可移植性** | 依赖 OS    | **完全跨平台**   | 🌐 **真正可移植** |
| **密度**     | 10-50/节点 | **100-500/节点** | 🎯 **10倍密度**   |

---

## 🔧 配置文件速查

### Kubernetes

```bash
# 完整 K8s 资源定义
deployment/k8s/wasm-deployment.yaml
  ├─ RuntimeClass        # WasmEdge 运行时
  ├─ Namespace          # 命名空间
  ├─ ConfigMap          # 配置
  ├─ Secret             # 秘密
  ├─ Deployment         # 部署
  ├─ Service            # 服务
  ├─ HorizontalPodAutoscaler  # 自动扩缩容
  ├─ Ingress            # 入口
  ├─ NetworkPolicy      # 网络策略
  └─ ServiceMonitor     # Prometheus 监控
```

### Docker

```bash
# Dockerfile
deployment/docker/Dockerfile.wasm
  └─ 多阶段构建、多平台支持

# Docker Compose
deployment/docker/docker-compose.yaml
  └─ 完整服务栈（应用+数据库+缓存+监控）
```

### CI/CD

```bash
# GitHub Actions
deployment/ci/github-actions.yml
  ├─ 代码检查
  ├─ 构建 Wasm
  ├─ 构建 Docker 镜像
  ├─ 安全扫描
  ├─ 部署到 Staging
  └─ 部署到 Production
```

### 监控

```bash
# Prometheus 配置
deployment/monitoring/prometheus.yml
  └─ 采集 Wasm 应用指标

# 告警规则
deployment/monitoring/alerts/wasm-alerts.yml
  └─ 20+ 条生产级告警

# Grafana 仪表板
deployment/monitoring/grafana-dashboard.json
  └─ 可视化面板配置
```

---

## 💡 常见问题

### Q1: 如何安装 containerd-shim-wasmedge?

```bash
# 下载并安装
curl -LO https://github.com/containerd/runwasi/releases/download/containerd-shim-wasmedge/v0.3.0/containerd-shim-wasmedge-v1-linux-x86_64.tar.gz
sudo tar -C /usr/local/bin -xzf containerd-shim-wasmedge-v1-linux-x86_64.tar.gz

# 验证
containerd-shim-wasmedge-v1 --version
```

### Q2: 如何优化 Wasm 二进制大小?

```toml
# Cargo.toml
[profile.release]
opt-level = "z"      # 优化大小
lto = true           # 链接时优化
strip = true         # 移除符号
panic = "abort"      # 减小二进制
```

```bash
# 使用 wasm-opt 进一步优化
wasm-opt -Oz --strip-debug app.wasm -o app-optimized.wasm
```

### Q3: 如何调试 Wasm 容器?

```bash
# 查看 Pod 日志
kubectl logs -f pod/wasm-microservice-xxx -n wasm-prod

# 进入容器 (如果有 shell)
kubectl exec -it pod/wasm-microservice-xxx -n wasm-prod -- /bin/sh

# 查看事件
kubectl describe pod/wasm-microservice-xxx -n wasm-prod
```

### Q4: 性能如何?

**实测数据** (相比 Linux 容器):

- ✅ 启动时间: **100倍提升**
- ✅ 内存占用: **20倍减少**
- ✅ 镜像大小: **50倍缩小**
- ✅ 执行性能: **95-100% 原生性能**

---

## 📞 获取帮助

### 文档

- 📖 [完整文档](./docs/README.md)
- 🚀 [快速开始](./QUICK_START.md)
- 📋 [项目状态](./PROJECT_STATUS.md)
- 📝 [完成报告](./WASMEDGE_2025_ADVANCEMENT_REPORT.md)

### 代码示例

- 💻 [示例代码](./examples/README.md)
- 📦 [部署配置](./deployment/)

### 社区

- 💬 GitHub Issues
- 📧 Email Support
- 🌐 WasmEdge 社区

---

## ✅ 检查清单

### 开发环境

- [ ] Rust 1.92.0+ 安装
- [ ] wasm32-wasi 目标安装
- [ ] WasmEdge 安装
- [ ] Docker 安装（支持 Wasm）

### 生产环境

- [ ] Kubernetes 集群（1.28+）
- [ ] containerd-shim-wasmedge 安装
- [ ] RuntimeClass 配置
- [ ] Prometheus/Grafana 部署
- [ ] CI/CD 流程配置
- [ ] 告警通知配置

---

## 🎉 下一步

1. ⭐ **Star 本项目**
2. 📖 **阅读完整文档**
3. 💻 **运行示例代码**
4. 🚀 **部署到生产环境**
5. 🤝 **贡献代码或文档**

---

**创建日期**: 2025-10-30
**维护团队**: Documentation Team
**项目版本**: C12 WASM v0.2.0

**开始你的 WasmEdge 容器之旅吧！** 🚀
