# 部署指南

本文档介绍如何将本项目部署到不同环境。

## 目录

- [Docker 部署](#docker-部署)
- [Kubernetes 部署](#kubernetes-部署)
- [Nix 部署](#nix-部署)

## Docker 部署

### 单机部署

```bash
# 构建镜像
docker build -t rust-lang:latest .

# 运行容器
docker run -d -p 8080:8080 --name rust-lang rust-lang:latest
```

### 使用 Docker Compose

```bash
# 启动所有服务
docker-compose up -d

# 查看状态
docker-compose ps
```

更多详情参见 [DOCKER_GUIDE.md](./DOCKER_GUIDE.md)

## Kubernetes 部署

### 前置要求

- Kubernetes 集群 (1.20+)
- kubectl 已配置

### 部署步骤

1. **应用 ConfigMap**
   ```bash
   kubectl apply -f k8s/configmap.yaml
   ```

2. **部署应用**
   ```bash
   kubectl apply -f k8s/deployment.yaml
   ```

3. **创建 Service**
   ```bash
   kubectl apply -f k8s/service.yaml
   ```

4. **验证部署**
   ```bash
   kubectl get pods -l app=rust-lang
   kubectl get svc rust-lang-service
   ```

### 扩展副本

```bash
kubectl scale deployment rust-lang-deployment --replicas=5
```

### 更新镜像

```bash
kubectl set image deployment/rust-lang-deployment rust-lang=rust-lang:v2.0
```

### 查看日志

```bash
kubectl logs -f deployment/rust-lang-deployment
```

## Nix 部署

### 使用 Nix 构建

```bash
nix build
```

### 运行 Nix 开发 Shell

```bash
nix develop
```

更多详情参见 [NIX_SETUP.md](./NIX_SETUP.md)

## 环境配置

### 生产环境变量

| 变量 | 说明 | 必需 |
|------|------|------|
| `RUST_LOG` | 日志级别 | 否 |
| `RUST_BACKTRACE` | 错误回溯 | 否 |
| `APP_ENVIRONMENT` | 运行环境 | 是 |

## 健康检查

应用提供以下端点:

- `/health` - 存活检查
- `/ready` - 就绪检查

## 监控

建议配置:

- **Prometheus**: 指标收集
- **Grafana**: 可视化监控
- **Loki**: 日志聚合

## 安全建议

1. 使用非 root 用户运行容器
2. 定期更新基础镜像
3. 配置资源限制
4. 启用网络策略
5. 使用 Secrets 管理敏感信息

## 参考

- [Docker 官方文档](https://docs.docker.com/)
- [Kubernetes 官方文档](https://kubernetes.io/docs/)
- [Nix 官方文档](https://nixos.org/manual/nix/stable/)
