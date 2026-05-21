# Docker 使用指南

本文档介绍如何使用 Docker 和 Docker Compose 构建和运行本项目。

## 前置要求
> **[来源: Rust Official Docs]**

- [Docker](https://docs.docker.com/get-docker/)
- [Docker Compose](https://docs.docker.com/compose/install/)

## 快速开始
> **[来源: Rust Official Docs]**

### 构建镜像
> **[来源: Rust Official Docs]**

```bash
docker build -t rust-lang .
```

### 运行容器

```bash
docker run -it --rm rust-lang
```

### 使用 Docker Compose

```bash
# 构建并启动服务
docker-compose up --build

# 后台运行
docker-compose up -d

# 停止服务
docker-compose down
```

## 多阶段构建

Dockerfile 使用多阶段构建优化镜像大小:

1. **Builder 阶段**: 使用 `rust:1.96-slim` 编译项目
2. **Runtime 阶段**: 使用精简的 `debian:bookworm-slim` 运行

## Docker Compose 配置

### 生产环境

```bash
docker-compose up rust-lang
```

### 开发环境（热重载）

```bash
docker-compose --profile dev up rust-lang-dev
```

开发模式使用 `cargo-watch` 监视文件变化并自动重新编译。

## 卷挂载

- `./:/app` - 源代码挂载
- `cargo-cache` - Cargo 依赖缓存
- `target-cache` - 编译目标缓存（仅开发模式）

## 环境变量

在 `docker-compose.yml` 中配置:

| 变量 | 说明 | 默认值 |
|------|------|--------|
| `RUST_LOG` | 日志级别 | `info` |

## 常用命令

```bash
# 查看日志
docker-compose logs -f

# 进入容器 shell
docker-compose exec rust-lang /bin/bash

# 清理缓存卷
docker-compose down -v

# 重新构建
docker-compose build --no-cache
```

## 故障排除

### 权限问题

如果遇到文件权限问题，确保宿主机用户有正确的权限:

```bash
# Linux/macOS
sudo chown -R $(id -u):$(id -g) .
```

### 编译缓慢

首次构建会下载依赖，可能较慢。后续构建会利用缓存加速。

### 端口冲突

如果 8080 端口被占用，修改 `docker-compose.yml` 中的端口映射。

## 参考

- [Docker 文档](https://docs.docker.com/)
- [Docker Compose 文档](https://docs.docker.com/compose/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)


---

- [README](./README.md)
