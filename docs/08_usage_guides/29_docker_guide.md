# Docker 使用指南 {#docker-使用指南}

> **EN**: Docker Guide
> **Summary**: Docker 使用指南 Docker Guide.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L2-L3

本文档介绍如何使用 Docker 和 Docker Compose 构建和运行本项目。

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Docker 使用指南 {#docker-使用指南}](#docker-使用指南-docker-使用指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [前置要求 {#前置要求}](#前置要求-前置要求)
  - [快速开始 {#快速开始}](#快速开始-快速开始)
    - [构建镜像 {#构建镜像}](#构建镜像-构建镜像)
    - [运行容器 {#运行容器}](#运行容器-运行容器)
    - [使用 Docker Compose {#使用-docker-compose}](#使用-docker-compose-使用-docker-compose)
  - [多阶段构建 {#多阶段构建}](#多阶段构建-多阶段构建)
  - [Docker Compose 配置 {#docker-compose-配置}](#docker-compose-配置-docker-compose-配置)
    - [生产环境 {#生产环境}](#生产环境-生产环境)
    - [开发环境（热重载） {#开发环境热重载}](#开发环境热重载-开发环境热重载)
  - [卷挂载 {#卷挂载}](#卷挂载-卷挂载)
  - [环境变量 {#环境变量}](#环境变量-环境变量)
  - [常用命令 {#常用命令}](#常用命令-常用命令)
  - [故障排除 {#故障排除}](#故障排除-故障排除)
    - [权限问题 {#权限问题}](#权限问题-权限问题)
    - [编译缓慢 {#编译缓慢}](#编译缓慢-编译缓慢)
    - [端口冲突 {#端口冲突}](#端口冲突-端口冲突)
  - [参考 {#参考}](#参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 前置要求 {#前置要求}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [Docker](https://docs.docker.com/get-docker/)
- [Docker Compose](https://docs.docker.com/compose/install/)

## 快速开始 {#快速开始}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 构建镜像 {#构建镜像}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```bash
docker build -t rust-lang .
```

### 运行容器 {#运行容器}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
docker run -it --rm rust-lang
```

### 使用 Docker Compose {#使用-docker-compose}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```bash
# 构建并启动服务 {#构建并启动服务}
docker-compose up --build

# 后台运行 {#后台运行}
docker-compose up -d

# 停止服务 {#停止服务}
docker-compose down
```

## 多阶段构建 {#多阶段构建}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

Dockerfile 使用多阶段构建优化镜像大小:

1. **Builder 阶段**: 使用 `rust:1.96-slim` 编译项目
2. **Runtime 阶段**: 使用精简的 `debian:bookworm-slim` 运行

## Docker Compose 配置 {#docker-compose-配置}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 生产环境 {#生产环境}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bash
docker-compose up rust-lang
```

### 开发环境（热重载） {#开发环境热重载}
>
> **[来源: [crates.io](https://crates.io/)]**

```bash
docker-compose --profile dev up rust-lang-dev
```

开发模式使用 `cargo-watch` 监视文件变化并自动重新编译。

## 卷挂载 {#卷挂载}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- `./:/app` - 源代码挂载
- `cargo-cache` - Cargo 依赖缓存
- `target-cache` - 编译目标缓存（仅开发模式）

## 环境变量 {#环境变量}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

在 `docker-compose.yml` 中配置:

| 变量 | 说明 | 默认值 |
|------|------|--------|
| `RUST_LOG` | 日志级别 | `info` |

## 常用命令 {#常用命令}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
# 查看日志 {#查看日志}
docker-compose logs -f

# 进入容器 shell {#进入容器-shell}
docker-compose exec rust-lang /bin/bash

# 清理缓存卷 {#清理缓存卷}
docker-compose down -v

# 重新构建 {#重新构建}
docker-compose build --no-cache
```

## 故障排除 {#故障排除}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 权限问题 {#权限问题}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

如果遇到文件权限问题，确保宿主机用户有正确的权限:

```bash
# Linux/macOS {#linuxmacos}
sudo chown -R $(id -u):$(id -g) .
```

### 编译缓慢 {#编译缓慢}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

首次构建会下载依赖，可能较慢。后续构建会利用缓存加速。

### 端口冲突 {#端口冲突}

如果 8080 端口被占用，修改 `docker-compose.yml` 中的端口映射。

## 参考 {#参考}

- [Docker 文档](https://docs.docker.com/)
- [Docker Compose 文档](https://docs.docker.com/compose/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念 {#相关概念}

- [docs 目录](README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
