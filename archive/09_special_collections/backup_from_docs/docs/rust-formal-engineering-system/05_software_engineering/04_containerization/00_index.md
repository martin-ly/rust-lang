# 容器化（Containerization）索引

## 📊 目录

- [容器化（Containerization）索引](#容器化containerization索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [与 Rust 的关联](#与-rust-的关联)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍容器化技术在 Rust 中的应用与实践。
- 提供容器化设计、构建、部署的最佳实践。

## 核心概念

- 容器技术：Docker、Podman、容器运行时
- 容器编排：Kubernetes、Docker Swarm、编排策略
- 镜像构建：多阶段构建、镜像优化、安全扫描
- 容器网络：网络模式、服务发现、负载均衡
- 存储管理：卷管理、持久化存储、存储类
- 配置管理：ConfigMap、Secret、环境变量
- 监控与日志：容器监控、日志收集、健康检查
- 安全策略：镜像安全、运行时安全、网络安全

## 与 Rust 的关联

- 性能优势：高效的容器化应用
- 内存安全：防止容器应用崩溃
- 并发安全：多容器并发处理
- 跨平台：支持多种容器平台

## 术语（Terminology）

- 容器化（Containerization）、容器技术（Container Technology）
- 容器编排（Container Orchestration）、镜像构建（Image Building）
- 容器网络（Container Networking）、存储管理（Storage Management）
- 配置管理（Configuration Management）、监控与日志（Monitoring & Logging）

## 实践与样例

- 容器化实现：参见 [crates/c51_containerization](../../../crates/c51_containerization/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)
- 服务网格：[crates/c50_service_mesh](../../../crates/c50_service_mesh/)

### 文件级清单（精选）

- `crates/c51_containerization/src/`：
  - `docker_integration.rs`：Docker 集成
  - `kubernetes_integration.rs`：Kubernetes 集成
  - `image_building.rs`：镜像构建
  - `container_runtime.rs`：容器运行时
  - `orchestration.rs`：容器编排

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 应用领域（云基础设施）：[`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)

## 导航

- 返回软件工程：[`../00_index.md`](../00_index.md)
- 服务网格：[`../03_service_mesh/00_index.md`](../03_service_mesh/00_index.md)
- DevOps：[`../05_devops/00_index.md`](../05_devops/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
