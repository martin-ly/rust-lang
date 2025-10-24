# c13_reliability - 快速配置参考


## 📊 目录

- [c13\_reliability - 快速配置参考](#c13_reliability---快速配置参考)
  - [📊 目录](#-目录)
  - [🚀 常见配置场景](#-常见配置场景)
    - [1️⃣ 最小配置（仅核心功能）](#1️⃣-最小配置仅核心功能)
    - [2️⃣ Web 应用标准配置](#2️⃣-web-应用标准配置)
    - [3️⃣ 云原生/Kubernetes 部署](#3️⃣-云原生kubernetes-部署)
    - [4️⃣ 高性能生产环境](#4️⃣-高性能生产环境)
    - [5️⃣ 开发环境（带验证工具）](#5️⃣-开发环境带验证工具)
    - [6️⃣ 嵌入式系统](#6️⃣-嵌入式系统)
  - [📋 完整特性列表](#-完整特性列表)
    - [默认启用的特性](#默认启用的特性)
    - [可选特性矩阵](#可选特性矩阵)
  - [🎯 按使用场景选择特性](#-按使用场景选择特性)
    - [Web 开发](#web-开发)
    - [微服务](#微服务)
    - [CLI 工具](#cli-工具)
    - [后台服务](#后台服务)
    - [数据处理](#数据处理)
  - [🔧 依赖获取方式](#-依赖获取方式)
    - [方式 1: 本地路径（开发推荐）](#方式-1-本地路径开发推荐)
    - [方式 2: Git 仓库](#方式-2-git-仓库)
    - [方式 3: Git 特定版本](#方式-3-git-特定版本)
    - [方式 4: crates.io（发布后）](#方式-4-cratesio发布后)
  - [📊 特性组合建议](#-特性组合建议)
    - [✅ 推荐组合](#-推荐组合)
    - [⚠️  注意事项](#️--注意事项)
  - [🏷️ 版本兼容性](#️-版本兼容性)
  - [📦 完整 Cargo.toml 模板](#-完整-cargotoml-模板)
    - [Web 服务完整配置](#web-服务完整配置)
  - [🚀 快速命令](#-快速命令)
  - [💡 提示](#-提示)
  - [📚 相关文档](#-相关文档)


## 🚀 常见配置场景

### 1️⃣ 最小配置（仅核心功能）

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1", 
    default-features = false, 
    features = ["std"] 
}
```

### 2️⃣ Web 应用标准配置

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = ["async", "monitoring", "fault-tolerance", "otlp", "logging"]
}
```

### 3️⃣ 云原生/Kubernetes 部署

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async", 
        "monitoring", 
        "fault-tolerance", 
        "otlp",
        "containers",
        "kubernetes"
    ]
}
```

### 4️⃣ 高性能生产环境

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async",
        "fault-tolerance",
        "monitoring",
        "jemalloc",  # 高性能内存分配
        "otlp"
    ]
}

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
```

### 5️⃣ 开发环境（带验证工具）

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = ["async", "logging", "verification"]
}

[dev-dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = ["chaos-engineering"]
}
```

### 6️⃣ 嵌入式系统

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    default-features = false,
    features = ["embedded-environment"]
}
```

## 📋 完整特性列表

### 默认启用的特性

```toml
default = [
    "std",                  # 标准库支持
    "async",                # 异步运行时
    "monitoring",           # 监控和指标
    "fault-tolerance",      # 容错机制
    "otlp",                 # OpenTelemetry
    "logging",              # 日志记录
    "os-environment"        # OS 环境支持
]
```

### 可选特性矩阵

| 特性 | 用途 | 依赖 | 推荐场景 |
|------|------|------|----------|
| `std` | 标准库支持 | - | 所有标准应用 |
| `async` | 异步支持 | tokio, futures | Web 服务、IO 密集 |
| `monitoring` | 监控指标 | prometheus, metrics | 生产环境 |
| `fault-tolerance` | 容错机制 | crossbeam, dashmap | 高可用服务 |
| `otlp` | 分布式追踪 | opentelemetry | 微服务架构 |
| `otlp-stdout` | OTLP 调试 | opentelemetry-stdout | 开发调试 |
| `otlp-proto` | OTLP 协议 | opentelemetry-proto | 协议解析 |
| `logging` | 日志记录 | env_logger | 所有应用 |
| `chaos-engineering` | 混沌测试 | proptest | 测试环境 |
| `jemalloc` | 内存优化 | jemallocator | 高性能需求 |
| `verification` | 验证基础 | - | 代码验证 |
| `prusti` | Prusti 验证 | - | 静态分析 |
| `creusot` | Creusot 验证 | - | 演绎验证 |
| `os-environment` | OS 环境 | sysinfo, hostname | 标准服务器 |
| `embedded-environment` | 嵌入式 | - | IoT 设备 |
| `container-environment` | 容器环境 | - | 容器部署 |
| `containers` | 容器支持 | - | Docker/Podman |
| `virtualization` | 虚拟化 | - | VM 环境 |
| `kubernetes` | K8s 集成 | - | K8s 部署 |
| `docker-runtime` | Docker 适配 | - | 本地 Docker |
| `oci` | OCI 规范 | oci-spec | OCI 容器 |

## 🎯 按使用场景选择特性

### Web 开发

```toml
features = ["async", "monitoring", "fault-tolerance", "otlp", "logging"]
```

**说明**:

- `async`: 处理并发请求
- `monitoring`: 跟踪性能指标
- `fault-tolerance`: 处理网络失败
- `otlp`: 分布式追踪
- `logging`: 请求日志

### 微服务

```toml
features = [
    "async",
    "monitoring", 
    "fault-tolerance",
    "otlp",
    "containers",
    "kubernetes"
]
```

**说明**:

- 包含 Web 开发的所有特性
- `containers`: 容器化支持
- `kubernetes`: K8s 服务发现和配置

### CLI 工具

```toml
default-features = false
features = ["std", "logging"]
```

**说明**:

- 最小化依赖
- 保留日志功能
- 快速启动

### 后台服务

```toml
features = [
    "async",
    "monitoring",
    "fault-tolerance",
    "jemalloc",
    "logging"
]
```

**说明**:

- `async`: 异步任务处理
- `jemalloc`: 长期运行的内存优化
- `monitoring`: 健康检查和指标

### 数据处理

```toml
features = ["fault-tolerance", "monitoring", "jemalloc"]
```

**说明**:

- `fault-tolerance`: 处理失败和重试
- `jemalloc`: 大量内存操作优化
- `monitoring`: 处理进度跟踪

## 🔧 依赖获取方式

### 方式 1: 本地路径（开发推荐）

```toml
[dependencies]
c13_reliability = { path = "../c13_reliability", features = [...] }
```

### 方式 2: Git 仓库

```toml
[dependencies]
c13_reliability = { 
    git = "https://github.com/rust-lang/c13_reliability",
    branch = "main",
    features = [...]
}
```

### 方式 3: Git 特定版本

```toml
[dependencies]
c13_reliability = { 
    git = "https://github.com/rust-lang/c13_reliability",
    tag = "v0.1.1",
    features = [...]
}
```

### 方式 4: crates.io（发布后）

```toml
[dependencies]
c13_reliability = { version = "0.1.1", features = [...] }
```

## 📊 特性组合建议

### ✅ 推荐组合

```toml
# 标准 Web 服务
features = ["async", "monitoring", "fault-tolerance", "otlp"]

# 云原生应用  
features = ["async", "monitoring", "otlp", "containers", "kubernetes"]

# 高性能服务
features = ["async", "fault-tolerance", "jemalloc", "monitoring"]
```

### ⚠️  注意事项

```toml
# ❌ 避免：同时启用多个环境特性
features = ["os-environment", "embedded-environment"]  # 冲突

# ✅ 正确：只选择一个环境
features = ["os-environment"]  # 或 "embedded-environment"
```

## 🏷️ 版本兼容性

| c13_reliability | Rust 版本 | Edition | 状态 |
|-----------------|-----------|---------|------|
| 0.1.1 | 1.90+ | 2024 | 当前 |
| 0.1.0 | 1.90+ | 2024 | 已过期 |

## 📦 完整 Cargo.toml 模板

### Web 服务完整配置

```toml
[package]
name = "my-web-service"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# 可靠性框架
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "logging",
        "os-environment"
    ]
}

# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# Web 框架
axum = "0.8"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 配置
config = "0.15"

[dev-dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["chaos-engineering"]
}
tokio-test = "0.4"
criterion = "0.6"

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true

[profile.dev]
opt-level = 0
debug = true
```

## 🚀 快速命令

```bash
# 检查配置
cargo check --features "async,monitoring"

# 构建
cargo build --release --features "async,monitoring,fault-tolerance"

# 运行测试
cargo test --features "async,monitoring"

# 运行示例
cargo run --example creusot_basic

# 查看特性
cargo tree --features "async,monitoring" --depth 1
```

## 💡 提示

1. **最小化特性**: 只启用需要的特性，减小二进制大小
2. **开发 vs 生产**: 开发环境可以启用更多调试特性
3. **性能优化**: 生产环境考虑启用 `jemalloc`
4. **可观测性**: 微服务架构强烈建议启用 `otlp`

## 📚 相关文档

- [完整使用指南](./docs/USAGE_GUIDE.md)
- [特性详细说明](./docs/FEATURES_GUIDE.md)
- [性能优化](./docs/PERFORMANCE_GUIDE.md)
- [部署指南](./docs/DEPLOYMENT_GUIDE.md)

---

**版本**: 0.1.1  
**更新**: 2025-10-20
