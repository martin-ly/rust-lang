# 真实案例（Real World Cases）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [真实案例（Real World Cases）索引](#真实案例real-world-cases索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心案例](#-核心案例)
    - [1. 系统编程案例（System Programming）](#1-系统编程案例system-programming)
    - [2. 网络服务案例（Network Services）](#2-网络服务案例network-services)
    - [3. 数据处理案例（Data Processing）](#3-数据处理案例data-processing)
    - [4. 安全应用案例（Security Applications）](#4-安全应用案例security-applications)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c13_microservice/src/`](#cratesc13_microservicesrc)
      - [`crates/c10_networks/src/`](#cratesc10_networkssrc)
    - [真实项目案例](#真实项目案例)
      - [知名 Rust 项目](#知名-rust-项目)
      - [开源项目参考](#开源项目参考)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 在真实项目中的应用案例，涵盖系统编程、网络服务、数据处理和安全应用等核心领域。所有案例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **真实场景**: 基于实际项目的真实案例
- **最佳实践**: 展示 Rust 在实际场景中的最佳实践
- **完整覆盖**: 涵盖多个应用领域
- **易于理解**: 提供详细的案例说明和代码示例

## 📚 核心案例

### 1. 系统编程案例（System Programming）

**推荐库**: `libc`, `nix`, `syscall`, `winapi`

- **操作系统内核模块**: 内核模块开发示例
- **嵌入式系统开发**: 嵌入式 Rust 应用案例
- **设备驱动程序**: 设备驱动开发示例
- **系统工具开发**: 系统工具和实用程序

**相关资源**:

- [Rust for Embedded Systems](https://docs.rust-embedded.org/)
- [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [nix crate 文档](https://docs.rs/nix/)

### 2. 网络服务案例（Network Services）

**推荐库**: `tokio`, `axum`, `actix-web`, `warp`, `hyper`

- **Web 服务器实现**: 高性能 Web 服务器案例
- **微服务架构**: 微服务系统设计案例
- **分布式系统**: 分布式系统实现案例
- **网络协议实现**: 自定义网络协议实现

**相关资源**:

- [Tokio 文档](https://tokio.rs/)
- [axum 文档](https://docs.rs/axum/)
- [actix-web 文档](https://actix.rs/)

### 3. 数据处理案例（Data Processing）

**推荐库**: `polars`, `arrow`, `datafusion`, `ndarray`, `image`

- **数据库引擎**: 数据库系统实现案例
- **数据分析工具**: 数据分析应用案例
- **机器学习框架**: ML 框架使用案例
- **图像处理库**: 图像处理应用案例

**相关资源**:

- [Polars 文档](https://pola-rs.github.io/polars/)
- [Apache Arrow Rust](https://arrow.apache.org/docs/rust/)
- [ndarray 文档](https://docs.rs/ndarray/)

### 4. 安全应用案例（Security Applications）

**推荐库**: `ring`, `rustls`, `openssl`, `bcrypt`, `argon2`

- **加密库实现**: 加密算法实现案例
- **安全工具开发**: 安全工具开发案例
- **区块链应用**: 区块链系统实现案例
- **身份认证系统**: 认证系统实现案例

**相关资源**:

- [ring 文档](https://docs.rs/ring/)
- [rustls 文档](https://docs.rs/rustls/)
- [RustCrypto 项目](https://github.com/RustCrypto)

## 💻 实践与样例

### 代码示例位置

- **真实案例**: [crates/c13_microservice](../../../crates/c13_microservice/)
- **网络编程**: [crates/c10_networks](../../../crates/c10_networks/)
- **分布式系统**: [crates/c20_distributed](../../../crates/c20_distributed/)

### 文件级清单（精选）

#### `crates/c13_microservice/src/`

- `real_world_microservice.rs` - 真实微服务案例
- `production_ready_service.rs` - 生产就绪服务
- `enterprise_integration.rs` - 企业集成案例

#### `crates/c10_networks/src/`

- `production_web_server.rs` - 生产 Web 服务器
- `high_performance_proxy.rs` - 高性能代理
- `distributed_cache.rs` - 分布式缓存

### 真实项目案例

#### 知名 Rust 项目

- **Firefox**: Mozilla 使用 Rust 重写浏览器组件
- **Deno**: 使用 Rust 构建的 JavaScript/TypeScript 运行时
- **Rustls**: 纯 Rust 实现的 TLS 库
- **Tokio**: 异步运行时框架
- **Diesel**: Rust ORM 框架
- **Rocket**: Web 框架

#### 开源项目参考

- [Awesome Rust](https://github.com/rust-unofficial/awesome-rust) - Rust 资源集合
- [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/) - Rust 实用示例
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/) - Rust 示例教程

---

## 🔗 相关索引

- **应用领域（云基础设施）**: [`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)
- **软件工程（微服务）**: [`../../05_software_engineering/02_microservices/00_index.md`](../../05_software_engineering/02_microservices/00_index.md)
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **高级示例**: [`../02_advanced_examples/00_index.md`](../02_advanced_examples/00_index.md)
- **性能示例**: [`../04_performance_examples/00_index.md`](../04_performance_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
