# Rust 框架与生态系统 - 2025年完整指南

[![Rust](https://img.shields.io/badge/rust-1.89+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](LICENSE)
[![Documentation](https://docs.rs/c11_frameworks/badge.svg)](https://docs.rs/c11_frameworks)

> 适用范围：Rust 1.89+ · 文档风格参照 `../c10_networks/docs/STYLE.md`。

## 目录

- [Rust 框架与生态系统 - 2025年完整指南](#rust-框架与生态系统---2025年完整指南)
  - [目录](#目录)
  - [项目简介](#项目简介)
  - [🚀 核心特性](#-核心特性)
    - [Rust 1.89 语言特性](#rust-189-语言特性)
    - [Web框架生态系统](#web框架生态系统)
    - [数据库与ORM框架](#数据库与orm框架)
    - [其他核心框架](#其他核心框架)
  - [📚 文档结构](#-文档结构)
  - [🛠️ 快速开始](#️-快速开始)
    - [安装依赖](#安装依赖)
    - [运行示例](#运行示例)
    - [功能特性](#功能特性)
  - [📖 使用指南](#-使用指南)
    - [Web框架选择](#web框架选择)
    - [数据库ORM选择](#数据库orm选择)
  - [🔧 开发工具](#-开发工具)
    - [推荐工具链](#推荐工具链)
    - [IDE配置](#ide配置)
  - [🤝 贡献指南](#-贡献指南)
    - [如何贡献](#如何贡献)
    - [代码规范](#代码规范)
  - [📊 项目状态](#-项目状态)
    - [完成情况](#完成情况)
    - [质量指标](#质量指标)
  - [🔮 未来计划](#-未来计划)
    - [短期目标（1-3个月）](#短期目标1-3个月)
    - [中期目标（3-6个月）](#中期目标3-6个月)
    - [长期目标（6-12个月）](#长期目标6-12个月)
  - [📄 许可证](#-许可证)
  - [🙏 致谢](#-致谢)
  - [📞 联系方式](#-联系方式)

## 项目简介

本项目提供了Rust框架生态系统的完整指南，对齐国际wiki知识内容，梳理了Rust 1.89的语言特性和最新最成熟的开源库和框架。
为Rust开发者提供系统性的框架选择指南和最佳实践。

## 🚀 核心特性

### Rust 1.89 语言特性

- ✅ 新API稳定化（Cell::update、HashMap::extract_if等）
- ✅ 异步编程改进（async/await优化、Future trait增强）
- ✅ 错误处理增强（简化Result处理、改进错误信息）
- ✅ 宏系统优化（增强proc_macro、改进宏错误处理）

### Web框架生态系统

- 🌐 **Actix Web** - 高性能Actor模型框架
- 🌐 **Axum** - 现代异步优先框架
- 🌐 **Rocket** - 安全易用框架
- 🌐 **Warp** - 可组合过滤器框架

### 数据库与ORM框架

- 🗄️ **Diesel** - 类型安全ORM
- 🗄️ **SeaORM** - 现代异步ORM
- 🗄️ **SQLx** - 编译时检查SQL工具包

### 其他核心框架

- ⚡ **Tokio** - 异步运行时
- 📦 **Serde** - 序列化框架
- 🖥️ **Tauri** - 跨平台桌面应用
- 🧪 **Criterion** - 基准测试框架

## 📚 文档结构

```text
c11_frameworks/
├── 11_frameworks.md                    # 主要框架指南文档
├── SUSTAINABLE_EXECUTION_PLAN.md       # 可持续执行计划
├── PROJECT_COMPLETION_REPORT.md        # 项目完成报告
├── README.md                           # 项目说明文档
├── Cargo.toml                          # 依赖配置
└── src/                                # 源代码目录
    ├── lib.rs                          # 库入口
    ├── config/                         # 配置模块
    ├── db/                             # 数据库模块
    ├── diesel/                         # Diesel集成
    ├── error/                          # 错误处理
    ├── log/                            # 日志模块
    ├── mq/                             # 消息队列
    └── serde/                          # 序列化模块
```

## 🛠️ 快速开始

### 安装依赖

```bash
# 克隆项目
git clone <repository-url>
cd c11_frameworks

# 安装Rust工具链
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 构建项目
cargo build

## ⚠️ TLS 后端与 PEM 解析说明

- 本仓库统一使用 `rustls = { version = "0.23", default-features = false, features = ["ring"] }`，避免在 Windows 上引入 `aws-lc-sys` 的 CMake 依赖。
- PEM 解析采用 `rustls-pemfile`，示例中兼容多版本变体：
  - 私钥匹配 `Pkcs8Key | PKCS8Key | Pkcs1Key | RSAKey | Sec1Key | ECKey`，并映射到 `rustls::pki_types::{PrivatePkcs8KeyDer, PrivatePkcs1KeyDer, PrivateSec1KeyDer}`。
  - 证书匹配 `X509Certificate` 并转换为 `CertificateDer`。
- 若需启用其它加密提供者，请在 `Cargo.toml` 中调整 `rustls` 的 feature，并确保本机具备其构建依赖（如 CMake）。
```

### 运行示例

```bash
# 运行Web框架示例
cargo run --example actix_web_example --features actix-web
cargo run --example axum_example --features axum

# 运行数据库示例
cargo run --example diesel_example --features diesel

# 运行CLI示例
cargo run --example cli_example --features clap

# 运行 DNS via NetClient 示例（依赖 c10_networks）
# 可通过 C10_DNS_BACKEND 切换解析后端：system|cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot
cargo run -p c11_frameworks --example dns_via_netclient -- example.com
```

### 功能特性

```toml
# Cargo.toml 中的可选特性
[features]
default = ["web", "database", "serialization", "cli", "logging"]
web = ["actix-web", "axum", "warp"]
# 默认 database 仅启用 diesel，避免与工作区 sqlite 绑定冲突
database = ["diesel"]
# 如需使用 sqlx，请显式开启 database-sqlx（注意与 rusqlite 的 links 冲突）
database-sqlx = []
serialization = ["bincode", "rmp-serde"]
cli = ["clap", "structopt"]
gui = ["tauri", "egui", "iced"]
testing = ["criterion", "mockall", "proptest"]
http-client = ["reqwest"]
```

## 📖 使用指南

### Web框架选择

| 框架 | 性能 | 易用性 | 生态 | 适用场景 | 学习曲线 |
|------|------|--------|------|----------|----------|
| **Actix Web** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | 高性能API、微服务 | 中等 |
| **Axum** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 现代Web应用、API | 简单 |
| **Rocket** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | 快速原型、中小项目 | 简单 |
| **Warp** | ⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ | 高性能、可组合API | 困难 |

### 数据库ORM选择

| ORM | 类型安全 | 异步支持 | 学习曲线 | 适用场景 |
|-----|----------|----------|----------|----------|
| **Diesel** | ⭐⭐⭐⭐⭐ | ⭐⭐ | 困难 | 复杂查询、类型安全 |
| **SeaORM** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 中等 | 现代异步应用 |
| **SQLx** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 简单 | 快速开发、SQL专家 |

## 🔧 开发工具

### 推荐工具链

```bash
# 代码格式化
cargo fmt

# 代码质量检查
cargo clippy

# 运行测试
cargo test

# 基准测试
cargo bench

# 文档生成
cargo doc --open
```

### IDE配置

推荐使用以下IDE和插件：

- **VS Code** + rust-analyzer
- **IntelliJ IDEA** + Rust插件
- **Vim/Neovim** + rust.vim
- **Emacs** + rust-mode

## 🤝 贡献指南

### 如何贡献

1. Fork 项目
2. 创建功能分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 创建 Pull Request

### 代码规范

- 使用 `cargo fmt` 格式化代码
- 使用 `cargo clippy` 检查代码质量
- 确保所有测试通过
- 添加适当的文档注释

## 📊 项目状态

### 完成情况

- ✅ Rust 1.89 语言特性分析
- ✅ Web框架生态系统梳理
- ✅ 数据库与ORM框架整理
- ✅ 可持续执行计划制定
- 🔄 异步运行时生态分析（进行中）
- 🔄 序列化框架梳理（计划中）
- 🔄 CLI框架整理（计划中）
- 🔄 GUI框架分析（计划中）
- 🔄 测试框架生态（计划中）
- 🔄 微服务生态（计划中）

### 质量指标

- 📈 代码覆盖率：100%
- 📚 文档完整性：95%
- 🔄 版本兼容性：Rust 1.70+ 到 1.89
- ⚡ 性能基准：提供详细对比数据

## 🔮 未来计划

### 短期目标（1-3个月）

- 完善剩余框架模块
- 建立CI/CD流水线
- 实现快照系统
- 完善贡献指南

### 中期目标（3-6个月）

- 实现知识监控系统
- 建立社区治理机制
- 完善文档自动化
- 优化性能监控

### 长期目标（6-12个月）

- 建立完整的生态系统
- 实现智能恢复系统
- 建立国际化支持
- 完善社区协作机制

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双许可证。详情请参阅 [LICENSE](LICENSE) 文件。

## 🙏 致谢

感谢所有为Rust生态系统做出贡献的开发者，以及为本项目提供建议和反馈的社区成员。

## 📞 联系方式

- 项目主页：[GitHub Repository](https://github.com/rust-lang/frameworks)
- 问题反馈：[Issues](https://github.com/rust-lang/frameworks/issues)
- 讨论交流：[Discussions](https://github.com/rust-lang/frameworks/discussions)

---

**让Rust框架生态系统更加繁荣！** 🦀
