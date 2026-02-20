# C10 网络编程: 主索引 (Master Index)

> **文档定位**: 网络编程学习路径总导航，快速定位所有网络相关资源
> **使用方式**: 作为学习起点，根据需求选择合适的文档和代码模块
> **相关文档**: [README](./README.md) | [FAQ](references/FAQ.md) | [Glossary](references/Glossary.md)

📄 **一页纸总结**: [ONE_PAGE_SUMMARY](./ONE_PAGE_SUMMARY.md) - 核心概念、常见坑、速选表、学习路径

## 📚 官方资源映射

| 官方资源 | 链接 | 与本模块对应 |
| :--- | :--- | :--- || **RBE 练习** | [TCP](https://doc.rust-lang.org/rust-by-example/std_misc/net.html) | 网络基础实践 |
| **Tokio** | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | 异步网络 |
| **Hyper** | [Hyper Guide](https://hyper.rs/guides/) | HTTP 实现 |
| **Rust std** | [std::net](https://doc.rust-lang.org/std/net/) | TCP/UDP 基础 API |

## 📊 目录

- [C10 网络编程: 主索引 (Master Index)](#c10-网络编程-主索引-master-index)
  - [📚 官方资源映射](#-官方资源映射)
  - [📊 目录](#-目录)
  - [🆕 2025-10-19 重大更新](#-2025-10-19-重大更新)
    - [📊 可视化增强文档](#-可视化增强文档)
    - [💻 Rust 1.92.0 实战示例](#-rust-1920-实战示例)
  - [📋 快速导航](#-快速导航)
    - [🎯 按角色导航](#-按角色导航)
    - [📚 按主题导航](#-按主题导航)
  - [📁 文档组织结构](#-文档组织结构)
    - [📖 guides/ - 实践指南](#-guides---实践指南)
    - [🔬 theory/ - 理论文档](#-theory---理论文档)
    - [📚 references/ - 参考文档](#-references---参考文档)
    - [🎓 tutorials/ - 教程文档](#-tutorials---教程文档)
    - [📦 archives/ - 归档文档](#-archives---归档文档)
  - [📖 学习路径](#-学习路径)
    - [🚀 初学者路径 (1-2周)](#-初学者路径-1-2周)
    - [🎓 中级路径 (3-4周)](#-中级路径-3-4周)
    - [🔬 高级路径 (5-8周)](#-高级路径-5-8周)
    - [🏆 专家路径 (持续学习)](#-专家路径-持续学习)
  - [🎯 按场景导航](#-按场景导航)
    - [构建HTTP服务](#构建http服务)
    - [实时通信](#实时通信)
    - [性能敏感应用](#性能敏感应用)
    - [安全通信](#安全通信)
  - [📊 可运行示例](#-可运行示例)
    - [基础示例](#基础示例)
    - [高级示例](#高级示例)
  - [🔗 其他资源](#-其他资源)
    - [项目文档](#项目文档)
    - [项目报告](#项目报告)
    - [工具与配置](#工具与配置)
    - [外部资源](#外部资源)
  - [📞 获取帮助](#-获取帮助)
    - [问题解决顺序](#问题解决顺序)
    - [社区支持](#社区支持)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+, Tokio 1.35+
**文档类型**: 📚 导航索引

---

## 🆕 2025-10-19 重大更新

本次更新新增了以下高质量文档，全面增强 C10 Networks 的学习和实践体验：

### 📊 可视化增强文档

1. **[知识图谱与概念关系](theory/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)** ⭐⭐⭐⭐⭐
   - Mermaid 可视化图表
   - 概念三元组关系 (IS_A, HAS_A, USES...)
   - OSI 七层模型映射
   - 协议演化时间线
   - 学习依赖路径

2. **[多维矩阵对比分析](theory/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)** ⭐⭐⭐⭐⭐
   - 协议全面对比 (TCP/UDP/QUIC/HTTP/WebSocket...)
   - 并发模型对比 (OS线程/async/Actor/CSP)
   - 异步运行时对比 (Tokio/async-std/smol...)
   - 序列化格式对比 (JSON/Protobuf/Bincode...)
   - 包含性能基准测试代码

3. **[网络编程思维导图](RUST_190_COMPREHENSIVE_EXAMPLES.md)** ⭐⭐⭐⭐⭐
   - ASCII 艺术知识结构图
   - 分层知识体系
   - 完整学习路径 (初级/中级/高级)
   - 每周学习计划

### 💻 Rust 1.92.0 实战示例

1. **[实战示例大全 Part 1](RUST_190_EXAMPLES_COLLECTION.md)** ⭐⭐⭐⭐⭐
   - async trait 详解与示例
   - async closure 实战应用
   - const 泛型推断
   - TCP 完整实现 (服务器+客户端)
   - UDP 完整实现 (含多播)

2. **[实战示例大全 Part 2](RUST_190_EXAMPLES_PART2.md)** ⭐⭐⭐⭐⭐
   - HTTP 客户端 (重试、缓存、并发)
   - WebSocket 客户端 (自动重连、心跳)
   - DNS 解析器 (多记录类型、缓存)

3. **[实战示例大全 Part 3 - 高级协议](RUST_190_EXAMPLES_PART3_ADVANCED_PROTOCOLS.md)** ⭐⭐⭐⭐⭐
   - **gRPC**: 4种RPC模式 (Unary/Server Streaming/Client Streaming/Bidirectional) + 拦截器
   - **MQTT**: 发布订阅 (QoS 0/1/2、自动重连、桥接器)
   - **QUIC**: 低延迟传输 + 多路复用
   - **AMQP**: 消息队列 (生产者/消费者/工作池)
   - **GraphQL**: 查询和变更
   - **SSE**: Server-Sent Events 实时推送
   - **微服务架构**: 服务注册发现 + API网关 + 事件总线

4. **[Rust 1.92.0 现代网络技术 (2025)](RUST_192_MODERN_NETWORK_TECHNOLOGIES_2025.md)** ⭐⭐⭐⭐⭐ 🆕🔥
   - **io_uring 革命性异步I/O**:
     - tokio-uring: Tokio集成，零系统调用开销
     - Monoio: 字节跳动运行时，Rent API零拷贝
     - Glommio: Datadog运行时，线程本地设计
   - **零拷贝技术深入**:
     - sendfile/splice/mmap 系统调用对比
     - io_uring Fixed Buffers
     - 性能对比分析 (延迟降低50-70%)
   - **HTTP/3 和 QUIC 深入**:
     - 完整 HTTP/3 服务器/客户端实现
     - 0-RTT 连接建立
     - 连接迁移 (WiFi↔4G无感切换)
   - **内核旁路技术**:
     - AF_XDP: 10Gbps+ 线速包处理
     - eBPF 网络监控 (Aya框架)
   - **综合实战**: 基于io_uring的高性能文件服务器 (~2500行生产级代码)
   - **性能对比**: 传统I/O vs io_uring (吞吐量提升2-5倍)
   - **技术选型指南**: Web API/文件服务器/实时通信/IoT/高频交易

5. **[文档索引与导航](RUST_190_PRACTICAL_EXAMPLES.md)** ⭐⭐⭐⭐⭐
   - 所有增强文档的总索引
   - 学习路径推荐 (初级/中级/高级/专家)
   - 文档对比矩阵
   - 专项技能路径 (IoT/微服务/实时通信/高性能I/O)

---

## 📋 快速导航

### 🎯 按角色导航

| 角色           | 推荐路径                                                                                               | 关键文档           |
| :--- | :--- | :--- || **初学者**     | [快速开始](tutorials/QUICK_START.md) → [基础概念](theory/CONCEPT_DEFINITIONS_ENHANCED.md) → Socket编程 | TCP/UDP基础        |
| **中级开发者** | HTTP客户端 → WebSocket → 异步IO                                                                        | 协议实现、性能优化 |
| **架构师**     | [网络理论](theory/NETWORK_THEORY_FOUNDATION.md) → [性能分析](guides/PERFORMANCE_ANALYSIS_GUIDE.md)     | 架构设计、扩展性   |
| **研究者**     | [形式化验证](theory/FORMAL_VERIFICATION_FRAMEWORK.md) → [语义模型](theory/SEMANTIC_MODEL_ANALYSIS.md)  | 理论证明、模型分析 |

### 📚 按主题导航

| 主题         | 文档入口                                                                      | 说明                   |
| :--- | :--- | :--- || **入门教程** | [QUICK_START.md](tutorials/QUICK_START.md)                                    | 5分钟快速上手          |
| **核心概念** | [CONCEPT_DEFINITIONS_ENHANCED.md](theory/CONCEPT_DEFINITIONS_ENHANCED.md)     | 网络通信概念详解       |
| **协议实现** | [PROTOCOL_IMPLEMENTATION_GUIDE.md](guides/PROTOCOL_IMPLEMENTATION_GUIDE.md)   | TCP/UDP/HTTP/WebSocket |
| **性能优化** | [PERFORMANCE_OPTIMIZATION_GUIDE.md](guides/PERFORMANCE_OPTIMIZATION_GUIDE.md) | 性能调优指南           |
| **安全实践** | [SECURITY_GUIDE.md](guides/SECURITY_GUIDE.md)                                 | TLS/SSL、安全最佳实践  |
| **API参考**  | [API_DOCUMENTATION.md](references/API_DOCUMENTATION.md)                       | 完整API文档            |

---

## 📁 文档组织结构

### 📖 [guides/](guides/) - 实践指南

包含各种网络编程的实践指南和操作手册。

**协议指南**:

- [HTTP_CLIENT_GUIDE.md](guides/HTTP_CLIENT_GUIDE.md) - HTTP客户端
- [WEBSOCKET_GUIDE.md](guides/WEBSOCKET_GUIDE.md) - WebSocket通信
- [DNS_RESOLVER_GUIDE.md](guides/DNS_RESOLVER_GUIDE.md) - DNS解析
- [SOCKET_GUIDE.md](guides/SOCKET_GUIDE.md) - TCP/UDP套接字

**实现指南**:

- [PROTOCOL_IMPLEMENTATION_GUIDE.md](guides/PROTOCOL_IMPLEMENTATION_GUIDE.md) - 协议实现
- [dns_hickory_integration.md](guides/dns_hickory_integration.md) - Hickory-DNS集成
- [libpnet_guide.md](guides/libpnet_guide.md) - 抓包与流量分析

**性能优化**:

- [PERFORMANCE_OPTIMIZATION_GUIDE.md](guides/PERFORMANCE_OPTIMIZATION_GUIDE.md) - 性能优化
- [PERFORMANCE_ANALYSIS_GUIDE.md](guides/PERFORMANCE_ANALYSIS_GUIDE.md) - 性能分析
- [PERFORMANCE_ANALYSIS_AND_OPTIMIZATION_ENHANCED.md](guides/PERFORMANCE_ANALYSIS_AND_OPTIMIZATION_ENHANCED.md) - 性能分析增强版
- [benchmark_minimal_guide.md](guides/benchmark_minimal_guide.md) - 基准测试

**安全与部署**:

- [SECURITY_GUIDE.md](guides/SECURITY_GUIDE.md) - 安全实践
- [DEPLOYMENT_GUIDE.md](guides/DEPLOYMENT_GUIDE.md) - 部署指南

### 🔬 [theory/](theory/) - 理论文档

包含网络编程的理论基础、数学建模和形式化验证。

**网络理论**:

- [NETWORK_COMMUNICATION_THEORY_ENHANCED.md](theory/NETWORK_COMMUNICATION_THEORY_ENHANCED.md) - 网络通信理论增强版
- [NETWORK_THEORY_FOUNDATION.md](theory/NETWORK_THEORY_FOUNDATION.md) - 网络理论基础
- [NETWORK_THEORY_AND_COMMUNICATION_MECHANISMS.md](theory/NETWORK_THEORY_AND_COMMUNICATION_MECHANISMS.md) - 网络理论与通信机制

**数学基础**:

- [MATHEMATICAL_FOUNDATIONS.md](theory/MATHEMATICAL_FOUNDATIONS.md) - 数学基础理论
- [NETWORK_PERFORMANCE_MODELS.md](theory/NETWORK_PERFORMANCE_MODELS.md) - 网络性能模型

**形式化方法**:

- [FORMAL_VERIFICATION_FRAMEWORK.md](theory/FORMAL_VERIFICATION_FRAMEWORK.md) - 形式化验证框架
- [FORMAL_PROTOCOL_SPECIFICATIONS.md](theory/FORMAL_PROTOCOL_SPECIFICATIONS.md) - 形式化协议规范
- [FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md](theory/FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md) - 形式化证明
- [SEMANTIC_MODEL_ANALYSIS.md](theory/SEMANTIC_MODEL_ANALYSIS.md) - 语义模型分析

**概念定义**:

- [CONCEPT_DEFINITIONS_ENHANCED.md](theory/CONCEPT_DEFINITIONS_ENHANCED.md) - 概念定义增强版

### 📚 [references/](references/) - 参考文档

包含API参考、最佳实践和规范文档。

- [API_DOCUMENTATION.md](references/API_DOCUMENTATION.md) - API参考文档
- [BEST_PRACTICES.md](references/BEST_PRACTICES.md) - 最佳实践指南
- [DOCUMENTATION_STANDARDS.md](references/DOCUMENTATION_STANDARDS.md) - 文档标准
- [DOCUMENTATION_STYLE_GUIDE.md](references/DOCUMENTATION_STYLE_GUIDE.md) - 文档风格指南
- [STYLE.md](references/STYLE.md) - 代码和文档风格
- [Glossary.md](references/Glossary.md) - 术语表
- [FAQ.md](references/FAQ.md) - 常见问题解答

### 🎓 [tutorials/](tutorials/) - 教程文档

包含从入门到精通的完整教程和示例。

- [QUICK_START.md](tutorials/QUICK_START.md) - 快速开始指南
- [COMPREHENSIVE_TUTORIAL_GUIDE.md](tutorials/COMPREHENSIVE_TUTORIAL_GUIDE.md) - 综合教程指南
- [TUTORIALS.md](tutorials/TUTORIALS.md) - 主题教程集合
- [EXAMPLES_GUIDE.md](tutorials/EXAMPLES_GUIDE.md) - 示例代码指南
- [EXAMPLES_AND_APPLICATIONS_ENHANCED.md](tutorials/EXAMPLES_AND_APPLICATIONS_ENHANCED.md) - 示例与应用增强版

### 📦 [archives/](archives/) - 归档文档

包含已被更新版本替代的旧版文档，保留用于历史参考。

- [NETWORK_COMMUNICATION_THEORY.md](archives/NETWORK_COMMUNICATION_THEORY.md) - 网络通信理论（旧版）
- [CONCEPT_DEFINITIONS.md](archives/CONCEPT_DEFINITIONS.md) - 概念定义（旧版）
- [EXAMPLES_AND_APPLICATION_SCENARIOS.md](archives/EXAMPLES_AND_APPLICATION_SCENARIOS.md) - 示例场景（旧版）
- [NETWORK_COMMUNICATION_CONCEPTS.md](archives/NETWORK_COMMUNICATION_CONCEPTS.md) - 网络通信概念（旧版）

---

## 📖 学习路径

### 🚀 初学者路径 (1-2周)

**目标**: 掌握基础网络编程

1. **快速开始**: [tutorials/QUICK_START.md](tutorials/QUICK_START.md)
2. **核心概念**: [theory/CONCEPT_DEFINITIONS_ENHANCED.md](theory/CONCEPT_DEFINITIONS_ENHANCED.md)
3. **TCP/UDP**: [guides/SOCKET_GUIDE.md](guides/SOCKET_GUIDE.md)
4. **实践**: 运行 `examples/tcp_*.rs`、`examples/udp_*.rs`

**学习成果**:

- ✅ 创建TCP服务器和客户端
- ✅ 理解UDP通信特点
- ✅ 掌握基本错误处理

### 🎓 中级路径 (3-4周)

**目标**: 掌握高级协议和异步编程

1. **HTTP客户端**: [guides/HTTP_CLIENT_GUIDE.md](guides/HTTP_CLIENT_GUIDE.md)
2. **WebSocket**: [guides/WEBSOCKET_GUIDE.md](guides/WEBSOCKET_GUIDE.md)
3. **DNS解析**: [guides/DNS_RESOLVER_GUIDE.md](guides/DNS_RESOLVER_GUIDE.md)
4. **综合教程**: [tutorials/COMPREHENSIVE_TUTORIAL_GUIDE.md](tutorials/COMPREHENSIVE_TUTORIAL_GUIDE.md)

**学习成果**:

- ✅ 熟练使用HTTP客户端
- ✅ 实现WebSocket实时通信
- ✅ 掌握异步编程模式

### 🔬 高级路径 (5-8周)

**目标**: 深入理解网络编程，性能优化

1. **网络理论**: [theory/NETWORK_THEORY_FOUNDATION.md](theory/NETWORK_THEORY_FOUNDATION.md)
2. **性能优化**: [guides/PERFORMANCE_OPTIMIZATION_GUIDE.md](guides/PERFORMANCE_OPTIMIZATION_GUIDE.md)
3. **安全实践**: [guides/SECURITY_GUIDE.md](guides/SECURITY_GUIDE.md)
4. **协议实现**: [guides/PROTOCOL_IMPLEMENTATION_GUIDE.md](guides/PROTOCOL_IMPLEMENTATION_GUIDE.md)

**学习成果**:

- ✅ 设计高性能网络架构
- ✅ 实现安全网络通信
- ✅ 进行性能调优

### 🏆 专家路径 (持续学习)

**目标**: 成为网络编程专家

1. **深度理论**: [theory/](theory/) 所有文档
2. **形式化方法**: [theory/FORMAL_VERIFICATION_FRAMEWORK.md](theory/FORMAL_VERIFICATION_FRAMEWORK.md)
3. **源码分析**: 深入研究核心实现
4. **创新实践**: 改进实现或设计新协议

---

## 🎯 按场景导航

### 构建HTTP服务

| 需求         | 推荐方案            | 文档                                                |
| :--- | :--- | :--- || HTTP客户端   | `reqwest`           | [HTTP_CLIENT_GUIDE.md](guides/HTTP_CLIENT_GUIDE.md) |
| HTTP/2、gRPC | `tonic`             | 示例: `grpc_*.rs`                                   |
| WebSocket    | `tokio-tungstenite` | [WEBSOCKET_GUIDE.md](guides/WEBSOCKET_GUIDE.md)     |

### 实时通信

| 需求     | 推荐方案  | 文档                                            |
| :--- | :--- | :--- || 双向通信 | WebSocket | [WEBSOCKET_GUIDE.md](guides/WEBSOCKET_GUIDE.md) |
| 低延迟   | UDP       | [SOCKET_GUIDE.md](guides/SOCKET_GUIDE.md)       |
| P2P      | libp2p    | 示例: `p2p_minimal.rs`                          |

### 性能敏感应用

| 需求       | 推荐方案         | 文档                                                                          |
| :--- | :--- | :--- || 高吞吐量   | Tokio + 连接池   | [PERFORMANCE_OPTIMIZATION_GUIDE.md](guides/PERFORMANCE_OPTIMIZATION_GUIDE.md) |
| 低延迟     | UDP + 零拷贝     | [PERFORMANCE_ANALYSIS_GUIDE.md](guides/PERFORMANCE_ANALYSIS_GUIDE.md)         |
| 大规模并发 | Tokio + 背压控制 | [BEST_PRACTICES.md](references/BEST_PRACTICES.md)                             |

### 安全通信

| 需求    | 推荐方案                  | 文档                                                            |
| :--- | :--- | :--- || HTTPS   | `reqwest` + TLS           | [SECURITY_GUIDE.md](guides/SECURITY_GUIDE.md)                   |
| WSS     | `tokio-tungstenite` + TLS | [WEBSOCKET_GUIDE.md](guides/WEBSOCKET_GUIDE.md)                 |
| DoH/DoT | `hickory-dns`             | [dns_hickory_integration.md](guides/dns_hickory_integration.md) |

---

## 📊 可运行示例

所有示例代码位于项目根目录的 `examples/` 目录：

### 基础示例

| 示例           | 文件                 | 运行命令                              |
| :--- | :--- | :--- || **TCP服务器**  | `tcp_echo_server.rs` | `cargo run --example tcp_echo_server` |
| **TCP客户端**  | `tcp_client.rs`      | `cargo run --example tcp_client`      |
| **UDP通信**    | `udp_echo.rs`        | `cargo run --example udp_echo`        |
| **HTTP客户端** | `http_client.rs`     | `cargo run --example http_client`     |
| **WebSocket**  | `websocket_demo.rs`  | `cargo run --example websocket_demo`  |

### 高级示例

| 示例                | 文件                              | 运行命令                                           |
| :--- | :--- | :--- || **DNS解析**         | `dns_lookup.rs`                   | `cargo run --example dns_lookup`                   |
| **DoH/DoT**         | `dns_doh_dot.rs`                  | `cargo run --example dns_doh_dot`                  |
| **gRPC**            | `grpc_server.rs` `grpc_client.rs` | `cargo run --example grpc_server`                  |
| **流量分析**        | `pcap_offline.rs`                 | `cargo run --example pcap_offline`                 |
| **Rust 1.92.0特性** | `rust_192_async_features_demo.rs` | `cargo run --example rust_192_async_features_demo` |

---

## 🔗 其他资源

### 项目文档

- [项目README](../README.md) - 项目概述
- [贡献指南](../CONTRIBUTING.md) - 如何贡献
- [部署指南](../DEPLOYMENT_GUIDE.md) - 生产部署
- [安全指南](../SECURITY.md) - 安全实践

### 项目报告

- [项目报告目录](../reports/) - 包含所有项目报告、完成报告、技术分析等
- [项目路线图](../reports/ROADMAP.md) - 项目发展规划
- [Rust 1.92.0特性](../reports/RUST_192_ALIGNMENT_COMPLETION_SUMMARY.md) - Rust 1.92.0对齐总结

### 工具与配置

- **Cargo.toml**: 依赖配置
- **build.rs**: 构建脚本（gRPC proto编译）
- **proto/**: Protocol Buffers定义
- **scripts/**: 自动化脚本

### 外部资源

- [Tokio 文档](https://tokio.rs/)
- [reqwest 文档](https://docs.rs/reqwest/)
- [hickory-dns 文档](https://docs.rs/hickory-dns/)
- [libp2p 文档](https://docs.rs/libp2p/)

---

## 📞 获取帮助

### 问题解决顺序

1. **查看FAQ**: [references/FAQ.md](references/FAQ.md)
2. **查看术语表**: [references/Glossary.md](references/Glossary.md)
3. **查看示例**: `examples/` 目录
4. **运行测试**: `cargo test -p c10_networks`
5. **提交Issue**: GitHub Issues

### 社区支持

- **GitHub Issues**: 报告问题和建议
- **代码审查**: 提交 PR 获得反馈
- **技术讨论**: 参与社区讨论

---

**文档维护**: C10 Networks 开发团队
**更新频率**: 跟随项目进度持续更新
**文档版本**: v2.0
**Rust 版本**: 1.92.0+, Tokio 1.35+
