# C10 网络编程: 主索引 (Master Index)

> **文档定位**: 网络编程学习路径总导航，快速定位所有网络相关资源  
> **使用方式**: 作为学习起点，根据需求选择合适的文档和代码模块  
> **相关文档**: [README](./README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+, Tokio 1.35+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | [快速开始](./QUICK_START.md) → [基础概念](./CONCEPT_DEFINITIONS.md) → Socket编程 | TCP/UDP基础 |
| **中级开发者** | HTTP客户端 → WebSocket → 异步IO | 协议实现、性能优化 |
| **架构师** | [网络理论](./NETWORK_THEORY_FOUNDATION.md) → [性能分析](./PERFORMANCE_ANALYSIS_GUIDE.md) | 架构设计、扩展性 |
| **研究者** | [形式化验证](./FORMAL_VERIFICATION_FRAMEWORK.md) → [语义模型](./SEMANTIC_MODEL_ANALYSIS.md) | 理论证明、模型分析 |

### 📚 按主题导航

| 主题 | 文档入口 | 说明 |
|------|---------|------|
| **入门教程** | [QUICK_START.md](./QUICK_START.md) | 5分钟快速上手 |
| **核心概念** | [CONCEPT_DEFINITIONS.md](./CONCEPT_DEFINITIONS.md) | 网络通信概念详解 |
| **协议实现** | [PROTOCOL_IMPLEMENTATION_GUIDE.md](./PROTOCOL_IMPLEMENTATION_GUIDE.md) | TCP/UDP/HTTP/WebSocket |
| **性能优化** | [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md) | 性能调优指南 |
| **安全实践** | [SECURITY_GUIDE.md](./SECURITY_GUIDE.md) | TLS/SSL、安全最佳实践 |
| **API参考** | [API_DOCUMENTATION.md](./API_DOCUMENTATION.md) | 完整API文档 |

---

## 🏗️ 核心内容结构

### 第一部分：基础入门

#### 1. 快速开始

| 文档 | 说明 | 适用对象 |
|------|------|---------|
| [QUICK_START.md](./QUICK_START.md) | 快速上手指南 | 初学者 |
| [CONCEPT_DEFINITIONS.md](./CONCEPT_DEFINITIONS.md) | 核心概念定义 | 所有人 |
| [DOCUMENTATION_STANDARDS.md](./DOCUMENTATION_STANDARDS.md) | 文档规范 | 贡献者 |
| [STYLE.md](./STYLE.md) | 代码风格指南 | 开发者 |

#### 2. 基础协议

| 协议 | 文档 | 示例代码 |
|------|------|---------|
| **TCP** | [SOCKET_GUIDE.md](./SOCKET_GUIDE.md) | `examples/tcp_*.rs` |
| **UDP** | [SOCKET_GUIDE.md](./SOCKET_GUIDE.md) | `examples/udp_*.rs` |
| **DNS** | [DNS_RESOLVER_GUIDE.md](./DNS_RESOLVER_GUIDE.md) | `examples/dns_*.rs` |
| **HTTP** | [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md) | `examples/http_*.rs` |
| **WebSocket** | [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md) | `examples/ws_*.rs` |

### 第二部分：协议实现

#### 3. 应用层协议

| 协议 | 说明 | 关键特性 |
|------|------|---------|
| **HTTP/1.1** | 基于 `reqwest` | 连接池、超时控制 |
| **HTTP/2** | gRPC 支持 | 多路复用、流控制 |
| **WebSocket** | 全双工通信 | 心跳检测、自动重连 |
| **DNS** | 基于 `hickory-dns` | DoH/DoT、缓存 |

#### 4. 传输层协议

| 协议 | 文档 | 特点 |
|------|------|------|
| **TCP** | [SOCKET_GUIDE.md](./SOCKET_GUIDE.md) | 可靠传输、流量控制 |
| **UDP** | [SOCKET_GUIDE.md](./SOCKET_GUIDE.md) | 低延迟、无连接 |
| **QUIC** | 规划中 | HTTP/3 基础 |

#### 5. 网络层协议

| 工具 | 说明 | 用途 |
|------|------|------|
| **libpnet** | [libpnet_guide.md](./libpnet_guide.md) | 数据包捕获与分析 |
| **pcap** | 示例: `pcap_*.rs` | 流量监控 |
| **ARP** | 示例: `arp_sniff.rs` | 地址解析 |

### 第三部分：理论基础

#### 6. 网络理论

| 文档 | 主题 | 核心内容 |
|------|------|---------|
| [NETWORK_THEORY_FOUNDATION.md](./NETWORK_THEORY_FOUNDATION.md) | 理论基础 | OSI模型、TCP/IP栈 |
| [NETWORK_COMMUNICATION_THEORY.md](./NETWORK_COMMUNICATION_THEORY.md) | 通信理论 | 可靠性、拥塞控制 |
| [MATHEMATICAL_FOUNDATIONS.md](./MATHEMATICAL_FOUNDATIONS.md) | 数学基础 | 排队论、性能模型 |
| [NETWORK_PERFORMANCE_MODELS.md](./NETWORK_PERFORMANCE_MODELS.md) | 性能模型 | 吞吐量、延迟分析 |

#### 7. 形式化方法

| 文档 | 说明 | 应用 |
|------|------|------|
| [FORMAL_VERIFICATION_FRAMEWORK.md](./FORMAL_VERIFICATION_FRAMEWORK.md) | 验证框架 | 协议正确性证明 |
| [SEMANTIC_MODEL_ANALYSIS.md](./SEMANTIC_MODEL_ANALYSIS.md) | 语义模型 | 行为语义分析 |
| [FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md](./FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md) | 数学证明 | 定理证明 |
| [FORMAL_PROTOCOL_SPECIFICATIONS.md](./FORMAL_PROTOCOL_SPECIFICATIONS.md) | 协议规范 | 形式化描述 |

### 第四部分：性能优化

#### 8. 性能分析

| 文档 | 说明 | 工具 |
|------|------|------|
| [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md) | 优化指南 | Criterion、perf |
| [PERFORMANCE_ANALYSIS_GUIDE.md](./PERFORMANCE_ANALYSIS_GUIDE.md) | 分析方法 | 火焰图、追踪 |
| [benchmark_minimal_guide.md](./benchmark_minimal_guide.md) | 基准测试 | Criterion |

#### 9. 运行时选择

| 运行时 | 文档 | 特点 |
|--------|------|------|
| **Tokio** | 默认选择 | 成熟稳定、生态完善 |
| **async-std** | 备选方案 | 类标准库API |
| **对比分析** | [NETWORK_RUNTIME_COMPARISON_ANALYSIS.md](../NETWORK_RUNTIME_COMPARISON_ANALYSIS.md) | 性能、特性对比 |

### 第五部分：安全实践

#### 10. 安全通信

| 主题 | 文档 | 说明 |
|------|------|------|
| **TLS/SSL** | [SECURITY_GUIDE.md](./SECURITY_GUIDE.md) | 加密通信 |
| **证书管理** | [SECURITY_GUIDE.md](./SECURITY_GUIDE.md) | 证书验证、ALPN |
| **DoH/DoT** | [dns_hickory_integration.md](./dns_hickory_integration.md) | DNS加密 |
| **最佳实践** | [BEST_PRACTICES.md](./BEST_PRACTICES.md) | 安全检查清单 |

### 第六部分：高级特性

#### 11. P2P网络

| 功能 | 示例 | 说明 |
|------|------|------|
| **libp2p** | `p2p_minimal.rs` | 点对点网络 |
| **DHT** | 规划中 | 分布式哈希表 |
| **NAT穿透** | 规划中 | 连接建立 |

#### 12. 流量分析

| 工具 | 示例 | 用途 |
|------|------|------|
| **pcap** | `pcap_*.rs` | 离线分析 |
| **live capture** | `pcap_live_tcp.rs` | 实时监控 |
| **ARP** | `arp_sniff.rs` | 协议分析 |

---

## 📖 实践示例

### 可运行示例 (examples/)

| 示例 | 文件 | 说明 | 运行命令 |
|------|------|------|----------|
| **TCP服务器** | `tcp_echo_server.rs` | Echo服务器 | `cargo run --example tcp_echo_server` |
| **TCP客户端** | `tcp_client.rs` | TCP客户端 | `cargo run --example tcp_client` |
| **UDP通信** | `udp_echo.rs` | UDP Echo | `cargo run --example udp_echo` |
| **HTTP客户端** | `http_client.rs` | HTTP请求 | `cargo run --example http_client` |
| **WebSocket** | `websocket_demo.rs` | WebSocket通信 | `cargo run --example websocket_demo` |
| **DNS解析** | `dns_lookup.rs` | DNS查询 | `cargo run --example dns_lookup` |
| **DoH/DoT** | `dns_doh_dot.rs` | 加密DNS | `cargo run --example dns_doh_dot` |
| **gRPC** | `grpc_server.rs` `grpc_client.rs` | gRPC服务 | `cargo run --example grpc_server` |
| **pcap** | `pcap_offline.rs` | 流量分析 | `cargo run --example pcap_offline` |
| **Rust 1.90特性** | `rust_190_async_features_demo.rs` | 最新特性 | `cargo run --example rust_190_async_features_demo` |

### 性能基准测试 (benches/)

| 基准 | 文件 | 说明 | 运行命令 |
|------|------|------|----------|
| **网络基准** | `network_benchmarks.rs` | 综合网络性能 | `cargo bench` |
| **协议基准** | `protocol_performance.rs` | 协议实现性能 | `cargo bench --bench protocol_performance` |
| **并发基准** | `concurrency_performance.rs` | 并发处理性能 | `cargo bench --bench concurrency_performance` |
| **错误处理** | `error_handling_performance.rs` | 错误处理开销 | `cargo bench --bench error_handling_performance` |

---

## 🧪 测试与验证

### 测试套件 (tests/)

| 测试 | 文件 | 说明 |
|------|------|------|
| **DNS测试** | `dns_tests.rs` | DNS功能测试 |
| **协议测试** | `protocol_tests.rs` | 协议实现测试 |
| **安全测试** | `security_tests.rs` | 安全功能测试 |
| **性能测试** | `performance_tests.rs` | 性能验证测试 |
| **集成测试** | `integration_tests.rs` | 端到端测试 |

### 运行测试

```bash
# 运行所有测试
cargo test -p c10_networks

# 运行特定测试
cargo test -p c10_networks --test dns_tests

# 运行带输出的测试
cargo test -p c10_networks -- --nocapture

# 运行性能基准
cargo bench -p c10_networks
```

---

## 📚 学习路径

### 🚀 初学者路径 (1-2周)

1. **起步**: [QUICK_START.md](./QUICK_START.md)
2. **概念**: [CONCEPT_DEFINITIONS.md](./CONCEPT_DEFINITIONS.md)
3. **TCP/UDP**: [SOCKET_GUIDE.md](./SOCKET_GUIDE.md)
4. **实践**: 运行 `tcp_echo_server.rs`、`udp_echo.rs`
5. **巩固**: 完成 FAQ 中的练习题

**推荐阅读顺序**:

```text
QUICK_START.md
  ↓
CONCEPT_DEFINITIONS.md
  ↓
SOCKET_GUIDE.md (TCP/UDP)
  ↓
examples/tcp_*.rs
  ↓
FAQ.md (基础问题)
```

### 🎓 中级路径 (3-4周)

1. **HTTP客户端**: [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md)
2. **WebSocket**: [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md)
3. **DNS解析**: [DNS_RESOLVER_GUIDE.md](./DNS_RESOLVER_GUIDE.md)
4. **异步编程**: [Tutorials](./TUTORIALS.md)
5. **性能优化**: [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md)

**推荐阅读顺序**:

```text
HTTP_CLIENT_GUIDE.md
  ↓
examples/http_client.rs
  ↓
WEBSOCKET_GUIDE.md
  ↓
DNS_RESOLVER_GUIDE.md
  ↓
PERFORMANCE_OPTIMIZATION_GUIDE.md
```

### 🔬 高级路径 (5-8周)

1. **网络理论**: [NETWORK_THEORY_FOUNDATION.md](./NETWORK_THEORY_FOUNDATION.md)
2. **形式化验证**: [FORMAL_VERIFICATION_FRAMEWORK.md](./FORMAL_VERIFICATION_FRAMEWORK.md)
3. **性能模型**: [NETWORK_PERFORMANCE_MODELS.md](./NETWORK_PERFORMANCE_MODELS.md)
4. **协议实现**: [PROTOCOL_IMPLEMENTATION_GUIDE.md](./PROTOCOL_IMPLEMENTATION_GUIDE.md)
5. **安全实践**: [SECURITY_GUIDE.md](./SECURITY_GUIDE.md)

**推荐阅读顺序**:

```text
NETWORK_THEORY_FOUNDATION.md
  ↓
FORMAL_VERIFICATION_FRAMEWORK.md
  ↓
PROTOCOL_IMPLEMENTATION_GUIDE.md
  ↓
SECURITY_GUIDE.md
  ↓
实战项目
```

### 🏆 专家路径 (持续学习)

1. **深度研究**: 所有理论文档
2. **源码分析**: 阅读并分析核心实现
3. **性能调优**: 运行并分析所有基准测试
4. **贡献代码**: 改进现有实现或添加新功能
5. **分享经验**: 撰写技术博客或教程

---

## 🎯 按场景导航

### 构建HTTP服务

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| HTTP客户端 | `reqwest` | [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md) |
| HTTP/2、gRPC | `tonic` | 示例: `grpc_*.rs` |
| WebSocket | `tokio-tungstenite` | [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md) |

### 实时通信

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 双向通信 | WebSocket | [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md) |
| 低延迟 | UDP | [SOCKET_GUIDE.md](./SOCKET_GUIDE.md) |
| P2P | libp2p | 示例: `p2p_minimal.rs` |

### 性能敏感应用

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 高吞吐量 | Tokio + 连接池 | [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md) |
| 低延迟 | UDP + 零拷贝 | [PERFORMANCE_ANALYSIS_GUIDE.md](./PERFORMANCE_ANALYSIS_GUIDE.md) |
| 大规模并发 | Tokio + 背压控制 | [BEST_PRACTICES.md](./BEST_PRACTICES.md) |

### 安全通信

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| HTTPS | `reqwest` + TLS | [SECURITY_GUIDE.md](./SECURITY_GUIDE.md) |
| WSS | `tokio-tungstenite` + TLS | [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md) |
| DoH/DoT | `hickory-dns` | [dns_hickory_integration.md](./dns_hickory_integration.md) |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md) - 项目概述
- [网络模块说明](../10_networks.md) - 模块介绍
- [部署指南](../DEPLOYMENT_GUIDE.md) - 生产部署
- [贡献指南](../CONTRIBUTING.md) - 如何贡献

### 工具与配置

- **Cargo.toml**: 依赖配置
- **build.rs**: 构建脚本（gRPC proto编译）
- **proto/**: Protocol Buffers定义

### 外部资源

- [Tokio 文档](https://tokio.rs/)
- [reqwest 文档](https://docs.rs/reqwest/)
- [hickory-dns 文档](https://docs.rs/hickory-dns/)
- [libp2p 文档](https://docs.rs/libp2p/)

---

## 📊 项目统计

### 代码规模

- **核心模块**: 20+ 模块
- **协议实现**: TCP/UDP/HTTP/WebSocket/DNS/gRPC
- **示例程序**: 20+ 可运行示例
- **基准测试**: 6 个性能基准套件
- **测试用例**: 8 个测试套件

### 文档规模

- **核心文档**: 40+ 文档
- **理论文档**: 10+ 理论分析
- **指南文档**: 15+ 实践指南
- **API文档**: 完整的 rustdoc

---

## 🆕 最新更新

### 2025-10-19

- ✅ 创建主索引文档
- ✅ 完善文档导航结构
- ✅ 添加学习路径指导

### 2025年

- ✅ 集成 Rust 1.90 特性
- ✅ 添加 hickory-dns 集成
- ✅ 实现 gRPC 示例
- ✅ 完善性能基准测试

---

## 📞 获取帮助

### 问题解决

1. **查看 FAQ**: [FAQ.md](./FAQ.md) - 常见问题解答
2. **查看术语表**: [Glossary.md](./Glossary.md) - 核心概念定义
3. **查看示例**: examples/ - 可运行的示例代码
4. **运行测试**: `cargo test` - 验证功能

### 社区支持

- **GitHub Issues**: 报告问题和建议
- **代码审查**: 提交 PR 获得反馈
- **技术讨论**: 参与社区讨论

---

**文档维护**: Rust 学习社区  
**更新频率**: 跟随项目进度持续更新  
**文档版本**: v1.0  
**Rust 版本**: 1.90+, Tokio 1.35+
