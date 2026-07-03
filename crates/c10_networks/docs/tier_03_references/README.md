# Tier 3: 技术参考层

> **完成状态**: ✅ **100%** (5篇核心文档 + 8篇现有参考)
> **最后更新**: 2025-12-11 (核心技术参考完成)

---

## 📚 核心技术参考 (NEW!)

**5篇深度技术参考文档**:

1. **[01\_网络协议分类参考.md](01_network_protocol_categories_reference.md)** (~1,100 行, 90+ 示例)
   - OSI七层模型完整映射
   - TCP/IP协议族实现
   - HTTP/1.1, HTTP/2, HTTP/3对比
   - WebSocket, DNS, gRPC, MQTT等应用层协议
   - 协议选择决策树
2. **[02\_网络库对比选择.md](02_network_library_comparison.md)** (~950 行, 80+ 示例)
   - 异步运行时对比 (Tokio vs smol)
   - HTTP库对比 (reqwest vs hyper vs surf)
   - 服务器框架对比 (axum vs actix-web vs warp vs rocket)
   - TLS库对比 (rustls vs native-tls vs openssl)
   - QUIC/HTTP3库对比 (quinn vs quiche)
   - 生产环境推荐组合
3. **[03_rust_190_networking_features_reference.md](03_rust_190_networking_features_reference.md)** (~800 行, 60+ 示例)
   - 异步Trait稳定化 (RPITIT)
   - GATs在网络编程中的应用
   - let-else模式匹配
   - impl Trait增强
   - 常量泛型改进
   - Edition 2024 特性（1.85.0+ stable；`gen {}` 仍为 nightly）
4. **[04\_网络性能基准参考.md](04_network_performance_benchmarks_reference.md)** (~850 行, 50+ 基准)
   - HTTP服务器性能对比
   - 异步运行时性能测试
   - WebSocket吞吐量基准
   - gRPC性能数据
   - TLS握手性能
   - 序列化库性能对比
   - io_uring vs epoll性能
5. **[05\_网络安全参考.md](05_network_security_reference.md)** (~900 行, 70+ 示例)
   - TLS/SSL安全配置
   - 证书管理
   - JWT认证与OAuth2
   - 输入验证与过滤
   - DoS防护 (速率限制、连接限制)
   - 加密通信 (AES-GCM, RSA, HMAC)
   - 常见漏洞防护 (SQL注入、XSS、CSRF)

---

## 📖 现有参考文档

**8篇现有参考**:

- [API_DOCUMENTATION.md](../references/api_documentation.md)
- [BEST_PRACTICES.md](../references/best_practices.md)
- [DOCUMENTATION_STANDARDS.md](../references/DOCUMENTATION_STANDARDS.md)
- [STYLE.md](../references/STYLE.md)
- [DOCUMENTATION_STYLE_GUIDE.md](../references/DOCUMENTATION_STYLE_GUIDE.md)
- [README.md](../references/README.md)

---

## 🗺️ 思维导图与图谱

| 资源                                                                            | 说明         |
| :--- | :--- || [RUST_190_COMPREHENSIVE_MINDMAP.md](../rust_190_comprehensive_mindmap.md)       | 综合思维导图 |
| [COMPREHENSIVE_DOCUMENTATION_INDEX.md](../comprehensive_documentation_index.md) | 文档总索引   |

---

## 📊 统计数据

- **核心文档**: 5 篇
- **现有参考**: 8 篇
- **总行数**: ~4,600 行
- **代码示例**: 350+ 个
- **性能表格**: 40+ 个
- **覆盖协议**: 20+ 种

---

**返回**: [Tier 2](../tier_02_guides/README.md) | **下一步**: [Tier 4](../tier_04_advanced/README.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
