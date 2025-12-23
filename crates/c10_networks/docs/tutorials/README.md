# 教程文档 (Tutorials)

本目录包含从入门到精通的完整教程和示例代码。

## 📋 目录

### 快速入门

- [QUICK_START.md](QUICK_START.md) - 5分钟快速上手指南
  - 环境准备
  - 第一个网络程序
  - 基本概念

### 综合教程

- [COMPREHENSIVE_TUTORIAL_GUIDE.md](COMPREHENSIVE_TUTORIAL_GUIDE.md) - 完整的学习路径
  - 第一阶段：基础入门
  - 第二阶段：协议实现
  - 第三阶段：高级特性
  - 第四阶段：实际应用
  - 第五阶段：安全实践
  - 第六阶段：测试与验证

### 主题教程

- [TUTORIALS.md](TUTORIALS.md) - 各种主题的教程集合
  - TCP/UDP编程
  - HTTP客户端
  - WebSocket通信
  - 异步编程
  - 性能优化

### 示例代码

- [EXAMPLES_GUIDE.md](EXAMPLES_GUIDE.md) - 示例代码使用指南
- [EXAMPLES_AND_APPLICATIONS_ENHANCED.md](EXAMPLES_AND_APPLICATIONS_ENHANCED.md) - 示例代码与应用场景增强版
  - 基础示例
  - 高级示例
  - 实际应用场景
  - 性能优化示例
  - 安全示例
  - 测试示例

## 🎯 学习路径

### 🚀 初学者路径 (1-2周)

**目标**: 掌握基础网络编程概念和TCP/UDP通信

1. **快速开始**: [QUICK_START.md](QUICK_START.md)
2. **基础教程**: [TUTORIALS.md](TUTORIALS.md) - TCP/UDP章节
3. **实践练习**: 运行 `examples/tcp_*.rs` 和 `examples/udp_*.rs`
4. **巩固**: 完成教程中的练习题

**学习成果**:

- ✅ 能够创建TCP服务器和客户端
- ✅ 理解UDP通信特点
- ✅ 掌握基本的错误处理

### 🎓 中级路径 (3-4周)

**目标**: 掌握HTTP/WebSocket/DNS等高级协议

1. **协议学习**: [COMPREHENSIVE_TUTORIAL_GUIDE.md](COMPREHENSIVE_TUTORIAL_GUIDE.md) - 第二阶段
2. **示例分析**: [EXAMPLES_GUIDE.md](EXAMPLES_GUIDE.md)
3. **实战项目**: 构建一个简单的Web服务或聊天应用
4. **性能优化**: 学习异步编程和连接池

**学习成果**:

- ✅ 熟练使用HTTP客户端
- ✅ 实现WebSocket实时通信
- ✅ 理解DNS解析机制
- ✅ 掌握异步编程模式

### 🔬 高级路径 (5-8周)

**目标**: 深入理解网络编程，能够进行性能优化和安全加固

1. **高级特性**: [COMPREHENSIVE_TUTORIAL_GUIDE.md](COMPREHENSIVE_TUTORIAL_GUIDE.md) - 第三阶段
2. **应用场景**: [EXAMPLES_AND_APPLICATIONS_ENHANCED.md](EXAMPLES_AND_APPLICATIONS_ENHANCED.md)
3. **性能优化**: 学习零拷贝、连接池、负载均衡
4. **安全实践**: TLS加密、身份认证、访问控制
5. **实战项目**: 构建生产级别的网络服务

**学习成果**:

- ✅ 能够设计高性能网络架构
- ✅ 实现安全的网络通信
- ✅ 进行性能调优和故障排查
- ✅ 掌握分布式系统设计

### 🏆 专家路径 (持续学习)

**目标**: 成为网络编程专家，能够解决复杂问题

1. **理论深入**: 阅读 [../theory/](../theory/) 所有文档
2. **源码分析**: 深入研究核心实现
3. **创新实践**: 改进现有实现或设计新协议
4. **知识分享**: 撰写技术博客或教程

## 📚 教程使用建议

### 如何使用教程

1. **顺序学习**: 按照学习路径顺序进行
2. **动手实践**: 每学一个概念都要写代码验证
3. **查阅参考**: 遇到问题查看 [../references/](../references/)
4. **深入理解**: 想要深入理解原理查看 [../theory/](../theory/)

### 示例代码位置

所有可运行的示例代码在项目的 `examples/` 目录：

```bash
# 运行TCP服务器示例
cargo run --example tcp_echo_server

# 运行HTTP客户端示例
cargo run --example http_client

# 运行WebSocket示例
cargo run --example websocket_demo

# 运行DNS解析示例
cargo run --example dns_lookup
```

### 配套资源

- **实践指南**: [../guides/](../guides/) - 详细的使用指南
- **API参考**: [../references/API_DOCUMENTATION.md](../references/API_DOCUMENTATION.md)
- **理论基础**: [../theory/](../theory/) - 深入理解原理

## 🧪 练习项目建议

### 初级项目

1. **TCP Echo服务器**: 实现一个简单的回显服务器
2. **HTTP客户端工具**: 类似curl的命令行工具
3. **UDP聊天室**: 简单的P2P聊天应用

### 中级项目

1. **Web代理服务器**: 实现HTTP代理
2. **WebSocket聊天服务**: 多人实时聊天
3. **DNS缓存服务器**: 本地DNS缓存

### 高级项目

1. **负载均衡器**: 实现简单的负载均衡
2. **API网关**: 微服务API网关
3. **分布式爬虫**: 高性能网络爬虫

## 📞 获取帮助

遇到问题时：

1. **查看FAQ**: [../references/FAQ.md](../references/FAQ.md)
2. **查看术语表**: [../references/Glossary.md](../references/Glossary.md)
3. **查看实践指南**: [../guides/](../guides/)
4. **提交Issue**: GitHub Issues

---

*最后更新: 2025-12-11*
*维护者: C10 Networks 开发团队*
