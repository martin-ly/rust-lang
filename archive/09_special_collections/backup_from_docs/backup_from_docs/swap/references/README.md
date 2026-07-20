# 参考文档 (References)

本目录包含API参考、文档标准、最佳实践等参考资料。

## 📋 目录

### API参考

- [API_DOCUMENTATION.md](API_DOCUMENTATION.md) - 完整的API参考文档
  - 核心API
  - 协议API
  - 性能API
  - 安全API
  - 测试API

### 文档规范

- [DOCUMENTATION_STANDARDS.md](DOCUMENTATION_STANDARDS.md) - 文档标准和规范
- [DOCUMENTATION_STYLE_GUIDE.md](DOCUMENTATION_STYLE_GUIDE.md) - 文档风格指南
- [STYLE.md](STYLE.md) - 代码和文档风格约定

### 最佳实践

- [BEST_PRACTICES.md](BEST_PRACTICES.md) - 最佳实践指南
  - 代码质量
  - 性能优化
  - 安全实践
  - 错误处理
  - 测试策略
  - 部署运维

### 参考资料

- [Glossary.md](Glossary.md) - 术语表
- [FAQ.md](FAQ.md) - 常见问题解答

## 🎯 使用指南

### 查找API

使用 [API_DOCUMENTATION.md](API_DOCUMENTATION.md) 查找具体的API使用方法：

```rust
// 查找网络连接API
use c10_networks::socket::TcpStream;

// 查找HTTP客户端API
use c10_networks::protocol::http::HttpClient;
```

### 遵循规范

在编写代码和文档时，请参考：

- **代码风格**: [STYLE.md](STYLE.md)
- **最佳实践**: [BEST_PRACTICES.md](BEST_PRACTICES.md)
- **文档标准**: [DOCUMENTATION_STANDARDS.md](DOCUMENTATION_STANDARDS.md)

### 解决问题

遇到问题时的查找顺序：

1. **快速查找**: [Glossary.md](Glossary.md) - 理解术语
2. **常见问题**: [FAQ.md](FAQ.md) - 找到解决方案
3. **深入学习**: [BEST_PRACTICES.md](BEST_PRACTICES.md) - 了解最佳实践

## 📚 相关文档

- [实践指南](../guides/) - 详细的使用指南
- [理论文档](../theory/) - 理论基础
- [教程文档](../tutorials/) - 学习教程

## 🔍 快速索引

### 按主题查找

- **网络连接**: API_DOCUMENTATION.md → 核心API → 网络连接
- **错误处理**: BEST_PRACTICES.md → 错误处理
- **性能优化**: BEST_PRACTICES.md → 性能优化
- **安全实践**: BEST_PRACTICES.md → 安全实践

### 按场景查找

- **开始新项目**: STYLE.md + BEST_PRACTICES.md
- **性能调优**: BEST_PRACTICES.md → 性能优化章节
- **安全加固**: BEST_PRACTICES.md → 安全实践章节
- **编写文档**: DOCUMENTATION_STANDARDS.md

## 📊 文档质量

所有参考文档都经过：

- ✅ 技术审查
- ✅ 代码验证
- ✅ 示例测试
- ✅ 定期更新

---

*最后更新: 2025-10-19*  
*维护者: C10 Networks 开发团队*
