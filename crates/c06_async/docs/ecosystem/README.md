# 生态系统 (Ecosystem)

本目录包含Rust异步生态系统的综合分析、语言特性更新和形式化方法。

## 📚 文档列表

- **[01_ecosystem_analysis_2025.md](./01_ecosystem_analysis_2025.md)** ⭐⭐⭐⭐⭐  
  2025年Rust异步生态系统全面分析（合并了多个生态分析文档）

- **[02_language_features_190.md](./02_language_features_190.md)** ⭐⭐⭐⭐  
  Rust 1.90及后续版本的异步语言特性

- **[03_formal_methods.md](./03_formal_methods.md)** ⭐⭐⭐  
  异步编程的形式化验证方法

## 🌐 生态系统概览

### 运行时
- **Tokio** - 生产首选
- **async-std** - 学习友好
- **Smol** - 轻量极简

### Web框架
- **Axum** - 现代化、类型安全
- **Actix-web** - 高性能
- **Rocket** - 易用性强

### 网络库
- **hyper** - HTTP核心
- **tonic** - gRPC
- **quinn** - QUIC

### 工具
- **tokio-console** - 运行时监控
- **criterion** - 性能测试
- **tracing** - 分布式追踪

## 📈 最新特性

### Rust 1.75+
- ✅ async fn in traits
- ✅ RPITIT支持

### Rust 1.80+
- ✅ 改进的错误信息
- ✅ 更好的IDE支持

### 未来展望
- 🔮 async closures
- 🔮 async drop
- 🔮 更好的生成器支持

## 🔗 相关资源

- [../runtimes/](../runtimes/) - 运行时详细对比
- [../comprehensive/](../comprehensive/) - 综合指南

**最后更新**: 2025-10-19

