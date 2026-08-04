# Rust 异步生态系统文档

## 概述

本文档提供了Rust异步编程生态系统的全面指南，包括std、smol、async-std、tokio等主要库的详细分析、使用示例和最佳实践。

## 目录

- [快速开始](quick_start.md)
- [核心概念](core_concepts.md)
- [运行时对比](runtime_comparison.md)
- [集成框架](integration_framework.md)
- [性能优化](performance_optimization.md)
- [最佳实践](best_practices.md)
- [API参考](api_reference.md)
- [示例代码](examples.md)
- [故障排除](troubleshooting.md)

## 核心库

### std - 标准库异步支持

- 基础异步编程支持
- Future trait 和 async/await 语法
- 跨平台兼容性

### tokio - 高性能异步运行时

- 生产级异步运行时
- 丰富的生态系统
- 高性能网络编程

### async-std - 标准库风格API

- 易用性优先设计
- 标准库风格API
- 快速开发体验

### smol - 轻量级异步运行时

- 极简设计（约1500行代码）
- 嵌入式友好
- 快速启动

## 快速开始

### 安装依赖

```toml
[dependencies]
tokio = { version = "1.40", features = ["full"] }
futures = "0.3"
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
```

### 基本使用

```rust
use tokio::time::sleep;
use std::time::Duration;

#[tokio::main]
async fn main() {
    println!("Hello, async world!");
    
    sleep(Duration::from_secs(1)).await;
    
    println!("Async operation completed!");
}
```

## 特性

- ✅ 全面的异步运行时分析
- ✅ 性能基准测试
- ✅ 集成框架支持
- ✅ 异步同步转换
- ✅ 聚合组合设计模式
- ✅ 完整的测试套件
- ✅ 详细的文档和示例

## 贡献

欢迎贡献代码、文档和示例！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解详细信息。

## 许可证

本项目采用 MIT 许可证。详情请查看 [LICENSE](LICENSE) 文件。
