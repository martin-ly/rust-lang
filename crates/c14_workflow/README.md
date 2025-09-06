# Rust 工作流系统 (Rust Workflow System)

[![Rust Version](https://img.shields.io/badge/rust-1.89+-blue.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/c14_workflow.svg)](https://crates.io/crates/c14_workflow)

一个基于 Rust 1.89 特性的高级工作流系统，集成了二十多个设计模式和完整的中间件支持。

An advanced workflow system based on Rust 1.89 features, integrating over twenty design patterns and complete middleware support.

## 🚀 特性 (Features)

### Rust 1.89 语言特性集成 (Rust 1.89 Language Features Integration)

- **生命周期语法检查改进** - 更严格的生命周期标注和检查
- **常量泛型推断** - 支持 `_` 占位符的常量泛型推断
- **跨平台文档测试** - 真正的跨平台文档测试支持
- **FFI 改进** - `i128`/`u128` 类型在 `extern "C"` 中的安全使用
- **API 稳定化** - `Result::flatten` 等实用 API 的稳定化

### 工作流设计模式 (Workflow Design Patterns)

- **创建型模式** (Creational Patterns)
  - 建造者模式 (Builder Pattern)
  - 工厂模式 (Factory Pattern)
  - 原型模式 (Prototype Pattern)
  - 单例模式 (Singleton Pattern)

- **结构型模式** (Structural Patterns)
  - 适配器模式 (Adapter Pattern)
  - 桥接模式 (Bridge Pattern)
  - 组合模式 (Composite Pattern)
  - 装饰器模式 (Decorator Pattern)
  - 外观模式 (Facade Pattern)
  - 享元模式 (Flyweight Pattern)
  - 代理模式 (Proxy Pattern)

- **行为型模式** (Behavioral Patterns)
  - 责任链模式 (Chain of Responsibility Pattern)
  - 命令模式 (Command Pattern)
  - 解释器模式 (Interpreter Pattern)
  - 迭代器模式 (Iterator Pattern)
  - 中介者模式 (Mediator Pattern)
  - 备忘录模式 (Memento Pattern)
  - 观察者模式 (Observer Pattern)
  - 状态模式 (State Pattern)
  - 策略模式 (Strategy Pattern)
  - 模板方法模式 (Template Method Pattern)
  - 访问者模式 (Visitor Pattern)

- **并发模式** (Concurrent Patterns)
  - Actor 模式 (Actor Pattern)
  - 生产者-消费者模式 (Producer-Consumer Pattern)
  - 管道模式 (Pipeline Pattern)
  - 反应器模式 (Reactor Pattern)
  - 线程池模式 (Thread Pool Pattern)

### 工作流中间件系统 (Workflow Middleware System)

- **核心中间件** (Core Middleware)
  - 认证中间件 (Authentication Middleware)
  - 授权中间件 (Authorization Middleware)
  - 日志中间件 (Logging Middleware)
  - 监控中间件 (Monitoring Middleware)
  - 限流中间件 (Rate Limiting Middleware)

- **扩展中间件** (Extension Middleware)
  - 缓存中间件 (Caching Middleware)
  - 压缩中间件 (Compression Middleware)
  - 加密中间件 (Encryption Middleware)
  - 重试中间件 (Retry Middleware)
  - 超时中间件 (Timeout Middleware)

- **插件中间件** (Plugin Middleware)
  - 自定义插件支持 (Custom Plugin Support)
  - 动态加载 (Dynamic Loading)
  - 插件生命周期管理 (Plugin Lifecycle Management)

## 📦 安装 (Installation)

在 `Cargo.toml` 中添加依赖：

Add to your `Cargo.toml`:

```toml
[dependencies]
c14_workflow = { version = "1.0.0", features = ["full"] }
```

### 特性选项 (Feature Options)

```toml
[dependencies]
c14_workflow = { version = "1.0.0", features = ["rust189", "patterns", "middleware"] }
```

- `rust189` - 启用 Rust 1.89 特性支持
- `patterns` - 启用设计模式支持
- `middleware` - 启用中间件系统
- `monitoring` - 启用监控功能
- `persistence` - 启用持久化支持
- `full` - 启用所有特性

## 🎯 快速开始 (Quick Start)

### 基础工作流 (Basic Workflow)

```rust
use c14_workflow::*;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建工作流引擎 / Create workflow engine
    let engine = WorkflowEngine::new();
    
    // 定义工作流 / Define workflow
    let definition = WorkflowDefinition {
        name: "order_processing".to_string(),
        description: Some("订单处理工作流 / Order processing workflow".to_string()),
        version: "1.0.0".to_string(),
        states: vec![
            "pending".to_string(),
            "processing".to_string(),
            "completed".to_string(),
        ],
        transitions: vec![
            StateTransition {
                from_state: "pending".to_string(),
                to_state: "processing".to_string(),
                condition: Some("start_processing".to_string()),
                action: Some("begin_processing".to_string()),
                metadata: json!({}),
            },
            StateTransition {
                from_state: "processing".to_string(),
                to_state: "completed".to_string(),
                condition: Some("processing_done".to_string()),
                action: Some("complete_processing".to_string()),
                metadata: json!({}),
            },
        ],
        initial_state: "pending".to_string(),
        final_states: vec!["completed".to_string()],
        metadata: json!({}),
    };
    
    // 注册工作流 / Register workflow
    engine.register_workflow("order_processing".to_string(), definition).await?;
    
    // 创建初始数据 / Create initial data
    let initial_data = WorkflowData {
        id: "order_123".to_string(),
        data: json!({
            "order_id": "12345",
            "customer_id": "67890",
            "amount": 100.0
        }),
        metadata: json!({}),
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };
    
    // 启动工作流实例 / Start workflow instance
    let instance_id = engine.start_workflow("order_processing", initial_data).await?;
    println!("工作流实例已启动 / Workflow instance started: {}", instance_id);
    
    Ok(())
}
```

### 使用设计模式 (Using Design Patterns)

```rust
use c14_workflow::patterns::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();
    
    // 获取所有可用模式 / Get all available patterns
    let patterns = factory.get_all_patterns();
    
    for pattern_info in patterns {
        println!("模式 / Pattern: {} - {}", pattern_info.name, pattern_info.description);
    }
    
    // 使用特定模式 / Use specific pattern
    let builder_pattern = factory.create_pattern("WorkflowBuilder", PatternCategory::Creational);
    if let Some(pattern) = builder_pattern {
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({"test": "data"}),
            metadata: std::collections::HashMap::new(),
        };
        
        let result = pattern.apply(&context)?;
        println!("模式应用结果 / Pattern application result: {:?}", result);
    }
    
    Ok(())
}
```

### 使用中间件 (Using Middleware)

```rust
use c14_workflow::middleware::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();
    
    // 注册中间件 / Register middleware
    manager.register_middleware(Box::new(
        core::AuthenticationMiddleware::new()
    )).await?;
    
    manager.register_middleware(Box::new(
        core::LoggingMiddleware::new()
    )).await?;
    
    // 创建中间件上下文 / Create middleware context
    let context = MiddlewareContext::new(
        "req_1".to_string(),
        "workflow_1".to_string(),
        json!({"test": "data"})
    );
    
    // 创建中间件链 / Create middleware chain
    let mut chain = manager.create_chain(context).await?;
    
    // 执行中间件链 / Execute middleware chain
    let result = chain.execute().await?;
    println!("中间件执行结果 / Middleware execution result: {:?}", result);
    
    Ok(())
}
```

## 🏗️ 项目结构 (Project Structure)

```text
c14_workflow/
├── src/
│   ├── lib.rs                 # 主库文件 / Main library file
│   ├── types.rs              # 核心类型定义 / Core type definitions
│   ├── engine.rs             # 工作流引擎 / Workflow engine
│   ├── state.rs              # 状态管理 / State management
│   ├── error.rs              # 错误处理 / Error handling
│   ├── tools.rs              # 工具函数 / Utility functions
│   ├── rust189/              # Rust 1.89 特性 / Rust 1.89 features
│   │   ├── mod.rs
│   │   ├── features.rs
│   │   ├── async_features.rs
│   │   └── ...
│   ├── patterns/             # 设计模式 / Design patterns
│   │   ├── mod.rs
│   │   ├── creational/
│   │   ├── structural/
│   │   ├── behavioral/
│   │   └── concurrent/
│   ├── middleware/           # 中间件系统 / Middleware system
│   │   ├── mod.rs
│   │   ├── core/
│   │   ├── extensions/
│   │   └── plugins/
│   ├── examples/             # 示例代码 / Example code
│   │   ├── mod.rs
│   │   ├── basic_workflow.rs
│   │   ├── rust189_examples.rs
│   │   ├── pattern_examples.rs
│   │   └── middleware_examples.rs
│   └── tests/                # 测试代码 / Test code
├── docs/                     # 文档 / Documentation
├── examples/                 # 独立示例 / Standalone examples
├── benches/                  # 基准测试 / Benchmarks
├── Cargo.toml               # 项目配置 / Project configuration
└── README.md                # 项目说明 / Project description
```

## 📚 文档 (Documentation)

- [API 文档 / API Documentation](https://docs.rs/c14_workflow)
- [设计模式指南 / Design Patterns Guide](docs/patterns/)
- [中间件开发指南 / Middleware Development Guide](docs/middleware/)
- [Rust 1.89 特性使用指南 / Rust 1.89 Features Usage Guide](docs/rust189/)

## 🧪 测试 (Testing)

运行所有测试：

Run all tests:

```bash
cargo test
```

运行特定模块测试：

Run specific module tests:

```bash
cargo test patterns
cargo test middleware
cargo test rust189
```

运行示例：

Run examples:

```bash
cargo run --example basic_workflow
cargo run --example pattern_usage
cargo run --example middleware_usage
```

## 📊 基准测试 (Benchmarks)

运行基准测试：

Run benchmarks:

```bash
cargo bench
```

## 🤝 贡献 (Contributing)

我们欢迎贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解详细信息。

We welcome contributions! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for details.

## 📄 许可证 (License)

本项目采用 MIT 许可证。详见 [LICENSE](LICENSE) 文件。

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

## 🙏 致谢 (Acknowledgments)

- Rust 社区 / Rust Community
- 工作流引擎设计模式 / Workflow Engine Design Patterns
- 异步编程最佳实践 / Async Programming Best Practices

## 📞 支持 (Support)

- 问题报告 / Issue Reports: [GitHub Issues](https://github.com/rust-lang/c14_workflow/issues)
- 讨论 / Discussions: [GitHub Discussions](https://github.com/rust-lang/c14_workflow/discussions)
- 文档 / Documentation: [GitHub Wiki](https://github.com/rust-lang/c14_workflow/wiki)

---

**Rust 工作流系统** - 让工作流开发更简单、更安全、更高效！

**Rust Workflow System** - Making workflow development simpler, safer, and more efficient!
