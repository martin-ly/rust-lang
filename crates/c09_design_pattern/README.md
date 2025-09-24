# Rust 设计模式实践案例库

## 项目概述

本项目是基于Rust 1.90版本（Edition 2024，MSRV 1.90）的完整设计模式实践案例库，对标国际Wiki设计模式标准，提供了GoF 23个经典设计模式以及Rust特有模式的完整实现。

## 特性亮点

### 🚀 Rust 1.90 新特性与生态集成

- **Cell::update 方法（1.89）**：优化单例模式的线程安全实现
- **裸指针 Default（1.89）**：简化代理模式的初始化过程
- **数组/Vec 转换改进（1.89）**：提升享元模式的数据结构性能
- **I/O 句柄 AsFd/AsHandle/AsSocket（1.89/1.90 平台增强）**：改进网络与系统互操作性
- **稳定化改进（1.90）**：与 Edition 2024 协同的诊断/编译期改进，增强泛型推断与 lint 质量（面向开发体验）

### 📚 完整的模式覆盖

- **创建型模式**：单例、工厂、建造者、原型等7个模式
- **结构型模式**：适配器、装饰器、代理、享元等7个模式
- **行为型模式**：观察者、策略、命令、责任链等11个模式
- **并发模式**：异步、消息传递、生产者-消费者等6个子模块
- **并行模式**：数据并行、流水线、工作窃取等5个子模块

### 🛡️ 企业级质量

- **完整的错误处理机制**：统一的错误类型和恢复策略
- **性能基准测试**：使用Criterion框架进行性能监控
- **集成测试**：跨模式协作和并发安全验证
- **内存安全**：零内存泄漏保证

## 快速开始

### 安装依赖

```toml
[dependencies]
c09_design_pattern = "1.0.1"
```

### 基本使用

```rust
use c09_design_pattern::creational::singleton::define::Singleton;
use c09_design_pattern::structural::flyweight::define::*;
use c09_design_pattern::error_handling::*;

fn main() -> Result<(), DesignPatternError> {
    // 使用优化的单例模式
    let singleton = Singleton::new();
    let instance = singleton.get_instance(|| {
        "Hello, Rust Design Patterns!".to_string()
    });
    println!("{}", instance);
    
    // 使用享元模式
    let mut factory = OptimizedFlyweightFactory::new();
    let flyweight = factory.get_flyweight("demo", "Demo State".to_string());
    flyweight.operation("Demo Operation");
    
    // 使用错误处理
    let error_handler = SingletonErrorHandler::new();
    let result = error_handler.create_singleton(|| {
        Ok("Success".to_string())
    })?;
    
    println!("{}", result);
    Ok(())
}
```

### 异步示例

```rust
use c09_design_pattern::{ExecutionModel, get_patterns_by_execution_model};

#[tokio::main]
async fn main() {
    let async_patterns = get_patterns_by_execution_model(ExecutionModel::Async);
    println!("Async patterns: {}", async_patterns.len());

    // 启动一个简单的异步任务
    let handle = tokio::spawn(async {
        tokio::time::sleep(std::time::Duration::from_millis(50)).await;
        "task done"
    });

    let result = handle.await.unwrap();
    assert_eq!(result, "task done");
}
```

#### 限流与超时组合示例

```rust
use c09_design_pattern::concurrency::asynchronous::control::{RateLimiter, run_with_timeout};

#[tokio::main]
async fn main() {
    let limiter = RateLimiter::new(2);

    // 同时只允许2个并发任务，且每个任务有超时保护
    let mut handles = Vec::new();
    for i in 0..5u32 {
        let permit = limiter.acquire().await; // 拿到许可
        handles.push(tokio::spawn(async move {
            let _permit = permit; // 持有期间占用并发额度
            let work = async move {
                tokio::time::sleep(std::time::Duration::from_millis(30)).await;
                format!("job {} done", i)
            };
            run_with_timeout(std::time::Duration::from_millis(50), work).await
        }));
    }

    for h in handles {
        let res = h.await.unwrap();
        assert!(res.is_ok());
    }
}
```

## 模式分类

### 按执行模型分类（同步 vs 异步）

- **同步 (Sync)**：阻塞式执行，适合 CPU 绑定、确定性流程。
- **异步 (Async)**：基于 `async/await` 或事件驱动，适合 IO 绑定与高并发。
- **混合 (Hybrid)**：对外提供同步接口，内部用异步；或反之，通过边界适配器桥接。

示例获取列表：

```rust
use c09_design_pattern::{get_patterns_by_execution_model, ExecutionModel};

let async_patterns = get_patterns_by_execution_model(ExecutionModel::Async);
assert!(async_patterns.iter().any(|p| p.name.contains("Actor") || p.name.contains("Channel")));
```

### 创建型模式 (Creational Patterns)

- **单例模式**：线程安全的全局唯一实例
- **工厂模式**：抽象工厂和工厂方法的完整实现
- **建造者模式**：流式API构建复杂对象
- **原型模式**：高效的对象克隆机制

### 结构型模式 (Structural Patterns)

- **适配器模式**：接口转换和兼容性处理
- **装饰器模式**：动态功能扩展
- **代理模式**：访问控制和延迟加载
- **享元模式**：内存优化的对象共享

### 行为型模式 (Behavioral Patterns)

- **观察者模式**：事件驱动的松耦合通信
- **策略模式**：算法族的封装和切换
- **命令模式**：请求的封装和撤销支持
- **责任链模式**：请求的链式处理

### 并发模式 (Concurrency Patterns)

- **异步模式**：基于async/await的异步编程
- **消息传递**：线程间安全通信
- **生产者-消费者**：高效的任务队列处理

### 并行模式 (Parallel Patterns)

- **数据并行**：大规模数据的高效处理
- **流水线**：任务流水线并行执行
- **工作窃取**：动态负载均衡

## 性能优化

### 基准测试结果

| 模式 | 操作 | 性能 | 内存使用 |
|------|------|------|----------|
| 单例 | 10000次获取 | < 1ms | 零额外分配 |
| 享元 | 1000次创建 | < 10ms | 90%内存节省 |
| 代理 | 1000次请求 | < 20ms | 线性增长 |
| 责任链 | 链式处理 | < 5ms | 常量内存 |

### 运行基准测试

```bash
cargo bench
```

## 测试覆盖

### 单元测试

```bash
cargo test
```

### 集成测试

```bash
cargo test --test integration_tests
```

### 性能测试

```bash
cargo bench
```

## 错误处理

项目提供了完整的错误处理机制：

```rust
use c09_design_pattern::error_handling::*;

// 使用错误处理器
let handler = ErrorHandler::new(RecoveryStrategy::Retry {
    max_attempts: 3,
    delay_ms: 100,
});

let result = handler.handle_error(|| {
    // 可能失败的操作
    Ok("Success")
})?;
```

### 错误类型

- `SingletonError`：单例模式相关错误
- `FactoryError`：工厂模式相关错误
- `ProxyError`：代理模式相关错误
- `FlyweightError`：享元模式相关错误
- `ChainError`：责任链模式相关错误
- `ConcurrencyError`：并发模式相关错误

## 最佳实践

### 1. 单例模式使用

```rust
// 推荐：使用OnceLock确保线程安全
let singleton = Singleton::new();
let instance = singleton.get_instance(|| {
    // 初始化逻辑
    ExpensiveResource::new()
});
```

### 2. 享元模式优化

```rust
// 推荐：使用Arc共享享元对象
let mut factory = OptimizedFlyweightFactory::new();
let flyweight = factory.get_flyweight("key", "state".to_string());
// flyweight可以被多个地方共享使用
```

### 3. 错误处理策略

### 4. 执行模型选型决策树（简版）

```text
是否以 IO 为主？
 ├─ 是 → 是否需要高并发连接？
 │   ├─ 是 → Async（Tokio/async-std）
 │   └─ 否 → Hybrid（对外 Sync，内部 Async）
 └─ 否（以 CPU 为主） → 是否需要跨核并行？
     ├─ 是 → Sync + Rayon（并行迭代/流水线）
     └─ 否 → Sync（简单阻塞 API）
```

配套建议：对外门面保持稳定 Sync API，内部以适配器选择 Async/并行路径；在文档标注执行模型与线程安全性说明。

### 5. tracing 可观测示例（责任链/代理）

```rust
use tracing::{info_span, Instrument};

fn handle_request(input: &str) -> String {
    let span = info_span!("chain", request = input);
    async move {
        // step 1
        let s1 = format!("auth:{}", input);
        // step 2
        let s2 = format!("rate:{}", s1);
        // step 3
        format!("biz:{}", s2)
    }
    .instrument(span)
    .now_or_never()
    .unwrap()
}
```

建议启用 `tracing-subscriber` 并在测试中输出 span，用于观察链路时延与错误传播。

## Features 与运行指南

### 可选特性（features）

- `rayon`：用于对基准中并行路径做条件门控（默认关闭）。
- `tokio-bench`：启用 tokio 异步基准（默认关闭，避免 bench 时自动引入运行时）。
- `obs-tracing`：启用 `examples/tracing_chain.rs` 示例所需的 tracing 依赖。

### 常用命令

```bash
# 运行测试（含执行模型断言）
cargo test | cat

# 运行基准（同步并行）
cargo bench | cat

# 运行 tokio 异步基准
cargo bench --features tokio-bench | cat

# 运行可观测示例（需 obs-tracing）
cargo run --example tracing_chain --features obs-tracing | cat
```

## CI 建议工作流（示例）

> 说明：以下为 GitHub Actions 片段，建议在工作区根目录合并后按需调整。

```yaml
name: CI
on:
  push:
  pull_request:
jobs:
  build:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        toolchain: ["1.90.0", "stable", "beta", "nightly"]
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.toolchain }}
          components: rustfmt, clippy
      - run: cargo fmt --all -- --check
      - run: cargo clippy --all-targets --all-features -- -D warnings
      - run: cargo test --all-features
```

## 文档索引

- 可观测性指南：`docs/observability.md`

```rust
// 推荐：根据场景选择合适的恢复策略
let handler = match criticality {
    Criticality::High => ErrorHandler::new(RecoveryStrategy::Retry {
        max_attempts: 5,
        delay_ms: 1000,
    }),
    Criticality::Low => ErrorHandler::new(RecoveryStrategy::Fallback),
};
```

## 贡献指南

### 开发环境设置

```bash
# 克隆项目
git clone <repository-url>
cd c09_design_pattern

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行基准测试
cargo bench
```

### 代码规范

- 遵循Rust官方编码规范
- 使用rustfmt格式化代码
- 使用clippy进行代码检查
- 确保所有测试通过

### 提交规范

- 使用语义化提交信息
- 每个PR包含相应的测试
- 更新相关文档

## 版本历史

### v1.0.2 (2025-09)

- MSRV 提升至 1.90；对齐 README 与路线图到 Rust 1.90。
- 增补“生态映射与落地”建议清单；完善执行模型文档。
- 兼容性校验 stable 与 1.90，无行为变更。

### v1.0.1 (2025-09)

- 新增执行模型分类（Sync/Async/Hybrid），提供 `get_patterns_by_execution_model`。
- 文档增加“同步 vs 异步”综述与示例；新增相关集成测试。

### v1.0.0 (2025-01)

- 完整的GoF 23个设计模式实现
- Rust 1.89新特性集成
- 性能基准测试框架
- 完整的错误处理机制
- 跨模式集成测试

## 许可证

本项目采用MIT许可证 - 查看[LICENSE](LICENSE)文件了解详情。

## 致谢

- Rust社区提供的优秀工具和文档
- GoF设计模式经典著作的启发
- 所有贡献者的努力和支持

## 联系方式

- 项目主页：GitHub Repository
- 问题反馈：Issues
- 讨论交流：Discussions

---

**注意**：本项目基于Rust 1.89版本开发，建议使用最新稳定版本的Rust编译器以获得最佳体验。
