# 示例代码集合

> **完整的代码示例**，展示 c12_model 的实际使用

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

---

## 📋 示例列表

### 🎯 综合示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `comprehensive_model_showcase.rs` | 综合模型展示 | `cargo run --example comprehensive_model_showcase` |
| `model_rust_190_features_demo.rs` | Rust 1.90 特性演示 | `cargo run --example model_rust_190_features_demo` |

### ⚡ 并发模型示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `concurrency_models.rs` | 并发模型基础 | `cargo run --example concurrency_models` |
| `async_backpressure_demo.rs` | 异步背压控制 | `cargo run --example async_backpressure_demo` |
| `async_recursion_examples.rs` | 异步递归示例 | `cargo run --example async_recursion_examples` |

### 🌐 分布式系统示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `distributed_consensus.rs` | 分布式共识算法 | `cargo run --example distributed_consensus` |
| `raft_demo.rs` | Raft 共识演示 | `cargo run --example raft_demo` |

### 🏗️ 架构设计示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `architecture_patterns.rs` | 架构模式示例 | `cargo run --example architecture_patterns` |
| `microservices_demo.rs` | 微服务示例 | `cargo run --example microservices_demo` |
| `tower_reliability.rs` | Tower 可靠性 | `cargo run --example tower_reliability` |

### 🔬 形式化方法示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `formal_methods_examples.rs` | 形式化方法示例 | `cargo run --example formal_methods_examples` |
| `semantic_models_demo.rs` | 语义模型演示 | `cargo run --example semantic_models_demo` |

### 🤖 机器学习示例

| 示例 | 说明 | 运行命令 |
|------|------|---------|
| `machine_learning_examples.rs` | 机器学习基础 | `cargo run --example machine_learning_examples` |
| `rust_190_modern_ml_demo.rs` | Rust 1.90 ML 演示 | `cargo run --example rust_190_modern_ml_demo` |

---

## 🚀 快速开始

### 运行单个示例

```bash
# 基础示例
cargo run -p c12_model --example concurrency_models

# 带特性的示例
cargo run -p c12_model --example async_backpressure_demo --features tokio-adapter

# 释放模式运行
cargo run -p c12_model --example comprehensive_model_showcase --release
```

### 查看示例源码

```bash
# 查看示例代码
cat examples/concurrency_models.rs

# 使用编辑器打开
code examples/machine_learning_examples.rs
```

### 运行所有示例

```bash
# 编译所有示例
cargo build -p c12_model --examples

# 依次运行所有示例（需要脚本）
for example in examples/*.rs; do
    name=$(basename "$example" .rs)
    echo "Running: $name"
    cargo run -p c12_model --example "$name"
done
```

---

## 📚 示例分类

### 按难度分类

#### 🌟 初级示例

适合初学者，展示基本用法：

- `concurrency_models.rs` - 并发模型基础
- `architecture_patterns.rs` - 架构模式
- `machine_learning_examples.rs` - ML 基础

#### 🎓 中级示例

适合有一定基础的开发者：

- `async_backpressure_demo.rs` - 背压控制
- `distributed_consensus.rs` - 分布式共识
- `tower_reliability.rs` - 可靠性模式

#### 🔬 高级示例

适合高级开发者和研究者：

- `formal_methods_examples.rs` - 形式化方法
- `semantic_models_demo.rs` - 语义模型
- `rust_190_modern_ml_demo.rs` - 现代 ML 集成

### 按主题分类

#### 并发与异步

- Actor 模型示例
- CSP 模型示例
- 异步递归
- 背压控制
- 结构化并发

#### 分布式系统

- Raft 共识算法
- 分布式快照
- 向量时钟
- 2PC/3PC 示例

#### 架构设计

- 分层架构
- 六边形架构
- 事件驱动架构
- 微服务模式

#### 形式化方法

- 操作语义示例
- 指称语义示例
- 状态机验证

---

## 💡 使用建议

### 学习路径

1. **入门阶段**
   - 先运行综合示例 `comprehensive_model_showcase.rs`
   - 了解项目整体功能
   - 查看基础示例代码

2. **深入学习**
   - 选择感兴趣的主题
   - 运行相关示例
   - 阅读示例源码
   - 修改参数观察效果

3. **实践应用**
   - 基于示例创建自己的项目
   - 参考示例解决实际问题
   - 结合文档深入理解

### 最佳实践

1. **阅读代码**
   - 仔细阅读示例代码注释
   - 理解每个步骤的作用
   - 注意错误处理方式

2. **动手实验**
   - 修改参数观察结果
   - 尝试不同的配置
   - 添加日志输出

3. **结合文档**
   - 参考相关文档理解原理
   - 查看 API 文档了解细节
   - 阅读理论背景

---

## 🔧 示例特性

### 特性标志

某些示例需要启用特定特性：

```toml
# 异步相关示例
tokio-adapter = []
tower-examples = []

# ML 相关示例
ml-integration = []
pytorch-support = []

# 测试相关
loom-tests = []
```

### 运行带特性的示例

```bash
# Tokio 适配器
cargo run -p c12_model --example async_backpressure_demo --features tokio-adapter

# Tower 示例
cargo run -p c12_model --example tower_reliability --features tower-examples

# ML 集成
cargo run -p c12_model --example rust_190_modern_ml_demo --features ml-integration
```

---

## 📖 示例详解

### comprehensive_model_showcase.rs

**功能**: 综合展示项目的主要功能

**包含内容**:

- 并发模型演示
- 分布式系统示例
- 架构模式展示
- 形式化方法应用

**适合人群**: 所有用户，特别是初次接触项目的开发者

### async_backpressure_demo.rs

**功能**: 演示异步背压控制机制

**包含内容**:

- Token Bucket 算法
- Leaky Bucket 算法
- Sliding Window
- 自适应限流

**适合人群**: 中高级开发者，关注性能和流量控制

### formal_methods_examples.rs

**功能**: 形式化方法的实际应用

**包含内容**:

- 操作语义示例
- 指称语义示例
- 公理语义应用
- 状态机验证

**适合人群**: 研究者，形式化验证工程师

---

## 🐛 故障排除

### 编译错误

```bash
# 清理并重新编译
cargo clean -p c12_model
cargo build -p c12_model --examples

# 检查依赖
cargo check -p c12_model
```

### 运行错误

```bash
# 查看详细错误信息
RUST_BACKTRACE=1 cargo run -p c12_model --example your_example

# 使用调试模式
RUST_LOG=debug cargo run -p c12_model --example your_example
```

### 特性缺失

```bash
# 列出所有特性
cargo metadata --format-version 1 | jq '.packages[] | select(.name == "c12_model") | .features'

# 启用所有特性
cargo run -p c12_model --example your_example --all-features
```

---

## 📝 贡献示例

欢迎贡献新的示例！

### 示例要求

1. **代码质量**
   - 遵循 Rust 最佳实践
   - 包含充分的注释
   - 错误处理完善

2. **文档完整**
   - 说明示例目的
   - 列出依赖特性
   - 提供运行说明

3. **可运行性**
   - 确保示例可以编译
   - 测试运行结果
   - 更新本 README

### 提交流程

1. 创建示例文件 `examples/your_example.rs`
2. 添加必要的注释和文档
3. 测试示例运行
4. 更新本 README
5. 提交 Pull Request

参考 [贡献指南](../development/contributing.md) 了解更多。

---

## 🔗 相关资源

### 文档

- [使用指南](../guides/) - 详细的使用文档
- [API 参考](../api/) - API 文档
- [教程](../tutorials/) - 分步教程

### 源码

- [examples/](../../examples/) - 示例源码目录
- [src/](../../src/) - 库源码
- [tests/](../../tests/) - 测试代码

### 外部资源

- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)

---

**示例维护**: 项目维护团队  
**最后更新**: 2025-10-19  
**反馈**: [GitHub Issues](https://github.com/rust-lang/rust-lang/issues)

---

**开始探索**: 选择一个示例运行，开始你的学习之旅！ 🚀
