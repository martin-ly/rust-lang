# c18_model - Rust理论模型实现库

## 项目概述

c18_model 是一个使用 Rust 语言实现各种理论模型的完整库，专注于提供类型安全、高性能的数学模型实现。本库涵盖了系统建模、机器学习、形式化方法、数学建模等多个领域。

## 核心特性

- **类型安全**：充分利用 Rust 的类型系统确保代码安全性
- **高性能**：使用 Rust 的零成本抽象实现高性能算法
- **内存安全**：所有权系统防止内存泄漏和数据竞争
- **模块化设计**：清晰的模块分离和职责划分
- **完整测试**：87个测试全部通过，确保代码质量

## 主要模块

### 核心模型模块

- **排队论模型** (`queueing_models`)：M/M/1、M/M/c 排队系统，性能分析
- **机器学习模型** (`ml_models`)：线性回归、逻辑回归、KMeans聚类、决策树
- **形式化方法模型** (`formal_models`)：有限状态机、时序逻辑、进程代数
- **数学模型** (`math_models`)：概率分布、统计工具、数值积分、优化算法
- **性能分析模型** (`performance_models`)：负载生成、容量规划、性能预测

### 基础设施模块

- **配置管理** (`config`)：统一的配置管理和验证
- **错误处理** (`error`)：统一的错误处理机制
- **工具函数** (`utils`)：数学计算、数据处理、验证工具
- **可视化** (`visualization`)：图表生成、数据导出
- **基准测试** (`benchmarks`)：性能基准测试

### 标准和合规性模块

- **标准合规性** (`standards_compliance`)：ISO/IEC、IEEE 标准支持
- **大学课程对标** (`university_course_alignment`)：世界知名大学课程对齐
- **成熟度模型** (`maturity_models`)：CMMI、TMMi 等成熟度评估
- **企业架构框架** (`enterprise_frameworks`)：TOGAF、Zachman 等框架支持

## 快速开始

### 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c18_model = "0.2.0"
```

### 基本使用

```rust
use c18_model::{MM1Queue, LinearRegression, FiniteStateMachine, ModelConfig};

// 排队论模型
let queue = MM1Queue::new(1.0, 2.0);
println!("利用率: {:.2}%", queue.utilization() * 100.0);

// 机器学习模型
let mut model = LinearRegression::new(0.01, 1000);
// model.fit(&x, &y)?;

// 形式化方法
let mut fsm = FiniteStateMachine::new("idle".to_string());
// fsm.add_state(State::new("working".to_string()));

// 配置管理
let config = ModelConfig::default();
println!("{}", config.to_json()?);
```

## 文档结构

- [入门指南](getting-started/) - 安装、配置和基本使用
- [API 参考](api-reference/) - 完整的 API 文档
- [使用指南](guides/) - 详细的使用教程和最佳实践
- [示例代码](examples/) - 丰富的使用示例
- [开发文档](development/) - 贡献指南和架构说明

## 运行示例

```bash
# 系统建模示例
cargo run --example system_modeling_examples

# 机器学习示例
cargo run --example machine_learning_examples

# 形式化方法示例
cargo run --example formal_methods_examples
```

## 运行测试

```bash
# 运行所有测试
cargo test

# 运行库测试
cargo test --lib

# 运行基准测试
cargo bench
```

## 项目状态

- **测试状态**：✅ 87个测试全部通过
- **示例状态**：✅ 所有示例可正常运行
- **文档状态**：✅ 完整的API文档和示例
- **质量状态**：✅ 符合Rust最佳实践

## 贡献

欢迎贡献代码、文档和示例！请查看 [开发文档](development/) 了解如何参与项目开发。

## 许可证

本项目采用 MIT 或 Apache-2.0 双许可证。

## 联系方式

如有问题或建议，请通过以下方式联系：

- 提交 Issue
- 发送邮件
- 参与讨论

---

**版本**：0.2.0  
**最后更新**：2025年1月  
**Rust 版本要求**：≥ 1.70
