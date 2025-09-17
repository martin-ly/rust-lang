# Rust 建模与形式方法文档中心

## 📋 模块概述

c18_model 是一个聚焦核心建模技术的 Rust 实现库，涵盖排队论、机器学习、形式化方法、数学建模与性能模型。项目采用最小稳定内核设计，便于学习与集成，同时提供完整的理论背景和实践指导。

## 🚀 核心特性

### 系统建模

- **排队论模型** - M/M/1、M/M/c、M/G/1 等经典排队模型
- **性能模型** - 系统性能分析和预测模型
- **可靠性模型** - 系统可靠性和可用性建模
- **容量规划** - 基于历史数据的容量规划模型

### 形式化方法

- **有限状态机** - 完整的状态机建模和验证
- **Kripke 结构** - 模态逻辑的语义结构
- **时序逻辑** - LTL/CTL 时序逻辑支持
- **模型检查** - 自动化的模型验证和检查

### 机器学习模型

- **线性回归** - 经典线性回归算法
- **逻辑回归** - 分类问题的逻辑回归
- **决策树** - 决策树算法实现
- **聚类算法** - K-means 等聚类算法

### 数学建模

- **概率模型** - 概率分布和随机过程
- **统计模型** - 统计分析和推断
- **优化模型** - 线性规划和整数规划
- **图论模型** - 图算法和网络分析

## 📚 文档导航

### 总览与导航

- [文档索引](./README.md) - 本文档中心
- [文档总览](./SUMMARY.md) - 完整的文档结构概览

### 入门与指南

- [入门指南总览](./getting-started/README.md) - 快速入门指导
- [安装指南](./getting-started/installation.md) - 环境配置和依赖安装
- [快速开始](./getting-started/quick-start.md) - 10 分钟内运行首个模型

### 专题目录

- [形式化方法](./formal/README.md) - 形式化方法理论和实践
- [并发模型](./concurrency/README.md) - 并发和异步模型
- [架构设计](./architecture/README.md) - 系统架构设计模式
- [设计模式](./patterns/README.md) - 建模相关的设计模式
- [领域建模](./domain/README.md) - 特定领域的建模方法
- [IoT 建模](./iot/README.md) - 物联网系统建模
- [使用指南](./guides/README.md) - 详细的使用指南
- [开发指南](./development/README.md) - 开发和贡献指南

### API 参考

- [API 参考总目录](./api-reference/README.md) - API 文档导航
- [形式化模型 API](./api-reference/formal-models.md) - 形式化方法相关 API
- [机器学习模型 API](./api-reference/ml-models.md) - 机器学习相关 API
- [排队论模型 API](./api-reference/queueing-models.md) - 排队论相关 API

### 源码与示例

- [示例目录](./examples/README.md) - 完整的示例代码
- [源码实现](../src/) - 核心实现代码

## 🎯 快速开始

### 1. 环境准备

```bash
# 确保 Rust 1.70+ 已安装
rustc --version

# 克隆项目（如果尚未克隆）
git clone <repository-url>
cd rust-lang/crates/c18_model
```

### 2. 编译检查

```bash
# 编译检查
cargo check -p c18_model
```

### 3. 运行示例

```bash
# 系统建模示例
cargo run -p c18_model --example system_modeling_examples

# 机器学习示例
cargo run -p c18_model --example machine_learning_examples

# 形式化方法示例
cargo run -p c18_model --example formal_methods_examples
```

### 4. 运行测试

```bash
# 运行所有测试
cargo test -p c18_model

# 运行特定模块测试
cargo test -p c18_model queueing
cargo test -p c18_model formal
cargo test -p c18_model machine_learning
```

## 🏗️ 项目结构

```text
c18_model/
├── src/
│   ├── lib.rs                    # 主库文件
│   ├── types.rs                  # 核心类型定义
│   ├── queueing/                 # 排队论模型
│   │   ├── mm1_queue.rs         # M/M/1 排队模型
│   │   ├── mmc_queue.rs         # M/M/c 排队模型
│   │   └── mg1_queue.rs         # M/G/1 排队模型
│   ├── formal/                   # 形式化方法
│   │   ├── fsm.rs               # 有限状态机
│   │   ├── kripke.rs            # Kripke 结构
│   │   ├── temporal_logic.rs    # 时序逻辑
│   │   └── model_checking.rs    # 模型检查
│   ├── machine_learning/         # 机器学习
│   │   ├── linear_regression.rs # 线性回归
│   │   ├── logistic_regression.rs # 逻辑回归
│   │   ├── decision_tree.rs     # 决策树
│   │   └── clustering.rs        # 聚类算法
│   ├── mathematical/             # 数学建模
│   │   ├── probability.rs       # 概率模型
│   │   ├── statistics.rs        # 统计模型
│   │   ├── optimization.rs      # 优化模型
│   │   └── graph_theory.rs      # 图论模型
│   └── utils/                    # 工具函数
│       ├── math.rs              # 数学工具
│       ├── validation.rs        # 验证工具
│       └── serialization.rs     # 序列化工具
├── examples/                     # 示例代码
│   ├── system_modeling_examples.rs
│   ├── machine_learning_examples.rs
│   └── formal_methods_examples.rs
├── docs/                         # 文档目录
├── tests/                        # 测试代码
├── Cargo.toml                    # 项目配置
└── README.md                     # 项目说明
```

## 🧪 测试与验证

### 运行测试

```bash
# 运行所有测试
cargo test -p c18_model

# 运行特定模块测试
cargo test -p c18_model queueing
cargo test -p c18_model formal
cargo test -p c18_model machine_learning
cargo test -p c18_model mathematical
```

### 运行示例

```bash
# 系统建模示例
cargo run -p c18_model --example system_modeling_examples

# 机器学习示例
cargo run -p c18_model --example machine_learning_examples

# 形式化方法示例
cargo run -p c18_model --example formal_methods_examples
```

### 代码质量检查

```bash
# 代码格式化
cargo fmt -p c18_model

# 代码检查
cargo clippy -p c18_model

# 文档生成
cargo doc -p c18_model --open
```

## 🔬 核心模型

### 排队论模型1

- **M/M/1 队列** - 单服务器指数服务时间队列
- **M/M/c 队列** - 多服务器指数服务时间队列
- **M/G/1 队列** - 单服务器一般服务时间队列
- **G/G/1 队列** - 一般到达和服务时间队列

### 形式化方法1

- **有限状态机** - 状态转换和事件处理
- **Kripke 结构** - 模态逻辑的语义模型
- **时序逻辑** - 线性时序逻辑 (LTL) 和计算树逻辑 (CTL)
- **模型检查** - 自动化的属性验证

### 机器学习模型1

- **线性回归** - 最小二乘法线性回归
- **逻辑回归** - 二分类和多分类逻辑回归
- **决策树** - ID3 和 C4.5 决策树算法
- **聚类算法** - K-means 和层次聚类

### 数学建模1

- **概率分布** - 常见概率分布实现
- **统计推断** - 假设检验和置信区间
- **优化算法** - 线性规划和整数规划
- **图算法** - 最短路径和最小生成树

## 🎓 教育价值

### 学习路径

1. **基础概念** - 从基本建模概念开始
2. **数学基础** - 掌握必要的数学工具
3. **模型实现** - 学习各种模型的实现
4. **实践应用** - 通过实际项目加深理解

### 实践项目

- **系统性能分析** - 使用排队论分析系统性能
- **状态机设计** - 设计并验证复杂状态机
- **数据预测** - 使用机器学习进行数据预测
- **优化问题** - 解决实际的优化问题

### 参考资料

- **理论背景** - 完整的理论背景和证明
- **代码示例** - 详细的代码实现示例
- **最佳实践** - 建模的最佳实践指南
- **工具链** - 相关的工具和库推荐

## 🌟 创新亮点

### 技术创新

- **最小稳定内核** - 去除复杂依赖，聚焦核心功能
- **理论实践结合** - 完整的理论背景和实际实现
- **模块化设计** - 高度模块化和可扩展的架构
- **类型安全** - 充分利用 Rust 的类型系统

### 架构创新

- **清晰分层** - 理论层、实现层、应用层清晰分离
- **可组合性** - 模型可以灵活组合和扩展
- **可验证性** - 内置的模型验证和检查机制
- **可扩展性** - 易于添加新的模型和算法

### 生态创新

- **教育友好** - 专为学习和教育场景设计
- **开源协作** - 开放和协作的开发模式
- **标准兼容** - 遵循相关领域标准和最佳实践
- **社区驱动** - 基于社区反馈的持续改进

## 📞 支持与贡献

### 获取支持

- 问题报告: [GitHub Issues](https://github.com/rust-lang/c18_model/issues)
- 讨论区: [GitHub Discussions](https://github.com/rust-lang/c18_model/discussions)
- 文档: [GitHub Wiki](https://github.com/rust-lang/c18_model/wiki)

### 贡献指南

1. Fork 项目
2. 创建功能分支
3. 编写代码和测试
4. 提交 Pull Request
5. 参与代码审查

### 贡献类型

- 功能开发 - 新模型和算法的实现
- 性能优化 - 性能改进和优化
- 文档完善 - 文档的改进和补充
- 测试增强 - 测试覆盖率的提高
- 理论贡献 - 新的理论方法和证明

## 📄 许可证

本项目采用 MIT 许可证。详见 [LICENSE](LICENSE) 文件。

---

**Rust 建模与形式方法** - 让建模更简单、更安全、更高效！

**Rust Modeling & Formal Methods** - Making modeling simpler, safer, and more efficient!
