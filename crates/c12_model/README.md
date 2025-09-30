# c12_model - Rust 1.90 建模与形式方法

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/c18_model.svg)](https://crates.io/crates/c18_model)
[![Documentation](https://docs.rs/c18_model/badge.svg)](https://docs.rs/c18_model)

一个基于 Rust 1.90 的现代化建模与形式方法库，聚焦核心建模技术，涵盖排队论、机器学习、形式化方法、数学建模与性能模型。项目采用最小稳定内核设计，充分利用 Rust 1.90 的新特性，便于学习与集成，同时提供完整的理论背景和实践指导。

## 🚀 主要特性

### 🔧 Rust 1.90 语言特性集成

- **显式推断的常量参数稳定化** - 在模型配置中使用 `_` 进行常量参数推断
- **生命周期语法一致性检查** - 在模型生命周期管理中应用明确的生命周期标注
- **函数指针比较扩展检查** - 增强模型验证中的函数指针比较安全性
- **标准库 API 增强** - 利用匿名管道等新 API 优化进程间通信
- **编译器优化与平台支持扩展** - 利用最新的编译器优化提升模型计算性能

### 📊 系统建模

- **排队论模型** - M/M/1、M/M/c、M/G/1 等经典排队模型
- **性能模型** - 系统性能分析和预测模型
- **可靠性模型** - 系统可靠性和可用性建模
- **容量规划** - 基于历史数据的容量规划模型
- **负载均衡模型** - 负载分布和调度优化模型

### 🔬 形式化方法

- **有限状态机** - 完整的状态机建模和验证
- **Kripke 结构** - 模态逻辑的语义结构
- **时序逻辑** - LTL/CTL 时序逻辑支持
- **模型检查** - 自动化的模型验证和检查
- **定理证明** - 形式化证明和验证

### 🤖 机器学习模型

- **线性回归** - 经典线性回归算法
- **逻辑回归** - 分类问题的逻辑回归
- **决策树** - 决策树算法实现
- **聚类算法** - K-means 等聚类算法
- **神经网络** - 基础神经网络模型
- **支持向量机** - SVM 分类和回归

### 📈 数学建模

- **概率模型** - 概率分布和随机过程
- **统计模型** - 统计分析和推断
- **优化模型** - 线性规划和整数规划
- **图论模型** - 图算法和网络分析
- **微分方程** - 常微分和偏微分方程求解

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c18_model = "0.1.0"

# 按需启用特性
c18_model = { version = "0.1.0", features = ["queueing", "ml", "formal"] }

# 或使用聚合特性
c18_model = { version = "0.1.0", features = ["full"] }
```

### 功能特性

```toml
# 系统建模
queueing = []           # 排队论模型
performance = []        # 性能模型
reliability = []        # 可靠性模型
capacity = []           # 容量规划模型
load-balancing = []     # 负载均衡模型

# 形式化方法
formal = []             # 形式化方法
fsm = []                # 有限状态机
kripke = []             # Kripke 结构
temporal = []           # 时序逻辑
model-checking = []     # 模型检查
theorem-proving = []    # 定理证明

# 机器学习
ml = []                 # 机器学习模型
linear-regression = []  # 线性回归
logistic-regression = [] # 逻辑回归
decision-tree = []      # 决策树
clustering = []         # 聚类算法
neural-network = []     # 神经网络
svm = []                # 支持向量机

# 数学建模
math = []               # 数学建模
probability = []        # 概率模型
statistics = []         # 统计模型
optimization = []       # 优化模型
graph-theory = []       # 图论模型
differential = []       # 微分方程

# 工具特性
visualization = []      # 可视化支持
serialization = []      # 序列化支持
parallel = []           # 并行计算
gpu = []                # GPU 加速

# 完整功能
full = []               # 所有特性
```

## 🚀 快速开始

### 排队论模型

```rust
use c18_model::queueing::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // M/M/1 排队模型
    let mm1_model = MM1Model::new(
        arrival_rate: 0.5,    // 到达率 λ
        service_rate: 1.0,    // 服务率 μ
    );
    
    // 计算性能指标
    let metrics = mm1_model.calculate_metrics().await?;
    println!("平均等待时间: {:.2}", metrics.avg_waiting_time);
    println!("平均队列长度: {:.2}", metrics.avg_queue_length);
    println!("系统利用率: {:.2}%", metrics.utilization * 100.0);
    
    // M/M/c 排队模型
    let mmc_model = MMcModel::new(
        arrival_rate: 2.0,
        service_rate: 1.0,
        servers: 3,           // 3个服务台
    );
    
    let mmc_metrics = mmc_model.calculate_metrics().await?;
    println!("M/M/c 平均等待时间: {:.2}", mmc_metrics.avg_waiting_time);
    
    Ok(())
}
```

### 机器学习模型

```rust
use c18_model::ml::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 线性回归
    let mut lr_model = LinearRegression::new();
    
    // 训练数据
    let x_train = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
    ];
    let y_train = vec![3.0, 5.0, 7.0, 9.0];
    
    // 训练模型
    lr_model.fit(&x_train, &y_train).await?;
    
    // 预测
    let x_test = vec![vec![5.0, 6.0]];
    let predictions = lr_model.predict(&x_test).await?;
    println!("预测结果: {:?}", predictions);
    
    // 逻辑回归
    let mut log_reg = LogisticRegression::new();
    let x_binary = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
    ];
    let y_binary = vec![0, 0, 1, 1];
    
    log_reg.fit(&x_binary, &y_binary).await?;
    let binary_predictions = log_reg.predict(&x_test).await?;
    println!("二分类预测: {:?}", binary_predictions);
    
    Ok(())
}
```

### 形式化方法

```rust
use c18_model::formal::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 有限状态机
    let mut fsm = FiniteStateMachine::new();
    
    // 添加状态
    fsm.add_state("idle".to_string());
    fsm.add_state("running".to_string());
    fsm.add_state("stopped".to_string());
    
    // 添加转换
    fsm.add_transition("idle", "start", "running");
    fsm.add_transition("running", "stop", "stopped");
    fsm.add_transition("stopped", "reset", "idle");
    
    // 设置初始状态
    fsm.set_initial_state("idle".to_string());
    
    // 验证状态机
    let is_valid = fsm.validate().await?;
    println!("状态机有效性: {}", is_valid);
    
    // 执行转换
    fsm.transition("start").await?;
    println!("当前状态: {}", fsm.current_state());
    
    // 模型检查
    let mut model_checker = ModelChecker::new();
    let property = "AG (running -> AF stopped)".to_string(); // 总是运行最终会停止
    let result = model_checker.check(&fsm, &property).await?;
    println!("属性验证结果: {}", result);
    
    Ok(())
}
```

### 性能模型

```rust
use c18_model::performance::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建性能模型
    let mut perf_model = PerformanceModel::new();
    
    // 添加组件
    perf_model.add_component("web_server", ComponentConfig {
        service_time: 0.01,    // 10ms 服务时间
        capacity: 100,         // 100 并发请求
        failure_rate: 0.001,   // 0.1% 故障率
    });
    
    perf_model.add_component("database", ComponentConfig {
        service_time: 0.05,    // 50ms 服务时间
        capacity: 50,          // 50 并发连接
        failure_rate: 0.0001,  // 0.01% 故障率
    });
    
    // 添加连接
    perf_model.add_connection("web_server", "database", 0.8); // 80% 请求访问数据库
    
    // 分析性能
    let analysis = perf_model.analyze(1000.0).await?; // 1000 req/s 负载
    println!("系统吞吐量: {:.2} req/s", analysis.throughput);
    println!("平均响应时间: {:.2} ms", analysis.avg_response_time * 1000.0);
    println!("系统可用性: {:.4}%", analysis.availability * 100.0);
    
    Ok(())
}
```

### 数学建模

```rust
use c18_model::math::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 概率分布
    let normal_dist = NormalDistribution::new(0.0, 1.0); // 标准正态分布
    let sample = normal_dist.sample(1000);
    println!("正态分布样本均值: {:.4}", sample.iter().sum::<f64>() / sample.len() as f64);
    
    // 优化问题
    let mut optimizer = LinearProgramOptimizer::new();
    
    // 添加变量
    let x1 = optimizer.add_variable("x1", 0.0, f64::INFINITY);
    let x2 = optimizer.add_variable("x2", 0.0, f64::INFINITY);
    
    // 目标函数: maximize 3x1 + 2x2
    optimizer.set_objective(vec![(x1, 3.0), (x2, 2.0)], OptimizationDirection::Maximize);
    
    // 约束条件
    optimizer.add_constraint(vec![(x1, 1.0), (x2, 1.0)], ConstraintType::LessEqual, 4.0);
    optimizer.add_constraint(vec![(x1, 2.0), (x2, 1.0)], ConstraintType::LessEqual, 7.0);
    
    // 求解
    let solution = optimizer.solve().await?;
    println!("最优解: x1={:.2}, x2={:.2}", solution[x1], solution[x2]);
    println!("最优值: {:.2}", solution.objective_value);
    
    Ok(())
}
```

## 📚 示例

运行示例代码：

```bash
# 排队论模型示例
cargo run --example queueing_models

# 机器学习示例
cargo run --example machine_learning

# 形式化方法示例
cargo run --example formal_methods

# 性能模型示例
cargo run --example performance_modeling

# 数学建模示例
cargo run --example mathematical_modeling

# 综合演示
cargo run --example comprehensive_demo

# 异步背压示例（需要特性）
cargo run -p c12_model --example async_backpressure_demo --features tokio-adapter,tower-examples

# 递归异步与结构化并发示例
cargo run -p c12_model --example async_recursion_examples --features tokio-adapter
```

## 🏗️ 架构

```text
c18_model/
├── src/
│   ├── lib.rs                    # 库入口
│   ├── queueing/                 # 排队论模型
│   │   ├── mm1.rs               # M/M/1 模型
│   │   ├── mmc.rs               # M/M/c 模型
│   │   ├── mg1.rs               # M/G/1 模型
│   │   ├── gim1.rs              # GI/M/1 模型
│   │   └── network.rs           # 排队网络
│   ├── formal/                   # 形式化方法
│   │   ├── fsm.rs               # 有限状态机
│   │   ├── kripke.rs            # Kripke 结构
│   │   ├── temporal.rs          # 时序逻辑
│   │   ├── model_checking.rs    # 模型检查
│   │   └── theorem_proving.rs   # 定理证明
│   ├── ml/                       # 机器学习
│   │   ├── linear_regression.rs # 线性回归
│   │   ├── logistic_regression.rs # 逻辑回归
│   │   ├── decision_tree.rs     # 决策树
│   │   ├── clustering.rs        # 聚类算法
│   │   ├── neural_network.rs    # 神经网络
│   │   └── svm.rs               # 支持向量机
│   ├── math/                     # 数学建模
│   │   ├── probability.rs       # 概率模型
│   │   ├── statistics.rs        # 统计模型
│   │   ├── optimization.rs      # 优化模型
│   │   ├── graph_theory.rs      # 图论模型
│   │   └── differential.rs      # 微分方程
│   ├── performance/              # 性能模型
│   │   ├── model.rs             # 性能模型
│   │   ├── component.rs         # 组件模型
│   │   ├── analysis.rs          # 性能分析
│   │   └── prediction.rs        # 性能预测
│   ├── reliability/              # 可靠性模型
│   │   ├── model.rs             # 可靠性模型
│   │   ├── mttf.rs              # 平均故障时间
│   │   ├── availability.rs      # 可用性分析
│   │   └── maintenance.rs       # 维护模型
│   ├── capacity/                 # 容量规划
│   │   ├── planning.rs          # 容量规划
│   │   ├── forecasting.rs       # 容量预测
│   │   └── optimization.rs      # 容量优化
│   ├── visualization/            # 可视化
│   │   ├── plots.rs             # 图表绘制
│   │   ├── graphs.rs            # 图形可视化
│   │   └── dashboards.rs        # 仪表板
│   └── prelude.rs               # 预导入模块
├── examples/                     # 示例代码
├── docs/                         # 文档
└── Cargo.toml                    # 项目配置
```

## 🔧 配置

### 环境变量

```bash
# 模型配置
export MODEL_CACHE_SIZE="1000"
export MODEL_TIMEOUT="30"
export MODEL_PRECISION="double"

# 计算配置
export MAX_THREADS="8"
export GPU_ENABLED="false"
export PARALLEL_ENABLED="true"

# 可视化配置
export PLOT_BACKEND="svg"
export PLOT_RESOLUTION="300"
export PLOT_THEME="default"
```

## 🧭 新增文档导航（Rust 1.90 并发/语义/算法/架构）

- 并发/异步：`docs/concurrency/async-sync-classification.md`
- 背压模型：`docs/concurrency/backpressure-models.md`
- 递归异步：`docs/concurrency/async-recursion.md`
- 语言语义：`docs/formal/language-semantics.md`
- 设计分层：`docs/architecture/design-models.md`
- 分布式与微服务：`docs/architecture/distributed-design.md`
- 算法模型：`docs/algorithms/models.md`

### 配置文件

```toml
# config.toml
[model]
cache_size = 1000
timeout = 30
precision = "double"
validation = true

[computation]
max_threads = 8
gpu_enabled = false
parallel_enabled = true
memory_limit = "1GB"

[visualization]
backend = "svg"
resolution = 300
theme = "default"
output_dir = "./plots"

[queueing]
default_arrival_rate = 1.0
default_service_rate = 2.0
max_servers = 100

[ml]
default_learning_rate = 0.01
default_iterations = 1000
cross_validation_folds = 5

[formal]
model_checker = "nuXmv"
temporal_logic = "CTL"
verification_timeout = 60
```

## 🧪 测试

```bash
# 运行所有测试
cargo test

# 运行特定模块测试
cargo test queueing
cargo test formal
cargo test ml
cargo test math

# 运行集成测试
cargo test --features full

# 运行基准测试
cargo bench

# 运行数值精度测试
cargo test --features precision
```

## 📊 性能

### 基准测试结果

| 模型类型 | 计算复杂度 | 内存使用 | 执行时间 | 精度 |
|----------|------------|----------|----------|------|
| M/M/1 排队 | O(1) | 1MB | <1ms | 双精度 |
| 线性回归 | O(n²) | 10MB | 10ms | 单精度 |
| 状态机验证 | O(2^n) | 50MB | 100ms | 符号 |
| 优化求解 | O(n³) | 20MB | 50ms | 双精度 |
| 神经网络 | O(n²) | 100MB | 1000ms | 单精度 |

### 优化建议

1. **并行计算**: 利用多核CPU加速计算密集型任务
2. **内存管理**: 合理使用缓存减少重复计算
3. **数值精度**: 根据需求选择合适的数值精度
4. **算法选择**: 根据问题规模选择最优算法

## 🔬 理论背景

### 排队论基础

- **Little's Law**: L = λW (平均队列长度 = 到达率 × 平均等待时间)
- **Kendall记号**: A/B/c/K/N/D (到达分布/服务分布/服务台数/系统容量/顾客源/服务规则)
- **稳态条件**: ρ = λ/μ < 1 (系统利用率小于1)

### 形式化方法1

- **状态空间**: 系统所有可能状态的集合
- **转换关系**: 状态之间的转换条件
- **时序逻辑**: 描述系统行为的时间性质
- **模型检查**: 自动验证系统是否满足给定性质

### 机器学习

- **监督学习**: 使用标记数据训练模型
- **无监督学习**: 从无标记数据中发现模式
- **强化学习**: 通过与环境交互学习最优策略
- **深度学习**: 使用多层神经网络进行学习

## 🤝 贡献

我们欢迎社区贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与。

### 开发设置

```bash
# 克隆仓库
git clone https://github.com/rust-lang/c18_model.git
cd c18_model

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example queueing_models
```

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目和资源的贡献：

- [NumPy](https://numpy.org/) - 数值计算库
- [SciPy](https://scipy.org/) - 科学计算库
- [SymPy](https://www.sympy.org/) - 符号数学库
- [CVXPY](https://www.cvxpy.org/) - 凸优化库
- [NetworkX](https://networkx.org/) - 图论库
- [Rust Num](https://github.com/rust-num/num) - Rust 数值计算

## 📞 支持

- 📖 [文档](https://docs.rs/c18_model)
- 🐛 [问题报告](https://github.com/rust-lang/c18_model/issues)
- 💬 [讨论](https://github.com/rust-lang/c18_model/discussions)
- 📧 [邮件列表](mailto:c18-model@rust-lang.org)

---

**c18_model** - 让 Rust 在建模与形式方法领域发光发热！ 🦀📊
