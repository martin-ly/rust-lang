# 快速开始指南

## 📊 目录

- [快速开始指南](#快速开始指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [基本设置](#基本设置)
  - [示例 1：排队论模型](#示例-1排队论模型)
  - [示例 2：机器学习模型](#示例-2机器学习模型)
  - [示例 3：形式化方法](#示例-3形式化方法)
  - [示例 4：配置管理](#示例-4配置管理)
  - [示例 5：错误处理](#示例-5错误处理)
  - [运行示例](#运行示例)
  - [下一步](#下一步)
  - [获取帮助](#获取帮助)

本指南将帮助您快速上手 c18_model 库，通过几个简单的示例展示主要功能。

---

## 📋 目录

- [快速开始指南](#快速开始指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [基本设置](#基本设置)
  - [示例 1：排队论模型](#示例-1排队论模型)
  - [示例 2：机器学习模型](#示例-2机器学习模型)
  - [示例 3：形式化方法](#示例-3形式化方法)
  - [示例 4：配置管理](#示例-4配置管理)
  - [示例 5：错误处理](#示例-5错误处理)
  - [运行示例](#运行示例)
  - [下一步](#下一步)
  - [获取帮助](#获取帮助)

---

## 基本设置

首先，创建一个新的 Rust 项目：

```bash
cargo new my_model_project
cd my_model_project
```

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c18_model = "0.2.0"
```

## 示例 1：排队论模型

```rust
use c18_model::{MM1Queue, MMcQueue};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 M/M/1 排队系统
    let queue = MM1Queue::new(1.0, 2.0); // 到达率=1.0, 服务率=2.0
    
    println!("=== M/M/1 排队系统分析 ===");
    println!("利用率: {:.2}%", queue.utilization() * 100.0);
    println!("平均队长: {:.2}", queue.average_queue_length()?);
    println!("平均等待时间: {:.2} 秒", queue.average_waiting_time()?);
    println!("平均响应时间: {:.2} 秒", queue.average_response_time()?);
    
    // 创建 M/M/c 多服务器系统
    let multi_queue = MMcQueue::new(1.0, 1.0, 2); // 到达率=1.0, 服务率=1.0, 服务器数=2
    println!("\n=== M/M/c 多服务器系统分析 ===");
    println!("利用率: {:.2}%", multi_queue.utilization() * 100.0);
    println!("平均队长: {:.2}", multi_queue.average_queue_length()?);
    
    Ok(())
}
```

## 示例 2：机器学习模型

```rust
use c18_model::{LinearRegression, LogisticRegression, KMeans};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 准备训练数据
    let x = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
        vec![5.0, 6.0],
    ];
    let y = vec![3.0, 5.0, 7.0, 9.0, 11.0];
    
    // 线性回归
    let mut lr = LinearRegression::new(0.01, 1000);
    lr.fit(&x, &y)?;
    
    let test_x = vec![vec![6.0, 7.0]];
    let predictions = lr.predict(&test_x);
    println!("线性回归预测: {:?}", predictions);
    
    // 逻辑回归
    let mut log_reg = LogisticRegression::new(0.01, 1000);
    let binary_y = vec![0.0, 0.0, 1.0, 1.0, 1.0];
    log_reg.fit(&x, &binary_y)?;
    
    let log_predictions = log_reg.predict(&test_x);
    println!("逻辑回归预测: {:?}", log_predictions);
    
    // KMeans 聚类
    let mut kmeans = KMeans::new(2, 100);
    kmeans.fit(&x)?;
    
    let labels = kmeans.predict(&x);
    println!("KMeans 聚类标签: {:?}", labels);
    
    Ok(())
}
```

## 示例 3：形式化方法

```rust
use c18_model::{FiniteStateMachine, State, Transition, TemporalFormula};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建有限状态机
    let mut fsm = FiniteStateMachine::new("idle".to_string());
    
    // 添加状态
    let working_state = State::new("working".to_string())
        .with_property("busy".to_string(), true);
    let error_state = State::new("error".to_string())
        .with_property("error".to_string(), true);
    
    fsm.add_state(working_state);
    fsm.add_state(error_state);
    
    // 添加转换
    let start_transition = Transition::new("idle".to_string(), "working".to_string(), "start".to_string());
    let error_transition = Transition::new("working".to_string(), "error".to_string(), "error".to_string());
    
    fsm.add_transition(start_transition);
    fsm.add_transition(error_transition);
    
    println!("=== 有限状态机分析 ===");
    println!("当前状态: {}", fsm.get_current_state().id);
    
    // 执行状态转换
    fsm.transition("start")?;
    println!("转换后状态: {}", fsm.get_current_state().id);
    
    // 检查可达状态
    let reachable = fsm.get_reachable_states();
    println!("可达状态: {:?}", reachable);
    
    // 检查死锁
    let has_deadlock = fsm.has_deadlock();
    println!("存在死锁: {}", has_deadlock);
    
    Ok(())
}
```

## 示例 4：配置管理

```rust
use c18_model::{ModelConfig, ConfigManager, LogLevel};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建默认配置
    let config = ModelConfig::default();
    println!("默认配置:");
    println!("{}", config.to_json()?);
    
    // 创建自定义配置
    let custom_config = ModelConfig::new()
        .with_log_level(LogLevel::Debug)
        .with_logging(true);
    
    println!("\n自定义配置:");
    println!("日志级别: {}", custom_config.log_level);
    println!("启用日志: {}", custom_config.enable_logging);
    
    // 使用配置管理器
    let mut manager = ConfigManager::from_config(custom_config)?;
    println!("\n配置摘要:");
    println!("{}", manager.get_summary());
    
    // 保存配置到文件
    manager.save_to_file("config.json")?;
    println!("\n配置已保存到 config.json");
    
    Ok(())
}
```

## 示例 5：错误处理

```rust
use c18_model::{ModelError, ErrorHandler, Result as ModelResult};

fn risky_calculation(x: f64) -> ModelResult<f64> {
    if x < 0.0 {
        return Err(ErrorHandler::parameter_range_error("输入值不能为负数"));
    }
    
    if x == 0.0 {
        return Err(ErrorHandler::division_by_zero_error("除数不能为零"));
    }
    
    let result = 1.0 / x;
    if result.is_infinite() {
        return Err(ErrorHandler::overflow_error("计算结果溢出"));
    }
    
    Ok(result)
}

fn main() {
    // 测试正常情况
    match risky_calculation(2.0) {
        Ok(result) => println!("计算结果: {}", result),
        Err(e) => println!("错误: {}", e),
    }
    
    // 测试错误情况
    match risky_calculation(-1.0) {
        Ok(result) => println!("计算结果: {}", result),
        Err(e) => {
            println!("错误: {}", e);
            println!("错误代码: {}", e.error_code());
            println!("严重级别: {}", e.severity());
            if let Some(suggestion) = e.suggestion() {
                println!("建议: {}", suggestion);
            }
        }
    }
}
```

## 运行示例

将上述代码保存到 `main.rs` 文件中，然后运行：

```bash
cargo run
```

## 下一步

现在您已经了解了 c18_model 的基本用法，可以：

1. 查看 [详细使用指南](guides/)
2. 探索 [API 参考文档](api-reference/)
3. 运行 [更多示例](examples/)
4. 了解 [高级功能](guides/advanced-usage.md)

## 获取帮助

如果在使用过程中遇到问题：

1. 查看错误信息和建议
2. 阅读相关文档
3. 查看示例代码
4. 提交 Issue 或寻求帮助
