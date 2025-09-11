# 基础使用示例

本页面提供了 c18_model 库的基础使用示例，帮助您快速上手各种功能。

## 示例 1：排队论模型分析

```rust
use c18_model::{MM1Queue, MMcQueue, PerformanceAnalyzer};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 排队论模型分析示例 ===");
    
    // 1. M/M/1 排队系统
    let queue = MM1Queue::new(1.0, 2.0); // 到达率=1.0, 服务率=2.0
    
    println!("\n1. M/M/1 排队系统:");
    println!("   利用率: {:.2}%", queue.utilization() * 100.0);
    println!("   平均队长: {:.2}", queue.average_queue_length()?);
    println!("   平均等待时间: {:.2} 秒", queue.average_waiting_time()?);
    println!("   平均响应时间: {:.2} 秒", queue.average_response_time()?);
    println!("   系统空闲概率: {:.2}%", queue.idle_probability()? * 100.0);
    
    // 2. M/M/c 多服务器系统
    let multi_queue = MMcQueue::new(1.0, 1.0, 2); // 到达率=1.0, 服务率=1.0, 服务器数=2
    
    println!("\n2. M/M/c 多服务器系统:");
    println!("   利用率: {:.2}%", multi_queue.utilization() * 100.0);
    println!("   平均队长: {:.2}", multi_queue.average_queue_length()?);
    println!("   平均等待时间: {:.2} 秒", multi_queue.average_waiting_time()?);
    println!("   所有服务器忙碌概率: {:.2}%", multi_queue.probability_all_busy()? * 100.0);
    
    // 3. 性能分析
    let mut analyzer = PerformanceAnalyzer::new();
    
    // 模拟性能数据
    for i in 0..100 {
        analyzer.add_metric("response_time", 100.0 + (i as f64 * 0.1));
        analyzer.add_metric("throughput", 1000.0 - (i as f64 * 0.5));
    }
    
    println!("\n3. 性能分析:");
    println!("{}", analyzer.generate_report());
    
    Ok(())
}
```

## 示例 2：机器学习模型训练

```rust
use c18_model::{LinearRegression, LogisticRegression, KMeans, DecisionTree};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 机器学习模型训练示例 ===");
    
    // 准备训练数据
    let x = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
        vec![5.0, 6.0],
        vec![6.0, 7.0],
        vec![7.0, 8.0],
        vec![8.0, 9.0],
    ];
    let y_regression = vec![3.0, 5.0, 7.0, 9.0, 11.0, 13.0, 15.0, 17.0];
    let y_classification = vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0];
    
    // 1. 线性回归
    println!("\n1. 线性回归:");
    let mut lr = LinearRegression::new(0.01, 1000);
    lr.fit(&x, &y_regression)?;
    
    let test_x = vec![vec![9.0, 10.0], vec![10.0, 11.0]];
    let predictions = lr.predict(&test_x);
    let r2 = lr.r2_score(&x, &y_regression);
    
    println!("   预测结果: {:?}", predictions);
    println!("   R²分数: {:.4}", r2);
    println!("   MSE: {:.4}", lr.mse(&x, &y_regression));
    
    // 2. 逻辑回归
    println!("\n2. 逻辑回归:");
    let mut log_reg = LogisticRegression::new(0.01, 1000);
    log_reg.fit(&x, &y_classification)?;
    
    let log_predictions = log_reg.predict(&test_x);
    let log_proba = log_reg.predict_proba(&test_x);
    let accuracy = log_reg.accuracy(&x, &y_classification);
    
    println!("   预测结果: {:?}", log_predictions);
    println!("   预测概率: {:?}", log_proba);
    println!("   准确率: {:.4}", accuracy);
    
    // 3. KMeans 聚类
    println!("\n3. KMeans 聚类:");
    let mut kmeans = KMeans::new(2, 100);
    kmeans.fit(&x)?;
    
    let labels = kmeans.predict(&x);
    let silhouette = kmeans.silhouette_score(&x);
    let inertia = kmeans.inertia(&x);
    
    println!("   聚类标签: {:?}", labels);
    println!("   轮廓系数: {:.4}", silhouette);
    println!("   惯性: {:.4}", inertia);
    
    // 4. 决策树
    println!("\n4. 决策树:");
    let mut dt = DecisionTree::new();
    dt.fit(&x, &y_classification)?;
    
    let dt_predictions = dt.predict(&test_x);
    let dt_accuracy = dt.accuracy(&x, &y_classification);
    let feature_importance = dt.feature_importance();
    
    println!("   预测结果: {:?}", dt_predictions);
    println!("   准确率: {:.4}", dt_accuracy);
    println!("   特征重要性: {:?}", feature_importance);
    
    Ok(())
}
```

## 示例 3：形式化方法应用

```rust
use c18_model::{
    FiniteStateMachine, State, Transition, TemporalFormula, 
    TemporalModelChecker, ProcessTerm, ProcessAlgebraInterpreter,
    AdvancedFormalMethodsToolkit
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 形式化方法应用示例 ===");
    
    // 1. 有限状态机
    println!("\n1. 有限状态机:");
    let mut fsm = FiniteStateMachine::new("idle".to_string());
    
    // 添加状态
    let working_state = State::new("working".to_string())
        .with_property("busy".to_string(), true);
    let error_state = State::new("error".to_string())
        .with_property("error".to_string(), true);
    let goal_state = State::new("goal".to_string())
        .with_property("completed".to_string(), true);
    
    fsm.add_state(working_state);
    fsm.add_state(error_state);
    fsm.add_state(goal_state);
    
    // 添加转换
    let transitions = vec![
        Transition::new("idle".to_string(), "working".to_string(), "start".to_string()),
        Transition::new("working".to_string(), "goal".to_string(), "complete".to_string()),
        Transition::new("working".to_string(), "error".to_string(), "fail".to_string()),
        Transition::new("error".to_string(), "idle".to_string(), "reset".to_string()),
    ];
    
    for transition in transitions {
        fsm.add_transition(transition);
    }
    
    println!("   初始状态: {}", fsm.get_current_state().id);
    
    // 执行状态转换
    fsm.transition("start")?;
    println!("   转换后状态: {}", fsm.get_current_state().id);
    
    // 分析状态机
    let reachable = fsm.get_reachable_states();
    let has_deadlock = fsm.has_deadlock();
    
    println!("   可达状态: {:?}", reachable);
    println!("   存在死锁: {}", has_deadlock);
    
    // 2. 时序逻辑模型检查
    println!("\n2. 时序逻辑模型检查:");
    let checker = TemporalModelChecker::new(fsm);
    
    let formulas = vec![
        ("G(safe)", TemporalFormula::Always(Box::new(TemporalFormula::Atomic("safe".to_string())))),
        ("F(goal)", TemporalFormula::Eventually(Box::new(TemporalFormula::Atomic("goal".to_string())))),
        ("X(working)", TemporalFormula::Next(Box::new(TemporalFormula::Atomic("working".to_string())))),
    ];
    
    for (name, formula) in formulas {
        let result = checker.check_formula(&formula);
        println!("   公式 {}: {}", name, result);
    }
    
    // 3. 进程代数
    println!("\n3. 进程代数:");
    let interpreter = ProcessAlgebraInterpreter::new();
    
    let processes = vec![
        ("简单进程", ProcessTerm::Prefix("a".to_string(), Box::new(ProcessTerm::Nil))),
        ("选择进程", ProcessTerm::Choice(
            Box::new(ProcessTerm::Prefix("a".to_string(), Box::new(ProcessTerm::Nil))),
            Box::new(ProcessTerm::Prefix("b".to_string(), Box::new(ProcessTerm::Nil)))
        )),
        ("并行进程", ProcessTerm::Parallel(
            Box::new(ProcessTerm::Prefix("a".to_string(), Box::new(ProcessTerm::Nil))),
            Box::new(ProcessTerm::Prefix("b".to_string(), Box::new(ProcessTerm::Nil)))
        )),
    ];
    
    for (name, process) in processes {
        let trace = interpreter.execute(&process);
        println!("   {}: {:?}", name, trace);
    }
    
    // 4. 高级形式化方法
    println!("\n4. 高级形式化方法:");
    let toolkit = AdvancedFormalMethodsToolkit::new();
    
    // 验证代数性质
    let properties = vec!["associativity", "commutativity", "identity", "distributivity"];
    for prop in properties {
        let result = toolkit.verify_algebraic_property(prop);
        println!("   代数性质 {}: {}", prop, result);
    }
    
    // 检查逻辑公式
    let formulas = vec!["P → Q", "P ∧ Q", "P ∨ Q", "¬P"];
    for formula in formulas {
        let result = toolkit.check_logical_formula(formula);
        println!("   逻辑公式 {}: {}", formula, result);
    }
    
    // 验证进程等价性
    let process_pairs = vec![
        ("a.b.0", "a.b.0"),
        ("a.0 + b.0", "b.0 + a.0"),
        ("a.0", "b.0"),
    ];
    
    for (p1, p2) in process_pairs {
        let result = toolkit.verify_process_equivalence(p1, p2);
        println!("   进程等价性 {} ≡ {}: {}", p1, p2, result);
    }
    
    Ok(())
}
```

## 示例 4：配置管理和错误处理

```rust
use c18_model::{
    ModelConfig, ConfigManager, LogLevel, PrecisionConfig, PerformanceConfig,
    ModelError, ErrorHandler, Result as ModelResult
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 配置管理和错误处理示例 ===");
    
    // 1. 配置管理
    println!("\n1. 配置管理:");
    
    // 创建默认配置
    let default_config = ModelConfig::default();
    println!("   默认配置:");
    println!("   {}", default_config.to_json()?);
    
    // 创建自定义配置
    let custom_config = ModelConfig::new()
        .with_log_level(LogLevel::Debug)
        .with_logging(true)
        .with_precision(PrecisionConfig {
            default_precision: 1e-8,
            convergence_threshold: 1e-8,
            max_iterations: 2000,
            stability_threshold: 1e-14,
        })
        .with_performance(PerformanceConfig {
            enable_parallel: true,
            thread_count: 4,
            enable_cache: true,
            cache_size_limit: 2000,
            enable_profiling: true,
        });
    
    println!("\n   自定义配置:");
    println!("   日志级别: {}", custom_config.log_level);
    println!("   启用日志: {}", custom_config.enable_logging);
    println!("   默认精度: {}", custom_config.precision.default_precision);
    println!("   最大迭代次数: {}", custom_config.precision.max_iterations);
    println!("   启用并行: {}", custom_config.performance.enable_parallel);
    println!("   线程数: {}", custom_config.performance.thread_count);
    
    // 使用配置管理器
    let mut manager = ConfigManager::from_config(custom_config)?;
    println!("\n   配置摘要:");
    println!("   {}", manager.get_summary());
    
    // 保存和加载配置
    manager.save_to_file("config.json")?;
    println!("\n   配置已保存到 config.json");
    
    let mut new_manager = ConfigManager::new();
    new_manager.load_from_file("config.json")?;
    println!("   配置已从文件加载");
    
    // 2. 错误处理
    println!("\n2. 错误处理:");
    
    // 演示各种错误类型
    let errors = vec![
        ("数学错误", ErrorHandler::math_error("除零运算")),
        ("验证错误", ErrorHandler::validation_error("输入数据格式不正确")),
        ("配置错误", ErrorHandler::config_error("配置文件格式错误")),
        ("计算错误", ErrorHandler::computation_error("数值计算溢出")),
        ("溢出错误", ErrorHandler::overflow_error("结果超出数值范围")),
        ("除零错误", ErrorHandler::division_by_zero_error("除数不能为零")),
        ("收敛错误", ErrorHandler::convergence_error("算法无法收敛")),
        ("维度不匹配", ErrorHandler::dimension_mismatch_error("矩阵维度不匹配")),
        ("参数范围错误", ErrorHandler::parameter_range_error("参数超出有效范围")),
        ("系统不稳定", ErrorHandler::system_unstable_error("系统利用率过高")),
    ];
    
    for (name, error) in errors {
        println!("   {}: {}", name, error);
        println!("     错误代码: {}", error.error_code());
        println!("     严重级别: {}", error.severity());
        println!("     是否严重: {}", error.is_critical());
        println!("     是否可恢复: {}", error.is_recoverable());
        if let Some(suggestion) = error.suggestion() {
            println!("     建议: {}", suggestion);
        }
        println!();
    }
    
    // 3. 错误处理最佳实践
    println!("3. 错误处理最佳实践:");
    
    fn risky_operation(x: f64) -> ModelResult<f64> {
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
    
    let test_values = vec![2.0, -1.0, 0.0, 1e-300];
    
    for value in test_values {
        match risky_operation(value) {
            Ok(result) => println!("   risky_operation({}) = {}", value, result),
            Err(e) => {
                println!("   risky_operation({}) 失败: {}", value, e);
                println!("     错误代码: {}", e.error_code());
                println!("     建议: {}", e.suggestion().unwrap_or("无建议"));
            }
        }
    }
    
    Ok(())
}
```

## 运行示例

将上述代码保存到相应的文件中，然后运行：

```bash
# 排队论模型分析
cargo run --example queueing_analysis

# 机器学习模型训练
cargo run --example ml_training

# 形式化方法应用
cargo run --example formal_methods

# 配置管理和错误处理
cargo run --example config_and_errors
```

## 预期输出

每个示例都会产生详细的输出，展示相应功能的使用方法和结果。这些示例涵盖了 c18_model 库的主要功能，帮助您理解如何在实际项目中使用这些功能。

## 下一步

完成基础示例后，您可以：

1. 查看 [高级使用示例](advanced-usage.md)
2. 探索 [API 参考文档](api-reference/)
3. 阅读 [使用指南](guides/)
4. 尝试修改示例代码以满足您的具体需求
