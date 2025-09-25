//! Rust 1.90 特性演示
//!
//! 本示例展示了如何使用 c12_model 库中的 Rust 1.90 新特性，
//! 包括常量泛型推断、生命周期语法改进等。

use c12_model::{
    queueing_models::{
        MM1Queue, QueueConfig, PriorityQueue, MultiLevelFeedbackQueue,
        // QueueMetrics,
    },
    ml_models::{
        //LinearRegression, 
        MLConfig, SupportVectorMachine, NeuralNetwork, 
        ActivationFunction, KernelType, MLMetrics,
    },
    formal_models::{
        FiniteStateMachine, State, Transition, TemporalFormula, TemporalModelChecker,
    },
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Rust 1.90 特性演示 ===\n");

    // 演示常量泛型推断
    demo_const_generics()?;
    
    // 演示生命周期语法改进
    demo_lifetime_improvements()?;
    
    // 演示高级排队论模型
    demo_advanced_queueing_models()?;
    
    // 演示高级机器学习模型
    demo_advanced_ml_models()?;
    
    // 演示形式化方法增强
    demo_formal_methods_enhancements()?;

    println!("\n=== 演示完成 ===");
    Ok(())
}

/// 演示常量泛型推断特性
fn demo_const_generics() -> Result<(), Box<dyn std::error::Error>> {
    println!("1. 常量泛型推断演示");
    println!("===================");
    
    // 使用常量泛型创建排队系统配置
    let config_2d = QueueConfig::<2>::new([1.0, 2.0]);
    let _config_3d = QueueConfig::<3>::new([1.0, 2.0, 3.0]);
    
    // 使用配置创建 M/M/1 排队系统
    let queue = MM1Queue::from_config(config_2d);
    
    println!("   M/M/1 排队系统利用率: {:.2}", queue.utilization());
    println!("   平均队长: {:.2}", queue.average_queue_length()?);
    
    // 演示机器学习配置的常量泛型
    let ml_config = MLConfig::<5>::new(0.01, 0.1);
    println!("   ML 配置特征数量: {}", ml_config.feature_count);
    
    println!();
    Ok(())
}

/// 演示生命周期语法改进
fn demo_lifetime_improvements() -> Result<(), Box<dyn std::error::Error>> {
    println!("2. 生命周期语法改进演示");
    println!("=======================");
    
    // 创建具有明确生命周期的数据结构
    let data = create_long_lived_data();
    let result = process_data(&data);
    
    println!("   处理结果: {}", result);
    
    // 演示引用传递的生命周期管理
    let metrics = calculate_metrics(&data);
    println!("   计算指标: {:.2}", metrics);
    
    println!();
    Ok(())
}

fn create_long_lived_data() -> Vec<f64> {
    vec![1.0, 2.0, 3.0, 4.0, 5.0]
}

fn process_data<'a>(data: &'a [f64]) -> f64 {
    data.iter().sum()
}

fn calculate_metrics(data: &[f64]) -> f64 {
    let mean = data.iter().sum::<f64>() / data.len() as f64;
    let variance = data.iter()
        .map(|&x| (x - mean).powi(2))
        .sum::<f64>() / data.len() as f64;
    variance.sqrt()
}

/// 演示高级排队论模型
fn demo_advanced_queueing_models() -> Result<(), Box<dyn std::error::Error>> {
    println!("3. 高级排队论模型演示");
    println!("=====================");
    
    // 创建优先级排队系统
    let arrival_rates = [0.5, 1.0, 0.8];
    let service_rates = [1.0, 1.5, 1.2];
    let priority_queue = PriorityQueue::<3>::new(arrival_rates, service_rates);
    
    println!("   优先级排队系统利用率: {:.2}", priority_queue.utilization());
    
    let waiting_times = priority_queue.priority_waiting_times();
    for (i, &waiting_time) in waiting_times.iter().enumerate() {
        println!("   优先级 {} 平均等待时间: {:.2}", i + 1, waiting_time);
    }
    
    // 创建多级反馈队列系统
    let level_configs = [
        QueueConfig::new([1.0, 2.0, 0.1]),
        QueueConfig::new([0.5, 1.5, 0.2]),
        QueueConfig::new([0.3, 1.0, 0.5]),
    ];
    let promotion_probs = [0.1, 0.2, 0.0];
    let demotion_probs = [0.0, 0.1, 0.3];
    
    let mlfq = MultiLevelFeedbackQueue::<3>::new(
        level_configs,
        promotion_probs,
        demotion_probs,
    );
    
    let metrics = mlfq.overall_metrics();
    println!("   多级反馈队列吞吐量: {:.2}", metrics.throughput);
    println!("   平均响应时间: {:.2}", metrics.avg_response_time);
    
    println!();
    Ok(())
}

/// 演示高级机器学习模型
fn demo_advanced_ml_models() -> Result<(), Box<dyn std::error::Error>> {
    println!("4. 高级机器学习模型演示");
    println!("=======================");
    
    // 创建支持向量机
    let kernel = KernelType::RBF { gamma: 0.1 };
    let mut svm = SupportVectorMachine::<2>::new(1.0, kernel);
    
    // 训练数据
    let x = [
        [1.0, 2.0],
        [2.0, 3.0],
        [3.0, 4.0],
        [4.0, 5.0],
    ];
    let y = [1.0, -1.0, 1.0, -1.0];
    
    svm.fit(&x, &y)?;
    println!("   SVM 训练完成");
    
    // 预测
    let test_data = [[1.5, 2.5], [3.5, 4.5]];
    let predictions = svm.predict(&test_data);
    println!("   SVM 预测结果: {:?}", predictions);
    
    // 创建神经网络
    let activation = ActivationFunction::ReLU;
    let nn = NeuralNetwork::<2, 4, 1>::new(0.01, activation);
    
    println!("   神经网络创建完成，输入层: 2, 隐藏层: 4, 输出层: 1");
    
    // 前向传播演示
    let input = [1.0, 2.0];
    let output = nn.forward(&input);
    println!("   神经网络前向传播结果: {:?}", output);
    
    // 创建 ML 性能指标
    let metrics = MLMetrics {
        accuracy: 0.95,
        precision: 0.92,
        recall: 0.88,
        f1_score: 0.90,
        mse: 0.05,
        mae: 0.08,
    };
    
    println!("   ML 性能指标:");
    println!("     准确率: {:.2}", metrics.accuracy);
    println!("     精确率: {:.2}", metrics.precision);
    println!("     召回率: {:.2}", metrics.recall);
    println!("     F1 分数: {:.2}", metrics.f1_score);
    
    println!();
    Ok(())
}

/// 演示形式化方法增强
fn demo_formal_methods_enhancements() -> Result<(), Box<dyn std::error::Error>> {
    println!("5. 形式化方法增强演示");
    println!("=====================");
    
    // 创建增强的有限状态机
    let mut fsm = FiniteStateMachine::new("idle".to_string());
    
    // 添加状态
    let working_state = State::new("working".to_string())
        .with_property("busy".to_string(), true)
        .with_property("safe".to_string(), true);
    fsm.add_state(working_state);
    
    let error_state = State::new("error".to_string())
        .with_property("busy".to_string(), false)
        .with_property("safe".to_string(), false);
    fsm.add_state(error_state);
    
    // 添加转换
    let transition1 = Transition::new(
        "idle".to_string(),
        "working".to_string(),
        "start".to_string(),
    );
    
    let transition2 = Transition::new(
        "working".to_string(),
        "error".to_string(),
        "fail".to_string(),
    ).with_action("log_error".to_string());
    
    fsm.add_transition(transition1);
    fsm.add_transition(transition2);
    
    println!("   状态机创建完成");
    
    // 执行转换
    fsm.transition("start")?;
    println!("   执行 'start' 转换，当前状态: {}", fsm.get_current_state().id);
    
    // 检查可达状态
    let reachable = fsm.get_reachable_states();
    println!("   可达状态: {:?}", reachable);
    
    // 检查死锁
    let has_deadlock = fsm.has_deadlock();
    println!("   存在死锁: {}", has_deadlock);
    
    // 创建时序逻辑模型检查器
    let checker = TemporalModelChecker::new(fsm.clone());
    
    // 创建时序逻辑公式
    let formula = TemporalFormula::Globally(
        Box::new(TemporalFormula::Atomic("safe".to_string()))
    );
    
    println!("   时序逻辑公式: G(safe)");
    let result = checker.check_formula(&formula);
    println!("   公式验证结果: {}", result);
    
    // 生成反例（如果存在）
    if let Some(counterexample) = checker.generate_counterexample(&formula) {
        println!("   反例路径: {:?}", counterexample);
    }
    
    println!();
    Ok(())
}
