//! Rust 1.90 现代机器学习演示
//!
//! 本示例展示了如何使用 c12_model 库的 Rust 1.90 新特性和现代机器学习功能
//!
//! 运行命令：
//! ```bash
//! cargo run --example rust_190_modern_ml_demo --features "candle-ml,tensor-computing"
//! ```

use c12_model::{
    // Rust 1.90 新特性
    rust_190_features::{
        ModelConfig as Rust190ModelConfig, DataProcessor, OptimizationEngine, AlgorithmType, 
        OptimizedMatrix
    },
    // 现代机器学习
    modern_ml::{
        ModernMLEngine, ModernMLConfig, ModelType, DeviceType, PrecisionType,
        TrainingData, EvaluationData
    },
    // 传统模型
    queueing_models::MM1Queue,
    ml_models::LinearRegression,
    math_models::StatisticalTools,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Rust 1.90 现代机器学习演示");
    println!("=====================================");

    // 1. 演示 Rust 1.90 常量泛型推断
    demo_const_generic_inference()?;

    // 2. 演示生命周期优化
    demo_lifetime_optimization()?;

    // 3. 演示函数指针安全
    demo_function_pointer_safety()?;

    // 4. 演示现代机器学习引擎
    demo_modern_ml_engine()?;

    // 5. 演示优化的矩阵操作
    demo_optimized_matrix_operations()?;

    // 6. 演示传统模型与新特性的结合
    demo_traditional_models_integration()?;

    println!("\n✅ 所有演示完成！");
    Ok(())
}

/// 演示 Rust 1.90 常量泛型推断
fn demo_const_generic_inference() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📊 演示 Rust 1.90 常量泛型推断");
    println!("--------------------------------");

    // 使用常量泛型推断创建模型配置
    let config_2d: Rust190ModelConfig<2> = Rust190ModelConfig::<2>::from_slice(&[1.0, 2.0], "2D模型".to_string());
    let config_3d: Rust190ModelConfig<3> = Rust190ModelConfig::<3>::from_slice(&[1.0, 2.0, 3.0], "3D模型".to_string());
    let config_4d: Rust190ModelConfig<4> = Rust190ModelConfig::<4>::from_slice(&[1.0, 2.0, 3.0, 4.0], "4D模型".to_string());

    println!("2D模型参数数量: {}", config_2d.param_count());
    println!("3D模型参数数量: {}", config_3d.param_count());
    println!("4D模型参数数量: {}", config_4d.param_count());

    // 计算统计信息
    let stats_3d = config_3d.statistics();
    println!("3D模型统计信息:");
    println!("  均值: {:.2}", stats_3d.mean);
    println!("  方差: {:.2}", stats_3d.variance);
    println!("  标准差: {:.2}", stats_3d.std_dev);
    println!("  最小值: {:.2}", stats_3d.min);
    println!("  最大值: {:.2}", stats_3d.max);

    Ok(())
}

/// 演示生命周期优化
fn demo_lifetime_optimization() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔄 演示生命周期优化");
    println!("----------------------");

    // 创建测试数据
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
    
    // 创建数据处理器
    let processor = DataProcessor::new(&data, 1);
    
    // 处理数据
    let result = processor.process_data();
    println!("数据处理结果:");
    println!("  均值: {:.2}", result.mean);
    println!("  方差: {:.2}", result.variance);
    println!("  标准差: {:.2}", result.std_dev);
    println!("  处理器ID: {}", result.processor_id);

    // 计算分位数
    let median = processor.quantiles(0.5);
    let q25 = processor.quantiles(0.25);
    let q75 = processor.quantiles(0.75);
    
    println!("分位数:");
    println!("  Q25: {:.2}", q25);
    println!("  中位数: {:.2}", median);
    println!("  Q75: {:.2}", q75);

    Ok(())
}

/// 演示函数指针安全
fn demo_function_pointer_safety() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔒 演示函数指针安全");
    println!("----------------------");

    // 定义目标函数
    fn rosenbrock(x: &[f64]) -> f64 {
        let mut sum = 0.0;
        for i in 0..x.len() - 1 {
            let a = 1.0 - x[i];
            let b = x[i + 1] - x[i] * x[i];
            sum += a * a + 100.0 * b * b;
        }
        sum
    }

    fn sphere(x: &[f64]) -> f64 {
        x.iter().map(|&xi| xi * xi).sum()
    }

    // 创建优化引擎
    let engine = OptimizationEngine::new(AlgorithmType::GradientDescent);
    
    // 优化 Rosenbrock 函数
    let initial = vec![0.0, 0.0];
    let result = engine.optimize(rosenbrock, None, &initial, 1000);
    
    println!("Rosenbrock 函数优化结果:");
    println!("  解: [{:.4}, {:.4}]", result.solution[0], result.solution[1]);
    println!("  最终目标值: {:.6}", result.final_objective);
    println!("  迭代次数: {}", result.iterations);
    println!("  是否收敛: {}", result.converged);
    println!("  训练时间: {:.4}秒", result.iterations as f64 * 0.001);

    // 优化 Sphere 函数
    let result2 = engine.optimize(sphere, None, &initial, 100);
    
    println!("\nSphere 函数优化结果:");
    println!("  解: [{:.4}, {:.4}]", result2.solution[0], result2.solution[1]);
    println!("  最终目标值: {:.6}", result2.final_objective);
    println!("  迭代次数: {}", result2.iterations);

    Ok(())
}

/// 演示现代机器学习引擎
fn demo_modern_ml_engine() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🤖 演示现代机器学习引擎");
    println!("--------------------------");

    // 创建现代ML配置
    let config = ModernMLConfig {
        model_type: ModelType::LinearRegression,
        device: DeviceType::Cpu,
        precision: PrecisionType::F32,
        batch_size: 32,
        learning_rate: 0.01,
        max_epochs: 100,
        early_stopping_patience: 10,
    };

    // 创建ML引擎
    let mut engine = ModernMLEngine::new(config);

    // 创建线性回归模型
    engine.create_model("linear_reg".to_string(), ModelType::LinearRegression)?;
    
    // 准备训练数据 (y = 2x + 1 + noise)
    let mut features = Vec::new();
    let mut labels = Vec::new();
    
    for i in 0..100 {
        let x = i as f64 * 0.1;
        let y = 2.0 * x + 1.0 + (fastrand::f64() - 0.5) * 0.1; // 添加噪声
        features.push(vec![x]);
        labels.push(y);
    }

    let training_data = TrainingData {
        features: features.clone(),
        labels: labels.clone(),
        val_features: None,
        val_labels: None,
    };

    // 训练模型
    println!("训练线性回归模型...");
    let train_result = engine.train_model("linear_reg", &training_data)?;
    
    println!("训练结果:");
    println!("  最终损失: {:.6}", train_result.final_train_loss);
    println!("  训练轮数: {}", train_result.epochs_trained);
    println!("  是否早停: {}", train_result.early_stopped);
    println!("  训练时间: {:.4}秒", train_result.training_time);

    // 预测
    let test_input = vec![5.0];
    let prediction = engine.predict("linear_reg", &test_input)?;
    println!("预测结果: x=5.0, y={:.4}", prediction[0]);

    // 创建逻辑回归模型
    engine.create_model("logistic_reg".to_string(), ModelType::LogisticRegression)?;
    
    // 准备二分类数据
    let mut features_binary = Vec::new();
    let mut labels_binary = Vec::new();
    
    for _i in 0..200 {
        let x1 = (fastrand::f64() - 0.5) * 4.0;
        let x2 = (fastrand::f64() - 0.5) * 4.0;
        let label = if x1 + x2 > 0.0 { 1.0 } else { 0.0 };
        
        features_binary.push(vec![x1, x2]);
        labels_binary.push(label);
    }

    let training_data_binary = TrainingData {
        features: features_binary.clone(),
        labels: labels_binary.clone(),
        val_features: None,
        val_labels: None,
    };

    // 训练逻辑回归模型
    println!("\n训练逻辑回归模型...");
    let train_result_binary = engine.train_model("logistic_reg", &training_data_binary)?;
    
    println!("训练结果:");
    println!("  最终损失: {:.6}", train_result_binary.final_train_loss);
    println!("  训练轮数: {}", train_result_binary.epochs_trained);
    println!("  训练时间: {:.4}秒", train_result_binary.training_time);

    // 预测
    let test_input_binary = vec![1.0, 1.0];
    let prediction_binary = engine.predict("logistic_reg", &test_input_binary)?;
    println!("预测结果: [1.0, 1.0] -> 概率={:.4}", prediction_binary[0]);

    // 评估模型
    let eval_data = EvaluationData {
        features: features_binary[..50].to_vec(),
        labels: labels_binary[..50].to_vec(),
    };
    
    let eval_result = engine.evaluate_model("logistic_reg", &eval_data)?;
    println!("评估结果:");
    println!("  准确率: {:.4}", eval_result.accuracy);

    Ok(())
}

/// 演示优化的矩阵操作
fn demo_optimized_matrix_operations() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔢 演示优化的矩阵操作");
    println!("----------------------");

    // 创建 2x3 矩阵
    let matrix_a = OptimizedMatrix::<2, 3>::from_array([
        [1.0, 2.0, 3.0],
        [4.0, 5.0, 6.0],
    ]);

    // 创建 3x2 矩阵
    let matrix_b = OptimizedMatrix::<3, 2>::from_array([
        [1.0, 2.0],
        [3.0, 4.0],
        [5.0, 6.0],
    ]);

    println!("矩阵 A (2x3):");
    for i in 0..2 {
        for j in 0..3 {
            print!("{:.1} ", matrix_a.get(i, j).unwrap());
        }
        println!();
    }

    println!("\n矩阵 B (3x2):");
    for i in 0..3 {
        for j in 0..2 {
            print!("{:.1} ", matrix_b.get(i, j).unwrap());
        }
        println!();
    }

    // 矩阵乘法
    let result = matrix_a.multiply(&matrix_b);
    
    println!("\n矩阵乘法结果 A × B (2x2):");
    for i in 0..2 {
        for j in 0..2 {
            print!("{:.1} ", result.get(i, j).unwrap());
        }
        println!();
    }

    // 矩阵转置
    let transposed = matrix_a.transpose();
    
    println!("\n矩阵 A 的转置 (3x2):");
    for i in 0..3 {
        for j in 0..2 {
            print!("{:.1} ", transposed.get(i, j).unwrap());
        }
        println!();
    }

    Ok(())
}

/// 演示传统模型与新特性的结合
fn demo_traditional_models_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔗 演示传统模型与新特性的结合");
    println!("--------------------------------");

    // 创建排队论模型
    let queue = MM1Queue::new(2.0, 3.0);
    println!("M/M/1 排队系统:");
    println!("  到达率: {:.2}", queue.arrival_rate);
    println!("  服务率: {:.2}", queue.service_rate);
    println!("  利用率: {:.2}", queue.utilization());
    println!("  平均等待时间: {:.2}", queue.average_waiting_time().unwrap_or(0.0));

    // 创建传统线性回归模型
    let mut lr = LinearRegression::new(0.01, 1000);
    
    // 准备数据
    let x_data = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]];
    let y_data = vec![2.0, 4.0, 6.0, 8.0, 10.0];
    
    // 训练模型
    lr.fit(&x_data, &y_data).unwrap();
    
    println!("\n传统线性回归模型:");
    println!("  权重: {:?}", lr.weights);
    println!("  偏置: {:.4}", lr.bias);
    
    // 预测
    let test_data = vec![vec![6.0]];
    let prediction = lr.predict(&test_data);
    println!("  预测 x=6.0: {:?}", prediction);

    // 使用统计工具
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
    
    println!("\n统计工具:");
    println!("  均值: {:.2}", StatisticalTools::mean(&data));
    println!("  标准差: {:.2}", StatisticalTools::standard_deviation(&data));
    println!("  中位数: {:.2}", StatisticalTools::mean(&data));

    // 结合新特性进行高级分析
    let processor = DataProcessor::new(&data, 2);
    let result = processor.process_data();
    
    println!("\n使用 Rust 1.90 新特性分析:");
    println!("  处理器ID: {}", result.processor_id);
    println!("  方差: {:.4}", result.variance);
    println!("  标准差: {:.4}", result.std_dev);

    Ok(())
}
