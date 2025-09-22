//! Rust 1.90 性能基准测试
//!
//! 本基准测试展示了 Rust 1.90 新特性带来的性能提升
//!
//! 运行命令：
//! ```bash
//! cargo bench --bench rust_190_performance_bench
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c12_model::{
    rust_190_features::{
        ModelConfig, DataProcessor, OptimizationEngine, AlgorithmType, OptimizedMatrix
    },
    modern_ml::{
        ModernMLEngine, ModernMLConfig, ModelType, DeviceType, PrecisionType, TrainingData
    },
    queueing_models::MM1Queue,
    ml_models::LinearRegression,
    math_models::StatisticalTools,
};

/// 基准测试：常量泛型推断性能
fn bench_const_generic_inference(c: &mut Criterion) {
    let mut group = c.benchmark_group("const_generic_inference");
    
    // 测试2维模型配置创建
    group.bench_function("model_config_creation_2d", |b| {
        let data: Vec<f64> = (0..2).map(|i| i as f64).collect();
        b.iter(|| {
            let config: ModelConfig<2> = ModelConfig::<2>::from_slice(&data, "test".to_string());
            black_box(config)
        });
    });
    
    // 测试4维模型配置创建
    group.bench_function("model_config_creation_4d", |b| {
        let data: Vec<f64> = (0..4).map(|i| i as f64).collect();
        b.iter(|| {
            let config: ModelConfig<4> = ModelConfig::<4>::from_slice(&data, "test".to_string());
            black_box(config)
        });
    });
    
    // 测试8维模型配置创建
    group.bench_function("model_config_creation_8d", |b| {
        let data: Vec<f64> = (0..8).map(|i| i as f64).collect();
        b.iter(|| {
            let config: ModelConfig<8> = ModelConfig::<8>::from_slice(&data, "test".to_string());
            black_box(config)
        });
    });
    
    // 测试16维模型配置创建
    group.bench_function("model_config_creation_16d", |b| {
        let data: Vec<f64> = (0..16).map(|i| i as f64).collect();
        b.iter(|| {
            let config: ModelConfig<16> = ModelConfig::<16>::from_slice(&data, "test".to_string());
            black_box(config)
        });
    });
    
    // 测试32维模型配置创建
    group.bench_function("model_config_creation_32d", |b| {
        let data: Vec<f64> = (0..32).map(|i| i as f64).collect();
        b.iter(|| {
            let config: ModelConfig<32> = ModelConfig::<32>::from_slice(&data, "test".to_string());
            black_box(config)
        });
    });
    
    group.finish();
}

/// 基准测试：生命周期优化性能
fn bench_lifetime_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("lifetime_optimization");
    
    for size in [100, 1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("data_processing", size), size, |b, &size| {
            let data: Vec<f64> = (0..size).map(|i| (i as f64).sin()).collect();
            let processor = DataProcessor::new(&data, 1);
            
            b.iter(|| {
                black_box(processor.process_data())
            });
        });
    }
    
    group.finish();
}

/// 基准测试：函数指针安全性能
fn bench_function_pointer_safety(c: &mut Criterion) {
    let mut group = c.benchmark_group("function_pointer_safety");
    
    // 定义测试函数
    fn sphere(x: &[f64]) -> f64 {
        x.iter().map(|&xi| xi * xi).sum()
    }
    
    fn rosenbrock(x: &[f64]) -> f64 {
        let mut sum = 0.0;
        for i in 0..x.len() - 1 {
            let a = 1.0 - x[i];
            let b = x[i + 1] - x[i] * x[i];
            sum += a * a + 100.0 * b * b;
        }
        sum
    }
    
    let engine = OptimizationEngine::new(AlgorithmType::GradientDescent);
    let initial = vec![0.0, 0.0];
    
    group.bench_function("sphere_optimization", |b| {
        b.iter(|| {
            black_box(engine.optimize(sphere, None, &initial, 100))
        });
    });
    
    group.bench_function("rosenbrock_optimization", |b| {
        b.iter(|| {
            black_box(engine.optimize(rosenbrock, None, &initial, 100))
        });
    });
    
    group.finish();
}

/// 基准测试：现代机器学习引擎性能
fn bench_modern_ml_engine(c: &mut Criterion) {
    let mut group = c.benchmark_group("modern_ml_engine");
    
    // 准备训练数据
    let mut features = Vec::new();
    let mut labels = Vec::new();
    
    for i in 0..1000 {
        let x = i as f64 * 0.01;
        let y = 2.0 * x + 1.0 + (fastrand::f64() - 0.5) * 0.1;
        features.push(vec![x]);
        labels.push(y);
    }
    
    let training_data = TrainingData {
        features,
        labels,
        val_features: None,
        val_labels: None,
    };
    
    let config = ModernMLConfig {
        model_type: ModelType::LinearRegression,
        device: DeviceType::Cpu,
        precision: PrecisionType::F32,
        batch_size: 32,
        learning_rate: 0.01,
        max_epochs: 50,
        early_stopping_patience: 10,
    };
    
    group.bench_function("linear_regression_training", |b| {
        b.iter(|| {
            let mut engine = ModernMLEngine::new(config.clone());
            let _ = engine.create_model("test".to_string(), ModelType::LinearRegression);
            let _ = engine.train_model("test", &training_data);
            black_box(engine);
        });
    });
    
    group.finish();
}

/// 基准测试：优化矩阵操作性能
fn bench_optimized_matrix_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimized_matrix_operations");
    
    // 测试2x2矩阵乘法
    group.bench_function("matrix_multiplication_2x2", |b| {
        b.iter(|| {
            let mut matrix_a = OptimizedMatrix::<2, 2>::new();
            let mut matrix_b = OptimizedMatrix::<2, 2>::new();
            
            for i in 0..2 {
                for j in 0..2 {
                    matrix_a.set(i, j, (i + j) as f64);
                    matrix_b.set(i, j, (i * j) as f64);
                }
            }
            
            black_box(matrix_a.multiply(&matrix_b))
        });
    });
    
    // 测试4x4矩阵乘法
    group.bench_function("matrix_multiplication_4x4", |b| {
        b.iter(|| {
            let mut matrix_a = OptimizedMatrix::<4, 4>::new();
            let mut matrix_b = OptimizedMatrix::<4, 4>::new();
            
            for i in 0..4 {
                for j in 0..4 {
                    matrix_a.set(i, j, (i + j) as f64);
                    matrix_b.set(i, j, (i * j) as f64);
                }
            }
            
            black_box(matrix_a.multiply(&matrix_b))
        });
    });
    
    // 测试8x8矩阵乘法
    group.bench_function("matrix_multiplication_8x8", |b| {
        b.iter(|| {
            let mut matrix_a = OptimizedMatrix::<8, 8>::new();
            let mut matrix_b = OptimizedMatrix::<8, 8>::new();
            
            for i in 0..8 {
                for j in 0..8 {
                    matrix_a.set(i, j, (i + j) as f64);
                    matrix_b.set(i, j, (i * j) as f64);
                }
            }
            
            black_box(matrix_a.multiply(&matrix_b))
        });
    });
    
    // 测试16x16矩阵乘法
    group.bench_function("matrix_multiplication_16x16", |b| {
        b.iter(|| {
            let mut matrix_a = OptimizedMatrix::<16, 16>::new();
            let mut matrix_b = OptimizedMatrix::<16, 16>::new();
            
            for i in 0..16 {
                for j in 0..16 {
                    matrix_a.set(i, j, (i + j) as f64);
                    matrix_b.set(i, j, (i * j) as f64);
                }
            }
            
            black_box(matrix_a.multiply(&matrix_b))
        });
    });
    
    // 测试2x2矩阵转置
    group.bench_function("matrix_transpose_2x2", |b| {
        b.iter(|| {
            let mut matrix = OptimizedMatrix::<2, 2>::new();
            for i in 0..2 {
                for j in 0..2 {
                    matrix.set(i, j, (i + j) as f64);
                }
            }
            black_box(matrix.transpose())
        });
    });
    
    // 测试4x4矩阵转置
    group.bench_function("matrix_transpose_4x4", |b| {
        b.iter(|| {
            let mut matrix = OptimizedMatrix::<4, 4>::new();
            for i in 0..4 {
                for j in 0..4 {
                    matrix.set(i, j, (i + j) as f64);
                }
            }
            black_box(matrix.transpose())
        });
    });
    
    // 测试8x8矩阵转置
    group.bench_function("matrix_transpose_8x8", |b| {
        b.iter(|| {
            let mut matrix = OptimizedMatrix::<8, 8>::new();
            for i in 0..8 {
                for j in 0..8 {
                    matrix.set(i, j, (i + j) as f64);
                }
            }
            black_box(matrix.transpose())
        });
    });
    
    // 测试16x16矩阵转置
    group.bench_function("matrix_transpose_16x16", |b| {
        b.iter(|| {
            let mut matrix = OptimizedMatrix::<16, 16>::new();
            for i in 0..16 {
                for j in 0..16 {
                    matrix.set(i, j, (i + j) as f64);
                }
            }
            black_box(matrix.transpose())
        });
    });
    
    group.finish();
}

/// 基准测试：传统模型性能对比
fn bench_traditional_models_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("traditional_models_comparison");
    
    // 排队论模型创建性能
    group.bench_function("mm1_queue_creation", |b| {
        b.iter(|| {
            black_box(MM1Queue::new(2.0, 3.0))
        });
    });
    
    // 排队论模型计算性能
    group.bench_function("mm1_queue_calculations", |b| {
        let queue = MM1Queue::new(2.0, 3.0);
        b.iter(|| {
            black_box(queue.utilization());
            let _ = queue.average_waiting_time();
            let _ = queue.average_queue_length();
        });
    });
    
    // 线性回归模型训练性能
    group.bench_function("linear_regression_training", |b| {
        let x_data: Vec<Vec<f64>> = (0..1000).map(|i| vec![i as f64]).collect();
        let y_data: Vec<f64> = x_data.iter().map(|x| 2.0 * x[0] + 1.0).collect();
        
        b.iter(|| {
            let mut lr = LinearRegression::new(0.01, 100);
            let _ = lr.fit(&x_data, &y_data);
            black_box(lr);
        });
    });
    
    // 统计工具性能
    group.bench_function("statistical_tools", |b| {
        let data: Vec<f64> = (0..10000).map(|i| (i as f64).sin()).collect();
        
        b.iter(|| {
            black_box(StatisticalTools::mean(&data));
            black_box(StatisticalTools::standard_deviation(&data));
            black_box(StatisticalTools::median(&data));
        });
    });
    
    group.finish();
}

/// 基准测试：内存使用效率
fn bench_memory_efficiency(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");
    
    // 测试大量数据处理的内存效率
    group.bench_function("large_data_processing", |b| {
        let data: Vec<f64> = (0..100000).map(|i| (i as f64).sin()).collect();
        let processor = DataProcessor::new(&data, 1);
        
        b.iter(|| {
            black_box(processor.process_data())
        });
    });
    
    // 测试矩阵操作的内存效率
    group.bench_function("large_matrix_operations", |b| {
        let mut matrix_a = OptimizedMatrix::<32, 32>::new();
        let mut matrix_b = OptimizedMatrix::<32, 32>::new();
        
        for i in 0..32 {
            for j in 0..32 {
                matrix_a.set(i, j, (i + j) as f64);
                matrix_b.set(i, j, (i * j) as f64);
            }
        }
        
        b.iter(|| {
            black_box(matrix_a.multiply(&matrix_b))
        });
    });
    
    group.finish();
}

/// 基准测试：并发性能
fn bench_concurrent_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_performance");
    
    use std::thread;
    
    // 测试多线程数据处理
    group.bench_function("multi_thread_data_processing", |b| {
        let data: Vec<f64> = (0..10000).map(|i| (i as f64).sin()).collect();
        
        b.iter(|| {
            let handles: Vec<_> = (0..4).map(|i| {
                let data_clone = data.clone();
                thread::spawn(move || {
                    let processor = DataProcessor::new(&data_clone, i);
                    let result = processor.process_data();
                    // 返回拥有的数据而不是引用
                    (result.mean, result.variance, result.std_dev, result.processor_id)
                })
            }).collect();
            
            let results: Vec<_> = handles.into_iter()
                .map(|h| h.join().unwrap())
                .collect();
            
            black_box(results);
        });
    });
    
    group.finish();
}

/// 基准测试：编译时优化效果
fn bench_compile_time_optimizations(c: &mut Criterion) {
    let mut group = c.benchmark_group("compile_time_optimizations");
    
    // 测试常量泛型带来的编译时优化
    group.bench_function("const_generic_optimization", |b| {
        b.iter(|| {
            let config = ModelConfig::<4>::new([1.0, 2.0, 3.0, 4.0], "test".to_string());
            black_box(config.statistics())
        });
    });
    
    // 测试内联优化
    group.bench_function("inline_optimization", |b| {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let processor = DataProcessor::new(&data, 1);
        
        b.iter(|| {
            black_box(processor.quantiles(0.5))
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_const_generic_inference,
    bench_lifetime_optimization,
    bench_function_pointer_safety,
    bench_modern_ml_engine,
    bench_optimized_matrix_operations,
    bench_traditional_models_comparison,
    bench_memory_efficiency,
    bench_concurrent_performance,
    bench_compile_time_optimizations
);

criterion_main!(benches);