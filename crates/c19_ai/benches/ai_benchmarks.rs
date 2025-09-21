//! AI/ML 性能基准测试
//! 
//! 本文件包含各种AI/ML算法的性能基准测试，用于评估2025年最新优化后的性能

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use ndarray::{Array2, Array3};
use rand::{Rng, rng};

/// 神经网络前向传播基准测试
fn bench_neural_network_forward(c: &mut Criterion) {
    let mut group = c.benchmark_group("neural_network_forward");
    
    // 测试不同大小的网络
    let sizes = [(100, 50), (500, 250), (1000, 500)];
    
    for (input_size, hidden_size) in sizes.iter() {
        let mut rng = rng();
        let input = Array2::from_shape_fn((*input_size, 1), |_| rng.random::<f64>());
        let weights1 = Array2::from_shape_fn((*hidden_size, *input_size), |_| rng.random::<f64>());
        let weights2 = Array2::from_shape_fn((1, *hidden_size), |_| rng.random::<f64>());
        
        group.bench_with_input(
            BenchmarkId::new("forward_pass", format!("{}x{}", input_size, hidden_size)),
            &(input_size, hidden_size),
            |b, _| {
                b.iter(|| {
                    // 模拟前向传播
                    let hidden = weights1.dot(&input);
                    let output = weights2.dot(&hidden);
                    output
                })
            }
        );
    }
    
    group.finish();
}

/// 矩阵运算基准测试
fn bench_matrix_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("matrix_operations");
    
    let sizes = [100, 500, 1000];
    
    for size in sizes.iter() {
        let mut rng = rng();
        let a = Array2::from_shape_fn((*size, *size), |_| rng.random::<f64>());
        let b = Array2::from_shape_fn((*size, *size), |_| rng.random::<f64>());
        
        group.bench_with_input(BenchmarkId::new("matrix_multiply", size), size, |bench, _| {
            bench.iter(|| {
                a.dot(&b)
            })
        });
        
        group.bench_with_input(BenchmarkId::new("matrix_add", size), size, |bench, _| {
            bench.iter(|| {
                &a + &b
            })
        });
    }
    
    group.finish();
}

/// 卷积操作基准测试
fn bench_convolution_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("convolution_operations");
    
    let sizes = [(32, 32), (64, 64), (128, 128)];
    
    for (height, width) in sizes.iter() {
        let mut rng = rng();
        let input = Array3::from_shape_fn((3, *height, *width), |_| rng.random::<f64>());
        let kernel = Array3::from_shape_fn((3, 3, 3), |_| rng.random::<f64>());
        
        group.bench_with_input(
            BenchmarkId::new("conv2d", format!("{}x{}", height, width)),
            &(height, width),
            |b, _| {
                b.iter(|| {
                    // 简化的卷积操作
                    let mut output = Array3::zeros((3, height - 2, width - 2));
                    for c in 0..3 {
                        for h in 0..height - 2 {
                            for w in 0..width - 2 {
                                let mut sum = 0.0;
                                for kc in 0..3 {
                                    for kh in 0..3 {
                                        for kw in 0..3 {
                                            sum += input[[c, h + kh, w + kw]] * kernel[[kc, kh, kw]];
                                        }
                                    }
                                }
                                output[[c, h, w]] = sum;
                            }
                        }
                    }
                    output
                })
            }
        );
    }
    
    group.finish();
}

/// 梯度下降基准测试
fn bench_gradient_descent(c: &mut Criterion) {
    let mut group = c.benchmark_group("gradient_descent");
    
    let sizes = [100, 1000, 10000];
    
    for size in sizes.iter() {
        let mut rng = rng();
        let x = Array2::from_shape_fn((*size, 1), |_| rng.random::<f64>());
        let y = Array2::from_shape_fn((*size, 1), |_| rng.random::<f64>());
        let mut weights = Array2::zeros((1, 1));
        let learning_rate = 0.01;
        
        group.bench_with_input(BenchmarkId::new("gradient_descent", size), size, |b, _| {
            b.iter(|| {
                // 简化的梯度下降
                let predictions = weights.dot(&x);
                let error = &predictions - &y;
                let gradient = error.dot(&x.t()) / *size as f64;
                weights = &weights - learning_rate * &gradient;
                weights.clone()
            })
        });
    }
    
    group.finish();
}

/// 数据预处理基准测试
fn bench_data_preprocessing(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_preprocessing");
    
    let sizes = [1000, 10000, 100000];
    
    for size in sizes.iter() {
        let data: Vec<f64> = (0..*size).map(|i| i as f64).collect();
        
        group.bench_with_input(BenchmarkId::new("normalization", size), size, |b, _| {
            b.iter(|| {
                let mean = data.iter().sum::<f64>() / *size as f64;
                let variance = data.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / *size as f64;
                let std = variance.sqrt();
                data.iter().map(|x| (x - mean) / std).collect::<Vec<_>>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("scaling", size), size, |b, _| {
            b.iter(|| {
                let min = data.iter().fold(f64::INFINITY, |a, &b| a.min(b));
                let max = data.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
                data.iter().map(|x| (x - min) / (max - min)).collect::<Vec<_>>()
            })
        });
    }
    
    group.finish();
}

/// 特征提取基准测试
fn bench_feature_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("feature_extraction");
    
    let sizes = [100, 1000, 10000];
    
    for size in sizes.iter() {
        let data: Vec<f64> = (0..*size).map(|i| (i as f64).sin()).collect();
        
        group.bench_with_input(BenchmarkId::new("statistical_features", size), size, |b, _| {
            b.iter(|| {
                let mean = data.iter().sum::<f64>() / *size as f64;
                let variance = data.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / *size as f64;
                let skewness = data.iter().map(|x| ((x - mean) / variance.sqrt()).powi(3)).sum::<f64>() / *size as f64;
                let kurtosis = data.iter().map(|x| ((x - mean) / variance.sqrt()).powi(4)).sum::<f64>() / *size as f64;
                (mean, variance, skewness, kurtosis)
            })
        });
        
        group.bench_with_input(BenchmarkId::new("frequency_features", size), size, |b, _| {
            b.iter(|| {
                // 简化的FFT
                let mut real = data.clone();
                let mut imag = vec![0.0; *size];
                
                // 简化的DFT
                for k in 0..*size {
                    let mut sum_real = 0.0;
                    let mut sum_imag = 0.0;
                    for n in 0..*size {
                        let angle = -2.0 * std::f64::consts::PI * k as f64 * n as f64 / *size as f64;
                        sum_real += data[n] * angle.cos();
                        sum_imag += data[n] * angle.sin();
                    }
                    real[k] = sum_real;
                    imag[k] = sum_imag;
                }
                
                (real, imag)
            })
        });
    }
    
    group.finish();
}

/// 模型推理基准测试
fn bench_model_inference(c: &mut Criterion) {
    let mut group = c.benchmark_group("model_inference");
    
    let batch_sizes = [1, 10, 100];
    
    for batch_size in batch_sizes.iter() {
        let mut rng = rng();
        let input = Array2::from_shape_fn((*batch_size, 784), |_| rng.random::<f64>());
        let weights = Array2::from_shape_fn((784, 10), |_| rng.random::<f64>());
        let bias = Array2::from_shape_fn((1, 10), |_| rng.random::<f64>());
        
        group.bench_with_input(BenchmarkId::new("linear_layer", batch_size), batch_size, |b, _| {
            b.iter(|| {
                input.dot(&weights) + &bias
            })
        });
        
        group.bench_with_input(BenchmarkId::new("relu_activation", batch_size), batch_size, |b, _| {
            b.iter(|| {
                input.mapv(|x| x.max(0.0))
            })
        });
        
        group.bench_with_input(BenchmarkId::new("softmax", batch_size), batch_size, |b, _| {
            b.iter(|| {
                let exp = input.mapv(|x| x.exp());
                let sum = exp.sum();
                exp / sum
            })
        });
    }
    
    group.finish();
}

/// 内存分配基准测试
fn bench_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");
    
    let sizes = [1000, 10000, 100000];
    
    for size in sizes.iter() {
        group.bench_with_input(BenchmarkId::new("array_allocation", size), size, |b, _| {
            b.iter(|| {
                Array2::<f64>::zeros((*size, *size))
            })
        });
        
        group.bench_with_input(BenchmarkId::new("vector_allocation", size), size, |b, _| {
            b.iter(|| {
                vec![0.0; *size * *size]
            })
        });
    }
    
    group.finish();
}

/// 并行计算基准测试
fn bench_parallel_computing(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel_computing");
    
    let size = 10000;
    let data: Vec<f64> = (0..size).map(|i| i as f64).collect();
    
    group.bench_function("parallel_map", |b| {
        b.iter(|| {
            use rayon::prelude::*;
            data.par_iter().map(|x| x * 2.0).collect::<Vec<_>>()
        })
    });
    
    group.bench_function("sequential_map", |b| {
        b.iter(|| {
            data.iter().map(|x| x * 2.0).collect::<Vec<_>>()
        })
    });
    
    group.bench_function("parallel_reduce", |b| {
        b.iter(|| {
            use rayon::prelude::*;
            data.par_iter().sum::<f64>()
        })
    });
    
    group.bench_function("sequential_reduce", |b| {
        b.iter(|| {
            data.iter().sum::<f64>()
        })
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_neural_network_forward,
    bench_matrix_operations,
    bench_convolution_operations,
    bench_gradient_descent,
    bench_data_preprocessing,
    bench_feature_extraction,
    bench_model_inference,
    bench_memory_allocation,
    bench_parallel_computing
);

criterion_main!(benches);
