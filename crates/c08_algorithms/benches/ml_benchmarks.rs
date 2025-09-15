use c08_algorithms::machine_learning::*;
use c08_algorithms::machine_learning::clustering::*;
use c08_algorithms::machine_learning::neural_network::*;
use c08_algorithms::machine_learning::regression::*;
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

fn generate_synthetic_data(n_samples: usize, n_features: usize) -> (Dataset, Labels) {
    use rand::{Rng, rngs::ThreadRng};
    let mut rng = ThreadRng::default();
    
    let mut data = Vec::with_capacity(n_samples);
    let mut labels = Vec::with_capacity(n_samples);
    
    for _ in 0..n_samples {
        let sample: Vec<f64> = (0..n_features)
            .map(|_| rng.random_range(-1.0..1.0))
            .collect();
        
        // 简单的分类规则：特征和大于0为类别1，否则为类别0
        let label = if sample.iter().sum::<f64>() > 0.0 { 1 } else { 0 };
        
        data.push(sample);
        labels.push(label);
    }
    
    (data, labels)
}

fn generate_regression_data(n_samples: usize, n_features: usize) -> (Dataset, Vec<f64>) {
    use rand::{Rng, rngs::ThreadRng};
    let mut rng = ThreadRng::default();
    
    let mut data = Vec::with_capacity(n_samples);
    let mut targets = Vec::with_capacity(n_samples);
    
    for _ in 0..n_samples {
        let sample: Vec<f64> = (0..n_features)
            .map(|_| rng.random_range(-1.0..1.0))
            .collect();
        
        // 线性关系：y = sum(x) + noise
        let target = sample.iter().sum::<f64>() + rng.random_range(-0.1..0.1);
        
        data.push(sample);
        targets.push(target);
    }
    
    (data, targets)
}

fn benchmark_kmeans(c: &mut Criterion) {
    let (data, _) = generate_synthetic_data(1000, 10);
    
    c.bench_function("kmeans_clustering_1000_samples", |b| {
        b.iter(|| {
            let mut kmeans = KMeans::new(5);
            kmeans.fit(black_box(&data)).unwrap();
            kmeans.predict(black_box(&data)).unwrap()
        })
    });
}

fn benchmark_neural_network_training(c: &mut Criterion) {
    let (data, targets) = generate_regression_data(500, 5);
    
    c.bench_function("mlp_regression_training_500_samples", |b| {
        b.iter(|| {
            let layer_sizes = vec![5, 10, 1];
            let activations = vec![ActivationFunction::ReLU, ActivationFunction::Linear];
            let mut mlp = MLP::new(&layer_sizes, activations, 0.01).unwrap();
            Regression::train(&mut mlp, black_box(&data), black_box(&targets)).unwrap()
        })
    });
}

fn benchmark_linear_regression(c: &mut Criterion) {
    let (data, targets) = generate_regression_data(1000, 10);
    
    c.bench_function("linear_regression_1000_samples", |b| {
        b.iter(|| {
            let mut lr = LinearRegression::new();
            lr.train(black_box(&data), black_box(&targets)).unwrap()
        })
    });
}

fn benchmark_data_preprocessing(c: &mut Criterion) {
    let (data, _) = generate_synthetic_data(5000, 20);
    
    c.bench_function("data_standardization_5000_samples", |b| {
        b.iter(|| {
            let mut data_copy = data.clone();
            preprocessing::standardize(black_box(&mut data_copy)).unwrap()
        })
    });
    
    c.bench_function("data_normalization_5000_samples", |b| {
        b.iter(|| {
            let mut data_copy = data.clone();
            preprocessing::normalize(black_box(&mut data_copy)).unwrap()
        })
    });
}

fn benchmark_clustering_metrics(c: &mut Criterion) {
    let (data, labels) = generate_synthetic_data(1000, 10);
    
    c.bench_function("silhouette_score_1000_samples", |b| {
        b.iter(|| {
            ClusteringMetrics::silhouette_score(black_box(&data), black_box(&labels)).unwrap()
        })
    });
    
    c.bench_function("davies_bouldin_score_1000_samples", |b| {
        b.iter(|| {
            ClusteringMetrics::davies_bouldin_score(black_box(&data), black_box(&labels)).unwrap()
        })
    });
}

fn benchmark_ml_performance_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("ML_Algorithm_Comparison");
    
    // 生成不同大小的数据集进行对比
    for size in [100, 500, 1000].iter() {
        let (data, _labels) = generate_synthetic_data(*size, 5);
        let (reg_data, targets) = generate_regression_data(*size, 5);
        
        // K-means 聚类性能
        group.bench_with_input(format!("KMeans_{}_samples", size), size, |b, _| {
            b.iter(|| {
                let mut kmeans = KMeans::new(3);
                kmeans.fit(&data).unwrap();
                kmeans.predict(&data).unwrap()
            })
        });
        
        // 线性回归性能
        group.bench_with_input(format!("LinearRegression_{}_samples", size), size, |b, _| {
            b.iter(|| {
                let mut lr = LinearRegression::new();
                lr.train(&reg_data, &targets).unwrap()
            })
        });
        
        // 神经网络性能
        group.bench_with_input(format!("MLP_{}_samples", size), size, |b, _| {
            b.iter(|| {
                let layer_sizes = vec![5, 8, 1];
                let activations = vec![ActivationFunction::ReLU, ActivationFunction::Linear];
                let mut mlp = MLP::new(&layer_sizes, activations, 0.1).unwrap();
                // 减少训练轮数以加快基准测试
                for (sample, &target) in reg_data.iter().zip(targets.iter()).take(10) {
                    mlp.train_step(sample, &[target]).unwrap();
                }
            })
        });
    }
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_kmeans,
    benchmark_neural_network_training,
    benchmark_linear_regression,
    benchmark_data_preprocessing,
    benchmark_clustering_metrics,
    benchmark_ml_performance_comparison
);
criterion_main!(benches);
