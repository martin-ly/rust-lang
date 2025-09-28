use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ai_ml_frameworks::{
    MLFramework, ModelType, HardwareAcceleration, ModelPerformance, MLFrameworkAnalyzer,
    MLBenchmarker, BenchmarkConfig, BenchmarkScenario
};
use std::time::Duration;

fn benchmark_ml_frameworks(c: &mut Criterion) {
    let mut group = c.benchmark_group("ml_frameworks");
    
    // 模拟Transformer模型推理
    group.bench_function("transformer_inference", |b| {
        b.iter(|| {
            // 模拟Transformer模型推理
            std::thread::sleep(Duration::from_millis(100));
            black_box(())
        })
    });
    
    // 模拟CNN模型推理
    group.bench_function("cnn_inference", |b| {
        b.iter(|| {
            // 模拟CNN模型推理
            std::thread::sleep(Duration::from_millis(50));
            black_box(())
        })
    });
    
    // 模拟线性模型推理
    group.bench_function("linear_inference", |b| {
        b.iter(|| {
            // 模拟线性模型推理
            std::thread::sleep(Duration::from_millis(10));
            black_box(())
        })
    });
    
    // 模拟矩阵运算
    group.bench_function("matrix_operations", |b| {
        b.iter(|| {
            // 模拟矩阵运算
            let mut result = vec![0.0; 1000];
            for i in 0..1000 {
                result[i] = (i as f64).sin() * (i as f64).cos();
            }
            black_box(result)
        })
    });
    
    group.finish();
}

fn benchmark_analyzer_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("ml_framework_analyzer");
    
    group.bench_function("analyzer_creation", |b| {
        b.iter(|| {
            let analyzer = MLFrameworkAnalyzer::new();
            black_box(analyzer)
        })
    });
    
    group.bench_function("report_generation", |b| {
        b.iter(|| {
            let mut analyzer = MLFrameworkAnalyzer::new();
            
            // 添加示例性能数据
            analyzer.add_performance(ModelPerformance {
                framework: MLFramework::Candle,
                model_type: ModelType::Transformer,
                hardware: HardwareAcceleration::CPU,
                inference_time: Duration::from_millis(100),
                throughput: 100.0,
                memory_usage: 1024 * 1024,
                gpu_memory_usage: None,
                accuracy: Some(0.95),
                model_size: 100 * 1024 * 1024,
            });
            
            let report = analyzer.generate_performance_report();
            black_box(report)
        })
    });
    
    group.bench_function("recommendation_engine", |b| {
        b.iter(|| {
            let analyzer = MLFrameworkAnalyzer::new();
            let framework_rec = analyzer.get_framework_recommendation("research");
            let hardware_rec = analyzer.get_hardware_recommendation(100_000_000, "high");
            black_box((framework_rec, hardware_rec))
        })
    });
    
    group.finish();
}

fn benchmark_scenario_testing(c: &mut Criterion) {
    let mut group = c.benchmark_group("scenario_testing");
    
    // 测试不同场景的基准测试
    group.bench_function("single_inference", |b| {
        b.iter(|| {
            let mut benchmarker = MLBenchmarker::new();
            let config = BenchmarkConfig {
                iterations: 100,
                batch_size: 1,
                concurrent_tasks: 1,
                memory_limit_mb: None,
                scenario: BenchmarkScenario::SingleInference,
            };
            
            let result = benchmarker.benchmark_scenario(
                MLFramework::Candle,
                ModelType::Transformer,
                HardwareAcceleration::CPU,
                config,
            );
            black_box(result)
        })
    });
    
    group.bench_function("batch_inference", |b| {
        b.iter(|| {
            let mut benchmarker = MLBenchmarker::new();
            let config = BenchmarkConfig {
                iterations: 100,
                batch_size: 32,
                concurrent_tasks: 1,
                memory_limit_mb: None,
                scenario: BenchmarkScenario::BatchInference,
            };
            
            let result = benchmarker.benchmark_scenario(
                MLFramework::Candle,
                ModelType::CNN,
                HardwareAcceleration::CPU,
                config,
            );
            black_box(result)
        })
    });
    
    group.bench_function("high_concurrency", |b| {
        b.iter(|| {
            let mut benchmarker = MLBenchmarker::new();
            let config = BenchmarkConfig {
                iterations: 100,
                batch_size: 16,
                concurrent_tasks: 8,
                memory_limit_mb: None,
                scenario: BenchmarkScenario::HighConcurrency,
            };
            
            let result = benchmarker.benchmark_scenario(
                MLFramework::Candle,
                ModelType::Linear,
                HardwareAcceleration::CPU,
                config,
            );
            black_box(result)
        })
    });
    
    group.bench_function("memory_constrained", |b| {
        b.iter(|| {
            let mut benchmarker = MLBenchmarker::new();
            let config = BenchmarkConfig {
                iterations: 100,
                batch_size: 8,
                concurrent_tasks: 2,
                memory_limit_mb: Some(512),
                scenario: BenchmarkScenario::MemoryConstrained,
            };
            
            let result = benchmarker.benchmark_scenario(
                MLFramework::Candle,
                ModelType::RNN,
                HardwareAcceleration::CPU,
                config,
            );
            black_box(result)
        })
    });
    
    group.finish();
}

criterion_group!(benches, benchmark_ml_frameworks, benchmark_analyzer_performance, benchmark_scenario_testing);
criterion_main!(benches);
