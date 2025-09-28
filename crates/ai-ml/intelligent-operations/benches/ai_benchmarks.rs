//! AI模块基准测试

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use intelligent_operations::{
    IntelligentOperationsEngine, TimeSeriesData, MetricDataPoint, PerformanceSnapshot
};
use std::collections::HashMap;
use std::time::Duration;

fn benchmark_prediction_training(c: &mut Criterion) {
    let mut group = c.benchmark_group("prediction_training");
    
    group.bench_function("train_model", |b| {
        let mut engine = IntelligentOperationsEngine::new();
        
        b.iter(|| {
            black_box(engine.train_prediction_model("cpu_usage"));
        });
    });
    
    group.finish();
}

fn benchmark_anomaly_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("anomaly_detection");
    
    group.bench_function("detect_anomalies", |b| {
        let engine = IntelligentOperationsEngine::new();
        let data = vec![
            MetricDataPoint {
                timestamp: 1000,
                metric_name: "cpu_usage".to_string(),
                value: 50.0,
                tags: HashMap::new(),
                metadata: HashMap::new(),
            },
            MetricDataPoint {
                timestamp: 1001,
                metric_name: "cpu_usage".to_string(),
                value: 95.0,
                tags: HashMap::new(),
                metadata: HashMap::new(),
            },
        ];
        
        b.iter(|| {
            black_box(engine.detect_anomalies("cpu_usage", &data));
        });
    });
    
    group.finish();
}

fn benchmark_performance_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_analysis");
    
    group.bench_function("generate_optimization_suggestions", |b| {
        let mut engine = IntelligentOperationsEngine::new();
        
        // 添加性能快照
        let snapshot = PerformanceSnapshot {
            timestamp: 1000,
            cpu_usage: 85.0,
            memory_usage: 90.0,
            disk_usage: 70.0,
            network_usage: 60.0,
            response_time: Duration::from_millis(600),
            throughput: 800.0,
            error_rate: 0.05,
        };
        engine.record_performance_snapshot(snapshot);
        
        b.iter(|| {
            black_box(engine.generate_optimization_suggestions());
        });
    });
    
    group.finish();
}

criterion_group!(benches, benchmark_prediction_training, benchmark_anomaly_detection, benchmark_performance_analysis);
criterion_main!(benches);
