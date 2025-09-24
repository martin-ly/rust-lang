//! 异常检测性能基准测试
//!
//! 测试各种异常检测器的性能表现。

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use c13_reliability::runtime_monitoring::anomaly_detection::*;
use c13_reliability::runtime_monitoring::MonitoringState;
use std::time::Duration;
use std::hint::black_box;

/// 基准测试：配置创建性能
fn bench_config_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("config_creation");
    
    group.bench_function("default_config", |b| {
        b.iter(|| AnomalyDetectionConfig::default())
    });
    
    group.bench_function("custom_config", |b| {
        b.iter(|| {
            AnomalyDetectionConfig {
                detection_interval: Duration::from_secs(30),
                enabled: true,
                detectors: vec![
                    AnomalyDetectorItem {
                        name: "statistical".to_string(),
                        detector_type: AnomalyDetectorType::Statistical,
                        enabled: true,
                    },
                    AnomalyDetectorItem {
                        name: "threshold".to_string(),
                        detector_type: AnomalyDetectorType::Threshold,
                        enabled: true,
                    },
                ],
                alert_thresholds: AnomalyAlertThresholds {
                    statistical_threshold: 2.5,
                    threshold_anomaly_threshold: 0.8,
                    ml_anomaly_threshold: 0.7,
                    time_series_threshold: 0.75,
                    pattern_matching_threshold: 0.6,
                    network_traffic_threshold: 0.85,
                    resource_usage_threshold: 0.9,
                },
            }
        })
    });
    
    group.finish();
}

/// 基准测试：检测器创建性能
fn bench_detector_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("detector_creation");
    
    for detector_count in [1, 3, 6, 10, 20].iter() {
        group.bench_with_input(
            BenchmarkId::new("detectors", detector_count),
            detector_count,
            |b, &count| {
                b.iter(|| {
                    let config = AnomalyDetectionConfig {
                        detection_interval: Duration::from_secs(1),
                        enabled: true,
                        detectors: (0..count)
                            .map(|i| AnomalyDetectorItem {
                                name: format!("detector_{}", i),
                                detector_type: match i % 6 {
                                    0 => AnomalyDetectorType::Statistical,
                                    1 => AnomalyDetectorType::Threshold,
                                    2 => AnomalyDetectorType::TimeSeries,
                                    3 => AnomalyDetectorType::PatternMatching,
                                    4 => AnomalyDetectorType::NetworkTraffic,
                                    _ => AnomalyDetectorType::ResourceUsage,
                                },
                                enabled: true,
                            })
                            .collect(),
                        alert_thresholds: AnomalyAlertThresholds::default(),
                    };
                    
                    AnomalyDetector::new(config)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：序列化性能
fn bench_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("serialization");
    
    let result = AnomalyDetectionResult {
        timestamp: chrono::Utc::now(),
        state: MonitoringState::Warning,
        items: vec![
            AnomalyDetectorItemResult {
                name: "statistical".to_string(),
                detector_type: AnomalyDetectorType::Statistical,
                state: MonitoringState::Healthy,
                anomaly_score: 0.5,
                anomaly_detected: false,
                anomaly_details: std::collections::HashMap::new(),
            },
            AnomalyDetectorItemResult {
                name: "threshold".to_string(),
                detector_type: AnomalyDetectorType::Threshold,
                state: MonitoringState::Warning,
                anomaly_score: 0.8,
                anomaly_detected: true,
                anomaly_details: {
                    let mut map = std::collections::HashMap::new();
                    map.insert("threshold".to_string(), "0.8".to_string());
                    map.insert("current_value".to_string(), "0.85".to_string());
                    map
                },
            },
        ],
        total_detectors: 2,
        normal_detectors: 1,
        anomaly_detectors: 1,
        anomalies_detected: 1,
    };
    
    group.bench_function("serialize_json", |b| {
        b.iter(|| serde_json::to_string(black_box(&result)))
    });
    
    group.bench_function("deserialize_json", |b| {
        let json = serde_json::to_string(&result).unwrap();
        b.iter(|| serde_json::from_str::<AnomalyDetectionResult>(black_box(&json)))
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_config_creation,
    bench_detector_creation,
    bench_serialization
);
criterion_main!(benches);