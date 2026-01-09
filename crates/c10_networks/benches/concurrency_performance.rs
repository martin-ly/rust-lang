//! 并发性能基准测试
//!
//! 这个模块包含了 c10_networks 库并发处理相关的性能基准测试

use c10_networks::{
    error::{ErrorRecovery, NetworkError, ErrorStats, ProtocolError, PerformanceError, SecurityError},
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 错误创建性能测试
fn bench_error_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_creation");

    group.bench_function("network_error", |b| {
        b.iter(|| {
            let error = NetworkError::Timeout(black_box(Duration::from_secs(5)));
            black_box(error)
        })
    });

    group.bench_function("protocol_error", |b| {
        b.iter(|| {
            let error = ProtocolError::Http {
                status: black_box(400),
                message: black_box("Bad Request".to_string()),
            };
            black_box(error)
        })
    });

    group.bench_function("performance_error", |b| {
        b.iter(|| {
            let error = PerformanceError::HighLoad { load: black_box(95.0) };
            black_box(error)
        })
    });

    group.bench_function("security_error", |b| {
        b.iter(|| {
            let error = SecurityError::CertificateVerification(black_box("test".to_string()));
            black_box(error)
        })
    });

    group.finish();
}

/// 错误恢复性能测试
fn bench_error_recovery(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_recovery");

    group.bench_function("is_retryable", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));
        b.iter(|| {
            let retryable = black_box(&error).is_retryable();
            black_box(retryable)
        })
    });

    group.bench_function("retry_delay", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));
        b.iter(|| {
            let delay = black_box(&error).retry_delay();
            black_box(delay)
        })
    });

    group.bench_function("max_retries", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));
        b.iter(|| {
            let max_retries = black_box(&error).max_retries();
            black_box(max_retries)
        })
    });

    group.bench_function("should_retry", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));
        b.iter(|| {
            let should_retry = black_box(&error).is_retryable() &&
                black_box(&error).max_retries().map_or(false, |max| 3 < max);
            black_box(should_retry)
        })
    });

    group.finish();
}

/// 错误统计性能测试
fn bench_error_stats(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_stats");

    group.bench_function("stats_creation", |b| {
        b.iter(|| {
            let stats = ErrorStats::default();
            black_box(stats)
        })
    });

    group.bench_function("stats_record", |b| {
        let mut stats = ErrorStats::default();
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            stats.record_error(black_box(&error));
        })
    });

    group.bench_function("stats_get_count", |b| {
        let mut stats = ErrorStats::default();
        let error = NetworkError::Timeout(Duration::from_secs(5));
        stats.record_error(&error);

        b.iter(|| {
            let count = stats.timeout_errors;
            black_box(count)
        })
    });

    group.bench_function("stats_get_total", |b| {
        let mut stats = ErrorStats::default();
        let error = NetworkError::Timeout(Duration::from_secs(5));
        stats.record_error(&error);

        b.iter(|| {
            let total = stats.total_errors;
            black_box(total)
        })
    });

    group.bench_function("stats_reset", |b| {
        let mut stats = ErrorStats::default();
        let error = NetworkError::Timeout(Duration::from_secs(5));
        stats.record_error(&error);

        b.iter(|| {
            stats = ErrorStats::default();
        })
    });

    group.finish();
}

/// 错误传播性能测试
fn bench_error_propagation(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_propagation");

    group.bench_function("result_creation", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(black_box(NetworkError::Timeout(Duration::from_secs(5))));
            black_box(result)
        })
    });

    group.bench_function("result_match", |b| {
        let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

        b.iter(|| {
            match black_box(&result) {
                Ok(_) => black_box(0),
                Err(e) => black_box(e.max_retries().unwrap_or(0)),
            }
        })
    });

    group.bench_function("result_map", |b| {
        let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

        b.iter(|| {
            let mapped = black_box(&result).as_ref().map_err(|e| e.max_retries().unwrap_or(0));
            black_box(mapped)
        })
    });

    group.bench_function("result_and_then", |b| {
        let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

        b.iter(|| {
            let chained = black_box(&result).as_ref().map(|_| ());
            black_box(chained)
        })
    });

    group.finish();
}

/// 错误处理链性能测试
fn bench_error_handling_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling_chain");

    group.bench_function("simple_chain", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            let processed = result
                .map_err(|e| e.max_retries().unwrap_or(0))
                .and_then(|_| Ok(()))
                .map_err(|retries| NetworkError::Timeout(Duration::from_secs(retries as u64)));

            black_box(processed)
        })
    });

    group.bench_function("complex_chain", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            let processed = result
                .map_err(|e| e.max_retries().unwrap_or(0))
                .and_then(|_| Ok(()))
                .map_err(|retries| NetworkError::Timeout(Duration::from_secs(retries as u64)))
                .and_then(|_| Ok(()))
                .map_err(|e| e.retry_delay().unwrap_or(Duration::from_millis(100)));

            black_box(processed)
        })
    });

    group.bench_function("nested_chain", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            let processed = result
                .map_err(|e| e.max_retries().unwrap_or(0))
                .and_then(|_| {
                    let inner_result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(3)));
                    inner_result.map_err(|e| e.max_retries().unwrap_or(0))
                })
                .map_err(|retries| NetworkError::Timeout(Duration::from_secs(retries as u64)));

            black_box(processed)
        })
    });

    group.finish();
}

/// 错误日志记录性能测试
fn bench_error_logging(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_logging");

    group.bench_function("error_to_string", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let error_str = black_box(&error).to_string();
            black_box(error_str)
        })
    });

    group.bench_function("error_debug", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let debug_str = format!("{:?}", black_box(&error));
            black_box(debug_str)
        })
    });

    group.bench_function("error_display", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let display_str = format!("{}", black_box(&error));
            black_box(display_str)
        })
    });

    group.finish();
}

/// 错误序列化性能测试
fn bench_error_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_serialization");

    group.bench_function("error_to_string", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let serialized = black_box(&error).to_string();
            black_box(serialized)
        })
    });

    group.bench_function("error_debug_format", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let debug_str = format!("{:?}", black_box(&error));
            black_box(debug_str)
        })
    });

    group.bench_function("error_display_format", |b| {
        let error = NetworkError::Timeout(Duration::from_secs(5));

        b.iter(|| {
            let display_str = format!("{}", black_box(&error));
            black_box(display_str)
        })
    });

    group.finish();
}

/// 错误处理性能测试
fn bench_error_handling_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling_performance");

    group.bench_function("error_handling_overhead", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            match result {
                Ok(_) => black_box(0),
                Err(e) => {
                    let retryable = e.is_retryable();
                    let delay = e.retry_delay().unwrap_or(Duration::from_millis(100));
                    let max_retries = e.max_retries().unwrap_or(0);
                    black_box(retryable as u64 + delay.as_secs() + max_retries as u64)
                }
            }
        })
    });

    group.bench_function("error_handling_with_stats", |b| {
        let mut stats = ErrorStats::default();

        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            match result {
                Ok(_) => black_box(0),
                Err(e) => {
                    stats.record_error(&e);
                    let retryable = e.is_retryable();
                    let delay = e.retry_delay().unwrap_or(Duration::from_millis(100));
                    let max_retries = e.max_retries().unwrap_or(0);
                    black_box(retryable as u64 + delay.as_secs() + max_retries as u64)
                }
            }
        })
    });

    group.bench_function("error_handling_with_recovery", |b| {
        b.iter(|| {
            let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

            match result {
                Ok(_) => black_box(0),
                Err(e) => {
                    if e.is_retryable() {
                        let delay = e.retry_delay().unwrap_or(Duration::from_millis(100));
                        let max_retries = e.max_retries().unwrap_or(0);
                        black_box(delay.as_secs() + max_retries as u64)
                    } else {
                        black_box(0)
                    }
                }
            }
        })
    });

    group.finish();
}

/// 错误处理并发性能测试
fn bench_error_handling_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling_concurrency");

    group.bench_function("concurrent_error_stats", |b| {
        let stats = Arc::new(Mutex::new(ErrorStats::default()));

        b.iter(|| {
            let mut handles = Vec::new();

            for _thread_id in 0..4 {
                let stats_clone = Arc::clone(&stats);
                let handle = thread::spawn(move || {
                    let error = NetworkError::Timeout(Duration::from_secs(5));
                    let mut stats = stats_clone.lock().unwrap();
                    stats.record_error(&error);
                    stats.total_errors
                });
                handles.push(handle);
            }

            let mut total = 0;
            for handle in handles {
                total += handle.join().unwrap();
            }

            black_box(total)
        })
    });

    group.bench_function("concurrent_error_processing", |b| {
        b.iter(|| {
            let mut handles = Vec::new();

            for _thread_id in 0..4 {
                let handle = thread::spawn(move || {
                    let error = NetworkError::Timeout(Duration::from_secs(5));
                    let retryable = error.is_retryable();
                    let delay = error.retry_delay().unwrap_or(Duration::from_millis(100));
                    let max_retries = error.max_retries().unwrap_or(0);
                    retryable as u64 + delay.as_secs() + max_retries as u64
                });
                handles.push(handle);
            }

            let mut total = 0;
            for handle in handles {
                total += handle.join().unwrap();
            }

            black_box(total)
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_error_creation,
    bench_error_recovery,
    bench_error_stats,
    bench_error_propagation,
    bench_error_handling_chain,
    bench_error_logging,
    bench_error_serialization,
    bench_error_handling_performance,
    bench_error_handling_concurrency
);

criterion_main!(benches);
