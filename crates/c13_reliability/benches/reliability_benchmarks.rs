//! 可靠性框架性能基准测试

use criterion::{criterion_group, criterion_main, Criterion, Bencher};
use std::hint::black_box;
use c13_reliability::prelude::*;
use c13_reliability::fault_tolerance::{CircuitBreakerConfig, RetryConfig};
use c13_reliability::runtime_monitoring::HealthCheckConfig;

fn bench_circuit_breaker(c: &mut Criterion) {
    c.bench_function("circuit_breaker_execution", |b: &mut Bencher| {
        b.iter(|| {
            let config = CircuitBreakerConfig::default();
            let circuit_breaker = CircuitBreaker::new(config);
            black_box(circuit_breaker.can_execute())
        })
    });
}

fn bench_retry_policy(c: &mut Criterion) {
    c.bench_function("retry_policy_execution", |b: &mut Bencher| {
        b.iter(|| {
            let config = RetryConfig::default();
            let retry_policy = RetryPolicy::new(config);
            black_box(retry_policy.get_stats())
        })
    });
}

fn bench_error_handling(c: &mut Criterion) {
    c.bench_function("error_creation", |b| {
        b.iter(|| {
            black_box(UnifiedError::new(
                "benchmark error",
                ErrorSeverity::Low,
                "benchmark",
                ErrorContext::new("benchmark", "test", file!(), line!(), ErrorSeverity::Low, "benchmark")
            ))
        })
    });
}

fn bench_health_check(c: &mut Criterion) {
    c.bench_function("health_check_execution", |b: &mut Bencher| {
        b.iter(|| {
            let config = HealthCheckConfig::default();
            let health_checker = HealthChecker::new(config);
            black_box(health_checker.get_last_result())
        })
    });
}

criterion_group!(
    benches,
    bench_circuit_breaker,
    bench_retry_policy,
    bench_error_handling,
    bench_health_check
);
criterion_main!(benches);
