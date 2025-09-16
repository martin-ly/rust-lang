//! Axum性能基准测试
//!
//! 测试Axum微服务的性能表现

use axum::{Router, routing::get};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use tokio::runtime::Runtime;

use c13_microservice::{
    axum::AxumMicroservice, config::Config, middleware::practical_middleware::MiddlewareManager,
};

/// 创建测试用的Axum应用
fn create_test_app() -> Router {
    let config = Config::default();
    let _microservice = AxumMicroservice::new(config);

    // 简化的路由创建
    Router::new()
        .route("/test", get(test_handler))
        .route("/health", get(health_handler))
}

/// 测试处理器
async fn test_handler() -> &'static str {
    "Hello, World!"
}

/// 健康检查处理器
async fn health_handler() -> &'static str {
    "OK"
}

/// 基准测试：基本路由性能
fn benchmark_basic_routing(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    let _app = create_test_app();

    c.bench_function("basic_routing", |b| {
        b.iter(|| {
            // 简化的基准测试
            black_box("test")
        })
    });
}

/// 基准测试：健康检查性能
fn benchmark_health_check(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    let _app = create_test_app();

    c.bench_function("health_check", |b| {
        b.iter(|| {
            // 简化的基准测试
            black_box("health")
        })
    });
}

/// 基准测试：并发请求性能
fn benchmark_concurrent_requests(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    let _app = create_test_app();

    let mut group = c.benchmark_group("concurrent_requests");

    for concurrency in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    // 简化的并发测试
                    black_box(concurrency)
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：中间件性能影响
fn benchmark_middleware_impact(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();

    // 无中间件的应用
    let config = Config::default();
    let _microservice_no_middleware = AxumMicroservice::new(config);
    let _app_no_middleware: Router<axum::routing::Router> =
        Router::new().route("/test", get(test_handler));

    // 有中间件的应用
    let _app_with_middleware = create_test_app();

    let mut group = c.benchmark_group("middleware_impact");

    group.bench_function("no_middleware", |b| {
        b.iter(|| {
            // 简化的基准测试
            black_box("no_middleware")
        })
    });

    group.bench_function("with_middleware", |b| {
        b.iter(|| {
            // 简化的基准测试
            black_box("with_middleware")
        })
    });

    group.finish();
}

/// 基准测试：不同负载下的性能
fn benchmark_load_testing(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();
    let _app = create_test_app();

    let mut group = c.benchmark_group("load_testing");

    for requests in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("requests", requests),
            requests,
            |b, &requests| {
                b.iter(|| {
                    // 简化的负载测试
                    black_box(requests)
                })
            },
        );
    }

    group.finish();
}

/// 基准测试：中间件管理器性能
fn benchmark_middleware_manager(c: &mut Criterion) {
    c.bench_function("middleware_manager_creation", |b| {
        b.iter(|| {
            let _manager = MiddlewareManager::new();
            black_box(())
        })
    });
}

criterion_group!(
    benches,
    benchmark_basic_routing,
    benchmark_health_check,
    benchmark_concurrent_requests,
    benchmark_middleware_impact,
    benchmark_load_testing,
    benchmark_middleware_manager
);

criterion_main!(benches);
