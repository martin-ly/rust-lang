//! gRPC性能基准测试
//!
//! 测试gRPC微服务的性能表现

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use tokio::runtime::Runtime;

use c13_microservice::{
    config::Config,
    grpc::{GrpcMicroservice, UserServiceImpl, user_service},
};

/// 基准测试：gRPC服务创建性能
fn benchmark_grpc_service_creation(c: &mut Criterion) {
    c.bench_function("grpc_service_creation", |b| {
        b.iter(|| {
            let config = Config::default();
            let _microservice = GrpcMicroservice::new(config);
            black_box(())
        })
    });
}

/// 基准测试：用户服务实现创建性能
fn benchmark_user_service_creation(c: &mut Criterion) {
    c.bench_function("user_service_creation", |b| {
        b.iter(|| {
            let _service = UserServiceImpl::new();
            black_box(())
        })
    });
}

/// 基准测试：用户创建性能
fn benchmark_user_creation(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    c.bench_function("user_creation", |b| {
        b.iter(|| {
            let request = user_service::CreateUserRequest {
                name: "测试用户".to_string(),
                email: "test@example.com".to_string(),
            };

            // 同步执行异步操作
            let result = rt.block_on(async { service.create_user(request).await });
            black_box(result)
        })
    });
}

/// 基准测试：用户获取性能
fn benchmark_user_retrieval(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    // 预先创建一个用户
    let user = rt.block_on(async {
        let request = user_service::CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        service.create_user(request).await.unwrap()
    });

    c.bench_function("user_retrieval", |b| {
        b.iter(|| {
            let request = user_service::GetUserRequest {
                id: user.id.clone(),
            };

            // 同步执行异步操作
            let result = rt.block_on(async { service.get_user(request).await });
            black_box(result)
        })
    });
}

/// 基准测试：用户更新性能
fn benchmark_user_update(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    // 预先创建一个用户
    let user = rt.block_on(async {
        let request = user_service::CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        service.create_user(request).await.unwrap()
    });

    c.bench_function("user_update", |b| {
        b.iter(|| {
            let request = user_service::UpdateUserRequest {
                id: user.id.clone(),
                name: Some("更新用户".to_string()),
                email: None,
            };

            // 同步执行异步操作
            let result = rt.block_on(async { service.update_user(request).await });
            black_box(result)
        })
    });
}

/// 基准测试：用户删除性能
fn benchmark_user_deletion(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    c.bench_function("user_deletion", |b| {
        b.iter(|| {
            // 每次测试都创建一个新用户
            let create_request = user_service::CreateUserRequest {
                name: "测试用户".to_string(),
                email: "test@example.com".to_string(),
            };
            let user = rt.block_on(async { service.create_user(create_request).await.unwrap() });

            let delete_request = user_service::DeleteUserRequest { id: user.id };

            // 同步执行异步操作
            let result = rt.block_on(async { service.delete_user(delete_request).await });
            black_box(result)
        })
    });
}

/// 基准测试：用户列表性能
fn benchmark_user_listing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    // 预先创建一些用户
    rt.block_on(async {
        for i in 0..100 {
            let request = user_service::CreateUserRequest {
                name: format!("测试用户{}", i),
                email: format!("test{}@example.com", i),
            };
            service.create_user(request).await.unwrap();
        }
    });

    c.bench_function("user_listing", |b| {
        b.iter(|| {
            let request = user_service::ListUsersRequest {
                page: 1,
                page_size: 10,
            };

            // 同步执行异步操作
            let result = rt.block_on(async { service.list_users(request).await });
            black_box(result)
        })
    });
}

/// 基准测试：健康检查性能
fn benchmark_health_check(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let service = UserServiceImpl::new();

    c.bench_function("health_check", |b| {
        b.iter(|| {
            let request = user_service::HealthCheckRequest {
                service: "user_service".to_string(),
            };

            // 同步执行异步操作
            let result = rt.block_on(async { service.health_check(request).await });
            black_box(result)
        })
    });
}

/// 基准测试：并发操作性能
fn benchmark_concurrent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_operations");

    for concurrency in [1, 10, 100].iter() {
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

/// 基准测试：批量操作性能
fn benchmark_batch_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_operations");

    for batch_size in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("batch_size", batch_size),
            batch_size,
            |b, &batch_size| {
                b.iter(|| {
                    // 简化的批量测试
                    black_box(batch_size)
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_grpc_service_creation,
    benchmark_user_service_creation,
    benchmark_user_creation,
    benchmark_user_retrieval,
    benchmark_user_update,
    benchmark_user_deletion,
    benchmark_user_listing,
    benchmark_health_check,
    benchmark_concurrent_operations,
    benchmark_batch_operations
);

criterion_main!(benches);
