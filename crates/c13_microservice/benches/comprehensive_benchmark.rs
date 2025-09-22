//! 综合性能基准测试
//!
//! 测试微服务框架各个组件的性能表现

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main, Throughput};
use std::hint::black_box;
use std::time::Duration;
use tokio::runtime::Runtime;

use c13_microservice::{
    config::Config,
    middleware::{JwtAuthMiddleware, RequestValidationMiddleware, HttpCacheMiddleware},
    security::{SecurityManager, SecurityConfig},
    service_mesh::{ServiceMeshManager, ServiceMeshConfig, ServiceInstance},
    opentelemetry::{OpenTelemetryManager, OpenTelemetryConfig},
};

/// 基准测试：配置创建性能
fn benchmark_config_creation(c: &mut Criterion) {
    c.bench_function("config_creation", |b| {
        b.iter(|| {
            let _config = Config::default();
            black_box(())
        })
    });
}

/// 基准测试：JWT认证中间件性能
fn benchmark_jwt_auth_middleware(c: &mut Criterion) {
    c.bench_function("jwt_auth_middleware_creation", |b| {
        b.iter(|| {
            let _middleware = JwtAuthMiddleware::new(c13_microservice::middleware::JwtConfig::default());
            black_box(())
        })
    });
}

/// 基准测试：请求验证中间件性能
fn benchmark_request_validation_middleware(c: &mut Criterion) {
    c.bench_function("request_validation_middleware_creation", |b| {
        b.iter(|| {
            let _middleware = RequestValidationMiddleware::new(c13_microservice::middleware::ValidationConfig::default());
            black_box(())
        })
    });
}

/// 基准测试：缓存中间件性能
fn benchmark_cache_middleware(c: &mut Criterion) {
    c.bench_function("cache_middleware_creation", |b| {
        b.iter(|| {
            let _middleware = HttpCacheMiddleware::new(c13_microservice::middleware::CacheConfig::default());
            black_box(())
        })
    });
}

/// 基准测试：安全管理器性能
fn benchmark_security_manager(c: &mut Criterion) {
    c.bench_function("security_manager_creation", |b| {
        b.iter(|| {
            let config = SecurityConfig::default();
            let _manager = SecurityManager::new(config);
            black_box(())
        })
    });
}

/// 基准测试：服务网格管理器性能
fn benchmark_service_mesh_manager(c: &mut Criterion) {
    c.bench_function("service_mesh_manager_creation", |b| {
        b.iter(|| {
            let config = ServiceMeshConfig::default();
            let _manager = ServiceMeshManager::new(config);
            black_box(())
        })
    });
}

/// 基准测试：OpenTelemetry管理器性能
fn benchmark_opentelemetry_manager(c: &mut Criterion) {
    c.bench_function("opentelemetry_manager_creation", |b| {
        b.iter(|| {
            let config = OpenTelemetryConfig::default();
            let _manager = OpenTelemetryManager::new(config);
            black_box(())
        })
    });
}

/// 基准测试：服务实例创建性能
fn benchmark_service_instance_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("service_instance_creation");
    
    for count in [1, 10, 100, 1000].iter() {
        group.throughput(Throughput::Elements(*count as u64));
        group.bench_with_input(
            BenchmarkId::new("instances", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut instances = Vec::new();
                    for i in 0..count {
                        let instance = ServiceInstance::new(
                            format!("service-{}", i),
                            "test-service".to_string(),
                            "localhost".to_string(),
                            8080 + (i as u16),
                        );
                        instances.push(instance);
                    }
                    black_box(instances)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：内存分配性能
fn benchmark_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");
    
    for size in [1024, 10240, 102400, 1024000].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(
            BenchmarkId::new("bytes", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let data: Vec<u8> = (0..size).map(|i| (i % 256) as u8).collect();
                    black_box(data)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：字符串处理性能
fn benchmark_string_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_processing");
    
    for length in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("length", length),
            length,
            |b, &length| {
                let test_string = "a".repeat(length);
                b.iter(|| {
                    let result = test_string.to_uppercase();
                    black_box(result)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：JSON序列化/反序列化性能
fn benchmark_json_processing(c: &mut Criterion) {
    use serde_json::{json, Value};
    
    let mut group = c.benchmark_group("json_processing");
    
    // 创建测试数据
    let test_data = json!({
        "id": "12345",
        "name": "测试用户",
        "email": "test@example.com",
        "age": 30,
        "address": {
            "street": "测试街道",
            "city": "测试城市",
            "country": "测试国家"
        },
        "hobbies": ["阅读", "游泳", "编程"]
    });
    
    group.bench_function("serialize", |b| {
        b.iter(|| {
            let result = serde_json::to_string(&test_data).unwrap();
            black_box(result)
        })
    });
    
    group.bench_function("deserialize", |b| {
        let json_string = serde_json::to_string(&test_data).unwrap();
        b.iter(|| {
            let result: Value = serde_json::from_str(&json_string).unwrap();
            black_box(result)
        })
    });
    
    group.finish();
}

/// 基准测试：哈希计算性能
fn benchmark_hashing(c: &mut Criterion) {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut group = c.benchmark_group("hashing");
    
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("size", size),
            size,
            |b, &size| {
                let data: Vec<u8> = (0..size).map(|i| (i % 256) as u8).collect();
                b.iter(|| {
                    let mut hasher = DefaultHasher::new();
                    data.hash(&mut hasher);
                    let result = hasher.finish();
                    black_box(result)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：并发任务性能
fn benchmark_concurrent_tasks(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("concurrent_tasks");
    
    for task_count in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("tasks", task_count),
            task_count,
            |b, &task_count| {
                b.iter(|| {
                    let tasks: Vec<_> = (0..task_count)
                        .map(|i| {
                            tokio::spawn(async move {
                                // 模拟一些工作
                                std::thread::sleep(Duration::from_micros(1));
                                i * 2
                            })
                        })
                        .collect();
                    
                    let results = rt.block_on(async {
                        let mut results = Vec::new();
                        for task in tasks {
                            results.push(task.await.unwrap());
                        }
                        results
                    });
                    
                    black_box(results)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：错误处理性能
fn benchmark_error_handling(c: &mut Criterion) {
    c.bench_function("error_creation", |b| {
        b.iter(|| {
            let error = c13_microservice::error::Error::config("测试错误");
            black_box(error)
        })
    });
    
    c.bench_function("error_conversion", |b| {
        b.iter(|| {
            let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "文件未找到");
            let converted = c13_microservice::error::Error::from(io_error);
            black_box(converted)
        })
    });
}

/// 基准测试：配置验证性能
fn benchmark_config_validation(c: &mut Criterion) {
    c.bench_function("config_validation", |b| {
        b.iter(|| {
            let config = Config::default();
            let result = config.validate();
            black_box(result)
        })
    });
}

/// 基准测试：日志记录性能
fn benchmark_logging(c: &mut Criterion) {
    use tracing::{info, warn, error, debug};
    
    let mut group = c.benchmark_group("logging");
    
    group.bench_function("info_log", |b| {
        b.iter(|| {
            info!("基准测试信息日志");
        })
    });
    
    group.bench_function("warn_log", |b| {
        b.iter(|| {
            warn!("基准测试警告日志");
        })
    });
    
    group.bench_function("error_log", |b| {
        b.iter(|| {
            error!("基准测试错误日志");
        })
    });
    
    group.bench_function("debug_log", |b| {
        b.iter(|| {
            debug!("基准测试调试日志");
        })
    });
    
    group.finish();
}

/// 基准测试：UUID生成性能
fn benchmark_uuid_generation(c: &mut Criterion) {
    use uuid::Uuid;
    
    let mut group = c.benchmark_group("uuid_generation");
    
    for count in [1, 10, 100, 1000].iter() {
        group.throughput(Throughput::Elements(*count as u64));
        group.bench_with_input(
            BenchmarkId::new("count", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut uuids = Vec::new();
                    for _ in 0..count {
                        uuids.push(Uuid::new_v4());
                    }
                    black_box(uuids)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：时间戳生成性能
fn benchmark_timestamp_generation(c: &mut Criterion) {
    use std::time::{SystemTime, UNIX_EPOCH};
    
    let mut group = c.benchmark_group("timestamp_generation");
    
    for count in [1, 10, 100, 1000].iter() {
        group.throughput(Throughput::Elements(*count as u64));
        group.bench_with_input(
            BenchmarkId::new("count", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut timestamps = Vec::new();
                    for _ in 0..count {
                        timestamps.push(SystemTime::now().duration_since(UNIX_EPOCH).unwrap());
                    }
                    black_box(timestamps)
                })
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_config_creation,
    benchmark_jwt_auth_middleware,
    benchmark_request_validation_middleware,
    benchmark_cache_middleware,
    benchmark_security_manager,
    benchmark_service_mesh_manager,
    benchmark_opentelemetry_manager,
    benchmark_service_instance_creation,
    benchmark_memory_allocation,
    benchmark_string_processing,
    benchmark_json_processing,
    benchmark_hashing,
    benchmark_concurrent_tasks,
    benchmark_error_handling,
    benchmark_config_validation,
    benchmark_logging,
    benchmark_uuid_generation,
    benchmark_timestamp_generation
);

criterion_main!(benches);
