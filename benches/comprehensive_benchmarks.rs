//! 综合性能基准测试套件
//! 
//! 测试各个模块的性能表现和优化效果

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::time::Duration;
use std::collections::HashMap;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use tokio::runtime::Runtime;

// 导入我们项目的模块
use distributed_computing::{
    service_discovery::{ServiceRegistry, ServiceInstance, HealthStatus},
    load_balancer::{LoadBalancer, LoadBalancingStrategy, Backend},
    circuit_breaker::{CircuitBreaker, CircuitBreakerConfig},
    distributed_cache::{DistributedCache, CacheConfig, EvictionPolicy},
    message_queue::{MessageQueue, MessageQueueConfig, MessagePriority},
    containerization::{ContainerManager, ContainerConfig, ResourceRequirements, RestartPolicy},
};
use async_runtime_comparison::{
    ObservabilityPlatform, PerformanceAnalyzer, PerformanceTuner,
    error_handling::{ErrorHandler, StructuredError, ErrorType, ErrorSeverity},
};

/// 基准测试：服务注册和发现性能
fn benchmark_service_discovery(c: &mut Criterion) {
    let mut group = c.benchmark_group("service_discovery");
    
    group.bench_function("register_service", |b| {
        let mut registry = ServiceRegistry::new();
        let service = ServiceInstance {
            id: "test-service".to_string(),
            service_name: "benchmark-service".to_string(),
            address: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
            metadata: HashMap::new(),
            health_status: HealthStatus::Healthy,
            last_heartbeat: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            tags: vec!["benchmark".to_string()],
        };
        
        b.iter(|| {
            black_box(registry.register_service(service.clone()).unwrap());
        });
    });
    
    group.bench_function("discover_service", |b| {
        let mut registry = ServiceRegistry::new();
        // 预先注册一些服务
        for i in 0..100 {
            let service = ServiceInstance {
                id: format!("service-{}", i),
                service_name: "benchmark-service".to_string(),
                address: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080 + i),
                metadata: HashMap::new(),
                health_status: HealthStatus::Healthy,
                last_heartbeat: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                tags: vec!["benchmark".to_string()],
            };
            registry.register_service(service).unwrap();
        }
        
        b.iter(|| {
            black_box(registry.discover_service("benchmark-service"));
        });
    });
    
    group.finish();
}

/// 基准测试：负载均衡性能
fn benchmark_load_balancing(c: &mut Criterion) {
    let mut group = c.benchmark_group("load_balancing");
    
    for backend_count in [10, 50, 100, 500].iter() {
        group.bench_with_input(
            BenchmarkId::new("select_backend", backend_count),
            backend_count,
            |b, &backend_count| {
                let mut load_balancer = LoadBalancer::new(LoadBalancingStrategy::RoundRobin);
                
                // 添加后端服务器
                for i in 0..backend_count {
                    let backend = Backend {
                        id: format!("backend-{}", i),
                        address: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080 + i),
                        weight: 1,
                        active_connections: 0,
                        health_status: distributed_computing::load_balancer::HealthStatus::Healthy,
                        response_time: Duration::from_millis(10),
                    };
                    load_balancer.add_backend(backend);
                }
                
                b.iter(|| {
                    black_box(load_balancer.select_instance("test-service"));
                });
            },
        );
    }
    
    group.finish();
}

/// 基准测试：分布式缓存性能
fn benchmark_distributed_cache(c: &mut Criterion) {
    let mut group = c.benchmark_group("distributed_cache");
    
    group.bench_function("cache_insert", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 10000,
            default_ttl: Duration::from_secs(3600),
            cleanup_interval: Duration::from_secs(300),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        b.iter(|| {
            let key = format!("key_{}", black_box(rand::random::<u32>()));
            let value = format!("value_{}", black_box(rand::random::<u32>()));
            black_box(cache.insert(key, value, None));
        });
    });
    
    group.bench_function("cache_get", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 10000,
            default_ttl: Duration::from_secs(3600),
            cleanup_interval: Duration::from_secs(300),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        // 预先填充缓存
        for i in 0..1000 {
            cache.insert(format!("key_{}", i), format!("value_{}", i), None);
        }
        
        b.iter(|| {
            let key = format!("key_{}", black_box(rand::random::<u32>() % 1000));
            black_box(cache.get(&key));
        });
    });
    
    group.bench_function("cache_hit_rate", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 1000,
            default_ttl: Duration::from_secs(3600),
            cleanup_interval: Duration::from_secs(300),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        // 填充缓存
        for i in 0..500 {
            cache.insert(format!("key_{}", i), format!("value_{}", i), None);
        }
        
        b.iter(|| {
            // 模拟缓存命中场景
            for i in 0..100 {
                let key = format!("key_{}", i % 500);
                black_box(cache.get(&key));
            }
            black_box(cache.get_hit_rate());
        });
    });
    
    group.finish();
}

/// 基准测试：消息队列性能
fn benchmark_message_queue(c: &mut Criterion) {
    let mut group = c.benchmark_group("message_queue");
    
    group.bench_function("publish_message", |b| {
        let mut message_queue = MessageQueue::new(MessageQueueConfig::default());
        
        b.iter(|| {
            let topic = format!("topic_{}", black_box(rand::random::<u32>() % 10));
            let message = format!("message_{}", black_box(rand::random::<u32>()));
            black_box(message_queue.publish(
                topic,
                message.into_bytes(),
                MessagePriority::Normal,
            ));
        });
    });
    
    group.bench_function("consume_message", |b| {
        let mut message_queue = MessageQueue::new(MessageQueueConfig::default());
        
        // 预先发布一些消息
        for i in 0..1000 {
            message_queue.publish(
                "benchmark_topic".to_string(),
                format!("message_{}", i).into_bytes(),
                MessagePriority::Normal,
            ).unwrap();
        }
        
        b.iter(|| {
            black_box(message_queue.consume("benchmark_topic"));
        });
    });
    
    group.finish();
}

/// 基准测试：可观测性平台性能
fn benchmark_observability_platform(c: &mut Criterion) {
    let mut group = c.benchmark_group("observability_platform");
    
    group.bench_function("metrics_collection", |b| {
        let mut platform = ObservabilityPlatform::new();
        let mut metrics_collector = platform.get_metrics_collector();
        
        b.iter(|| {
            let mut labels = HashMap::new();
            labels.insert("service".to_string(), "benchmark".to_string());
            labels.insert("operation".to_string(), "test".to_string());
            
            metrics_collector.increment_counter("requests_total".to_string(), labels.clone());
            metrics_collector.set_gauge("memory_usage".to_string(), black_box(128.5), labels);
        });
    });
    
    group.bench_function("tracing_operations", |b| {
        let mut platform = ObservabilityPlatform::new();
        let mut tracer = platform.get_tracer();
        
        b.iter(|| {
            let context = tracer.start_span("benchmark_operation".to_string(), None);
            tracer.add_span_tag(&context, "service".to_string(), "benchmark".to_string());
            tracer.finish_span(context, async_runtime_comparison::observability_platform::SpanStatus::Ok);
        });
    });
    
    group.bench_function("log_aggregation", |b| {
        let mut platform = ObservabilityPlatform::new();
        let mut log_aggregator = platform.get_log_aggregator();
        
        b.iter(|| {
            let mut fields = HashMap::new();
            fields.insert("user_id".to_string(), serde_json::Value::String("123".to_string()));
            fields.insert("operation".to_string(), serde_json::Value::String("benchmark".to_string()));
            
            log_aggregator.info(
                "Benchmark log message".to_string(),
                fields,
                "benchmark".to_string(),
            );
        });
    });
    
    group.finish();
}

/// 基准测试：性能优化系统
fn benchmark_performance_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("performance_optimization");
    
    group.bench_function("performance_analysis", |b| {
        let mut analyzer = PerformanceAnalyzer::new();
        
        // 预先添加一些性能快照
        for i in 0..50 {
            let snapshot = async_runtime_comparison::performance_optimization::PerformanceSnapshot {
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs() + i,
                cpu_usage: 75.0 + (i as f64 * 0.5),
                memory_usage: 512 * 1024 * 1024 + (i * 1024 * 1024) as u64,
                throughput: 1000.0 + (i as f64 * 10.0),
                latency: Duration::from_millis(50 + i as u64),
                context_switches: 1000 + i * 10,
                cache_hits: 800 + i * 5,
                cache_misses: 200 + i * 2,
            };
            analyzer.record_snapshot(snapshot);
        }
        
        b.iter(|| {
            black_box(analyzer.get_optimization_suggestions());
        });
    });
    
    group.bench_function("auto_tuning", |b| {
        let mut tuner = PerformanceTuner::new();
        
        b.iter(|| {
            black_box(tuner.apply_optimizations());
        });
    });
    
    group.finish();
}

/// 基准测试：错误处理系统
fn benchmark_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");
    
    group.bench_function("error_creation_and_handling", |b| {
        let mut error_handler = ErrorHandler::new();
        
        b.iter(|| {
            let error = StructuredError {
                error_type: ErrorType::Network,
                severity: ErrorSeverity::Error,
                message: "Benchmark error message".to_string(),
                details: HashMap::from([("operation".to_string(), "benchmark".to_string())]),
                operation: "benchmark_operation".to_string(),
                runtime: "tokio".to_string(),
                timestamp: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            };
            
            black_box(error_handler.handle_error(error));
        });
    });
    
    group.bench_function("log_processing", |b| {
        let mut error_handler = ErrorHandler::new();
        let mut logger = error_handler.get_logger();
        
        b.iter(|| {
            logger.info("Benchmark info message".to_string(), Some("benchmark".to_string()));
            logger.warn("Benchmark warning message".to_string(), Some("benchmark".to_string()));
            logger.error("Benchmark error message".to_string(), Some("benchmark".to_string()));
        });
    });
    
    group.finish();
}

/// 基准测试：容器管理性能
fn benchmark_container_management(c: &mut Criterion) {
    let mut group = c.benchmark_group("container_management");
    
    group.bench_function("container_creation", |b| {
        let mut container_manager = ContainerManager::new();
        
        let config = ContainerConfig {
            image: "nginx:alpine".to_string(),
            tag: "latest".to_string(),
            ports: vec![],
            environment_variables: HashMap::new(),
            volumes: vec![],
            resources: ResourceRequirements {
                cpu_cores: 1.0,
                memory_mb: 512,
                disk_gb: 10,
            },
            restart_policy: RestartPolicy::Always,
            health_check: None,
        };
        
        b.iter(|| {
            let container_id = format!("benchmark_container_{}", black_box(rand::random::<u32>()));
            black_box(container_manager.create_container(container_id, config.clone()));
        });
    });
    
    group.bench_function("container_status_check", |b| {
        let mut container_manager = ContainerManager::new();
        
        // 预先创建一些容器
        for i in 0..100 {
            let config = ContainerConfig {
                image: "nginx:alpine".to_string(),
                tag: "latest".to_string(),
                ports: vec![],
                environment_variables: HashMap::new(),
                volumes: vec![],
                resources: ResourceRequirements {
                    cpu_cores: 1.0,
                    memory_mb: 512,
                    disk_gb: 10,
                },
                restart_policy: RestartPolicy::Always,
                health_check: None,
            };
            container_manager.create_container(format!("container_{}", i), config).unwrap();
        }
        
        b.iter(|| {
            let container_id = format!("container_{}", black_box(rand::random::<u32>() % 100));
            black_box(container_manager.get_container(&container_id));
        });
    });
    
    group.finish();
}

/// 基准测试：并发性能
fn benchmark_concurrent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_operations");
    
    group.bench_function("concurrent_cache_operations", |b| {
        let cache: DistributedCache<String> = DistributedCache::new(CacheConfig::default());
        
        b.iter(|| {
            let rt = Runtime::new().unwrap();
            rt.block_on(async {
                let mut handles = Vec::new();
                
                for i in 0..100 {
                    let mut cache_clone = cache.clone();
                    let handle = tokio::spawn(async move {
                        let key = format!("concurrent_key_{}", i);
                        let value = format!("concurrent_value_{}", i);
                        cache_clone.insert(key, value, None);
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    black_box(handle.await.unwrap());
                }
            });
        });
    });
    
    group.bench_function("concurrent_message_processing", |b| {
        let message_queue = MessageQueue::new(MessageQueueConfig::default());
        
        b.iter(|| {
            let rt = Runtime::new().unwrap();
            rt.block_on(async {
                let mut handles = Vec::new();
                
                for i in 0..50 {
                    let mut queue_clone = message_queue.clone();
                    let handle = tokio::spawn(async move {
                        let topic = format!("concurrent_topic_{}", i % 10);
                        let message = format!("concurrent_message_{}", i);
                        queue_clone.publish(topic, message.into_bytes(), MessagePriority::Normal).unwrap();
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    black_box(handle.await.unwrap());
                }
            });
        });
    });
    
    group.finish();
}

/// 基准测试：内存使用效率
fn benchmark_memory_efficiency(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");
    
    group.bench_function("large_dataset_handling", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 100000,
            default_ttl: Duration::from_secs(3600),
            cleanup_interval: Duration::from_secs(300),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        b.iter(|| {
            // 插入大量数据
            for i in 0..10000 {
                let key = format!("large_key_{}", i);
                let value = format!("large_value_{}", i);
                cache.insert(key, value, None);
            }
            
            // 访问数据
            for i in 0..1000 {
                let key = format!("large_key_{}", i);
                black_box(cache.get(&key));
            }
        });
    });
    
    group.bench_function("memory_cleanup", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 1000,
            default_ttl: Duration::from_secs(1), // 短TTL用于测试清理
            cleanup_interval: Duration::from_secs(1),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        b.iter(|| {
            // 填充缓存
            for i in 0..2000 {
                let key = format!("cleanup_key_{}", i);
                let value = format!("cleanup_value_{}", i);
                cache.insert(key, value, None);
            }
            
            // 等待清理
            std::thread::sleep(Duration::from_millis(100));
            
            // 检查清理效果
            black_box(cache.get_stats());
        });
    });
    
    group.finish();
}

/// 基准测试：网络性能
fn benchmark_network_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("network_performance");
    
    group.bench_function("high_throughput_messaging", |b| {
        let mut message_queue = MessageQueue::new(MessageQueueConfig::default());
        
        b.iter(|| {
            for i in 0..1000 {
                let topic = "high_throughput_topic".to_string();
                let message = format!("high_throughput_message_{}", i);
                message_queue.publish(topic, message.into_bytes(), MessagePriority::Normal).unwrap();
            }
        });
    });
    
    group.bench_function("low_latency_operations", |b| {
        let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig {
            max_size: 10000,
            default_ttl: Duration::from_secs(3600),
            cleanup_interval: Duration::from_secs(300),
            eviction_policy: EvictionPolicy::LRU,
        });
        
        // 预先填充缓存
        for i in 0..1000 {
            cache.insert(format!("latency_key_{}", i), format!("latency_value_{}", i), None);
        }
        
        b.iter(|| {
            // 快速访问
            for i in 0..100 {
                let key = format!("latency_key_{}", i % 1000);
                black_box(cache.get(&key));
            }
        });
    });
    
    group.finish();
}

/// 基准测试：系统整体性能
fn benchmark_system_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("system_performance");
    
    group.bench_function("end_to_end_workflow", |b| {
        b.iter(|| {
            // 模拟完整的业务流程
            let mut service_registry = ServiceRegistry::new();
            let mut cache: DistributedCache<String> = DistributedCache::new(CacheConfig::default());
            let mut message_queue = MessageQueue::new(MessageQueueConfig::default());
            let mut platform = ObservabilityPlatform::new();
            
            // 1. 服务注册
            let service = ServiceInstance {
                id: "benchmark_service".to_string(),
                service_name: "benchmark_service".to_string(),
                address: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
                metadata: HashMap::new(),
                health_status: HealthStatus::Healthy,
                last_heartbeat: std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
                tags: vec!["benchmark".to_string()],
            };
            service_registry.register_service(service).unwrap();
            
            // 2. 缓存操作
            cache.insert("benchmark_key".to_string(), "benchmark_value".to_string(), None);
            black_box(cache.get("benchmark_key"));
            
            // 3. 消息发布
            message_queue.publish(
                "benchmark_topic".to_string(),
                b"benchmark_message".to_vec(),
                MessagePriority::Normal,
            ).unwrap();
            
            // 4. 指标收集
            let mut metrics_collector = platform.get_metrics_collector();
            let mut labels = HashMap::new();
            labels.insert("operation".to_string(), "benchmark".to_string());
            metrics_collector.increment_counter("benchmark_operations".to_string(), labels);
            
            // 5. 生成报告
            black_box(platform.generate_observability_report());
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_service_discovery,
    benchmark_load_balancing,
    benchmark_distributed_cache,
    benchmark_message_queue,
    benchmark_observability_platform,
    benchmark_performance_optimization,
    benchmark_error_handling,
    benchmark_container_management,
    benchmark_concurrent_operations,
    benchmark_memory_efficiency,
    benchmark_network_performance,
    benchmark_system_performance
);

criterion_main!(benches);
