//! 综合性能基准测试
//! 
//! 测试各种场景下的性能表现

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use c19_ai::{AIEngine, AIModule, ModelConfig};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::runtime::Runtime;

/// 引擎初始化基准测试
fn bench_engine_initialization(c: &mut Criterion) {
    c.bench_function("engine_initialization", |b| {
        b.iter(|| {
            let engine = AIEngine::new().unwrap();
            black_box(engine);
        });
    });
}

/// 模块注册基准测试
fn bench_module_registration(c: &mut Criterion) {
    let mut group = c.benchmark_group("module_registration");
    
    for size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("single", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            b.iter(|| {
                let module = AIModule::new("test_module", "1.0.0");
                engine.register_module(module).unwrap();
            });
        });
        
        group.bench_with_input(BenchmarkId::new("batch", size), size, |b, &size| {
            b.iter(|| {
                let mut engine = AIEngine::new().unwrap();
                for i in 0..size {
                    let module = AIModule::new(&format!("module_{}", i), "1.0.0");
                    engine.register_module(module).unwrap();
                }
                black_box(engine);
            });
        });
    }
    
    group.finish();
}

/// 配置设置基准测试
fn bench_config_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("config_operations");
    
    for size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("set", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            b.iter(|| {
                for i in 0..size {
                    let config = ModelConfig {
                        name: format!("config_{}", i),
                        version: "1.0.0".to_string(),
                        model_type: "test".to_string(),
                        framework: "candle".to_string(),
                        parameters: HashMap::new(),
                    };
                    engine.set_config(&format!("config_{}", i), config).unwrap();
                }
            });
        });
        
        group.bench_with_input(BenchmarkId::new("get", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            // 预先设置配置
            for i in 0..size {
                let config = ModelConfig {
                    name: format!("config_{}", i),
                    version: "1.0.0".to_string(),
                    model_type: "test".to_string(),
                    framework: "candle".to_string(),
                    parameters: HashMap::new(),
                };
                engine.set_config(&format!("config_{}", i), config).unwrap();
            }
            
            b.iter(|| {
                for i in 0..size {
                    let config = engine.get_config(&format!("config_{}", i));
                    black_box(config);
                }
            });
        });
    }
    
    group.finish();
}

/// 指标记录基准测试
fn bench_metrics_recording(c: &mut Criterion) {
    let mut group = c.benchmark_group("metrics_recording");
    
    for size in [1, 10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("record", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            b.iter(|| {
                for i in 0..size {
                    engine.record_metric(&format!("metric_{}", i), i as f64).unwrap();
                }
            });
        });
        
        group.bench_with_input(BenchmarkId::new("get_all", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            // 预先记录指标
            for i in 0..size {
                engine.record_metric(&format!("metric_{}", i), i as f64).unwrap();
            }
            
            b.iter(|| {
                let metrics = engine.get_metrics();
                black_box(metrics);
            });
        });
    }
    
    group.finish();
}

/// 状态管理基准测试
fn bench_state_management(c: &mut Criterion) {
    let mut group = c.benchmark_group("state_management");
    
    for size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("set", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            b.iter(|| {
                for i in 0..size {
                    engine.set_state(&format!("state_{}", i), &format!("value_{}", i)).unwrap();
                }
            });
        });
        
        group.bench_with_input(BenchmarkId::new("get", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            // 预先设置状态
            for i in 0..size {
                engine.set_state(&format!("state_{}", i), &format!("value_{}", i)).unwrap();
            }
            
            b.iter(|| {
                for i in 0..size {
                    let value = engine.get_state(&format!("state_{}", i));
                    black_box(value);
                }
            });
        });
    }
    
    group.finish();
}

/// 事件系统基准测试
fn bench_event_system(c: &mut Criterion) {
    let mut group = c.benchmark_group("event_system");
    
    for size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("emit", size), size, |b, &size| {
            let mut engine = AIEngine::new().unwrap();
            // 注册事件监听器
            engine.on_event("test_event", Box::new(|_data| {
                // 空回调
            })).unwrap();
            
            b.iter(|| {
                for i in 0..size {
                    engine.emit_event("test_event", &format!("data_{}", i)).unwrap();
                }
            });
        });
    }
    
    group.finish();
}

/// 并发性能基准测试
fn bench_concurrent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_operations");
    
    for thread_count in [1, 2, 4, 8].iter() {
        group.bench_with_input(BenchmarkId::new("module_registration", thread_count), thread_count, |b, &thread_count| {
            let rt = Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    let engine = Arc::new(tokio::sync::Mutex::new(AIEngine::new().unwrap()));
                    let mut handles = Vec::new();
                    
                    for i in 0..thread_count {
                        let engine_clone = engine.clone();
                        let handle = tokio::spawn(async move {
                            let mut engine_guard = engine_clone.lock().await;
                            let module = AIModule::new(&format!("module_{}", i), "1.0.0");
                            engine_guard.register_module(module)
                        });
                        handles.push(handle);
                    }
                    
                    for handle in handles {
                        handle.await.unwrap().unwrap();
                    }
                });
            });
        });
    }
    
    group.finish();
}

/// 内存使用基准测试
fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("config_storage", size), size, |b, &size| {
            b.iter(|| {
                let mut engine = AIEngine::new().unwrap();
                for i in 0..size {
                    let config = ModelConfig {
                        name: format!("config_{}", i),
                        version: "1.0.0".to_string(),
                        model_type: "test".to_string(),
                        framework: "candle".to_string(),
                        parameters: HashMap::new(),
                    };
                    engine.set_config(&format!("config_{}", i), config).unwrap();
                }
                black_box(engine);
            });
        });
    }
    
    group.finish();
}

/// 资源清理基准测试
fn bench_cleanup_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("cleanup_operations");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("cleanup", size), size, |b, &size| {
            b.iter(|| {
                let mut engine = AIEngine::new().unwrap();
                // 预先创建资源
                for i in 0..size {
                    let module = AIModule::new(&format!("module_{}", i), "1.0.0");
                    engine.register_module(module).unwrap();
                    
                    let config = ModelConfig {
                        name: format!("config_{}", i),
                        version: "1.0.0".to_string(),
                        model_type: "test".to_string(),
                        framework: "candle".to_string(),
                        parameters: HashMap::new(),
                    };
                    engine.set_config(&format!("config_{}", i), config).unwrap();
                }
                
                // 清理资源
                engine.cleanup().unwrap();
            });
        });
    }
    
    group.finish();
}

/// 错误处理基准测试
fn bench_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("nonexistent_lookup", size), size, |b, &size| {
            let engine = AIEngine::new().unwrap();
            b.iter(|| {
                for i in 0..size {
                    let module = engine.get_module(&format!("nonexistent_module_{}", i));
                    black_box(module);
                }
            });
        });
    }
    
    group.finish();
}

/// 资源限制基准测试
fn bench_resource_limits(c: &mut Criterion) {
    let mut group = c.benchmark_group("resource_limits");
    
    for limit in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("limit_check", limit), limit, |b, &limit| {
            b.iter(|| {
                let mut engine = AIEngine::new().unwrap();
                engine.set_resource_limit("max_modules", limit).unwrap();
                
                for i in 0..limit {
                    let module = AIModule::new(&format!("module_{}", i), "1.0.0");
                    engine.register_module(module).unwrap();
                }
                
                black_box(engine);
            });
        });
    }
    
    group.finish();
}

/// 端到端性能基准测试
fn bench_end_to_end_performance(c: &mut Criterion) {
    c.bench_function("end_to_end_performance", |b| {
        b.iter(|| {
            let mut engine = AIEngine::new().unwrap();
            
            // 设置资源限制
            engine.set_resource_limit("max_modules", 100).unwrap();
            
            // 注册模块
            for i in 0..100 {
                let module = AIModule::new(&format!("module_{}", i), "1.0.0");
                engine.register_module(module).unwrap();
            }
            
            // 设置配置
            for i in 0..100 {
                let config = ModelConfig {
                    name: format!("config_{}", i),
                    version: "1.0.0".to_string(),
                    model_type: "test".to_string(),
                    framework: "candle".to_string(),
                    parameters: HashMap::new(),
                };
                engine.set_config(&format!("config_{}", i), config).unwrap();
            }
            
            // 记录指标
            for i in 0..100 {
                engine.record_metric(&format!("metric_{}", i), i as f64).unwrap();
            }
            
            // 设置状态
            for i in 0..100 {
                engine.set_state(&format!("state_{}", i), &format!("value_{}", i)).unwrap();
            }
            
            // 注册事件监听器
            engine.on_event("test_event", Box::new(|_data| {
                // 空回调
            })).unwrap();
            
            // 触发事件
            for i in 0..100 {
                engine.emit_event("test_event", &format!("data_{}", i)).unwrap();
            }
            
            // 获取信息
            let modules = engine.list_modules();
            let metrics = engine.get_metrics();
            
            black_box((modules, metrics));
            
            // 清理资源
            engine.cleanup().unwrap();
        });
    });
}

criterion_group!(
    benches,
    bench_engine_initialization,
    bench_module_registration,
    bench_config_operations,
    bench_metrics_recording,
    bench_state_management,
    bench_event_system,
    bench_concurrent_operations,
    bench_memory_usage,
    bench_cleanup_operations,
    bench_error_handling,
    bench_resource_limits,
    bench_end_to_end_performance
);

criterion_main!(benches);
