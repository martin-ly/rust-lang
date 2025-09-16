/// 性能基准测试
/// 
/// 使用Criterion框架进行设计模式的性能基准测试
/// 测试各种模式在不同场景下的性能表现

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c09_design_pattern::creational::singleton::define::Singleton;
use c09_design_pattern::structural::flyweight::define::OptimizedFlyweightFactory;
use c09_design_pattern::structural::proxy::define::{RealSubject, Proxy, VirtualProxy, Subject};
use c09_design_pattern::behavioral::chain_of_responsibility::define::{ConcreteHandlerA, ConcreteHandlerB, ConcreteHandlerC, Handler};
use std::sync::Arc;

/// 单例模式性能基准测试
fn benchmark_singleton(c: &mut Criterion) {
    let mut group = c.benchmark_group("singleton");
    
    // 测试单例实例获取性能
    group.bench_function("get_instance", |b| {
        let singleton = Singleton::new();
        b.iter(|| {
            let _instance = singleton.get_instance(|| {
                black_box(String::from("Benchmark Instance"))
            });
        });
    });
    
    // 测试多次获取同一实例的性能
    group.bench_function("repeated_get_instance", |b| {
        let singleton = Singleton::new();
        let _initial = singleton.get_instance(|| {
            black_box(String::from("Initial Instance"))
        });
        
        b.iter(|| {
            let _instance = singleton.get_instance(|| {
                black_box(String::from("Should Not Be Called"))
            });
        });
    });
    
    group.finish();
}

/// 享元模式性能基准测试
fn benchmark_flyweight(c: &mut Criterion) {
    let mut group = c.benchmark_group("flyweight");
    
    // 测试享元对象创建性能
    group.bench_function("create_flyweight", |b| {
        let mut factory = OptimizedFlyweightFactory::new();
        let mut counter = 0;
        
        b.iter(|| {
            let key = format!("bench_{}", counter);
            let state = format!("Benchmark State {}", counter);
            let _flyweight = factory.get_flyweight(&key, state);
            counter += 1;
        });
    });
    
    // 测试享元对象重用性能
    group.bench_function("reuse_flyweight", |b| {
        let mut factory = OptimizedFlyweightFactory::new();
        let _initial = factory.get_flyweight("reuse_test", "Initial State".to_string());
        
        b.iter(|| {
            let _flyweight = factory.get_flyweight("reuse_test", "Different State".to_string());
        });
    });
    
    // 测试批量创建性能
    group.bench_function("batch_create", |b| {
        let mut factory = OptimizedFlyweightFactory::new();
        
        b.iter(|| {
            let specs = vec![
                ("batch1".to_string(), "Batch State 1".to_string()),
                ("batch2".to_string(), "Batch State 2".to_string()),
                ("batch3".to_string(), "Batch State 3".to_string()),
            ];
            let _flyweights = factory.batch_create_flyweights(&specs);
        });
    });
    
    group.finish();
}

/// 代理模式性能基准测试
fn benchmark_proxy(c: &mut Criterion) {
    let mut group = c.benchmark_group("proxy");
    
    // 测试代理创建性能
    group.bench_function("create_proxy", |b| {
        b.iter(|| {
            let real_subject = RealSubject::new(black_box(42));
            let _proxy = Proxy::new(real_subject);
        });
    });
    
    // 测试代理请求处理性能
    group.bench_function("proxy_request", |b| {
        let real_subject = RealSubject::new(42);
        let proxy = Proxy::new(real_subject);
        
        b.iter(|| {
            proxy.request();
        });
    });
    
    // 测试虚拟代理性能
    group.bench_function("virtual_proxy", |b| {
        let mut virtual_proxy = VirtualProxy::new(42);
        virtual_proxy.ensure_real_subject();
        
        b.iter(|| {
            virtual_proxy.request();
        });
    });
    
    group.finish();
}

/// 责任链模式性能基准测试
fn benchmark_chain_of_responsibility(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_of_responsibility");
    
    // 测试责任链构建性能
    group.bench_function("build_chain", |b| {
        b.iter(|| {
            let mut handler_a = Arc::new(ConcreteHandlerA::new());
            let mut handler_b = Arc::new(ConcreteHandlerB::new());
            let handler_c = Arc::new(ConcreteHandlerC::new());
            
            Arc::make_mut(&mut handler_a).set_next(handler_b.clone());
            Arc::make_mut(&mut handler_b).set_next(handler_c.clone());
            
            black_box(handler_a)
        });
    });
    
    // 测试责任链处理性能
    group.bench_function("process_chain", |b| {
        let mut handler_a = Arc::new(ConcreteHandlerA::new());
        let mut handler_b = Arc::new(ConcreteHandlerB::new());
        let handler_c = Arc::new(ConcreteHandlerC::new());
        
        Arc::make_mut(&mut handler_a).set_next(handler_b.clone());
        Arc::make_mut(&mut handler_b).set_next(handler_c.clone());
        
        b.iter(|| {
            handler_a.handle(black_box("Test Request".to_string()));
        });
    });
    
    group.finish();
}

/// 内存使用基准测试
fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    
    // 测试享元模式的内存效率
    group.bench_function("flyweight_memory_efficiency", |b| {
        b.iter(|| {
            let mut factory = OptimizedFlyweightFactory::new();
            
            // 创建1000个享元对象，但只有100个唯一状态
            for i in 0..1000 {
                let key = format!("memory_test_{}", i % 100);
                let state = format!("Memory State {}", i % 100);
                let _flyweight = factory.get_flyweight(&key, state);
            }
            
            let (count, _) = factory.get_statistics();
            black_box(count)
        });
    });
    
    // 测试单例模式的内存效率
    group.bench_function("singleton_memory_efficiency", |b| {
        b.iter(|| {
            let singleton = Singleton::new();
            
            // 多次获取同一实例
            for _ in 0..1000 {
                let _instance = singleton.get_instance(|| {
                    black_box(String::from("Memory Test Instance"))
                });
            }
            
            black_box(())
        });
    });
    
    group.finish();
}

/// 并发性能基准测试
fn benchmark_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrency");
    
    // 测试多线程单例访问性能
    group.bench_function("singleton_concurrent_access", |b| {
        use std::thread;
        
        b.iter(|| {
            let singleton = Arc::new(Singleton::new());
            let mut handles = vec![];
            
            for _ in 0..10 {
                let singleton_clone = Arc::clone(&singleton);
                let handle = thread::spawn(move || {
                    let _instance = singleton_clone.get_instance(|| {
                        black_box(String::from("Concurrent Instance"))
                    });
                });
                handles.push(handle);
            }
            
            for handle in handles {
                handle.join().unwrap();
            }
        });
    });
    
    group.finish();
}

/// 可扩展性基准测试
fn benchmark_scalability(c: &mut Criterion) {
    let mut group = c.benchmark_group("scalability");
    
    // 测试不同规模下的享元模式性能
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("flyweight_scale", size), size, |b, &size| {
            b.iter(|| {
                let mut factory = OptimizedFlyweightFactory::new();
                
                for i in 0..size {
                    let key = format!("scale_test_{}", i);
                    let state = format!("Scale State {}", i);
                    let _flyweight = factory.get_flyweight(&key, state);
                }
                
                let (count, _) = factory.get_statistics();
                black_box(count)
            });
        });
    }
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_singleton,
    benchmark_flyweight,
    benchmark_proxy,
    benchmark_chain_of_responsibility,
    benchmark_memory_usage,
    benchmark_concurrency,
    benchmark_scalability
);

criterion_main!(benches);
