use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use c07_process::prelude::*;
use std::collections::HashMap;
use std::time::Duration;

/// 进程创建性能基准测试
fn benchmark_process_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Process Creation");
    
    group.bench_function("single_process_spawn", |b| {
        b.iter(|| {
            let mut env = HashMap::new();
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
            
            let config = ProcessConfig {
                program: "echo".to_string(),
                args: vec!["test".to_string()],
                env: env.clone(),
                working_dir: Some("/tmp".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            };
            
            let mut manager = ProcessManager::new();
            let _pid = manager.spawn(config).unwrap();
        });
    });
    
    group.bench_function("batch_process_spawn", |b| {
        b.iter(|| {
            let mut manager = ProcessManager::new();
            let mut env = HashMap::new();
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
            
            for i in 0..10 {
                let config = ProcessConfig {
                    program: "echo".to_string(),
                    args: vec![format!("test{}", i)],
                    env: env.clone(),
                    working_dir: Some("/tmp".to_string()),
                    user_id: None,
                    group_id: None,
                    priority: None,
                    resource_limits: ResourceLimits::default(),
                };
                
                let _pid = manager.spawn(config).unwrap();
            }
        });
    });
    
    group.finish();
}

/// 进程池性能基准测试
fn benchmark_process_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("Process Pool");
    
    group.bench_function("pool_creation", |b| {
        b.iter(|| {
            let pool_config = ProcessPoolConfig {
                min_processes: 5,
                max_processes: 10,
                initial_processes: 5,
                idle_timeout: Duration::from_secs(60),
                health_check_interval: Duration::from_secs(30),
                load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
                auto_scaling: AutoScalingConfig::default(),
            };
            
            let base_config = ProcessConfig {
                program: "worker".to_string(),
                args: Vec::new(),
                env: HashMap::new(),
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            };
            let _pool = ProcessPool::new(pool_config, base_config).unwrap();
        });
    });
    
    group.bench_function("pool_operations", |b| {
        b.iter(|| {
            let pool_config = ProcessPoolConfig {
                min_processes: 3,
                max_processes: 5,
                initial_processes: 3,
                idle_timeout: Duration::from_secs(60),
                health_check_interval: Duration::from_secs(30),
                load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
                auto_scaling: AutoScalingConfig::default(),
            };
            
            let base_config = ProcessConfig {
                program: "worker".to_string(),
                args: Vec::new(),
                env: HashMap::new(),
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            };
            let pool = ProcessPool::new(pool_config, base_config).unwrap();
            
            // 获取和释放进程
            for _ in 0..5 {
                if let Ok(pid) = pool.get_process() {
                    let _ = pool.release_process(pid);
                }
            }
        });
    });
    
    group.finish();
}

/// IPC通信性能基准测试
fn benchmark_ipc_communication(c: &mut Criterion) {
    let mut group = c.benchmark_group("IPC Communication");
    
    group.bench_function("message_queue_creation", |b| {
        b.iter(|| {
            let ipc_config = IpcConfig::default();
            let mut ipc = IpcManager::new(ipc_config);
            let _ = ipc.create_message_queue("benchmark_queue", 1000);
        });
    });
    
    group.bench_function("shared_memory_creation", |b| {
        b.iter(|| {
            let ipc_config = IpcConfig::default();
            let mut ipc = IpcManager::new(ipc_config);
            let _ = ipc.create_shared_memory("benchmark_memory", 1024);
        });
    });
    
    group.finish();
}

/// 同步原语性能基准测试
fn benchmark_synchronization(c: &mut Criterion) {
    let mut group = c.benchmark_group("Synchronization");
    
    group.bench_function("mutex_lock_unlock", |b| {
        b.iter(|| {
            let sync_config = SyncConfig::default();
            let mut sync = SyncManager::new(sync_config);
            let mutex = sync.create_mutex("benchmark_mutex").unwrap();
            
            for _ in 0..100 {
                let _guard = mutex.lock().unwrap();
                // 模拟工作
                black_box(42);
            }
        });
    });
    
    group.bench_function("semaphore_acquire_release", |b| {
        b.iter(|| {
            let sync_config = SyncConfig::default();
            let mut sync = SyncManager::new(sync_config);
            let semaphore = sync.create_semaphore("benchmark_semaphore", 5).unwrap();
            
            for _ in 0..100 {
                let _permit = semaphore.acquire().unwrap();
                // 模拟工作
                black_box(42);
            }
        });
    });
    
    group.bench_function("rwlock_read_write", |b| {
        b.iter(|| {
            let sync_config = SyncConfig::default();
            let mut sync = SyncManager::new(sync_config);
            let rwlock = sync.create_rwlock("benchmark_rwlock").unwrap();
            
            for _ in 0..50 {
                let _read_guard = rwlock.read().unwrap();
                black_box(42);
            }
            
            for _ in 0..50 {
                let _write_guard = rwlock.write().unwrap();
                black_box(42);
            }
        });
    });
    
    group.finish();
}

/// 并发性能基准测试
fn benchmark_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("Concurrency");
    
    group.bench_function("parallel_process_spawn", |b| {
        b.iter(|| {
            use std::thread;
            use std::sync::{Arc, Barrier};
            
            let manager = Arc::new(ProcessManager::new());
            let barrier = Arc::new(Barrier::new(4));
            let mut handles = Vec::new();
            
            for _ in 0..4 {
                let _manager_clone = manager.clone();
                let barrier_clone = barrier.clone();
                
                let handle = thread::spawn(move || {
                    let mut env = HashMap::new();
                    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
                    
                    let config = ProcessConfig {
                        program: "echo".to_string(),
                        args: vec!["parallel_test".to_string()],
                        env,
                        working_dir: Some("/tmp".to_string()),
                        user_id: None,
                        group_id: None,
                        priority: None,
                        resource_limits: ResourceLimits::default(),
                    };
                    
                    // 使用内部可变性来启动进程
                    let mut manager_inner = ProcessManager::new();
                    let _pid = manager_inner.spawn(config).unwrap();
                    barrier_clone.wait();
                });
                
                handles.push(handle);
            }
            
            for handle in handles {
                handle.join().unwrap();
            }
        });
    });
    
    group.bench_function("concurrent_sync_operations", |b| {
        b.iter(|| {
            use std::thread;
            use std::sync::{Arc, Barrier};
            
            let barrier = Arc::new(Barrier::new(4));
            let mut handles = Vec::new();
            
            for _ in 0..4 {
                let barrier_clone = barrier.clone();
                
                let handle = thread::spawn(move || {
                    let sync_config = SyncConfig::default();
                    let mut sync = SyncManager::new(sync_config);
                    let mutex = sync.create_mutex("concurrent_mutex").unwrap();
                    let semaphore = sync.create_semaphore("concurrent_semaphore", 2).unwrap();
                    
                    for _ in 0..25 {
                        let _permit = semaphore.acquire().unwrap();
                        let _guard = mutex.lock().unwrap();
                        black_box(42);
                    }
                    
                    barrier_clone.wait();
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

/// 内存使用性能基准测试
fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("Memory Usage");
    
    group.bench_function("large_process_pool", |b| {
        b.iter(|| {
            let pool_config = ProcessPoolConfig {
                min_processes: 50,
                max_processes: 100,
                initial_processes: 50,
                idle_timeout: Duration::from_secs(60),
                health_check_interval: Duration::from_secs(30),
                load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
                auto_scaling: AutoScalingConfig::default(),
            };
            
            let base_config = ProcessConfig {
                program: "worker".to_string(),
                args: Vec::new(),
                env: HashMap::new(),
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            };
            let _pool = ProcessPool::new(pool_config, base_config).unwrap();
        });
    });
    
    group.bench_function("large_shared_memory", |b| {
        b.iter(|| {
            let ipc_config = IpcConfig::default();
            let mut ipc = IpcManager::new(ipc_config);
            let _ = ipc.create_shared_memory("large_memory", 1024 * 1024); // 1MB
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_process_creation,
    benchmark_process_pool,
    benchmark_ipc_communication,
    benchmark_synchronization,
    benchmark_concurrency,
    benchmark_memory_usage
);

criterion_main!(benches);
