use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

// 基准测试：互斥锁 vs 读写锁 / Benchmark: Mutex vs RwLock
fn bench_mutex_vs_rwlock(c: &mut Criterion) {
    let mut group = c.benchmark_group("mutex_vs_rwlock");
    
    for size in [100, 1000, 10000].iter() {
        // 互斥锁测试 / Mutex test
        group.bench_with_input(BenchmarkId::new("mutex", size), size, |b, &size| {
            b.iter(|| {
                let data = Arc::new(Mutex::new(vec![0; size]));
                let mut handles = vec![];
                
                for _ in 0..4 {
                    let data_clone = data.clone();
                    let handle = thread::spawn(move || {
                        for _ in 0..100 {
                            let mut vec = data_clone.lock().unwrap();
                            for i in 0..vec.len() {
                                vec[i] += 1;
                            }
                        }
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.join().unwrap();
                }
                
                black_box(data);
            })
        });
        
        // 读写锁测试 / RwLock test
        group.bench_with_input(BenchmarkId::new("rwlock", size), size, |b, &size| {
            b.iter(|| {
                let data = Arc::new(RwLock::new(vec![0; size]));
                let mut handles = vec![];
                
                for _ in 0..4 {
                    let data_clone = data.clone();
                    let handle = thread::spawn(move || {
                        for _ in 0..100 {
                            let mut vec = data_clone.write().unwrap();
                            for i in 0..vec.len() {
                                vec[i] += 1;
                            }
                        }
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.join().unwrap();
                }
                
                black_box(data);
            })
        });
    }
    
    group.finish();
}

// 基准测试：原子操作 vs 锁 / Benchmark: Atomic operations vs locks
fn bench_atomic_vs_lock(c: &mut Criterion) {
    let mut group = c.benchmark_group("atomic_vs_lock");
    
    for operations in [1000, 10000, 100000].iter() {
        // 原子操作测试 / Atomic operations test
        group.bench_with_input(BenchmarkId::new("atomic", operations), operations, |b, &ops| {
            b.iter(|| {
                use std::sync::atomic::{AtomicUsize, Ordering};
                
                let counter = Arc::new(AtomicUsize::new(0));
                let mut handles = vec![];
                
                for _ in 0..4 {
                    let counter_clone = counter.clone();
                    let handle = thread::spawn(move || {
                        for _ in 0..ops {
                            counter_clone.fetch_add(1, Ordering::SeqCst);
                        }
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.join().unwrap();
                }
                
                black_box(counter.load(Ordering::SeqCst));
            })
        });
        
        // 锁测试 / Lock test
        group.bench_with_input(BenchmarkId::new("lock", operations), operations, |b, &ops| {
            b.iter(|| {
                let counter = Arc::new(Mutex::new(0usize));
                let mut handles = vec![];
                
                for _ in 0..4 {
                    let counter_clone = counter.clone();
                    let handle = thread::spawn(move || {
                        for _ in 0..ops {
                            let mut count = counter_clone.lock().unwrap();
                            *count += 1;
                        }
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.join().unwrap();
                }
                
                black_box(*counter.lock().unwrap());
            })
        });
    }
    
    group.finish();
}

// 基准测试：通道性能 / Benchmark: Channel performance
fn bench_channel_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("channel_performance");
    
    for message_count in [1000, 10000, 100000].iter() {
        // 无界通道测试 / Unbounded channel test
        group.bench_with_input(BenchmarkId::new("unbounded", message_count), message_count, |b, &count| {
            b.iter(|| {
                use std::sync::mpsc;
                
                let (tx, rx) = mpsc::channel();
                let tx_clone = tx.clone();
                
                let sender = thread::spawn(move || {
                    for i in 0..count {
                        tx_clone.send(i).unwrap();
                    }
                });
                
                let receiver = thread::spawn(move || {
                    let mut received = 0;
                    while let Ok(_) = rx.recv() {
                        received += 1;
                    }
                    received
                });
                
                sender.join().unwrap();
                let received = receiver.join().unwrap();
                
                black_box(received);
            })
        });
        
        // 有界通道测试 / Bounded channel test
        group.bench_with_input(BenchmarkId::new("bounded", message_count), message_count, |b, &count| {
            b.iter(|| {
                use std::sync::mpsc;
                
                let (tx, rx) = mpsc::sync_channel(1000);
                let tx_clone = tx.clone();
                
                let sender = thread::spawn(move || {
                    for i in 0..count {
                        tx_clone.send(i).unwrap();
                    }
                });
                
                let receiver = thread::spawn(move || {
                    let mut received = 0;
                    while let Ok(_) = rx.recv() {
                        received += 1;
                    }
                    received
                });
                
                sender.join().unwrap();
                let received = receiver.join().unwrap();
                
                black_box(received);
            })
        });
    }
    
    group.finish();
}

// 基准测试：线程池性能 / Benchmark: Thread pool performance
fn bench_thread_pool_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("thread_pool_performance");
    
    for task_count in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("spawn_threads", task_count), task_count, |b, &count| {
            b.iter(|| {
                let mut handles = vec![];
                
                for i in 0..count {
                    let handle = thread::spawn(move || {
                        // 模拟一些工作 / Simulate some work
                        let result = i * i;
                        black_box(result);
                    });
                    handles.push(handle);
                }
                
                for handle in handles {
                    handle.join().unwrap();
                }
            })
        });
        
        group.bench_with_input(BenchmarkId::new("rayon_parallel", task_count), task_count, |b, &count| {
            b.iter(|| {
                use rayon::prelude::*;
                
                let data: Vec<usize> = (0..count).collect();
                let result: Vec<usize> = data.par_iter().map(|&x| x * x).collect();
                black_box(result);
            })
        });
    }
    
    group.finish();
}

// 基准测试：内存分配性能 / Benchmark: Memory allocation performance
fn bench_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");
    
    for size in [1024, 10240, 102400].iter() {
        group.bench_with_input(BenchmarkId::new("vec_push", size), size, |b, &size| {
            b.iter(|| {
                let mut vec = Vec::with_capacity(size);
                for i in 0..size {
                    vec.push(i);
                }
                black_box(vec);
            })
        });
        
        group.bench_with_input(BenchmarkId::new("vec_with_capacity", size), size, |b, &size| {
            b.iter(|| {
                let mut vec = Vec::with_capacity(size);
                for i in 0..size {
                    vec.push(i);
                }
                black_box(vec);
            })
        });
        
        group.bench_with_input(BenchmarkId::new("boxed_slice", size), size, |b, &size| {
            b.iter(|| {
                let mut vec = vec![0; size];
                for i in 0..size {
                    vec[i] = i;
                }
                let boxed = vec.into_boxed_slice();
                black_box(boxed);
            })
        });
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_mutex_vs_rwlock,
    bench_atomic_vs_lock,
    bench_channel_performance,
    bench_thread_pool_performance,
    bench_memory_allocation
);
criterion_main!(benches);
