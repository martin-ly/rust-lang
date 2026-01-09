//! 内存性能基准测试
//!
//! 这个模块包含了 c10_networks 库内存管理相关的性能基准测试

use bytes::Bytes;
use c10_networks::{
    packet::{Packet, PacketStats, PacketType},
    performance::{memory_pool::MemoryPool, cache::Cache},
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::sync::Arc;
use std::thread;

/// 内存分配性能测试
fn bench_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");

    group.bench_function("bytes_creation", |b| {
        b.iter(|| {
            let data = Bytes::copy_from_slice(black_box(b"test data"));
            black_box(data)
        })
    });

    group.bench_function("vec_creation", |b| {
        b.iter(|| {
            let data = black_box(b"test data").to_vec();
            black_box(data)
        })
    });

    group.bench_function("string_creation", |b| {
        b.iter(|| {
            let data = black_box("test data").to_string();
            black_box(data)
        })
    });

    group.bench_function("boxed_creation", |b| {
        b.iter(|| {
            let data = Box::new(black_box([1, 2, 3, 4, 5]));
            black_box(data)
        })
    });

    group.finish();
}

/// 内存池性能测试
fn bench_memory_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_pool");

    group.bench_function("pool_creation", |b| {
        b.iter(|| {
            let pool = MemoryPool::new(black_box(1024));
            black_box(pool)
        })
    });

    group.bench_function("pool_allocation", |b| {
        let pool = MemoryPool::new(1024);
        b.iter(|| {
            let buffer = pool.allocate(black_box(512));
            black_box(buffer)
        })
    });

    group.bench_function("pool_allocation_failure", |b| {
        let pool = MemoryPool::new(1024);
        b.iter(|| {
            let buffer = pool.allocate(black_box(2048)); // 超过块大小
            black_box(buffer)
        })
    });

    group.bench_function("pool_reuse", |b| {
        let pool = MemoryPool::new(1024);
        b.iter(|| {
            let buffer1 = pool.allocate(black_box(256));
            let buffer2 = pool.allocate(black_box(512));
            // 内存池会自动管理内存，无需手动释放
            black_box((buffer1, buffer2))
        })
    });

    group.finish();
}

/// 缓存性能测试
fn bench_cache_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_performance");

    group.bench_function("cache_creation", |b| {
        b.iter(|| {
            let cache: Cache<String, String> = Cache::new(black_box(1000));
            black_box(cache)
        })
    });

    group.bench_function("cache_insert", |b| {
        let cache: Cache<String, String> = Cache::new(1000);
        b.iter(|| {
            cache.insert(black_box("key".to_string()), black_box("value".to_string()));
        })
    });

    group.bench_function("cache_get", |b| {
        let cache: Cache<String, String> = Cache::new(1000);
        cache.insert("key".to_string(), "value".to_string());
        b.iter(|| {
            let value = cache.get(black_box(&"key".to_string()));
            black_box(value)
        })
    });

    group.bench_function("cache_eviction", |b| {
        let cache: Cache<String, String> = Cache::new(10); // 小缓存，容易触发驱逐
        b.iter(|| {
            for i in 0..20 {
                cache.insert(format!("key{}", i), format!("value{}", i));
            }
        })
    });

    group.finish();
}

/// 数据包内存性能测试
fn bench_packet_memory(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_memory");

    group.bench_function("packet_creation", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Raw),
                black_box(Bytes::copy_from_slice(b"test data")),
            );
            black_box(packet)
        })
    });

    group.bench_function("packet_clone", |b| {
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
        b.iter(|| {
            let cloned = black_box(&packet).clone();
            black_box(cloned)
        })
    });

    group.bench_function("packet_move", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Raw),
                black_box(Bytes::copy_from_slice(b"test data")),
            );
            let moved = black_box(packet);
            black_box(moved)
        })
    });

    group.bench_function("packet_stats_memory", |b| {
        let mut stats = PacketStats::new();
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            stats.add_packet(black_box(&packet));
        })
    });

    group.finish();
}

/// 大数据块内存性能测试
fn bench_large_memory_blocks(c: &mut Criterion) {
    let mut group = c.benchmark_group("large_memory_blocks");

    let sizes = vec![1024, 4096, 16384, 65536, 262144]; // 1KB, 4KB, 16KB, 64KB, 256KB

    for size in sizes {
        group.bench_function(&format!("bytes_{}KB", size / 1024), |b| {
            let data = vec![0u8; size];
            b.iter(|| {
                let bytes = Bytes::copy_from_slice(black_box(&data));
                black_box(bytes)
            })
        });

        group.bench_function(&format!("vec_{}KB", size / 1024), |b| {
            b.iter(|| {
                let data = vec![0u8; black_box(size)];
                black_box(data)
            })
        });

        group.bench_function(&format!("boxed_{}KB", size / 1024), |b| {
            b.iter(|| {
                let data = Box::new(vec![0u8; black_box(size)]);
                black_box(data)
            })
        });

        group.bench_function(&format!("packet_{}KB", size / 1024), |b| {
            let data = vec![0u8; size];
            b.iter(|| {
                let packet = Packet::new(
                    black_box(PacketType::Raw),
                    black_box(Bytes::from(data.clone())),
                );
                black_box(packet)
            })
        });
    }

    group.finish();
}

/// 内存碎片化性能测试
fn bench_memory_fragmentation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_fragmentation");

    group.bench_function("fragmented_allocation", |b| {
        b.iter(|| {
            let mut allocations = Vec::new();

            // 分配不同大小的内存块
            for i in 0..100 {
                let size = (i % 10 + 1) * 64; // 64, 128, 192, ..., 640 bytes
                let data = vec![0u8; size];
                allocations.push(data);
            }

            // 释放一半的内存块
            for i in (0..100).step_by(2) {
                allocations[i] = Vec::new();
            }

            // 重新分配
            for i in (0..100).step_by(2) {
                let size = (i % 10 + 1) * 64;
                allocations[i] = vec![0u8; size];
            }

            black_box(allocations.len())
        })
    });

    group.bench_function("packet_fragmentation", |b| {
        b.iter(|| {
            let mut packets = Vec::new();

            // 创建不同大小的数据包
            for i in 0..100 {
                let size = (i % 10 + 1) * 64;
                let data = vec![0u8; size];
                let packet = Packet::new(PacketType::Raw, Bytes::from(data));
                packets.push(packet);
            }

            // 移除一半的数据包
            for i in (0..100).step_by(2) {
                packets[i] = Packet::new(PacketType::Raw, Bytes::new());
            }

            // 重新创建
            for i in (0..100).step_by(2) {
                let size = (i % 10 + 1) * 64;
                let data = vec![0u8; size];
                packets[i] = Packet::new(PacketType::Raw, Bytes::from(data));
            }

            black_box(packets.len())
        })
    });

    group.finish();
}

/// 并发内存分配性能测试
fn bench_concurrent_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_memory_allocation");

    group.bench_function("multi_thread_allocation", |b| {
        b.iter(|| {
            let mut handles = Vec::new();

            for thread_id in 0..4 {
                let handle = thread::spawn(move || {
                    let mut allocations = Vec::new();
                    for i in 0..100 {
                        let size = (thread_id * 100 + i) % 1000 + 64;
                        let data = vec![0u8; size];
                        allocations.push(data);
                    }
                    allocations.len()
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

    group.bench_function("multi_thread_packet_creation", |b| {
        b.iter(|| {
            let mut handles = Vec::new();

            for thread_id in 0..4 {
                let handle = thread::spawn(move || {
                    let mut packets = Vec::new();
                    for i in 0..100 {
                        let size = (thread_id * 100 + i) % 1000 + 64;
                        let data = vec![0u8; size];
                        let packet = Packet::new(PacketType::Raw, Bytes::from(data));
                        packets.push(packet);
                    }
                    packets.len()
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

    group.bench_function("shared_memory_pool", |b| {
        let pool = Arc::new(MemoryPool::new(1024 * 1024));

        b.iter(|| {
            let mut handles = Vec::new();

            for _thread_id in 0..4 {
                let pool_clone = Arc::clone(&pool);
                let handle = thread::spawn(move || {
                    let mut buffers = Vec::new();
                    for _i in 0..100 {
                        let buffer = pool_clone.allocate(64);
                        buffers.push(buffer);
                    }
                    buffers.len()
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

/// 内存使用模式性能测试
fn bench_memory_usage_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage_patterns");

    group.bench_function("sequential_allocation", |b| {
        b.iter(|| {
            let mut allocations = Vec::new();
            for i in 0..1000 {
                let size = (i % 100) + 64;
                let data = vec![0u8; size];
                allocations.push(data);
            }
            black_box(allocations.len())
        })
    });

    group.bench_function("random_allocation", |b| {
        b.iter(|| {
            let mut allocations = Vec::new();
            for i in 0..1000 {
                let size = ((i * 7) % 100) + 64; // 伪随机大小
                let data = vec![0u8; size];
                allocations.push(data);
            }
            black_box(allocations.len())
        })
    });

    group.bench_function("burst_allocation", |b| {
        b.iter(|| {
            let mut allocations = Vec::new();

            // 突发分配
            for _burst in 0..10 {
                for i in 0..100 {
                    let size = (i % 50) + 64;
                    let data = vec![0u8; size];
                    allocations.push(data);
                }
            }

            black_box(allocations.len())
        })
    });

    group.bench_function("lifo_allocation", |b| {
        b.iter(|| {
            let mut allocations = Vec::new();

            // 分配
            for i in 0..1000 {
                let size = (i % 100) + 64;
                let data = vec![0u8; size];
                allocations.push(data);
            }

            // LIFO 释放
            while !allocations.is_empty() {
                allocations.pop();
            }

            black_box(allocations.len())
        })
    });

    group.finish();
}

/// 内存泄漏检测性能测试
fn bench_memory_leak_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_leak_detection");

    group.bench_function("reference_counting", |b| {
        b.iter(|| {
            let data = Bytes::copy_from_slice(b"test data");
            let data1 = data.clone();
            let data2 = data.clone();
            let data3 = data.clone();

            // 模拟使用
            black_box(data1.len());
            black_box(data2.len());
            black_box(data3.len());

            // 自动释放
            drop(data1);
            drop(data2);
            drop(data3);
            drop(data);
        })
    });

    group.bench_function("weak_references", |b| {
        use std::rc::Rc;

        b.iter(|| {
            let data = Rc::new(vec![0u8; 1024]);
            let weak_ref = Rc::downgrade(&data);

            // 使用强引用
            black_box(data.len());

            // 释放强引用
            drop(data);

            // 检查弱引用
            let strong_ref = weak_ref.upgrade();
            black_box(strong_ref.is_none())
        })
    });

    group.bench_function("arc_usage", |b| {
        b.iter(|| {
            let data = Arc::new(vec![0u8; 1024]);
            let data1 = Arc::clone(&data);
            let data2 = Arc::clone(&data);

            // 模拟使用
            black_box(data1.len());
            black_box(data2.len());

            // 自动释放
            drop(data1);
            drop(data2);
            drop(data);
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_memory_allocation,
    bench_memory_pool,
    bench_cache_performance,
    bench_packet_memory,
    bench_large_memory_blocks,
    bench_memory_fragmentation,
    bench_concurrent_memory_allocation,
    bench_memory_usage_patterns,
    bench_memory_leak_detection
);

criterion_main!(benches);
