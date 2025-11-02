//! 网络性能基准测试
//!
//! 本文件包含各种网络操作的性能基准测试，用于评估2025年最新优化后的性能

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::io::{Read, Write};
use std::time::Duration;

/// HTTP请求处理基准测试
fn bench_http_request_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("http_request_processing");

    let request_sizes = [100, 1000, 10000];

    for size in request_sizes.iter() {
        let request = format!(
            "GET /test HTTP/1.1\r\n\
             Host: localhost\r\n\
             Content-Length: {}\r\n\
             \r\n\
             {}",
            size,
            "a".repeat(*size)
        );

        group.bench_with_input(BenchmarkId::new("parse_headers", size), size, |b, _| {
            b.iter(|| {
                // 模拟HTTP头部解析
                let lines: Vec<&str> = request.lines().collect();
                let mut headers = std::collections::HashMap::new();

                for line in &lines[1..] {
                    if line.is_empty() {
                        break;
                    }
                    if let Some((key, value)) = line.split_once(':') {
                        headers.insert(key.trim().to_string(), value.trim().to_string());
                    }
                }

                headers
            })
        });

        group.bench_with_input(BenchmarkId::new("parse_url", size), size, |b, _| {
            b.iter(|| {
                // 模拟URL解析
                let url = format!("http://localhost:8080/test?param={}", "a".repeat(*size));
                url::Url::parse(&url).unwrap()
            })
        });
    }

    group.finish();
}

/// 数据序列化基准测试
fn bench_data_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_serialization");

    let sizes = [100, 1000, 10000];

    for size in sizes.iter() {
        let data = create_test_data(*size);

        group.bench_with_input(BenchmarkId::new("json_serialize", size), size, |b, _| {
            b.iter(|| {
                serde_json::to_string(&data).unwrap()
            })
        });

        group.bench_with_input(BenchmarkId::new("json_deserialize", size), size, |b, _| {
            let json = serde_json::to_string(&data).unwrap();
            b.iter(|| {
                serde_json::from_str::<TestData>(&json).unwrap()
            })
        });

        group.bench_with_input(BenchmarkId::new("bincode_serialize", size), size, |b, _| {
            b.iter(|| {
                bincode::encode_to_vec(&data, bincode::config::standard()).unwrap()
            })
        });

        group.bench_with_input(BenchmarkId::new("bincode_deserialize", size), size, |b, _| {
            let binary = bincode::encode_to_vec(&data, bincode::config::standard()).unwrap();
            b.iter(|| {
                let (result, _) = bincode::decode_from_slice::<TestData, _>(&binary, bincode::config::standard()).unwrap();
                result
            })
        });
    }

    group.finish();
}

/// 加密解密基准测试
fn bench_encryption_decryption(c: &mut Criterion) {
    let mut group = c.benchmark_group("encryption_decryption");

    let sizes = [100, 1000, 10000];
    let key = b"0123456789abcdef0123456789abcdef"; // 32字节密钥

    for size in sizes.iter() {
        let data = vec![0u8; *size];

        group.bench_with_input(BenchmarkId::new("aes_encrypt", size), size, |b, _| {
            b.iter(|| {
                use aes_gcm::{Aes256Gcm, KeyInit};
                use aes_gcm::aead::Aead;

                #[allow(deprecated)]
                let cipher = Aes256Gcm::new_from_slice(key).unwrap();
                #[allow(deprecated)]
                let nonce = aes_gcm::Nonce::from_slice(b"unique nonce");
                cipher.encrypt(nonce, data.as_ref()).unwrap()
            })
        });

        group.bench_with_input(BenchmarkId::new("sha256_hash", size), size, |b, _| {
            b.iter(|| {
                use sha2::{Sha256, Digest};
                let mut hasher = Sha256::new();
                hasher.update(&data);
                hasher.finalize()
            })
        });
    }

    group.finish();
}

/// 网络I/O基准测试
fn bench_network_io(c: &mut Criterion) {
    let mut group = c.benchmark_group("network_io");

    let sizes = [1024, 10240, 102400]; // 1KB, 10KB, 100KB

    for size in sizes.iter() {
        let data = vec![0u8; *size];

        group.bench_with_input(BenchmarkId::new("tcp_write", size), size, |b, _| {
            b.iter(|| {
                // 模拟TCP写入
                let mut buffer = Vec::new();
                buffer.write_all(&data).unwrap();
                buffer
            })
        });

        group.bench_with_input(BenchmarkId::new("tcp_read", size), size, |b, _| {
            let buffer = data.clone();
            b.iter(|| {
                // 模拟TCP读取
                let mut result = vec![0u8; *size];
                buffer.as_slice().read_exact(&mut result).unwrap();
                result
            })
        });
    }

    group.finish();
}

/// 连接池基准测试
fn bench_connection_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("connection_pool");

    let pool_sizes = [10, 100, 1000];

    for pool_size in pool_sizes.iter() {
        group.bench_with_input(BenchmarkId::new("pool_acquire", pool_size), pool_size, |b, _| {
            b.iter(|| {
                // 模拟连接池获取
                let mut pool = Vec::new();
                for i in 0..*pool_size {
                    pool.push(format!("connection_{}", i));
                }
                pool
            })
        });

        group.bench_with_input(BenchmarkId::new("pool_release", pool_size), pool_size, |b, _| {
            let mut pool = Vec::new();
            for i in 0..*pool_size {
                pool.push(format!("connection_{}", i));
            }
            b.iter(|| {
                // 模拟连接池释放
                pool.clone()
            })
        });
    }

    group.finish();
}

/// 负载均衡基准测试
fn bench_load_balancing(c: &mut Criterion) {
    let mut group = c.benchmark_group("load_balancing");

    let server_counts = [5, 10, 20];

    for server_count in server_counts.iter() {
        let servers: Vec<String> = (0..*server_count)
            .map(|i| format!("server_{}", i))
            .collect();

        group.bench_with_input(BenchmarkId::new("round_robin", server_count), server_count, |b, _| {
            b.iter(|| {
                // 轮询负载均衡
                let mut index = 0;
                let mut selected = Vec::new();
                for _ in 0..1000 {
                    selected.push(&servers[index % servers.len()]);
                    index += 1;
                }
                selected
            })
        });

        group.bench_with_input(BenchmarkId::new("weighted_round_robin", server_count), server_count, |b, _| {
            let weights: Vec<u32> = (0..*server_count).map(|i| (i + 1) as u32).collect();
            b.iter(|| {
                // 加权轮询负载均衡
                let mut current_weight = 0;
                let mut selected = Vec::new();
                for _ in 0..1000 {
                    let mut max_weight = 0;
                    let mut selected_index = 0;
                    for (i, &weight) in weights.iter().enumerate() {
                        current_weight += weight;
                        if current_weight > max_weight {
                            max_weight = current_weight;
                            selected_index = i;
                        }
                    }
                    selected.push(&servers[selected_index]);
                    current_weight -= weights[selected_index];
                }
                selected
            })
        });
    }

    group.finish();
}

/// 缓存基准测试
fn bench_caching(c: &mut Criterion) {
    let mut group = c.benchmark_group("caching");

    let cache_sizes = [100, 1000, 10000];

    for cache_size in cache_sizes.iter() {
        group.bench_with_input(BenchmarkId::new("lru_cache", cache_size), cache_size, |b, _| {
            b.iter(|| {
                use lru::LruCache;
                let mut cache = LruCache::new(std::num::NonZeroUsize::new(*cache_size).unwrap());

                // 模拟缓存操作
                for i in 0..*cache_size {
                    cache.put(i, format!("value_{}", i));
                }

                // 模拟缓存访问
                for i in 0..*cache_size {
                    cache.get(&i);
                }

                cache
            })
        });

        group.bench_with_input(BenchmarkId::new("hash_map_cache", cache_size), cache_size, |b, _| {
            b.iter(|| {
                use std::collections::HashMap;
                let mut cache = HashMap::new();

                // 模拟缓存操作
                for i in 0..*cache_size {
                    cache.insert(i, format!("value_{}", i));
                }

                // 模拟缓存访问
                for i in 0..*cache_size {
                    cache.get(&i);
                }

                cache
            })
        });
    }

    group.finish();
}

/// 异步操作基准测试
fn bench_async_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("async_operations");

    let task_counts = [10, 100, 1000];

    for task_count in task_counts.iter() {
        group.bench_with_input(BenchmarkId::new("async_spawn", task_count), task_count, |b, _| {
            b.iter(|| {
                use tokio::runtime::Runtime;
                let rt = Runtime::new().unwrap();
                rt.block_on(async {
                    let mut handles = Vec::new();
                    for i in 0..*task_count {
                        let handle = tokio::spawn(async move {
                            // 模拟异步任务
                            tokio::time::sleep(Duration::from_millis(1)).await;
                            i * 2
                        });
                        handles.push(handle);
                    }

                    let mut results = Vec::new();
                    for handle in handles {
                        results.push(handle.await.unwrap());
                    }
                    results
                })
            })
        });

        group.bench_with_input(BenchmarkId::new("async_join", task_count), task_count, |b, _| {
            b.iter(|| {
                use tokio::runtime::Runtime;
                let rt = Runtime::new().unwrap();
                rt.block_on(async {
                    let mut tasks = Vec::new();
                    for i in 0..*task_count {
                        tasks.push(async move {
                            tokio::time::sleep(Duration::from_millis(1)).await;
                            i * 2
                        });
                    }

                    let results = futures::future::join_all(tasks).await;
                    results
                })
            })
        });
    }

    group.finish();
}

/// 创建测试数据
fn create_test_data(size: usize) -> TestData {
    TestData {
        id: 1,
        name: "test".to_string(),
        values: (0..size).map(|i| i as f64).collect(),
        metadata: std::collections::HashMap::new(),
    }
}

/// 测试数据结构
#[derive(serde::Serialize, serde::Deserialize, bincode::Encode, bincode::Decode, Clone)]
struct TestData {
    id: u32,
    name: String,
    values: Vec<f64>,
    metadata: std::collections::HashMap<String, String>,
}

criterion_group!(
    benches,
    bench_http_request_processing,
    bench_data_serialization,
    bench_encryption_decryption,
    bench_network_io,
    bench_connection_pool,
    bench_load_balancing,
    bench_caching,
    bench_async_operations
);

criterion_main!(benches);
