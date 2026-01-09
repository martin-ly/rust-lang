//! 数据包性能基准测试
//!
//! 这个模块包含了 c10_networks 库数据包处理的性能基准测试

use bytes::Bytes;
use c10_networks::{
    packet::{Packet, PacketBuilder, PacketBuffer, PacketFilter, PacketStats, PacketType},
    packet::buffer::BufferConfig,
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::Duration;

/// 数据包创建性能测试
fn bench_packet_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_creation");

    group.bench_function("raw_packet", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Raw),
                black_box(Bytes::copy_from_slice(b"test data")),
            );
            black_box(packet)
        })
    });

    group.bench_function("http_packet", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Http),
                black_box(Bytes::copy_from_slice(b"GET / HTTP/1.1")),
            );
            black_box(packet)
        })
    });

    group.bench_function("websocket_packet", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::WebSocket),
                black_box(Bytes::copy_from_slice(b"Hello, WebSocket!")),
            );
            black_box(packet)
        })
    });

    group.bench_function("tcp_packet", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Tcp),
                black_box(Bytes::copy_from_slice(b"TCP data")),
            );
            black_box(packet)
        })
    });

    group.bench_function("udp_packet", |b| {
        b.iter(|| {
            let packet = Packet::new(
                black_box(PacketType::Udp),
                black_box(Bytes::copy_from_slice(b"UDP data")),
            );
            black_box(packet)
        })
    });

    group.finish();
}

/// 带序列号的数据包创建性能测试
fn bench_packet_with_sequence(c: &mut Criterion) {
    c.bench_function("packet_with_sequence", |b| {
        b.iter(|| {
            let packet = Packet::with_sequence(
                black_box(PacketType::Tcp),
                black_box(Bytes::copy_from_slice(b"test data")),
                black_box(12345),
            );
            black_box(packet)
        })
    });
}

/// 数据包构建器性能测试
fn bench_packet_builder(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_builder");

    group.bench_function("simple_build", |b| {
        b.iter(|| {
            let mut builder = PacketBuilder::new(black_box(PacketType::Http));
            builder.add_data(black_box(b"GET /"));
            builder.add_data(black_box(b" HTTP/1.1"));
            let packet = builder.build();
            black_box(packet)
        })
    });

    group.bench_function("with_sequence", |b| {
        b.iter(|| {
            let mut builder = PacketBuilder::new(black_box(PacketType::Tcp));
            builder.add_data(black_box(b"data"));
            builder.sequence_number(black_box(12345));
            builder.flags(black_box(0x01));
            let packet = builder.build();
            black_box(packet)
        })
    });

    group.bench_function("large_payload", |b| {
        let large_data = vec![0u8; 1024];
        b.iter(|| {
            let mut builder = PacketBuilder::new(black_box(PacketType::Raw));
            builder.add_data(black_box(&large_data));
            let packet = builder.build();
            black_box(packet)
        })
    });

    group.finish();
}

/// 数据包统计性能测试
fn bench_packet_stats(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_stats");

    group.bench_function("add_packet", |b| {
        let mut stats = PacketStats::new();
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            stats.add_packet(black_box(&packet));
        })
    });

    group.bench_function("packets_of_type", |b| {
        let mut stats = PacketStats::new();
        let packet1 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data1"));
        let packet2 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"data2"));
        stats.add_packet(&packet1);
        stats.add_packet(&packet2);

        b.iter(|| {
            let count = stats.packets_of_type(black_box(&PacketType::Raw));
            black_box(count)
        })
    });

    group.bench_function("bytes_of_type", |b| {
        let mut stats = PacketStats::new();
        let packet1 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data1"));
        let packet2 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"data2"));
        stats.add_packet(&packet1);
        stats.add_packet(&packet2);

        b.iter(|| {
            let bytes = stats.bytes_of_type(black_box(&PacketType::Raw));
            black_box(bytes)
        })
    });

    group.finish();
}

/// 数据包过滤器性能测试
fn bench_packet_filter(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_filter");

    group.bench_function("type_filter", |b| {
        let filter = PacketFilter::new()
            .allow_type(PacketType::Http)
            .min_size(10)
            .max_size(100);
        let packet = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"GET / HTTP/1.1"));

        b.iter(|| {
            let matches = filter.matches(black_box(&packet));
            black_box(matches)
        })
    });

    group.bench_function("size_filter", |b| {
        let filter = PacketFilter::new()
            .min_size(5)
            .max_size(20);
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            let matches = filter.matches(black_box(&packet));
            black_box(matches)
        })
    });

    group.bench_function("sequence_filter", |b| {
        let filter = PacketFilter::new()
            .sequence_range(100, 200);
        let packet = Packet::with_sequence(PacketType::Tcp, Bytes::copy_from_slice(b"data"), 150);

        b.iter(|| {
            let matches = filter.matches(black_box(&packet));
            black_box(matches)
        })
    });

    group.finish();
}

/// 数据包缓冲区性能测试
fn bench_packet_buffer(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_buffer");

    group.bench_function("push_packet", |b| {
        let config = BufferConfig {
            max_size: 1024 * 1024,
            max_packets: 1000,
            timeout: Some(Duration::from_secs(30)),
            auto_flush: false,
            flush_interval: Duration::from_secs(1),
        };
        let mut buffer = PacketBuffer::new(config);
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            let _ = buffer.push(black_box(packet.clone()));
        })
    });

    group.bench_function("pop_packet", |b| {
        let config = BufferConfig {
            max_size: 1024 * 1024,
            max_packets: 1000,
            timeout: Some(Duration::from_secs(30)),
            auto_flush: false,
            flush_interval: Duration::from_secs(1),
        };
        let mut buffer = PacketBuffer::new(config);
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
        buffer.push(packet).unwrap();

        b.iter(|| {
            let _packet = buffer.pop();
        })
    });

    group.bench_function("buffer_stats", |b| {
        let config = BufferConfig {
            max_size: 1024 * 1024,
            max_packets: 1000,
            timeout: Some(Duration::from_secs(30)),
            auto_flush: false,
            flush_interval: Duration::from_secs(1),
        };
        let mut buffer = PacketBuffer::new(config);
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
        buffer.push(packet).unwrap();

        b.iter(|| {
            let stats = buffer.stats();
            black_box(stats)
        })
    });

    group.finish();
}

/// 数据包序列化性能测试
fn bench_packet_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_serialization");

    group.bench_function("serialize", |b| {
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            let serialized = serde_json::to_string(black_box(&packet)).unwrap();
            black_box(serialized)
        })
    });

    group.bench_function("deserialize", |b| {
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
        let serialized = serde_json::to_string(&packet).unwrap();

        b.iter(|| {
            let deserialized: Packet = serde_json::from_str(black_box(&serialized)).unwrap();
            black_box(deserialized)
        })
    });

    group.bench_function("round_trip", |b| {
        let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

        b.iter(|| {
            let serialized = serde_json::to_string(black_box(&packet)).unwrap();
            let deserialized: Packet = serde_json::from_str(&serialized).unwrap();
            black_box(deserialized)
        })
    });

    group.finish();
}

/// 大数据包性能测试
fn bench_large_packet_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("large_packet_performance");

    let sizes = vec![1024, 4096, 16384, 65536, 262144]; // 1KB, 4KB, 16KB, 64KB, 256KB

    for size in sizes {
        group.bench_function(&format!("create_{}KB", size / 1024), |b| {
            let data = vec![0u8; size];
            b.iter(|| {
                let packet = Packet::new(
                    black_box(PacketType::Raw),
                    black_box(Bytes::from(data.clone())),
                );
                black_box(packet)
            })
        });

        group.bench_function(&format!("clone_{}KB", size / 1024), |b| {
            let data = vec![0u8; size];
            let packet = Packet::new(PacketType::Raw, Bytes::from(data));
            b.iter(|| {
                let cloned = black_box(&packet).clone();
                black_box(cloned)
            })
        });

        group.bench_function(&format!("serialize_{}KB", size / 1024), |b| {
            let data = vec![0u8; size];
            let packet = Packet::new(PacketType::Raw, Bytes::from(data));
            b.iter(|| {
                let serialized = serde_json::to_string(black_box(&packet)).unwrap();
                black_box(serialized)
            })
        });
    }

    group.finish();
}

/// 并发数据包处理性能测试
fn bench_concurrent_packet_processing(c: &mut Criterion) {
    use std::sync::Arc;
    use std::thread;

    let mut group = c.benchmark_group("concurrent_packet_processing");

    group.bench_function("multi_thread_stats", |b| {
        b.iter(|| {
            let stats = Arc::new(std::sync::Mutex::new(PacketStats::new()));
            let mut handles = Vec::new();

            for thread_id in 0..4 {
                let stats_clone = Arc::clone(&stats);
                let handle = thread::spawn(move || {
                    let mut local_stats = PacketStats::new();
                    for i in 0..100 {
                        let packet = Packet::new(
                            PacketType::Raw,
                            Bytes::copy_from_slice(format!("thread {} data {}", thread_id, i).as_bytes()),
                        );
                        local_stats.add_packet(&packet);
                    }

                    let mut global_stats = stats_clone.lock().unwrap();
                    global_stats.total_packets += local_stats.total_packets;
                    global_stats.total_bytes += local_stats.total_bytes;
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }

            let final_stats = stats.lock().unwrap();
            black_box(final_stats.total_packets)
        })
    });

    group.bench_function("multi_thread_buffer", |b| {
        b.iter(|| {
            let config = BufferConfig {
                max_size: 1024 * 1024,
                max_packets: 1000,
                timeout: Some(Duration::from_secs(30)),
                auto_flush: false,
                flush_interval: Duration::from_secs(1),
            };
            let buffer = Arc::new(std::sync::Mutex::new(PacketBuffer::new(config)));
            let mut handles = Vec::new();

            for thread_id in 0..4 {
                let buffer_clone = Arc::clone(&buffer);
                let handle = thread::spawn(move || {
                    for i in 0..100 {
                        let packet = Packet::new(
                            PacketType::Raw,
                            Bytes::copy_from_slice(format!("thread {} data {}", thread_id, i).as_bytes()),
                        );
                        let _ = buffer_clone.lock().unwrap().push(packet);
                    }
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }

            let final_buffer = buffer.lock().unwrap();
            black_box(final_buffer.len())
        })
    });

    group.finish();
}

/// 数据包类型比较性能测试
#[allow(unused)]
fn bench_packet_type_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("packet_type_comparison");

    group.bench_function("equality", |b| {
        let types = vec![
            PacketType::Raw,
            PacketType::Http,
            PacketType::WebSocket,
            PacketType::Tcp,
            PacketType::Udp,
            PacketType::Custom("test".to_string()),
        ];

        b.iter(|| {
            for (i, type1) in types.iter().enumerate() {
                for (j, type2) in types.iter().enumerate() {
                    let equal = black_box(type1) == black_box(type2);
                    black_box(equal);
                }
            }
        })
    });

    group.bench_function("hash", |b| {
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert(PacketType::Raw, "raw");
        map.insert(PacketType::Http, "http");
        map.insert(PacketType::WebSocket, "websocket");
        map.insert(PacketType::Tcp, "tcp");
        map.insert(PacketType::Udp, "udp");
        map.insert(PacketType::Custom("test".to_string()), "custom");

        b.iter(|| {
            for packet_type in [
                PacketType::Raw,
                PacketType::Http,
                PacketType::WebSocket,
                PacketType::Tcp,
                PacketType::Udp,
                PacketType::Custom("test".to_string()),
            ] {
                let value = map.get(black_box(&packet_type));
                black_box(value);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_packet_creation,
    bench_packet_with_sequence,
    bench_packet_builder,
    bench_packet_stats,
    bench_packet_filter,
    bench_packet_buffer,
    bench_packet_serialization,
    bench_large_packet_performance,
    bench_concurrent_packet_processing,
    bench_packet_type_comparison
);

criterion_main!(benches);
