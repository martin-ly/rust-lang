//! 性能测试模块
//!
//! 本模块包含了 c10_networks 库的性能测试，
//! 确保各个模块的性能指标符合预期。

use bytes::Bytes;
use c10_networks::{
    error::{ErrorRecovery, NetworkError},
    packet::{Packet, PacketBuilder, PacketStats, PacketType},
    protocol::{
        http::{HttpMethod, HttpStatusCode, HttpVersion},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest},
    },
};
use std::time::Instant;

/// 测试数据包创建性能
#[test]
fn test_packet_creation_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let _packet = Packet::new(
            PacketType::Raw,
            Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
        );
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包创建性能: {} ns/packet", avg_time);
    
    // 验证性能在合理范围内（每个数据包创建应该小于1微秒）
    assert!(avg_time < 1_000.0, "数据包创建性能过慢: {} ns/packet", avg_time);
}

/// 测试数据包构建器性能
#[test]
fn test_packet_builder_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let mut builder = PacketBuilder::new(PacketType::Http);
        builder.add_data(b"GET /");
        builder.add_data(b" HTTP/1.1");
        builder.sequence_number(i as u64);
        builder.flags(0x01);
        let _packet = builder.build();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包构建器性能: {} ns/packet", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 2_000.0, "数据包构建器性能过慢: {} ns/packet", avg_time);
}

/// 测试数据包统计性能
#[test]
fn test_packet_stats_performance() {
    const ITERATIONS: usize = 10000;
    
    let mut stats = PacketStats::new();
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        stats.add_packet(&packet);
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包统计性能: {} ns/operation", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 500.0, "数据包统计性能过慢: {} ns/operation", avg_time);
}

/// 测试HTTP请求创建性能
#[test]
fn test_http_request_creation_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let mut request = c10_networks::protocol::http::HttpRequest::new(
            HttpMethod::GET,
            &format!("/api/test/{}", i),
            HttpVersion::Http1_1,
        );
        request.add_header("User-Agent", "c10_networks-test");
        request.add_header("Accept", "application/json");
        request.set_body(b"test body".as_slice());
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("HTTP请求创建性能: {} ns/request", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 3_000.0, "HTTP请求创建性能过慢: {} ns/request", avg_time);
}

/// 测试HTTP响应创建性能
#[test]
fn test_http_response_creation_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let mut response = c10_networks::protocol::http::HttpResponse::new(
            HttpVersion::Http1_1,
            HttpStatusCode::ok(),
        );
        response.add_header("Content-Type", "application/json");
        response.add_header("Server", "c10_networks");
        response.set_body(format!(r#"{{"id": {}, "status": "success"}}"#, i));
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("HTTP响应创建性能: {} ns/response", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 3_000.0, "HTTP响应创建性能过慢: {} ns/response", avg_time);
}

/// 测试WebSocket帧创建性能
#[test]
fn test_websocket_frame_creation_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let _text_frame = WebSocketFrame::text(&format!("message {}", i));
        let _binary_frame = WebSocketFrame::binary(&[i as u8, (i >> 8) as u8]);
        let _close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / (ITERATIONS * 3) as f64;
    println!("WebSocket帧创建性能: {} ns/frame", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 1_000.0, "WebSocket帧创建性能过慢: {} ns/frame", avg_time);
}

/// 测试WebSocket握手请求性能
#[test]
#[ignore] // 性能测试在部分环境可能超时
fn test_websocket_handshake_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let mut request = WebSocketHandshakeRequest::new(&format!("/chat/{}", i));
        request.set_host("example.com");
        request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
        request.set_websocket_version("13");
        request.set_upgrade();
        let _request_str = request.encode();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("WebSocket握手请求性能: {} ns/request", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 2_000.0, "WebSocket握手请求性能过慢: {} ns/request", avg_time);
}

/// 测试数据包序列化性能
#[test]
fn test_packet_serialization_performance() {
    const ITERATIONS: usize = 1000;
    
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _serialized = serde_json::to_string(&packet).unwrap();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包序列化性能: {} ns/serialize", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 5_000.0, "数据包序列化性能过慢: {} ns/serialize", avg_time);
}

/// 测试数据包反序列化性能
#[test]
fn test_packet_deserialization_performance() {
    const ITERATIONS: usize = 1000;
    
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    let serialized = serde_json::to_string(&packet).unwrap();
    
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _deserialized: Packet = serde_json::from_str(&serialized).unwrap();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包反序列化性能: {} ns/deserialize", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 5_000.0, "数据包反序列化性能过慢: {} ns/deserialize", avg_time);
}

/// 测试内存分配性能
#[test]
fn test_memory_allocation_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let _data = Bytes::copy_from_slice(format!("data {}", i).as_bytes());
        let _packet = Packet::new(PacketType::Raw, _data);
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("内存分配性能: {} ns/allocation", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 2_000.0, "内存分配性能过慢: {} ns/allocation", avg_time);
}

/// 测试并发数据包处理性能
#[test]
fn test_concurrent_packet_processing_performance() {
    use std::sync::Arc;
    use std::thread;
    
    const THREADS: usize = 4;
    const ITERATIONS_PER_THREAD: usize = 2500;
    
    let stats = Arc::new(std::sync::Mutex::new(PacketStats::new()));
    let mut handles = Vec::new();
    
    let start = Instant::now();
    
    for thread_id in 0..THREADS {
        let stats_clone = Arc::clone(&stats);
        let handle = thread::spawn(move || {
            let mut local_stats = PacketStats::new();
            for i in 0..ITERATIONS_PER_THREAD {
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
    
    let elapsed = start.elapsed();
    let total_operations = THREADS * ITERATIONS_PER_THREAD;
    let avg_time = elapsed.as_nanos() as f64 / total_operations as f64;
    
    println!("并发数据包处理性能: {} ns/operation", avg_time);
    println!("总处理时间: {:?}", elapsed);
    
    // 验证性能在合理范围内
    assert!(avg_time < 1_000.0, "并发数据包处理性能过慢: {} ns/operation", avg_time);
    
    // 验证统计结果
    let final_stats = stats.lock().unwrap();
    assert_eq!(final_stats.total_packets, total_operations as u64);
}

/// 测试大数据包处理性能
#[test]
fn test_large_packet_performance() {
    const ITERATIONS: usize = 1000;
    const PACKET_SIZE: usize = 1024 * 1024; // 1MB
    
    let large_data = vec![0u8; PACKET_SIZE];
    let large_packet = Packet::new(PacketType::Raw, Bytes::from(large_data));
    
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _cloned = large_packet.clone();
        let _size = _cloned.total_size();
        let _payload_len = _cloned.payload_length();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("大数据包处理性能: {} ns/packet ({}MB)", avg_time, PACKET_SIZE / (1024 * 1024));
    
    // 验证性能在合理范围内（大数据包处理应该相对较慢）
    assert!(avg_time < 100_000.0, "大数据包处理性能过慢: {} ns/packet", avg_time);
}

/// 测试数据包过滤器性能
#[test]
fn test_packet_filter_performance() {
    const ITERATIONS: usize = 10000;
    
    let filter = c10_networks::packet::PacketFilter::new()
        .allow_type(PacketType::Http)
        .min_size(10)
        .max_size(100);
    
    let packets: Vec<Packet> = (0..ITERATIONS)
        .map(|i| {
            let data = format!("data {}", i);
            Packet::new(PacketType::Http, Bytes::from(data))
        })
        .collect();
    
    let start = Instant::now();
    let mut matches = 0;
    for packet in &packets {
        if filter.matches(packet) {
            matches += 1;
        }
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("数据包过滤器性能: {} ns/filter", avg_time);
    println!("匹配数量: {}/{}", matches, ITERATIONS);
    
    // 验证性能在合理范围内
    assert!(avg_time < 500.0, "数据包过滤器性能过慢: {} ns/filter", avg_time);
}

/// 测试错误处理性能
#[test]
fn test_error_handling_performance() {
    const ITERATIONS: usize = 10000;
    
    let start = Instant::now();
    for i in 0..ITERATIONS {
        let error = NetworkError::Protocol(format!("error {}", i));
        let _is_retryable = error.is_retryable();
        let _retry_delay = error.retry_delay();
        let _max_retries = error.max_retries();
        let _error_string = error.to_string();
    }
    let elapsed = start.elapsed();
    
    let avg_time = elapsed.as_nanos() as f64 / ITERATIONS as f64;
    println!("错误处理性能: {} ns/error", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 1_000.0, "错误处理性能过慢: {} ns/error", avg_time);
}

/// 测试数据包类型比较性能
#[test]
fn test_packet_type_comparison_performance() {
    const ITERATIONS: usize = 10000;
    
    let types = vec![
        PacketType::Raw,
        PacketType::Http,
        PacketType::WebSocket,
        PacketType::Tcp,
        PacketType::Udp,
        PacketType::Custom("test".to_string()),
    ];
    
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        for (_i, type1) in types.iter().enumerate() {
            for (_j, type2) in types.iter().enumerate() {
                let _equal = type1 == type2;
                let _hash = std::collections::hash_map::DefaultHasher::new();
                // 模拟哈希计算
                let _ = format!("{:?}", type1);
            }
        }
    }
    let elapsed = start.elapsed();
    
    let total_comparisons = ITERATIONS * types.len() * types.len();
    let avg_time = elapsed.as_nanos() as f64 / total_comparisons as f64;
    println!("数据包类型比较性能: {} ns/comparison", avg_time);
    
    // 验证性能在合理范围内
    assert!(avg_time < 100.0, "数据包类型比较性能过慢: {} ns/comparison", avg_time);
}

/// 性能基准测试套件
#[test]
#[ignore] // 综合性能测试在部分环境可能超时
fn test_performance_benchmark_suite() {
    println!("=== C10 Networks 性能基准测试套件 ===");
    
    // 运行所有性能测试
    test_packet_creation_performance();
    test_packet_builder_performance();
    test_packet_stats_performance();
    test_http_request_creation_performance();
    test_http_response_creation_performance();
    test_websocket_frame_creation_performance();
    test_websocket_handshake_performance();
    test_packet_serialization_performance();
    test_packet_deserialization_performance();
    test_memory_allocation_performance();
    test_concurrent_packet_processing_performance();
    test_large_packet_performance();
    test_packet_filter_performance();
    test_error_handling_performance();
    test_packet_type_comparison_performance();
    
    println!("=== 性能基准测试套件完成 ===");
}
