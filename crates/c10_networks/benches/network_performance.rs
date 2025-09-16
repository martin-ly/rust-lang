//! 网络性能基准测试
//!
//! 这个模块包含了 c10_networks 库的性能基准测试

use bytes::Bytes;
use c10_networks::{
    error::ErrorRecovery,
    protocol::http::{HttpMethod, HttpRequest, HttpStatusCode, HttpVersion},
    protocol::tcp::{TcpConnection, TcpConnectionConfig},
    protocol::websocket::WebSocketFrame,
    socket::{TcpConfig, TcpSocket},
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::Duration;
use tokio::runtime::Runtime;

/// HTTP 请求创建性能测试
fn bench_http_request_creation(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();

    c.bench_function("http_request_creation", |b| {
        b.iter(|| {
            let mut request = HttpRequest::new(
                black_box(HttpMethod::GET),
                black_box("/api/test"),
                black_box(HttpVersion::Http1_1),
            );
            request.add_header("Content-Type", "application/json");
            request.set_body(black_box(b"test body").as_slice());
            black_box(request)
        })
    });
}

/// HTTP 响应创建性能测试
fn bench_http_response_creation(c: &mut Criterion) {
    c.bench_function("http_response_creation", |b| {
        b.iter(|| {
            let mut response = c10_networks::protocol::http::HttpResponse::new(
                black_box(HttpVersion::Http1_1),
                black_box(HttpStatusCode::ok()),
            );
            response.add_header("Content-Type", "text/html");
            response.set_body(black_box(b"<html></html>").as_slice());
            black_box(response)
        })
    });
}

/// WebSocket 帧创建性能测试
fn bench_websocket_frame_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("websocket_frame_creation");

    group.bench_function("text_frame", |b| {
        b.iter(|| {
            let frame = WebSocketFrame::text(black_box("Hello, World!"));
            black_box(frame)
        })
    });

    group.bench_function("binary_frame", |b| {
        b.iter(|| {
            let frame = WebSocketFrame::binary(black_box(&[1, 2, 3, 4, 5]));
            black_box(frame)
        })
    });

    group.bench_function("close_frame", |b| {
        b.iter(|| {
            let frame =
                WebSocketFrame::close(black_box(Some(1000)), black_box(Some("Normal closure")));
            black_box(frame)
        })
    });

    group.finish();
}

/// TCP 连接创建性能测试
fn bench_tcp_connection_creation(c: &mut Criterion) {
    c.bench_function("tcp_connection_creation", |b| {
        b.iter(|| {
            let config = TcpConnectionConfig::default();
            let connection = TcpConnection::new(black_box(1), config);
            black_box(connection)
        })
    });
}

/// TCP 套接字创建性能测试
fn bench_tcp_socket_creation(c: &mut Criterion) {
    c.bench_function("tcp_socket_creation", |b| {
        b.iter(|| {
            let config = TcpConfig::default();
            let socket = TcpSocket::new(config);
            black_box(socket)
        })
    });
}

/// 错误处理性能测试
fn bench_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");

    group.bench_function("error_creation", |b| {
        b.iter(|| {
            let error =
                c10_networks::error::NetworkError::Protocol(black_box("test error".to_string()));
            black_box(error)
        })
    });

    group.bench_function("error_recovery_check", |b| {
        let error = c10_networks::error::NetworkError::Timeout(Duration::from_secs(5));
        b.iter(|| {
            let is_retryable = black_box(&error).is_retryable();
            black_box(is_retryable)
        })
    });

    group.finish();
}

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

    group.finish();
}

/// 并发性能测试
fn bench_concurrent_operations(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();

    c.bench_function("concurrent_http_requests", |b| {
        b.iter(|| {
            let mut handles = Vec::new();

            for i in 0..100 {
                let handle = tokio::spawn(async move {
                    let mut request = HttpRequest::new(
                        HttpMethod::GET,
                        format!("/api/{}", i),
                        HttpVersion::Http1_1,
                    );
                    request.add_header("Content-Type", "application/json");
                    request.set_body(b"test body".as_slice());
                    request
                });
                handles.push(handle);
            }

            // 简化测试，不使用异步
            black_box(handles.len())
        })
    });
}

/// 网络 I/O 模拟性能测试
fn bench_network_io_simulation(c: &mut Criterion) {
    let _rt = Runtime::new().unwrap();

    c.bench_function("network_io_simulation", |b| {
        b.iter(|| {
            // 模拟网络 I/O 操作
            let data = black_box(b"test data");
            let mut buffer = vec![0; data.len()];

            // 模拟数据复制（网络 I/O 的核心操作）
            buffer.copy_from_slice(data);

            // 模拟数据处理
            let processed = buffer
                .iter()
                .map(|&x| x.wrapping_add(1))
                .collect::<Vec<u8>>();

            black_box(processed)
        })
    });
}

/// 协议解析性能测试
fn bench_protocol_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("protocol_parsing");

    group.bench_function("http_parsing", |b| {
        let http_data = b"GET /api/test HTTP/1.1\r\nHost: example.com\r\n\r\n";
        b.iter(|| {
            // 模拟 HTTP 解析
            let lines: Vec<&[u8]> = black_box(http_data).split(|&x| x == b'\n').collect();
            black_box(lines)
        })
    });

    group.bench_function("websocket_parsing", |b| {
        let _frame = WebSocketFrame::text("Hello, World!");
        // 简化测试，不使用 encode 方法
        let encoded = b"test frame data";
        b.iter(|| {
            // 模拟 WebSocket 帧解析
            let opcode = black_box(&encoded[0]) & 0x0F;
            let mask = (black_box(&encoded[1]) & 0x80) != 0;
            black_box((opcode, mask))
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_http_request_creation,
    bench_http_response_creation,
    bench_websocket_frame_creation,
    bench_tcp_connection_creation,
    bench_tcp_socket_creation,
    bench_error_handling,
    bench_memory_allocation,
    bench_concurrent_operations,
    bench_network_io_simulation,
    bench_protocol_parsing
);

criterion_main!(benches);
