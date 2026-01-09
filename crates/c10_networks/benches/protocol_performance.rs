//! 协议性能基准测试
//!
//! 这个模块包含了 c10_networks 库各种网络协议的性能基准测试

use c10_networks::{
    protocol::{
        http::{HttpMethod, HttpRequest, HttpStatusCode, HttpVersion},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest, WebSocketOpcode},
        tcp::{TcpConnection, TcpConnectionConfig, TcpState},
    },
    socket::{TcpConfig, UdpConfig, utils},
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::Duration;

/// HTTP 协议性能测试
fn bench_http_protocol(c: &mut Criterion) {
    let mut group = c.benchmark_group("http_protocol");

    group.bench_function("request_creation", |b| {
        b.iter(|| {
            let mut request = HttpRequest::new(
                black_box(HttpMethod::GET),
                black_box("/api/test"),
                black_box(HttpVersion::Http1_1),
            );
            request.add_header("User-Agent", "c10_networks-test");
            request.add_header("Accept", "application/json");
            request.add_header("Authorization", "Bearer token123");
            request.set_body(black_box(b"{\"query\": \"test\"}").as_slice());
            black_box(request)
        })
    });

    group.bench_function("response_creation", |b| {
        b.iter(|| {
            let mut response = c10_networks::protocol::http::HttpResponse::new(
                black_box(HttpVersion::Http1_1),
                black_box(HttpStatusCode::ok()),
            );
            response.add_header("Content-Type", "application/json");
            response.add_header("Server", "c10_networks");
            response.add_header("Cache-Control", "no-cache");
            response.set_body(black_box(r#"{"status": "success", "data": []}"#));
            black_box(response)
        })
    });

    group.bench_function("method_enumeration", |b| {
        let methods = vec![
            HttpMethod::GET,
            HttpMethod::POST,
            HttpMethod::PUT,
            HttpMethod::DELETE,
            HttpMethod::HEAD,
            HttpMethod::OPTIONS,
            HttpMethod::PATCH,
        ];

        b.iter(|| {
            for method in &methods {
                let request = HttpRequest::new(
                    black_box(method.clone()),
                    "/test",
                    HttpVersion::Http1_1,
                );
                black_box(request);
            }
        })
    });

    group.bench_function("status_code_creation", |b| {
        b.iter(|| {
            let status_codes = vec![
                HttpStatusCode::ok(),
                HttpStatusCode::new(201, "Created"),
                HttpStatusCode::new(400, "Bad Request"),
                HttpStatusCode::new(401, "Unauthorized"),
                HttpStatusCode::new(403, "Forbidden"),
                HttpStatusCode::not_found(),
                HttpStatusCode::internal_server_error(),
            ];

            for status in status_codes {
                black_box(status);
            }
        })
    });

    group.finish();
}

/// WebSocket 协议性能测试
fn bench_websocket_protocol(c: &mut Criterion) {
    let mut group = c.benchmark_group("websocket_protocol");

    group.bench_function("frame_creation", |b| {
        b.iter(|| {
            let text_frame = WebSocketFrame::text(black_box("Hello, WebSocket!"));
            let binary_frame = WebSocketFrame::binary(black_box(&[1, 2, 3, 4, 5]));
            let close_frame = WebSocketFrame::close(
                black_box(Some(1000)),
                black_box(Some("Normal closure")),
            );
            let ping_frame = WebSocketFrame::ping(black_box(Some(&[1, 2, 3, 4])));
            let pong_frame = WebSocketFrame::pong(black_box(Some(&[5, 6, 7, 8])));

            black_box((text_frame, binary_frame, close_frame, ping_frame, pong_frame))
        })
    });

    group.bench_function("handshake_request", |b| {
        b.iter(|| {
            let mut request = WebSocketHandshakeRequest::new(black_box("/chat"));
            request.set_host("example.com");
            request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
            request.set_websocket_version("13");
            request.set_upgrade();
            request.add_header("Origin", "https://example.com");
            let request_str = request.encode();
            black_box(request_str)
        })
    });

    group.bench_function("opcode_operations", |b| {
        let opcodes = vec![
            WebSocketOpcode::Continuation,
            WebSocketOpcode::Text,
            WebSocketOpcode::Binary,
            WebSocketOpcode::Close,
            WebSocketOpcode::Ping,
            WebSocketOpcode::Pong,
        ];

        b.iter(|| {
            for opcode in &opcodes {
                let is_control = black_box(opcode).is_control_frame();
                let is_data = black_box(opcode).is_data_frame();
                black_box((is_control, is_data));
            }
        })
    });

    group.bench_function("frame_validation", |b| {
        let frame = WebSocketFrame::text("Hello, World!");

        b.iter(|| {
            let fin = black_box(&frame).fin;
            let opcode = black_box(&frame).opcode.clone();
            let mask = black_box(&frame).mask;
            let payload_length = black_box(&frame).payload_length;
            let payload = black_box(&frame).payload.clone();
            black_box((fin, opcode, mask, payload_length, payload))
        })
    });

    group.finish();
}

/// TCP 协议性能测试
fn bench_tcp_protocol(c: &mut Criterion) {
    let mut group = c.benchmark_group("tcp_protocol");

    group.bench_function("connection_creation", |b| {
        b.iter(|| {
            let config = TcpConnectionConfig {
                local_addr: utils::localhost(0),
                remote_addr: utils::localhost(8080),
                timeout: Duration::from_secs(30),
                keep_alive: true,
                tcp_nodelay: true,
                send_buffer_size: 8192,
                recv_buffer_size: 8192,
                max_segment_size: 1460,
                window_size: 65535,
            };
            let connection = TcpConnection::new(black_box(1), config);
            black_box(connection)
        })
    });

    group.bench_function("state_operations", |b| {
        let config = TcpConnectionConfig::default();
        let connection = TcpConnection::new(1, config);

        b.iter(|| {
            let state = black_box(&connection).state();
            let can_send = state.can_send_data();
            let can_receive = state.can_receive_data();
            black_box((can_send, can_receive))
        })
    });

    group.bench_function("congestion_control", |b| {
        let config = TcpConnectionConfig::default();
        let mut connection = TcpConnection::new(1, config);

        b.iter(|| {
            connection.update_congestion_window();
            let window = connection.congestion_window;
            black_box(window)
        })
    });

    group.bench_function("connection_pool", |b| {
        use c10_networks::protocol::tcp::TcpConnectionPool;

        b.iter(|| {
            let pool = TcpConnectionPool::new(black_box(10), Duration::from_secs(30));
            let config = TcpConnectionConfig::default();
            let connection_id = futures::executor::block_on(
                pool.create_connection(config)
            ).unwrap();
            black_box(connection_id)
        })
    });

    group.finish();
}

/// 套接字配置性能测试
fn bench_socket_configuration(c: &mut Criterion) {
    let mut group = c.benchmark_group("socket_configuration");

    group.bench_function("tcp_config", |b| {
        b.iter(|| {
            let config = TcpConfig {
                address: utils::localhost(black_box(8080)),
                timeout: Some(Duration::from_secs(black_box(30))),
                buffer_size: black_box(8192),
                keep_alive: black_box(true),
                tcp_nodelay: black_box(true),
            };
            black_box(config)
        })
    });

    group.bench_function("udp_config", |b| {
        b.iter(|| {
            let config = UdpConfig {
                address: utils::localhost(black_box(8081)),
                timeout: Some(Duration::from_secs(black_box(10))),
                buffer_size: black_box(4096),
                broadcast: black_box(false),
                multicast_loop_v4: black_box(false),
            };
            black_box(config)
        })
    });

    group.bench_function("socket_creation", |b| {
        b.iter(|| {
            let tcp_config = TcpConfig::default();
            let tcp_socket = c10_networks::socket::TcpSocket::new(tcp_config);
            black_box(tcp_socket)
        })
    });

    group.finish();
}

/// 协议解析性能测试
fn bench_protocol_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("protocol_parsing");

    group.bench_function("http_header_parsing", |b| {
        let header_data = b"Content-Type: application/json\r\nUser-Agent: c10_networks\r\nAuthorization: Bearer token123\r\n";

        b.iter(|| {
            let headers: Vec<&[u8]> = black_box(header_data).split(|&x| x == b'\n').collect();
            let mut parsed_headers = Vec::new();

            for header in headers {
                if let Some(colon_pos) = header.iter().position(|&x| x == b':') {
                    let name = &header[..colon_pos];
                    let value = &header[colon_pos + 1..];
                    parsed_headers.push((name, value));
                }
            }

            black_box(parsed_headers)
        })
    });

    group.bench_function("websocket_frame_parsing", |b| {
        let frame_data = b"\x81\x0DHello, World!";

        b.iter(|| {
            let data = black_box(frame_data);
            let fin = (data[0] & 0x80) != 0;
            let opcode = data[0] & 0x0F;
            let mask = (data[1] & 0x80) != 0;
            let payload_length = data[1] & 0x7F;
            let payload = &data[2..];

            black_box((fin, opcode, mask, payload_length, payload))
        })
    });

    group.bench_function("tcp_header_parsing", |b| {
        let tcp_header = b"\x00\x50\x00\x00\x00\x00\x00\x00\x50\x02\x20\x00\x00\x00\x00\x00";

        b.iter(|| {
            let data = black_box(tcp_header);
            let src_port = u16::from_be_bytes([data[0], data[1]]);
            let dst_port = u16::from_be_bytes([data[2], data[3]]);
            let seq_num = u32::from_be_bytes([data[4], data[5], data[6], data[7]]);
            let ack_num = u32::from_be_bytes([data[8], data[9], data[10], data[11]]);
            let flags = data[13];

            black_box((src_port, dst_port, seq_num, ack_num, flags))
        })
    });

    group.finish();
}

/// 协议序列化性能测试
fn bench_protocol_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("protocol_serialization");

    group.bench_function("http_request_serialization", |b| {
        let mut request = HttpRequest::new(
            HttpMethod::GET,
            "/api/test",
            HttpVersion::Http1_1,
        );
        request.add_header("User-Agent", "c10_networks");
        request.add_header("Accept", "application/json");
        request.set_body(b"{\"query\": \"test\"}".as_slice());

        b.iter(|| {
            let serialized = serde_json::to_string(black_box(&request)).unwrap();
            black_box(serialized)
        })
    });

    group.bench_function("websocket_frame_serialization", |b| {
        let frame = WebSocketFrame::text("Hello, WebSocket!");

        b.iter(|| {
            let serialized = serde_json::to_string(black_box(&frame)).unwrap();
            black_box(serialized)
        })
    });

    group.bench_function("tcp_connection_debug", |b| {
        let config = TcpConnectionConfig::default();
        let connection = TcpConnection::new(1, config);

        b.iter(|| {
            let debug_str = format!("{:?}", black_box(&connection));
            black_box(debug_str)
        })
    });

    group.finish();
}

/// 协议兼容性性能测试
fn bench_protocol_compatibility(c: &mut Criterion) {
    let mut group = c.benchmark_group("protocol_compatibility");

    group.bench_function("http_version_compatibility", |b| {
        let versions = vec![
            HttpVersion::Http1_0,
            HttpVersion::Http1_1,
            HttpVersion::Http2_0,
        ];

        b.iter(|| {
            for version in &versions {
                let request = HttpRequest::new(
                    HttpMethod::GET,
                    "/test",
                    black_box(version.clone()),
                );
                black_box(request);
            }
        })
    });

    group.bench_function("websocket_version_compatibility", |b| {
        b.iter(|| {
            let mut request = WebSocketHandshakeRequest::new("/test");
            request.set_websocket_version(black_box("13")); // RFC 6455
            let request_str = request.encode();
            black_box(request_str)
        })
    });

    group.bench_function("tcp_state_compatibility", |b| {
        let states = vec![
            TcpState::Closed,
            TcpState::Listen,
            TcpState::SynSent,
            TcpState::SynReceived,
            TcpState::Established,
            TcpState::FinWait1,
            TcpState::FinWait2,
            TcpState::CloseWait,
            TcpState::Closing,
            TcpState::LastAck,
            TcpState::TimeWait,
        ];

        b.iter(|| {
            for state in &states {
                let can_send = black_box(state).can_send_data();
                let can_receive = black_box(state).can_receive_data();
                black_box((can_send, can_receive));
            }
        })
    });

    group.finish();
}

/// 协议错误处理性能测试
fn bench_protocol_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("protocol_error_handling");

    group.bench_function("http_error_creation", |b| {
        b.iter(|| {
            let error = c10_networks::error::ProtocolError::Http {
                status: black_box(404),
                message: black_box("Not Found".to_string()),
            };
            black_box(error)
        })
    });

    group.bench_function("websocket_error_creation", |b| {
        b.iter(|| {
            let error = c10_networks::error::ProtocolError::WebSocket(
                black_box("Connection failed".to_string()),
            );
            black_box(error)
        })
    });

    group.bench_function("tcp_error_creation", |b| {
        b.iter(|| {
            let error = c10_networks::error::ProtocolError::Tcp(
                black_box("Connection reset".to_string()),
            );
            black_box(error)
        })
    });

    group.bench_function("error_message_formatting", |b| {
        let errors = vec![
            c10_networks::error::ProtocolError::Http {
                status: 404,
                message: "Not Found".to_string(),
            },
            c10_networks::error::ProtocolError::WebSocket("Connection failed".to_string()),
            c10_networks::error::ProtocolError::Tcp("Connection reset".to_string()),
            c10_networks::error::ProtocolError::Udp("Port unreachable".to_string()),
            c10_networks::error::ProtocolError::Dns("Name resolution failed".to_string()),
        ];

        b.iter(|| {
            for error in &errors {
                let message = format!("{}", black_box(error));
                black_box(message);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_http_protocol,
    bench_websocket_protocol,
    bench_tcp_protocol,
    bench_socket_configuration,
    bench_protocol_parsing,
    bench_protocol_serialization,
    bench_protocol_compatibility,
    bench_protocol_error_handling
);

criterion_main!(benches);
