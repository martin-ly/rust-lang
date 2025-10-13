//! 协议测试模块
//!
//! 本模块包含了 c10_networks 库的协议测试，
//! 确保各种网络协议的正确实现和互操作性。

use bytes::Bytes;
use c10_networks::{
    packet::{Packet, PacketType},
    protocol::{
        http::{HttpMethod, HttpStatusCode, HttpVersion},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest, WebSocketOpcode},
        tcp::{TcpConnection, TcpConnectionConfig, TcpState},
    },
    socket::{TcpConfig, UdpConfig, utils},
};
use std::time::Duration;

/// 测试HTTP协议实现
#[test]
fn test_http_protocol_implementation() {
    // 测试HTTP请求创建
    let mut request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/api/users",
        HttpVersion::Http1_1,
    );
    
    request.add_header("User-Agent", "c10_networks-test");
    request.add_header("Accept", "application/json");
    request.add_header("Authorization", "Bearer token123");
    request.set_body(b"{\"query\": \"test\"}".as_slice());
    
    // 验证请求属性
    assert_eq!(request.method, HttpMethod::GET);
    assert_eq!(request.uri, "/api/users");
    assert_eq!(request.version, HttpVersion::Http1_1);
    assert!(request.headers.len() >= 3);
    assert_eq!(request.body.len(), 20);
    
    // 测试HTTP响应创建
    let mut response = c10_networks::protocol::http::HttpResponse::new(
        HttpVersion::Http1_1,
        HttpStatusCode::ok(),
    );
    
    response.add_header("Content-Type", "application/json");
    response.add_header("Server", "c10_networks");
    response.add_header("Cache-Control", "no-cache");
    response.set_body(r#"{"status": "success", "data": []}"#);
    
    // 验证响应属性
    assert_eq!(response.status.code, 200);
    assert_eq!(response.version, HttpVersion::Http1_1);
    assert!(response.headers.len() >= 3);
    assert!(response.body.len() >= 30);
}

/// 测试HTTP方法枚举
#[test]
fn test_http_methods() {
    let methods = vec![
        HttpMethod::GET,
        HttpMethod::POST,
        HttpMethod::PUT,
        HttpMethod::DELETE,
        HttpMethod::HEAD,
        HttpMethod::OPTIONS,
        HttpMethod::PATCH,
    ];
    
    for method in methods {
        let request = c10_networks::protocol::http::HttpRequest::new(
            method.clone(),
            "/test",
            HttpVersion::Http1_1,
        );
        
        // 验证方法设置
        assert_eq!(request.method, method);
        assert_eq!(request.uri, "/test");
        assert_eq!(request.version, HttpVersion::Http1_1);
    }
}

/// 测试HTTP状态码
#[test]
fn test_http_status_codes() {
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
        let response = c10_networks::protocol::http::HttpResponse::new(
            HttpVersion::Http1_1,
            status,
        );
        
        // 验证状态码设置
        assert!(response.status.code >= 100 && response.status.code < 600);
        assert_eq!(response.version, HttpVersion::Http1_1);
    }
}

/// 测试HTTP版本
#[test]
fn test_http_versions() {
    let versions = vec![
        HttpVersion::Http1_0,
        HttpVersion::Http1_1,
        HttpVersion::Http2_0,
    ];
    
    for version in versions {
        let request = c10_networks::protocol::http::HttpRequest::new(
            HttpMethod::GET,
            "/test",
            version.clone(),
        );
        
        // 验证版本设置
        assert_eq!(request.version, version);
    }
}

/// 测试WebSocket协议实现
#[test]
fn test_websocket_protocol_implementation() {
    // 测试WebSocket帧创建
    let text_frame = WebSocketFrame::text("Hello, WebSocket!");
    assert_eq!(text_frame.opcode, WebSocketOpcode::Text);
    assert_eq!(text_frame.payload, Bytes::from("Hello, WebSocket!"));
    assert!(text_frame.fin);
    assert!(!text_frame.mask);
    
    let binary_frame = WebSocketFrame::binary(&[1, 2, 3, 4, 5]);
    assert_eq!(binary_frame.opcode, WebSocketOpcode::Binary);
    assert_eq!(binary_frame.payload, Bytes::from(&[1, 2, 3, 4, 5][..]));
    assert!(binary_frame.fin);
    
    let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    assert_eq!(close_frame.opcode, WebSocketOpcode::Close);
    assert!(close_frame.fin);
    
    let ping_frame = WebSocketFrame::ping(Some(&[1, 2, 3, 4]));
    assert_eq!(ping_frame.opcode, WebSocketOpcode::Ping);
    assert_eq!(ping_frame.payload, Bytes::from(&[1, 2, 3, 4][..]));
    assert!(ping_frame.fin);
    
    let pong_frame = WebSocketFrame::pong(Some(&[5, 6, 7, 8]));
    assert_eq!(pong_frame.opcode, WebSocketOpcode::Pong);
    assert_eq!(pong_frame.payload, Bytes::from(&[5, 6, 7, 8][..]));
    assert!(pong_frame.fin);
}

/// 测试WebSocket握手请求
#[test]
fn test_websocket_handshake_request() {
    let mut request = WebSocketHandshakeRequest::new("/chat");
    request.set_host("example.com");
    request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
    request.set_websocket_version("13");
    request.set_upgrade();
    request.add_header("Origin", "https://example.com");
    
    let request_str = request.encode();
    
    // 验证握手请求格式
    assert!(request_str.contains("GET /chat HTTP/1.1"));
    assert!(request_str.contains("Host: example.com"));
    assert!(request_str.contains("Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ=="));
    assert!(request_str.contains("Sec-WebSocket-Version: 13"));
    assert!(request_str.contains("Upgrade: websocket"));
    assert!(request_str.contains("Origin: https://example.com"));
}

/// 测试WebSocket操作码
#[test]
fn test_websocket_opcodes() {
    let opcodes = vec![
        WebSocketOpcode::Continuation,
        WebSocketOpcode::Text,
        WebSocketOpcode::Binary,
        WebSocketOpcode::Close,
        WebSocketOpcode::Ping,
        WebSocketOpcode::Pong,
    ];
    
    for opcode in opcodes {
        let frame = WebSocketFrame {
            fin: true,
            opcode: opcode.clone(),
            mask: false,
            payload_length: 4,
            masking_key: None,
            payload: Bytes::copy_from_slice(b"test"),
        };
        
        // 验证操作码设置
        assert_eq!(frame.opcode, opcode);
        assert!(frame.fin);
        assert!(!frame.mask);
        assert_eq!(frame.payload, Bytes::copy_from_slice(b"test"));
    }
}

/// 测试TCP协议实现
#[test]
fn test_tcp_protocol_implementation() {
    // 测试TCP连接配置
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
    
    // 验证配置属性
    assert_eq!(config.local_addr.port(), 0);
    assert_eq!(config.remote_addr.port(), 8080);
    assert_eq!(config.timeout, Duration::from_secs(30));
    assert!(config.keep_alive);
    assert!(config.tcp_nodelay);
    assert_eq!(config.send_buffer_size, 8192);
    assert_eq!(config.recv_buffer_size, 8192);
    assert_eq!(config.max_segment_size, 1460);
    assert_eq!(config.window_size, 65535);
    
    // 测试TCP连接创建
    let connection = TcpConnection::new(1, config);
    assert_eq!(connection.id, 1);
    assert_eq!(*connection.state(), TcpState::Closed);
    assert!(!connection.state().can_send_data());
    assert!(!connection.state().can_receive_data());
}

/// 测试TCP状态机
#[test]
fn test_tcp_state_machine() {
    let config = TcpConnectionConfig::default();
    let connection = TcpConnection::new(1, config);
    
    // 测试初始状态
    assert_eq!(*connection.state(), TcpState::Closed);
    assert!(!connection.state().can_send_data());
    assert!(!connection.state().can_receive_data());
    
    // 测试状态转换（这里可以添加更多状态转换测试）
    // 注意：实际的状态转换需要网络操作，这里主要测试状态查询
}

/// 测试TCP拥塞控制
#[test]
fn test_tcp_congestion_control() {
    let config = TcpConnectionConfig::default();
    let mut connection = TcpConnection::new(1, config);
    
    // 测试拥塞窗口更新
    connection.update_congestion_window();
    assert_eq!(connection.congestion_window, 2);
    
    connection.update_congestion_window();
    assert_eq!(connection.congestion_window, 4);
    
    // 测试拥塞处理
    connection.handle_congestion();
    assert_eq!(connection.congestion_window, 1);
    assert_eq!(connection.slow_start_threshold, 2);
}

/// 测试套接字配置
#[test]
fn test_socket_configurations() {
    // 测试TCP套接字配置
    let tcp_config = TcpConfig {
        address: utils::localhost(8080),
        timeout: Some(Duration::from_secs(30)),
        buffer_size: 8192,
        keep_alive: true,
        tcp_nodelay: true,
    };
    
    assert_eq!(tcp_config.address.port(), 8080);
    assert_eq!(tcp_config.timeout, Some(Duration::from_secs(30)));
    assert_eq!(tcp_config.buffer_size, 8192);
    assert!(tcp_config.keep_alive);
    assert!(tcp_config.tcp_nodelay);
    
    // 测试UDP套接字配置
    let udp_config = UdpConfig {
        address: utils::localhost(8081),
        timeout: Some(Duration::from_secs(10)),
        buffer_size: 4096,
        broadcast: false,
        multicast_loop_v4: false,
    };
    
    assert_eq!(udp_config.address.port(), 8081);
    assert_eq!(udp_config.timeout, Some(Duration::from_secs(10)));
    assert_eq!(udp_config.buffer_size, 4096);
    assert!(!udp_config.broadcast);
    assert!(!udp_config.multicast_loop_v4);
}

/// 测试协议数据包
#[test]
fn test_protocol_packets() {
    // 测试HTTP数据包
    let http_packet = Packet::new(
        PacketType::Http,
        Bytes::copy_from_slice(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n"),
    );
    assert_eq!(http_packet.packet_type(), &PacketType::Http);
    assert!(http_packet.payload_length() > 0);
    
    // 测试WebSocket数据包
    let websocket_packet = Packet::new(
        PacketType::WebSocket,
        Bytes::copy_from_slice(b"Hello, WebSocket!"),
    );
    assert_eq!(websocket_packet.packet_type(), &PacketType::WebSocket);
    assert_eq!(websocket_packet.payload_length(), 17);
    
    // 测试TCP数据包
    let tcp_packet = Packet::new(
        PacketType::Tcp,
        Bytes::copy_from_slice(b"TCP data"),
    );
    assert_eq!(tcp_packet.packet_type(), &PacketType::Tcp);
    assert_eq!(tcp_packet.payload_length(), 8);
    
    // 测试UDP数据包
    let udp_packet = Packet::new(
        PacketType::Udp,
        Bytes::copy_from_slice(b"UDP data"),
    );
    assert_eq!(udp_packet.packet_type(), &PacketType::Udp);
    assert_eq!(udp_packet.payload_length(), 8);
}

/// 测试协议错误处理
#[test]
fn test_protocol_error_handling() {
    // 测试HTTP协议错误
    let http_error = c10_networks::error::ProtocolError::Http {
        status: 404,
        message: "Not Found".to_string(),
    };
    assert_eq!(format!("{}", http_error), "HTTP error: 404 - Not Found");
    
    // 测试WebSocket协议错误
    let websocket_error = c10_networks::error::ProtocolError::WebSocket(
        "Connection failed".to_string(),
    );
    assert_eq!(format!("{}", websocket_error), "WebSocket error: Connection failed");
    
    // 测试TCP协议错误
    let tcp_error = c10_networks::error::ProtocolError::Tcp(
        "Connection reset".to_string(),
    );
    assert_eq!(format!("{}", tcp_error), "TCP error: Connection reset");
    
    // 测试UDP协议错误
    let udp_error = c10_networks::error::ProtocolError::Udp(
        "Port unreachable".to_string(),
    );
    assert_eq!(format!("{}", udp_error), "UDP error: Port unreachable");
    
    // 测试DNS协议错误
    let dns_error = c10_networks::error::ProtocolError::Dns(
        "Name resolution failed".to_string(),
    );
    assert_eq!(format!("{}", dns_error), "DNS error: Name resolution failed");
}

/// 测试协议兼容性
#[test]
fn test_protocol_compatibility() {
    // 测试HTTP/1.1兼容性
    let http11_request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/test",
        HttpVersion::Http1_1,
    );
    assert_eq!(http11_request.version, HttpVersion::Http1_1);
    
    // 测试HTTP/2.0兼容性
    let http20_request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/test",
        HttpVersion::Http2_0,
    );
    assert_eq!(http20_request.version, HttpVersion::Http2_0);
    
    // 测试WebSocket RFC 6455兼容性
    let mut ws_request = WebSocketHandshakeRequest::new("/test");
    ws_request.set_websocket_version("13"); // RFC 6455 version
    let request_str = ws_request.encode();
    assert!(request_str.contains("Sec-WebSocket-Version: 13"));
}

/// 测试协议性能
#[test]
fn test_protocol_performance() {
    const ITERATIONS: usize = 1000;
    
    // 测试HTTP请求创建性能
    let start = std::time::Instant::now();
    for i in 0..ITERATIONS {
        let _request = c10_networks::protocol::http::HttpRequest::new(
            HttpMethod::GET,
            &format!("/api/test/{}", i),
            HttpVersion::Http1_1,
        );
    }
    let http_time = start.elapsed();
    
    // 测试WebSocket帧创建性能
    let start = std::time::Instant::now();
    for i in 0..ITERATIONS {
        let _frame = WebSocketFrame::text(&format!("message {}", i));
    }
    let websocket_time = start.elapsed();
    
    // 测试TCP连接创建性能
    let start = std::time::Instant::now();
    for i in 0..ITERATIONS {
        let _connection = TcpConnection::new(i as u64, TcpConnectionConfig::default());
    }
    let tcp_time = start.elapsed();
    
    println!("协议性能测试结果:");
    println!("  HTTP请求创建: {:?}", http_time);
    println!("  WebSocket帧创建: {:?}", websocket_time);
    println!("  TCP连接创建: {:?}", tcp_time);
    
    // 验证性能在合理范围内
    assert!(http_time < Duration::from_millis(100));
    assert!(websocket_time < Duration::from_millis(100));
    assert!(tcp_time < Duration::from_millis(100));
}

/// 测试协议边界条件
#[test]
fn test_protocol_boundary_conditions() {
    // 测试空HTTP请求
    let empty_request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "",
        HttpVersion::Http1_1,
    );
    assert_eq!(empty_request.uri, "");
    
    // 测试空WebSocket帧
    let empty_frame = WebSocketFrame::text("");
    assert_eq!(empty_frame.payload, Bytes::new());
    assert_eq!(empty_frame.payload.len(), 0);
    
    // 测试最大长度HTTP请求
    let long_uri = "/".repeat(1000);
    let long_request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        &long_uri,
        HttpVersion::Http1_1,
    );
    assert_eq!(long_request.uri, long_uri);
    
    // 测试最大长度WebSocket帧
    let long_message = "a".repeat(1000);
    let long_frame = WebSocketFrame::text(&long_message);
    assert_eq!(long_frame.payload, Bytes::from(long_message));
}

/// 协议测试套件
#[test]
fn test_protocol_test_suite() {
    println!("=== C10 Networks 协议测试套件 ===");
    
    // 运行所有协议测试
    test_http_protocol_implementation();
    test_http_methods();
    test_http_status_codes();
    test_http_versions();
    test_websocket_protocol_implementation();
    test_websocket_handshake_request();
    test_websocket_opcodes();
    test_tcp_protocol_implementation();
    test_tcp_state_machine();
    test_tcp_congestion_control();
    test_socket_configurations();
    test_protocol_packets();
    test_protocol_error_handling();
    test_protocol_compatibility();
    test_protocol_performance();
    test_protocol_boundary_conditions();
    
    println!("=== 协议测试套件完成 ===");
}
