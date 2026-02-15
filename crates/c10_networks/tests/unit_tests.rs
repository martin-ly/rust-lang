//! 单元测试模块
//!
//! 本模块包含了 c10_networks 库的单元测试，
//! 确保各个模块的功能正确性。

use bytes::Bytes;
use c10_networks::{
    error::{ErrorRecovery, NetworkError, ErrorStats, ProtocolError, PerformanceError, SecurityError},
    packet::{Packet, PacketBuilder, PacketFilter, PacketStats, PacketType},
    protocol::{
        http::{HttpMethod, HttpStatusCode, HttpVersion},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest, WebSocketOpcode},
    },
    socket::{TcpConfig, UdpConfig, utils},
};
use std::time::Duration;

/// 测试错误处理模块
#[test]
fn test_network_error_types() {
    // 测试不同类型的错误
    let errors = vec![
        NetworkError::Protocol("测试协议错误".to_string()),
        NetworkError::Connection("连接失败".to_string()),
        NetworkError::Timeout(Duration::from_secs(5)),
        NetworkError::Other("其他错误".to_string()),
        NetworkError::Configuration("配置错误".to_string()),
    ];

    for error in errors {
        // 验证错误消息不为空
        assert!(!error.to_string().is_empty());
        
        // 验证错误恢复特性
        let is_retryable = error.is_retryable();
        let retry_delay = error.retry_delay();
        let max_retries = error.max_retries();

        // 若可重试，则应至少给出重试次数或延迟
        if is_retryable {
            assert!(retry_delay.is_some() || max_retries.is_some());
        }
    }
}

/// 测试错误统计
#[test]
fn test_error_stats() {
    let mut stats = ErrorStats::default();
    
    // 记录不同类型的错误
    stats.record_error(&NetworkError::Protocol("test".to_string()));
    stats.record_error(&NetworkError::Connection("test".to_string()));
    stats.record_error(&NetworkError::Timeout(Duration::from_secs(1)));
    
    assert_eq!(stats.total_errors, 3);
    assert_eq!(stats.protocol_errors, 1);
    assert_eq!(stats.connection_errors, 1);
    assert_eq!(stats.timeout_errors, 1);
    
    // 测试错误率计算
    assert_eq!(stats.error_rate(10), 0.3);
    assert_eq!(stats.error_rate(0), 0.0);
}

/// 测试协议错误
#[test]
fn test_protocol_errors() {
    let http_error = ProtocolError::Http {
        status: 404,
        message: "Not Found".to_string(),
    };
    
    let websocket_error = ProtocolError::WebSocket("Connection failed".to_string());
    let tcp_error = ProtocolError::Tcp("Connection reset".to_string());
    let udp_error = ProtocolError::Udp("Port unreachable".to_string());
    let dns_error = ProtocolError::Dns("Name resolution failed".to_string());
    
    // 验证错误消息格式
    assert_eq!(format!("{}", http_error), "HTTP error: 404 - Not Found");
    assert_eq!(format!("{}", websocket_error), "WebSocket error: Connection failed");
    assert_eq!(format!("{}", tcp_error), "TCP error: Connection reset");
    assert_eq!(format!("{}", udp_error), "UDP error: Port unreachable");
    assert_eq!(format!("{}", dns_error), "DNS error: Name resolution failed");
}

/// 测试性能错误
#[test]
fn test_performance_errors() {
    let pool_error = PerformanceError::PoolExhausted;
    let rate_limit_error = PerformanceError::RateLimit {
        limit: 100,
        period: Duration::from_secs(60),
    };
    let memory_error = PerformanceError::InsufficientMemory {
        required: 1024,
        available: 512,
    };
    let load_error = PerformanceError::HighLoad { load: 95.5 };
    
    // 验证错误消息
    assert_eq!(format!("{}", pool_error), "Connection pool exhausted");
    assert_eq!(format!("{}", rate_limit_error), "Rate limit exceeded: 100 requests per 60s");
    assert_eq!(format!("{}", memory_error), "Insufficient memory: required 1024, available 512");
    assert_eq!(format!("{}", load_error), "High load: 95.5%");
}

/// 测试安全错误
#[test]
fn test_security_errors() {
    let cert_error = SecurityError::CertificateVerification("Invalid certificate".to_string());
    let sig_error = SecurityError::SignatureVerification("Invalid signature".to_string());
    let perm_error = SecurityError::InsufficientPermissions("Access denied".to_string());
    let malicious_error = SecurityError::MaliciousRequest("Suspicious activity".to_string());
    
    // 验证错误消息
    assert_eq!(format!("{}", cert_error), "Certificate verification failed: Invalid certificate");
    assert_eq!(format!("{}", sig_error), "Signature verification failed: Invalid signature");
    assert_eq!(format!("{}", perm_error), "Insufficient permissions: Access denied");
    assert_eq!(format!("{}", malicious_error), "Malicious request detected: Suspicious activity");
}

/// 测试数据包创建和基本操作
#[test]
fn test_packet_creation() {
    let payload = Bytes::copy_from_slice(b"test data");
    let packet = Packet::new(PacketType::Raw, payload.clone());
    
    assert_eq!(packet.packet_type(), &PacketType::Raw);
    assert_eq!(packet.payload_length(), payload.len());
    assert!(!packet.is_empty());
    assert_eq!(packet.total_size(), std::mem::size_of::<c10_networks::packet::PacketHeader>() + payload.len());
}

/// 测试带序列号的数据包
#[test]
fn test_packet_with_sequence() {
    let payload = Bytes::copy_from_slice(b"sequence test");
    let packet = Packet::with_sequence(PacketType::Tcp, payload, 12345);
    
    assert_eq!(packet.header.sequence_number, Some(12345));
    assert_eq!(packet.packet_type(), &PacketType::Tcp);
}

/// 测试数据包构建器
#[test]
fn test_packet_builder() {
    let mut builder = PacketBuilder::new(PacketType::Http);
    builder.add_data(b"GET /");
    builder.add_data(b" HTTP/1.1");
    builder.sequence_number(123);
    builder.flags(0x01);
    let packet = builder.build();
    
    assert_eq!(packet.packet_type(), &PacketType::Http);
    assert_eq!(packet.payload, Bytes::copy_from_slice(b"GET / HTTP/1.1"));
    assert_eq!(packet.header.sequence_number, Some(123));
    assert_eq!(packet.header.flags, 0x01);
}

/// 测试数据包统计
#[test]
fn test_packet_stats() {
    let mut stats = PacketStats::new();
    
    let packet1 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data1"));
    let packet2 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"data2"));
    let packet3 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"longer data"));
    
    stats.add_packet(&packet1);
    stats.add_packet(&packet2);
    stats.add_packet(&packet3);
    
    assert_eq!(stats.total_packets, 3);
    assert_eq!(stats.packets_of_type(&PacketType::Raw), 2);
    assert_eq!(stats.packets_of_type(&PacketType::Http), 1);
    assert_eq!(stats.bytes_of_type(&PacketType::Raw), 5 + 11); // "data1" + "longer data"
    assert_eq!(stats.bytes_of_type(&PacketType::Http), 5); // "data2"
    
    // 测试大小统计
    assert_eq!(stats.largest_packet_size, 11); // "longer data"
    assert_eq!(stats.smallest_packet_size, 5); // "data1" or "data2"
    assert!(stats.average_packet_size > 0.0);
}

/// 测试数据包过滤器
#[test]
fn test_packet_filter() {
    let filter = PacketFilter::new()
        .allow_type(PacketType::Http)
        .min_size(5)
        .max_size(10);
    
    let packet1 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"GET /"));
    let packet2 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data"));
    let packet3 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"very long data"));
    let packet4 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"ab")); // 2字节 < min_size(5)
    
    assert!(filter.matches(&packet1)); // HTTP类型，大小在范围内
    assert!(!filter.matches(&packet2)); // 类型不匹配
    assert!(!filter.matches(&packet3)); // 大小超出范围
    assert!(!filter.matches(&packet4)); // 大小小于最小值
}

/// 测试序列号过滤器
#[test]
fn test_packet_filter_sequence() {
    let filter = PacketFilter::new()
        .sequence_range(100, 200);
    
    let packet1 = Packet::with_sequence(PacketType::Raw, Bytes::copy_from_slice(b"data"), 150);
    let packet2 = Packet::with_sequence(PacketType::Raw, Bytes::copy_from_slice(b"data"), 50);
    let packet3 = Packet::with_sequence(PacketType::Raw, Bytes::copy_from_slice(b"data"), 250);
    let packet4 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data")); // 无序列号
    
    assert!(filter.matches(&packet1)); // 序列号在范围内
    assert!(!filter.matches(&packet2)); // 序列号小于范围
    assert!(!filter.matches(&packet3)); // 序列号大于范围
    assert!(!filter.matches(&packet4)); // 无序列号
}

/// 测试数据包类型
#[test]
fn test_packet_types() {
    let types = vec![
        PacketType::Raw,
        PacketType::Http,
        PacketType::WebSocket,
        PacketType::Tcp,
        PacketType::Udp,
        PacketType::Custom("test".to_string()),
    ];
    
    for packet_type in types {
        let packet = Packet::new(packet_type.clone(), Bytes::copy_from_slice(b"test"));
        assert_eq!(packet.packet_type(), &packet_type);
    }
}

/// 测试HTTP协议基本功能
#[test]
fn test_http_protocol() {
    // 测试HTTP方法
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
        let mut request = c10_networks::protocol::http::HttpRequest::new(
            method,
            "/api/test",
            HttpVersion::Http1_1,
        );
        
        request.add_header("User-Agent", "c10_networks-test");
        request.add_header("Accept", "application/json");
        request.set_body(b"test body".as_slice());
        
        // 验证请求属性
        assert_eq!(request.uri, "/api/test");
        assert_eq!(request.version, HttpVersion::Http1_1);
        assert!(request.headers.len() >= 2);
        assert_eq!(request.body.len(), 9);
    }
    
    // 测试HTTP响应
    let mut response = c10_networks::protocol::http::HttpResponse::new(
        HttpVersion::Http1_1,
        HttpStatusCode::ok(),
    );
    
    response.add_header("Content-Type", "application/json");
    response.add_header("Server", "c10_networks");
    response.set_body(r#"{"status": "success"}"#);
    
    // 验证响应属性
    assert_eq!(response.status.code, 200);
    assert_eq!(response.version, HttpVersion::Http1_1);
    assert!(response.headers.len() >= 2);
    assert!(response.body.len() >= 20);
}

/// 测试WebSocket协议基本功能
#[test]
fn test_websocket_protocol() {
    // 测试WebSocket帧创建
    let text_frame = WebSocketFrame::text("Hello, WebSocket!");
    assert_eq!(text_frame.opcode, WebSocketOpcode::Text);
    assert_eq!(text_frame.payload, Bytes::from("Hello, WebSocket!"));
    assert!(text_frame.fin);
    
    let binary_frame = WebSocketFrame::binary(&[1, 2, 3, 4, 5]);
    assert_eq!(binary_frame.opcode, WebSocketOpcode::Binary);
    assert_eq!(binary_frame.payload, Bytes::from(&[1, 2, 3, 4, 5][..]));
    
    let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    assert_eq!(close_frame.opcode, WebSocketOpcode::Close);
    
    // 测试WebSocket握手请求
    let mut request = WebSocketHandshakeRequest::new("/chat");
    request.set_host("example.com");
    request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
    request.set_websocket_version("13");
    request.set_upgrade();
    
    let request_str = request.encode();
    assert!(request_str.contains("GET /chat HTTP/1.1"));
    assert!(request_str.contains("Host: example.com"));
    assert!(request_str.contains("Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ=="));
    assert!(request_str.contains("Upgrade: websocket"));
}

/// 测试套接字配置
#[test]
fn test_socket_configs() {
    // 测试TCP配置
    let tcp_config = TcpConfig {
        address: utils::localhost(8080),
        timeout: Some(Duration::from_secs(30)),
        buffer_size: 8192,
        keep_alive: true,
        tcp_nodelay: true,
    };
    
    assert_eq!(tcp_config.address.port(), 8080);
    assert_eq!(tcp_config.buffer_size, 8192);
    assert!(tcp_config.keep_alive);
    assert!(tcp_config.tcp_nodelay);
    
    // 测试UDP配置
    let udp_config = UdpConfig {
        address: utils::localhost(8081),
        timeout: Some(Duration::from_secs(10)),
        buffer_size: 4096,
        broadcast: false,
        multicast_loop_v4: false,
    };
    
    assert_eq!(udp_config.address.port(), 8081);
    assert_eq!(udp_config.buffer_size, 4096);
    assert!(!udp_config.broadcast);
    assert!(!udp_config.multicast_loop_v4);
}

/// 测试数据包序列化和反序列化
#[test]
fn test_packet_serialization() {
    let original_packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    
    // 测试序列化
    let serialized = serde_json::to_string(&original_packet).unwrap();
    assert!(!serialized.is_empty());
    
    // 测试反序列化
    let deserialized: Packet = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized.packet_type(), original_packet.packet_type());
    assert_eq!(deserialized.payload, original_packet.payload);
    assert_eq!(deserialized.header.length, original_packet.header.length);
}

/// 测试数据包头部操作
#[test]
fn test_packet_header() {
    let header = c10_networks::packet::PacketHeader::new(PacketType::Http, 100);
    
    assert_eq!(header.packet_type, PacketType::Http);
    assert_eq!(header.length, 100);
    assert!(header.timestamp > 0);
    assert_eq!(header.sequence_number, None);
    assert_eq!(header.flags, 0);
    
    // 测试链式操作
    let header_with_seq = header
        .with_sequence_number(12345)
        .with_flags(0xFF);
    
    assert_eq!(header_with_seq.sequence_number, Some(12345));
    assert_eq!(header_with_seq.flags, 0xFF);
}

/// 测试数据包显示格式
#[test]
fn test_packet_display() {
    let packet = Packet::with_sequence(PacketType::Http, Bytes::copy_from_slice(b"test"), 123);
    let display_str = format!("{}", packet);
    
    assert!(display_str.contains("Http"));
    assert!(display_str.contains("123"));
    assert!(display_str.contains("0x0")); // flags
}

/// 测试数据包统计重置
#[test]
fn test_packet_stats_reset() {
    let mut stats = PacketStats::new();
    
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test"));
    stats.add_packet(&packet);
    
    assert_eq!(stats.total_packets, 1);
    assert_eq!(stats.total_bytes, 4);
    
    stats.reset();
    
    assert_eq!(stats.total_packets, 0);
    assert_eq!(stats.total_bytes, 0);
    assert_eq!(stats.largest_packet_size, 0);
    assert_eq!(stats.smallest_packet_size, 0);
}

/// 测试空数据包
#[test]
fn test_empty_packet() {
    let empty_packet = Packet::new(PacketType::Raw, Bytes::new());
    
    assert!(empty_packet.is_empty());
    assert_eq!(empty_packet.payload_length(), 0);
    assert_eq!(empty_packet.total_size(), std::mem::size_of::<c10_networks::packet::PacketHeader>());
}

/// 测试数据包构建器链式调用
#[test]
fn test_packet_builder_chaining() {
    let mut builder = PacketBuilder::new(PacketType::Custom("test".to_string()));
    builder.add_data(b"part1");
    builder.add_data(b"part2");
    builder.sequence_number(999);
    builder.flags(0xABCD);
    let packet = builder.build();
    
    assert_eq!(packet.packet_type(), &PacketType::Custom("test".to_string()));
    assert_eq!(packet.payload, Bytes::copy_from_slice(b"part1part2"));
    assert_eq!(packet.header.sequence_number, Some(999));
    assert_eq!(packet.header.flags, 0xABCD);
}

/// 测试数据包过滤器默认值
#[test]
fn test_packet_filter_default() {
    let filter = PacketFilter::default();
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test"));
    
    // 默认过滤器应该允许所有数据包通过
    assert!(filter.matches(&packet));
}

/// 测试数据包类型比较
#[test]
fn test_packet_type_equality() {
    assert_eq!(PacketType::Raw, PacketType::Raw);
    assert_eq!(PacketType::Http, PacketType::Http);
    assert_eq!(PacketType::Custom("test".to_string()), PacketType::Custom("test".to_string()));
    
    assert_ne!(PacketType::Raw, PacketType::Http);
    assert_ne!(PacketType::Custom("test".to_string()), PacketType::Custom("other".to_string()));
}

/// 测试数据包哈希
#[test]
fn test_packet_type_hash() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    map.insert(PacketType::Raw, "raw");
    map.insert(PacketType::Http, "http");
    map.insert(PacketType::Custom("test".to_string()), "custom");
    
    assert_eq!(map.get(&PacketType::Raw), Some(&"raw"));
    assert_eq!(map.get(&PacketType::Http), Some(&"http"));
    assert_eq!(map.get(&PacketType::Custom("test".to_string())), Some(&"custom"));
}
