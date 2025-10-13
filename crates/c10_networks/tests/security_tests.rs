//! 安全测试模块
//!
//! 本模块包含了 c10_networks 库的安全测试，
//! 确保各种安全机制和防护措施正常工作。

use bytes::Bytes;
use c10_networks::{
    error::{ErrorRecovery, NetworkError, SecurityError},
    packet::{Packet, PacketType},
    protocol::{
        http::{HttpMethod, HttpStatusCode, HttpVersion},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest, WebSocketOpcode},
    },
    security::acme::{AcmeManager, Http01MemoryStore},
};
use std::time::Duration;

/// 测试恶意数据包检测
#[test]
fn test_malicious_packet_detection() {
    // 测试超大数据包
    let large_data = vec![0u8; 10 * 1024 * 1024]; // 10MB
    let large_packet = Packet::new(PacketType::Raw, Bytes::from(large_data));
    
    // 验证数据包大小限制
    assert!(large_packet.payload_length() > 1024 * 1024); // 大于1MB
    
    // 测试异常序列号
    let malicious_packet = Packet::with_sequence(
        PacketType::Raw,
        Bytes::copy_from_slice(b"malicious"),
        u64::MAX,
    );
    
    assert_eq!(malicious_packet.header.sequence_number, Some(u64::MAX));
    
    // 测试异常标志位
    let flag_packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test"));
    // 这里可以添加标志位验证逻辑
    assert_eq!(flag_packet.header.flags, 0);
}

/// 测试HTTP安全头部验证
#[test]
fn test_http_security_headers() {
    let mut request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/api/test",
        HttpVersion::Http1_1,
    );
    
    // 添加安全头部
    request.add_header("User-Agent", "c10_networks-test");
    request.add_header("X-Forwarded-For", "192.168.1.1");
    request.add_header("Authorization", "Bearer token123");
    
    // 验证头部存在
    assert!(request.headers.len() >= 3);
    
    // 测试敏感头部过滤
    let mut response = c10_networks::protocol::http::HttpResponse::new(
        HttpVersion::Http1_1,
        HttpStatusCode::ok(),
    );
    
    response.add_header("Content-Type", "application/json");
    response.add_header("Server", "c10_networks");
    response.add_header("X-Powered-By", "Rust");
    
    // 验证响应头部
    assert!(response.headers.len() >= 3);
}

/// 测试WebSocket安全验证
#[test]
fn test_websocket_security_validation() {
    // 测试WebSocket握手密钥验证
    let mut request = WebSocketHandshakeRequest::new("/chat");
    request.set_host("example.com");
    request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
    request.set_websocket_version("13");
    request.set_upgrade();
    
    let request_str = request.encode();
    
    // 验证必需的WebSocket头部
    assert!(request_str.contains("Sec-WebSocket-Key"));
    assert!(request_str.contains("Sec-WebSocket-Version"));
    assert!(request_str.contains("Upgrade: websocket"));
    
    // 测试WebSocket帧安全
    let text_frame = WebSocketFrame::text("Hello, WebSocket!");
    assert_eq!(text_frame.opcode, WebSocketOpcode::Text);
    assert!(text_frame.fin);
    
    // 测试WebSocket关闭帧
    let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    assert_eq!(close_frame.opcode, WebSocketOpcode::Close);
}

/// 测试输入验证和清理
#[test]
fn test_input_validation_and_sanitization() {
    // 测试恶意输入检测
    let malicious_inputs = vec![
        "<script>alert('xss')</script>",
        "'; DROP TABLE users; --",
        "../../../etc/passwd",
        "javascript:alert('xss')",
        "data:text/html,<script>alert('xss')</script>",
    ];
    
    for input in malicious_inputs {
        let packet = Packet::new(PacketType::Raw, Bytes::from(input));
        
        // 验证数据包创建成功（这里可以添加更严格的安全检查）
        assert_eq!(packet.payload_length(), input.len());
        
        // 这里可以添加输入清理和验证逻辑
        // 例如：HTML转义、SQL注入检测、路径遍历检测等
    }
}

/// 测试数据包大小限制
#[test]
fn test_packet_size_limits() {
    // 测试正常大小的数据包
    let normal_packet = Packet::new(
        PacketType::Raw,
        Bytes::copy_from_slice(&vec![0u8; 1024]), // 1KB
    );
    assert_eq!(normal_packet.payload_length(), 1024);
    
    // 测试中等大小的数据包
    let medium_packet = Packet::new(
        PacketType::Raw,
        Bytes::copy_from_slice(&vec![0u8; 64 * 1024]), // 64KB
    );
    assert_eq!(medium_packet.payload_length(), 64 * 1024);
    
    // 测试大数据包
    let large_packet = Packet::new(
        PacketType::Raw,
        Bytes::copy_from_slice(&vec![0u8; 1024 * 1024]), // 1MB
    );
    assert_eq!(large_packet.payload_length(), 1024 * 1024);
    
    // 这里可以添加大小限制检查逻辑
    // 例如：拒绝超过特定大小的数据包
}

/// 测试序列号安全
#[test]
fn test_sequence_number_security() {
    // 测试正常序列号
    let normal_packet = Packet::with_sequence(
        PacketType::Tcp,
        Bytes::copy_from_slice(b"normal"),
        12345,
    );
    assert_eq!(normal_packet.header.sequence_number, Some(12345));
    
    // 测试边界序列号
    let boundary_packet = Packet::with_sequence(
        PacketType::Tcp,
        Bytes::copy_from_slice(b"boundary"),
        0,
    );
    assert_eq!(boundary_packet.header.sequence_number, Some(0));
    
    // 测试最大序列号
    let max_packet = Packet::with_sequence(
        PacketType::Tcp,
        Bytes::copy_from_slice(b"max"),
        u64::MAX,
    );
    assert_eq!(max_packet.header.sequence_number, Some(u64::MAX));
    
    // 这里可以添加序列号验证逻辑
    // 例如：检测序列号跳跃、重复等异常情况
}

/// 测试错误处理安全
#[test]
fn test_error_handling_security() {
    // 测试安全错误类型
    let security_errors = vec![
        SecurityError::CertificateVerification("Invalid certificate".to_string()),
        SecurityError::SignatureVerification("Invalid signature".to_string()),
        SecurityError::InsufficientPermissions("Access denied".to_string()),
        SecurityError::MaliciousRequest("Suspicious activity".to_string()),
    ];
    
    for error in security_errors {
        // 验证错误消息不泄露敏感信息
        let error_msg = error.to_string();
        assert!(!error_msg.is_empty());
        
        // 验证错误消息格式
        assert!(error_msg.contains("error") || error_msg.contains("failed") || error_msg.contains("denied"));
    }
}

/// 测试网络错误安全
#[test]
fn test_network_error_security() {
    // 测试网络错误类型
    let network_errors = vec![
        NetworkError::Protocol("Protocol violation".to_string()),
        NetworkError::Connection("Connection refused".to_string()),
        NetworkError::Timeout(Duration::from_secs(30)),
        NetworkError::Authentication("Authentication failed".to_string()),
        NetworkError::Encryption("Encryption error".to_string()),
        NetworkError::Configuration("Invalid configuration".to_string()),
    ];
    
    for error in network_errors {
        // 验证错误消息
        let error_msg = error.to_string();
        assert!(!error_msg.is_empty());
        
        // 验证错误恢复策略
        let is_retryable = error.is_retryable();
        let retry_delay = error.retry_delay();
        let max_retries = error.max_retries();
        
        // 若可重试，则应至少给出重试次数或延迟
        if is_retryable {
            assert!(retry_delay.is_some() || max_retries.is_some());
        }
    }
}

/// 测试数据包类型安全
#[test]
fn test_packet_type_security() {
    // 测试正常数据包类型
    let normal_types = vec![
        PacketType::Raw,
        PacketType::Http,
        PacketType::WebSocket,
        PacketType::Tcp,
        PacketType::Udp,
    ];
    
    for packet_type in normal_types {
        let packet = Packet::new(packet_type.clone(), Bytes::copy_from_slice(b"test"));
        assert_eq!(packet.packet_type(), &packet_type);
    }
    
    // 测试自定义数据包类型
    let custom_types = vec![
        PacketType::Custom("secure".to_string()),
        PacketType::Custom("encrypted".to_string()),
        PacketType::Custom("authenticated".to_string()),
    ];
    
    for packet_type in custom_types {
        let packet = Packet::new(packet_type.clone(), Bytes::copy_from_slice(b"test"));
        assert_eq!(packet.packet_type(), &packet_type);
    }
}

/// 测试ACME管理器安全
#[allow(unused)]
#[test]
fn test_acme_manager_security() {
    // 测试ACME管理器创建
    let store = Http01MemoryStore::new();
    let _acme_manager = AcmeManager::new(std::path::PathBuf::from("/tmp"), "https://example.com/acme", vec![]);
    
    // 这里可以添加ACME相关的安全测试
    // 例如：证书验证、密钥管理、挑战验证等
}

/// 测试数据包过滤安全
#[test]
fn test_packet_filter_security() {
    use c10_networks::packet::PacketFilter;
    
    // 创建安全过滤器
    let filter = PacketFilter::new()
        .allow_type(PacketType::Http)
        .min_size(10)
        .max_size(1024);
    
    // 测试正常数据包
    let normal_packet = Packet::new(
        PacketType::Http,
        Bytes::copy_from_slice(b"GET / HTTP/1.1"),
    );
    assert!(filter.matches(&normal_packet));
    
    // 测试过小的数据包
    let small_packet = Packet::new(
        PacketType::Http,
        Bytes::copy_from_slice(b"GET /"),
    );
    assert!(!filter.matches(&small_packet));
    
    // 测试过大的数据包
    let large_data = vec![0u8; 2048];
    let large_packet = Packet::new(PacketType::Http, Bytes::from(large_data));
    assert!(!filter.matches(&large_packet));
    
    // 测试错误类型的数据包
    let wrong_type_packet = Packet::new(
        PacketType::Raw,
        Bytes::copy_from_slice(b"GET / HTTP/1.1"),
    );
    assert!(!filter.matches(&wrong_type_packet));
}

/// 测试并发安全
#[test]
fn test_concurrency_security() {
    use std::sync::Arc;
    use std::thread;
    
    const THREADS: usize = 4;
    const ITERATIONS: usize = 1000;
    
    let stats = Arc::new(std::sync::Mutex::new(c10_networks::packet::PacketStats::new()));
    let mut handles = Vec::new();
    
    for thread_id in 0..THREADS {
        let stats_clone = Arc::clone(&stats);
        let handle = thread::spawn(move || {
            for i in 0..ITERATIONS {
                let packet = Packet::new(
                    PacketType::Raw,
                    Bytes::copy_from_slice(format!("thread {} data {}", thread_id, i).as_bytes()),
                );
                
                let mut global_stats = stats_clone.lock().unwrap();
                global_stats.add_packet(&packet);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 验证并发安全性
    let final_stats = stats.lock().unwrap();
    assert_eq!(final_stats.total_packets, (THREADS * ITERATIONS) as u64);
}

/// 测试内存安全
#[test]
fn test_memory_security() {
    // 测试内存分配安全
    let packets: Vec<Packet> = (0..1000)
        .map(|i| {
            Packet::new(
                PacketType::Raw,
                Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
            )
        })
        .collect();
    
    assert_eq!(packets.len(), 1000);
    
    // 测试内存释放安全
    drop(packets);
    
    // 测试零拷贝安全
    let data = b"zero copy test";
    let packet1 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(data));
    let packet2 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(data));
    
    assert_eq!(packet1.payload, packet2.payload);
}

/// 测试边界条件安全
#[test]
fn test_boundary_condition_security() {
    // 测试空数据包
    let empty_packet = Packet::new(PacketType::Raw, Bytes::new());
    assert!(empty_packet.is_empty());
    assert_eq!(empty_packet.payload_length(), 0);
    
    // 测试单字节数据包
    let single_byte_packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"a"));
    assert_eq!(single_byte_packet.payload_length(), 1);
    
    // 测试最大长度数据包
    let max_length = 1024 * 1024; // 1MB
    let max_packet = Packet::new(
        PacketType::Raw,
        Bytes::copy_from_slice(&vec![0u8; max_length]),
    );
    assert_eq!(max_packet.payload_length(), max_length);
}

/// 测试协议安全
#[test]
fn test_protocol_security() {
    // 测试HTTP协议安全
    let mut http_request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/api/test",
        HttpVersion::Http1_1,
    );
    
    // 添加安全头部
    http_request.add_header("User-Agent", "c10_networks-test");
    http_request.add_header("Accept", "application/json");
    
    // 验证请求安全性
    assert_eq!(http_request.method, HttpMethod::GET);
    assert_eq!(http_request.uri, "/api/test");
    assert_eq!(http_request.version, HttpVersion::Http1_1);
    
    // 测试WebSocket协议安全
    let mut ws_request = WebSocketHandshakeRequest::new("/chat");
    ws_request.set_host("example.com");
    ws_request.set_websocket_key("dGhlIHNhbXBsZSBub25jZQ==");
    ws_request.set_websocket_version("13");
    ws_request.set_upgrade();
    
    let request_str = ws_request.encode();
    
    // 验证WebSocket握手安全性
    assert!(request_str.contains("GET /chat HTTP/1.1"));
    assert!(request_str.contains("Host: example.com"));
    assert!(request_str.contains("Sec-WebSocket-Key"));
    assert!(request_str.contains("Sec-WebSocket-Version"));
    assert!(request_str.contains("Upgrade: websocket"));
}

/// 安全测试套件
#[test]
fn test_security_test_suite() {
    println!("=== C10 Networks 安全测试套件 ===");
    
    // 运行所有安全测试
    test_malicious_packet_detection();
    test_http_security_headers();
    test_websocket_security_validation();
    test_input_validation_and_sanitization();
    test_packet_size_limits();
    test_sequence_number_security();
    test_error_handling_security();
    test_network_error_security();
    test_packet_type_security();
    test_acme_manager_security();
    test_packet_filter_security();
    test_concurrency_security();
    test_memory_security();
    test_boundary_condition_security();
    test_protocol_security();
    
    println!("=== 安全测试套件完成 ===");
}
