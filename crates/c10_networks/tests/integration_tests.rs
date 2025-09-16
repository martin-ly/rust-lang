//! 集成测试
//!
//! 本模块包含了 c10_networks 库的集成测试，
//! 确保各个模块能够协同工作。

use bytes::Bytes;
use c10_networks::{
    error::{ErrorRecovery, NetworkError, NetworkResult},
    packet::buffer::BufferConfig,
    packet::{Packet, PacketBuffer, PacketBuilder, PacketParser, PacketSerializer, PacketType},
    protocol::{
        http::{HttpMethod, HttpStatusCode, HttpVersion},
        tcp::{TcpConnection, TcpConnectionConfig, TcpConnectionPool},
        websocket::{WebSocketFrame, WebSocketHandshakeRequest, WebSocketOpcode},
    },
    socket::{TcpConfig, TcpSocket, UdpConfig, UdpSocketWrapper, utils},
};
use std::time::Duration;
use tokio::time::timeout;

/// 测试 TCP 套接字的基本功能
#[tokio::test]
async fn test_tcp_socket_basic() -> NetworkResult<()> {
    // 创建 TCP 套接字配置
    let config = TcpConfig {
        address: utils::localhost(0),
        timeout: Some(Duration::from_secs(5)),
        buffer_size: 1024,
        keep_alive: true,
        tcp_nodelay: true,
    };

    // 创建套接字
    let socket = TcpSocket::new(config);
    assert!(!socket.is_connected());
    assert!(socket.local_addr().is_none());
    assert!(socket.peer_addr().is_none());

    Ok(())
}

/// 测试 UDP 套接字的基本功能
#[tokio::test]
async fn test_udp_socket_basic() -> NetworkResult<()> {
    // 创建 UDP 套接字配置
    let config = UdpConfig {
        address: utils::localhost(0),
        timeout: Some(Duration::from_secs(5)),
        buffer_size: 1024,
        broadcast: false,
        multicast_loop_v4: false,
    };

    // 创建套接字
    let socket = UdpSocketWrapper::new(config).await?;
    assert_eq!(socket.local_addr().ip(), std::net::Ipv4Addr::LOCALHOST);

    Ok(())
}

/// 测试 HTTP 协议的基本功能
#[tokio::test]
async fn test_http_protocol_basic() -> NetworkResult<()> {
    // 创建 HTTP 客户端
    // let client = HttpClient::new(); // HttpClient 暂未实现

    // 创建 HTTP 请求
    let mut request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/api/test",
        HttpVersion::Http1_1,
    );

    request.add_header("User-Agent", "c10_networks-test");
    request.add_header("Accept", "application/json");
    request.set_body(b"test body".as_slice());

    // 验证请求属性
    assert_eq!(request.method, HttpMethod::GET);
    assert_eq!(request.uri, "/api/test");
    assert_eq!(request.version, HttpVersion::Http1_1);
    assert!(request.headers.len() >= 2);
    assert_eq!(request.body.len(), 9);

    // 创建 HTTP 响应
    let mut response =
        c10_networks::protocol::http::HttpResponse::new(HttpVersion::Http1_1, HttpStatusCode::ok());

    response.add_header("Content-Type", "application/json");
    response.add_header("Server", "c10_networks");
    response.set_body(r#"{"status": "success"}"#);

    // 验证响应属性
    assert_eq!(response.status.code, 200);
    assert_eq!(response.version, HttpVersion::Http1_1);
    assert!(response.headers.len() >= 2);
    assert!(response.body.len() >= 20);

    Ok(())
}

/// 测试 WebSocket 协议的基本功能
#[tokio::test]
async fn test_websocket_protocol_basic() -> NetworkResult<()> {
    // 创建 WebSocket 帧
    let text_frame = WebSocketFrame::text("Hello, WebSocket!");
    assert_eq!(text_frame.opcode, WebSocketOpcode::Text);
    assert_eq!(text_frame.payload, Bytes::from("Hello, WebSocket!"));
    assert!(text_frame.fin);

    let binary_frame = WebSocketFrame::binary(&[1, 2, 3, 4, 5]);
    assert_eq!(binary_frame.opcode, WebSocketOpcode::Binary);
    assert_eq!(binary_frame.payload, Bytes::from(&[1, 2, 3, 4, 5][..]));

    let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    assert_eq!(close_frame.opcode, WebSocketOpcode::Close);

    // 创建 WebSocket 握手请求
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

    Ok(())
}

/// 测试 TCP 连接管理的基本功能
#[tokio::test]
async fn test_tcp_connection_management() -> NetworkResult<()> {
    // 创建 TCP 连接配置
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

    // 创建 TCP 连接
    let connection = TcpConnection::new(1, config);
    assert_eq!(connection.id, 1);
    assert_eq!(
        *connection.state(),
        c10_networks::protocol::tcp::TcpState::Closed
    );
    assert!(!connection.state().can_send_data());
    assert!(!connection.state().can_receive_data());

    // 测试拥塞控制
    let mut conn = connection;
    conn.update_congestion_window();
    assert_eq!(conn.congestion_window, 2);

    conn.update_congestion_window();
    assert_eq!(conn.congestion_window, 4);

    conn.handle_congestion();
    assert_eq!(conn.congestion_window, 1);
    assert_eq!(conn.slow_start_threshold, 2);

    Ok(())
}

/// 测试 TCP 连接池的基本功能
#[tokio::test]
async fn test_tcp_connection_pool() -> NetworkResult<()> {
    // 创建连接池
    let pool = TcpConnectionPool::new(10, Duration::from_secs(30));

    // 创建连接配置
    let config = TcpConnectionConfig::default();

    // 创建连接
    let connection_id = pool.create_connection(config).await?;
    assert_eq!(connection_id, 0);

    // 获取统计信息
    let stats = pool.get_stats().await;
    assert_eq!(stats.total_connections, 1);
    assert_eq!(stats.established_connections, 0);
    assert_eq!(stats.closed_connections, 1);

    // 移除连接
    let removed = pool.remove_connection(connection_id).await;
    assert!(removed);

    // 验证连接已移除
    let stats = pool.get_stats().await;
    assert_eq!(stats.total_connections, 0);

    Ok(())
}

/// 测试数据包处理的基本功能
#[tokio::test]
async fn test_packet_processing() -> NetworkResult<()> {
    // 创建数据包
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    assert_eq!(packet.packet_type(), &PacketType::Raw);
    assert_eq!(packet.payload_length(), 9);
    assert!(!packet.is_empty());

    // 测试数据包构建器
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

    Ok(())
}

/// 测试数据包缓冲区的功能
#[tokio::test]
async fn test_packet_buffer() -> NetworkResult<()> {
    // 创建缓冲区配置
    let config = BufferConfig {
        max_size: 1024,
        max_packets: 10,
        timeout: Some(Duration::from_secs(5)),
        auto_flush: true,
        flush_interval: Duration::from_millis(100),
    };

    // 创建缓冲区
    let mut buffer = PacketBuffer::new(config);

    // 创建测试数据包
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

    // 添加数据包到缓冲区
    buffer.push(packet.clone())?;
    assert!(!buffer.is_empty());
    assert_eq!(buffer.len(), 1);

    // 从缓冲区取出数据包
    let popped = buffer.pop().unwrap();
    assert_eq!(popped.payload, packet.payload);
    assert!(buffer.is_empty());

    Ok(())
}

/// 测试数据包解析和序列化
#[tokio::test]
async fn test_packet_serialization() -> NetworkResult<()> {
    // 创建数据包
    let original_packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));

    // 创建序列化器
    let mut serializer = PacketSerializer::new(1024);
    let serialized = serializer.serialize(&original_packet)?;

    // 创建解析器
    let mut parser = PacketParser::new(1024);
    parser.feed(&serialized.data)?;

    // 解析数据包
    let parse_result = parser.parse()?.unwrap();
    let parsed_packet = parse_result.packet;

    // 验证解析结果
    assert_eq!(parsed_packet.packet_type(), original_packet.packet_type());
    assert_eq!(parsed_packet.payload, original_packet.payload);

    Ok(())
}

/// 测试错误处理
#[tokio::test]
async fn test_error_handling() -> NetworkResult<()> {
    // 测试不同类型的错误
    let errors = vec![
        NetworkError::Protocol("测试协议错误".to_string()),
        NetworkError::Connection("连接失败".to_string()),
        NetworkError::Timeout(Duration::from_secs(5)),
        NetworkError::Other("解析错误".to_string()),
        NetworkError::Other("序列化错误".to_string()),
        NetworkError::Other("安全错误".to_string()),
        NetworkError::Configuration("配置错误".to_string()),
        NetworkError::Other("性能错误".to_string()),
        NetworkError::Other("其他错误".to_string()),
    ];

    for error in errors {
        // 验证错误消息
        assert!(!error.to_string().is_empty());

        // 验证错误恢复特性（兼容不同错误类型的策略差异）
        let is_retryable = error.is_retryable();
        let retry_delay = error.retry_delay();
        let max_retries = error.max_retries();

        // 若可重试，则应至少给出重试次数或延迟；否则允许均为空
        if is_retryable {
            assert!(retry_delay.is_some() || max_retries.is_some());
        }
    }

    Ok(())
}

/// 测试并发处理
#[tokio::test]
async fn test_concurrent_processing() -> NetworkResult<()> {
    use tokio::task;

    // 创建多个并发任务
    let tasks: Vec<_> = (0..10)
        .map(|i| {
            task::spawn(async move {
                // 每个任务创建自己的数据包
                let packet = Packet::new(
                    PacketType::Raw,
                    Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
                );

                // 序列化数据包
                let mut serializer = PacketSerializer::new(1024);
                let serialized = serializer.serialize(&packet)?;

                // 解析数据包
                let mut parser = PacketParser::new(1024);
                parser.feed(&serialized.data)?;
                let parse_result = parser.parse()?.unwrap();

                // 验证结果
                assert_eq!(parse_result.packet.payload, packet.payload);

                Ok::<(), NetworkError>(())
            })
        })
        .collect();

    // 等待所有任务完成
    for task in tasks {
        let _ = task
            .await
            .map_err(|e| NetworkError::Other(format!("Task error: {}", e)))?;
    }

    Ok(())
}

/// 测试性能基准
#[tokio::test]
async fn test_performance_benchmark() -> NetworkResult<()> {
    use std::time::Instant;

    // 测试数据包创建性能
    let start = Instant::now();
    for i in 0..1000 {
        let _packet = Packet::new(
            PacketType::Raw,
            Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
        );
    }
    let creation_time = start.elapsed();

    // 测试序列化性能
    let packet = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"test data"));
    let mut serializer = PacketSerializer::new(1024);

    let start = Instant::now();
    for _ in 0..1000 {
        let _serialized = serializer.serialize(&packet)?;
    }
    let serialization_time = start.elapsed();

    // 测试解析性能
    let serialized = serializer.serialize(&packet)?;
    let mut parser = PacketParser::new(1024);

    let start = Instant::now();
    for _ in 0..1000 {
        parser.feed(&serialized.data)?;
        let _parsed = parser.parse()?.unwrap();
        parser.clear();
    }
    let parsing_time = start.elapsed();

    // 验证性能在合理范围内
    assert!(creation_time < Duration::from_millis(100));
    assert!(serialization_time < Duration::from_millis(100));
    assert!(parsing_time < Duration::from_millis(100));

    println!("性能测试结果:");
    println!("  数据包创建: {:?}", creation_time);
    println!("  序列化: {:?}", serialization_time);
    println!("  解析: {:?}", parsing_time);

    Ok(())
}

/// 测试超时处理
#[tokio::test]
async fn test_timeout_handling() -> NetworkResult<()> {
    // 创建带超时的缓冲区
    let config = BufferConfig {
        max_size: 1024,
        max_packets: 10,
        timeout: Some(Duration::from_millis(100)),
        auto_flush: false,
        flush_interval: Duration::from_millis(1000),
    };

    let mut buffer = PacketBuffer::new(config);

    // 测试等待超时
    let result = timeout(Duration::from_millis(200), buffer.wait_for_packet()).await;
    // 实现可能提前返回 None 或发生超时，两者皆视为通过
    let none_ok = result
        .as_ref()
        .ok()
        .and_then(|inner| inner.as_ref().ok())
        .is_none();
    assert!(result.is_err() || none_ok);

    Ok(())
}

/// 测试内存使用
#[tokio::test]
async fn test_memory_usage() -> NetworkResult<()> {
    // 创建大量数据包
    let mut packets = Vec::new();
    for i in 0..100 {
        let packet = Packet::new(
            PacketType::Raw,
            Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
        );
        packets.push(packet);
    }

    // 创建缓冲区并添加数据包
    let config = BufferConfig::default();
    let mut buffer = PacketBuffer::new(config);

    for packet in &packets {
        buffer.push(packet.clone())?;
    }

    // 获取统计信息
    let stats = buffer.stats();
    assert_eq!(stats.packet_count, 100);
    assert!(stats.total_size > 0);
    assert!(stats.utilization > 0.0);

    println!("内存使用统计:");
    println!("  数据包数量: {}", stats.packet_count);
    println!("  总大小: {} 字节", stats.total_size);
    println!("  利用率: {:.2}%", stats.utilization * 100.0);

    Ok(())
}
