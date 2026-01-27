//! 网络编程模块错误路径测试套件 / Network Programming Module Error Paths Test Suite

use c10_networks::protocol::websocket::frame::WebSocketOpcode;
use c10_networks::socket::utils as socket_utils;

/// 测试错误输入情况
#[test]
fn test_error_inputs() {
    // 测试无效地址（解析失败）
    assert!(socket_utils::parse_address("not-an-addr").is_err());

    // 测试无效端口（超过 u16 范围）
    assert!(socket_utils::parse_address("127.0.0.1:99999").is_err());

    // 测试缺失端口
    assert!(socket_utils::parse_address("127.0.0.1").is_err());
}

/// 测试错误状态情况
#[test]
fn test_error_states() {
    // WebSocket：非法 opcode 应返回协议错误
    let err = WebSocketOpcode::from_u8(0x3).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("Invalid WebSocket opcode"),
        "unexpected error: {msg}"
    );
}

/// 测试异常情况
#[test]
fn test_exception_cases() {
    // WebSocket：合法 opcode 不应报错
    assert!(WebSocketOpcode::from_u8(0x1).is_ok()); // Text
    assert!(WebSocketOpcode::from_u8(0xA).is_ok()); // Pong
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 测试容量预留失败（不应触发 OOM，而是返回错误）
    let mut buf: Vec<u8> = Vec::new();
    assert!(buf.try_reserve(usize::MAX).is_err());
}

/// 测试并发安全
#[test]
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let connection_count = Arc::new(Mutex::new(0u32));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for _ in 0..10 {
        let count = Arc::clone(&connection_count);
        let handle = thread::spawn(move || {
            let mut cnt = count.lock().unwrap();
            *cnt += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证结果
    assert_eq!(*connection_count.lock().unwrap(), 10);
}
