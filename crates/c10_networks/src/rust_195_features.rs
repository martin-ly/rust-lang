//! Rust 1.95 特性 —— 网络场景
//!
//! # 概述
//!
//! Rust 1.95 为网络编程带来了多项关键增强：
//! - **`Atomic*::update`/`try_update`** — 无锁连接池计数器、并发统计
//! - **`core::hint::cold_path`** — 错误处理与异常路径优化
//! - **`if let` guards** — 协议解析状态机中的条件匹配
//! - **`cfg_select!`** — 跨平台网络系统调用抽象
//!
//! # 网络场景特性映射
//!
//! | 1.95 特性 | 网络应用场景 | 收益 |
//! |-----------|-------------|------|
//! | `AtomicUsize::update` | 连接池引用计数 | 无锁、零分配 |
//! | `AtomicU32::try_update` | 速率限制令牌桶 | 原子性条件扣减 |
//! | `cold_path()` | TCP 连接失败处理 | I-cache 友好 |
//! | `if let` guards | HTTP 头部解析 | 减少嵌套、提升可读性 |
//! | `cfg_select!` | socket 创建跨平台 | 零条件编译开销 |

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

// ============================================================================
// 1. Atomic*::update / try_update — 网络并发原语
// ============================================================================

/// # 原子操作在网络中的深度应用
///
/// 网络服务中常见的原子场景：连接计数、请求统计、速率限制。
pub struct NetworkAtomicExamples;

impl NetworkAtomicExamples {
    /// 连接池引用计数递增（update）
    ///
    /// 每个新连接建立时原子递增活跃连接数。
    pub fn increment_active_connections(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }

    /// 连接池引用计数递减（update）
    pub fn decrement_active_connections(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| {
            old.saturating_sub(1)
        })
    }

    /// 速率限制：令牌桶原子扣减（try_update）
    ///
    /// 尝试从令牌桶中消耗一个令牌。如果桶为空，返回 `Err`。
    pub fn try_consume_token(bucket: &AtomicU32) -> Result<u32, u32> {
        bucket.try_update(Ordering::Acquire, Ordering::Relaxed, |tokens| {
            if tokens > 0 { Some(tokens - 1) } else { None }
        })
    }

    /// 令牌桶 refill（update）
    pub fn refill_tokens(bucket: &AtomicU32, max_tokens: u32) -> u32 {
        bucket.update(Ordering::Relaxed, Ordering::Relaxed, |_old| max_tokens)
    }

    /// 请求统计：原子累加响应大小
    pub fn record_response_size(counter: &AtomicUsize, size: usize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + size)
    }
}

// ============================================================================
// 2. core::hint::cold_path — 网络错误路径优化
// ============================================================================

/// # 冷路径优化在网络服务中的应用
///
/// 网络服务中，错误路径（连接失败、超时、协议错误）应该远少于成功路径。
/// `cold_path()` 告诉编译器将这些分支移出热代码路径，改善 I-cache。
pub struct NetworkColdPathExamples;

impl NetworkColdPathExamples {
    /// TCP 连接建立：错误路径标记为冷
    pub fn handle_connect_result(
        result: Result<std::net::TcpStream, std::io::Error>,
    ) -> Option<std::net::TcpStream> {
        match result {
            Ok(stream) => Some(stream),
            Err(_e) => {
                std::hint::cold_path();
                // 连接失败是异常情况
                None
            }
        }
    }

    /// HTTP 解析：非法方法路径标记为冷
    pub fn parse_http_method(method: &str) -> Option<&str> {
        match method {
            "GET" | "POST" | "PUT" | "DELETE" | "HEAD" | "OPTIONS" | "PATCH" => Some(method),
            _ => {
                std::hint::cold_path();
                None
            }
        }
    }

    /// 限流检查：被限流路径标记为冷
    pub fn check_rate_limit(remaining: &AtomicU32) -> bool {
        match NetworkAtomicExamples::try_consume_token(remaining) {
            Ok(_) => true,
            Err(_) => {
                std::hint::cold_path();
                false
            }
        }
    }
}

// ============================================================================
// 3. if let guards — 协议解析状态机
// ============================================================================

/// # `if let` guards 在协议解析中的应用
///
/// HTTP/1.1 流水线或 WebSocket 握手状态机中，条件匹配可大幅简化代码。
pub struct ProtocolIfLetGuardExamples;

impl ProtocolIfLetGuardExamples {
    /// HTTP 头部解析：条件匹配 Content-Length
    pub fn parse_content_length(header_value: Option<&str>) -> Result<Option<usize>, &'static str> {
        match header_value {
            Some(v)
                if let Ok(n) = v.parse::<usize>()
                    && n > 0 =>
            {
                Ok(Some(n))
            }
            Some(v) if v.parse::<usize>().is_ok() => Ok(None), // Content-Length: 0
            Some(_) => Err("invalid Content-Length"),
            None => Ok(None),
        }
    }

    /// WebSocket 握手：验证 Upgrade 头部
    pub fn check_websocket_upgrade(upgrade: Option<&str>, connection: Option<&str>) -> bool {
        matches!(
            (upgrade, connection),
            (Some(u), Some(c))
                if u.eq_ignore_ascii_case("websocket")
                && c.to_lowercase().contains("upgrade")
        )
    }

    /// TCP 状态转换：仅在特定状态下允许转换
    pub fn tcp_state_transition(state: &str, event: &str) -> Option<&'static str> {
        match (state, event) {
            ("SYN_SENT", "SYN-ACK")
                if let Some(seq) = extract_seq(event)
                    && seq > 0 =>
            {
                Some("ESTABLISHED")
            }
            ("ESTABLISHED", "FIN") => Some("CLOSE_WAIT"),
            ("CLOSE_WAIT", "CLOSE") => Some("LAST_ACK"),
            _ => None,
        }
    }
}

fn extract_seq(event: &str) -> Option<u32> {
    // 占位实现
    if event.contains("SEQ") { Some(1) } else { None }
}

// ============================================================================
// 4. cfg_select! — 跨平台网络系统调用
// ============================================================================

/// # `cfg_select!` 在网络系统调用中的应用
///
/// 不同操作系统的 socket 创建、ioctl 调用有显著差异。
/// `cfg_select!` 提供了零开销的跨平台抽象。
pub struct NetworkCfgSelectExamples;

impl NetworkCfgSelectExamples {
    /// 获取系统默认的 TCP 发送缓冲区大小（概念值）
    pub const DEFAULT_TCP_SEND_BUFFER: usize = cfg_select! {
        target_os = "linux" => 16384,
        target_os = "macos" => 8192,
        target_os = "windows" => 8192,
        _ => 4096,
    };

    /// 获取系统默认的 TCP 接收缓冲区大小（概念值）
    pub const DEFAULT_TCP_RECV_BUFFER: usize = cfg_select! {
        target_os = "linux" => 87380,
        target_os = "macos" => 65536,
        target_os = "windows" => 65536,
        _ => 4096,
    };

    /// 最大并发连接数推荐值（基于平台限制）
    pub const MAX_CONNECTIONS_RECOMMENDED: usize = cfg_select! {
        target_os = "linux" => 65535,
        target_os = "macos" => 16384,
        target_os = "windows" => 16384,
        _ => 1024,
    };

    /// 跨平台 socket 创建标志（概念值）
    pub fn socket_creation_flags() -> i32 {
        cfg_select! {
            target_os = "linux" => 0x80000 | 0x800, // SOCK_CLOEXEC | SOCK_NONBLOCK
            target_os = "macos" => 1,               // SOCK_STREAM
            target_os = "windows" => 1,             // SOCK_STREAM
            _ => 0,
        }
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_connection_counter() {
        let counter = AtomicUsize::new(0);
        let old = NetworkAtomicExamples::increment_active_connections(&counter);
        assert_eq!(old, 0);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_token_bucket() {
        let bucket = AtomicU32::new(5);
        assert!(NetworkAtomicExamples::try_consume_token(&bucket).is_ok());
        assert_eq!(bucket.load(Ordering::Relaxed), 4);

        // 消耗剩余 4 个
        for _ in 0..4 {
            assert!(NetworkAtomicExamples::try_consume_token(&bucket).is_ok());
        }
        assert!(NetworkAtomicExamples::try_consume_token(&bucket).is_err());
    }

    #[test]
    fn test_cold_path_parse_method() {
        assert_eq!(
            NetworkColdPathExamples::parse_http_method("GET"),
            Some("GET")
        );
        assert_eq!(NetworkColdPathExamples::parse_http_method("UNKNOWN"), None);
    }

    #[test]
    fn test_content_length_parsing() {
        assert_eq!(
            ProtocolIfLetGuardExamples::parse_content_length(Some("1024")),
            Ok(Some(1024))
        );
        assert_eq!(
            ProtocolIfLetGuardExamples::parse_content_length(Some("0")),
            Ok(None)
        );
        assert_eq!(
            ProtocolIfLetGuardExamples::parse_content_length(Some("abc")),
            Err("invalid Content-Length")
        );
    }

    #[test]
    fn test_websocket_upgrade() {
        assert!(ProtocolIfLetGuardExamples::check_websocket_upgrade(
            Some("websocket"),
            Some("Upgrade")
        ));
        assert!(!ProtocolIfLetGuardExamples::check_websocket_upgrade(
            Some("http2"),
            Some("Upgrade")
        ));
    }

    #[test]
    fn test_cfg_select_buffer_sizes() {
        const { assert!(NetworkCfgSelectExamples::DEFAULT_TCP_SEND_BUFFER > 0) };
        const { assert!(NetworkCfgSelectExamples::DEFAULT_TCP_RECV_BUFFER > 0) };
        const { assert!(NetworkCfgSelectExamples::MAX_CONNECTIONS_RECOMMENDED > 0) };
    }
}


// ============================================================================
// 5. RealRust195Features — C string literals, if let guards, const blocks
// ============================================================================

use std::ffi::CStr;

/// # 真实 Rust 1.95 特性演示
///
/// 展示 `c"..."` C 字符串字面量、`if let` guards 以及 `const {}` 块。
pub struct RealRust195Features;

impl RealRust195Features {
    /// 使用 `c"HTTP/1.1"` 表示协议版本
    pub fn protocol_cstr_literal() -> &'static CStr {
        c"HTTP/1.1"
    }

    /// 使用 `if let` guard 解析数据包
    ///
    /// 在 match 臂中直接解构 `Option` 并检查条件。
    pub fn parse_packet_with_guard(packet: Option<Vec<u8>>) -> Result<usize, &'static str> {
        match packet {
            Some(data)
                if let Some(first) = data.first()
                    && *first == 0xAB =>
            {
                Ok(data.len())
            }
            Some(_) => Err("invalid packet header"),
            None => Err("no packet"),
        }
    }

    /// 使用 `const {}` 计算协议头大小
    pub const fn const_block_header_size() -> usize {
        const { 4 + 2 + 2 }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_protocol_cstr_literal() {
        assert_eq!(
            RealRust195Features::protocol_cstr_literal().to_str(),
            Ok("HTTP/1.1")
        );
    }

    #[test]
    fn test_parse_packet_with_guard() {
        assert_eq!(
            RealRust195Features::parse_packet_with_guard(Some(vec![0xAB, 0x01, 0x02])),
            Ok(3)
        );
        assert_eq!(
            RealRust195Features::parse_packet_with_guard(Some(vec![0x00])),
            Err("invalid packet header")
        );
        assert_eq!(
            RealRust195Features::parse_packet_with_guard(None),
            Err("no packet")
        );
    }

    #[test]
    fn test_const_block_header_size() {
        const { assert!(RealRust195Features::const_block_header_size() == 8) };
    }
}
