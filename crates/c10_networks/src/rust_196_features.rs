//! # Rust 1.96.0 特性 — 网络编程
//! # Rust 1.96.0 feature — network programming
//! - **`assert_matches!`**: network Result / Option 模式断言Test for

use std::sync::LazyLock;

// ==================== core::range::Range 在端口范围中的应用 ====================

/// 使用 core::range::Range 表示端口范围
/// core::range::Range represent scope
#[derive(Debug, Clone, Copy)]
pub struct PortRange {
    pub inner: core::range::Range<u16>,
}

impl PortRange {
    /// 直接构造端口范围
    /// scope
    pub fn new(start: u16, end: u16) -> Self {
        Self {
            inner: core::range::Range { start, end },
        }
    }

    /// 检查端口是否在范围内
    /// in scope inside
    pub fn contains(&self, port: u16) -> bool {
        let core::range::Range { start, end } = self.inner;
        port >= start && port < end
    }

    /// 获取起始端口
    pub fn start(&self) -> u16 {
        self.inner.start
    }

    /// 获取结束端口
    /// end
    pub fn end(&self) -> u16 {
        self.inner.end
    }
}

/// 知名端口范围（1..1024）
/// scope （1..1024）
/// 知名端口range（1..1024）
/// range（1..1024）
pub const WELL_KNOWN_PORTS: core::range::Range<u16> = core::range::Range {
    start: 1,
    end: 1024,
};

/// 注册端口范围（1024..49152）
/// scope （1024..49152）
pub const REGISTERED_PORTS: core::range::Range<u16> = core::range::Range {
    start: 1024,
    end: 49152,
};

/// 动态端口范围（49152..65535）
/// scope （49152..65535）
/// 动态端口range（49152..65535）
/// range（49152..65535）
pub const DYNAMIC_PORTS: core::range::Range<u16> = core::range::Range {
    start: 49152,
    end: 65535,
};

pub fn classify_port(port: u16) -> &'static str {
    if WELL_KNOWN_PORTS.contains(&port) {
        "well_known"
    } else if REGISTERED_PORTS.contains(&port) {
        "registered"
    } else if DYNAMIC_PORTS.contains(&port) {
        "dynamic"
    } else {
        "invalid"
    }
}

pub fn is_valid_inclusive_port(port: u16, bounds: core::range::RangeInclusive<u16>) -> bool {
    let core::range::RangeInclusive { start, last } = bounds;
    port >= start && port <= last
}

// ==================== assert_matches! 在网络 Result/Option 测试中的应用 ====================

/// 网络请求结果类型
/// network result type
pub type NetworkResult<T> = Result<T, NetworkError>;

/// 网络错误类型
/// network error type
#[derive(Debug, Clone, PartialEq)]
pub enum NetworkError {
    Timeout,
    ConnectionRefused,
    DnsFailure(String),
    InvalidResponse(u16),
}

/// 使用 assert_matches! 测试网络结果
/// assert_matches! network result
pub fn handle_response(result: NetworkResult<String>) -> Option<String> {
    match result {
        Ok(data) => Some(data),
        Err(NetworkError::InvalidResponse(404)) => None,
        Err(_) => None,
    }
}

// ==================== LazyLock::from 在连接池中的应用 ====================

pub struct ConnectionPool {
    name: LazyLock<String>,
    max_connections: LazyLock<usize>,
}

impl ConnectionPool {
    /// 从已知配置创建连接池
    /// from configuration connection pool
    /// from
    pub fn from_config(name: &str, max: usize) -> Self {
        Self {
            name: LazyLock::from(name.to_string()),
            max_connections: LazyLock::from(max),
        }
    }

    /// 获取池名称
    pub fn name(&self) -> &str {
        &self.name
    }

    /// 获取最大连接数
    /// maximum
    pub fn max_connections(&self) -> usize {
        *self.max_connections
    }
}

pub struct NetworkConfig {
    endpoint: LazyLock<String>,
    timeout_ms: LazyLock<u64>,
}

impl NetworkConfig {
    pub fn new(endpoint: &str, timeout: u64) -> Self {
        Self {
            endpoint: LazyLock::from(endpoint.to_string()),
            timeout_ms: LazyLock::from(timeout),
        }
    }

    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }

    pub fn timeout_ms(&self) -> u64 {
        *self.timeout_ms
    }
}

// ==================== 演示函数 ====================

/// 演示 Rust 1.96 网络特性
/// demonstration Rust 1.96 network feature
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 网络编程特性演示");
    println!("========================================\n");

    println!("--- core::range::Range 端口范围 ---");
    println!(
        "well_known ports: {}..{}",
        WELL_KNOWN_PORTS.start, WELL_KNOWN_PORTS.end
    );
    println!(
        "registered ports: {}..{}",
        REGISTERED_PORTS.start, REGISTERED_PORTS.end
    );
    println!(
        "dynamic ports: {}..{}",
        DYNAMIC_PORTS.start, DYNAMIC_PORTS.end
    );

    println!("port 80 = {}", classify_port(80));
    println!("port 8080 = {}", classify_port(8080));
    println!("port 50000 = {}", classify_port(50000));

    println!("\n--- LazyLock::from 连接池 ---");
    let pool = ConnectionPool::from_config("primary", 100);
    println!("pool name = {}", pool.name());
    println!("pool max = {}", pool.max_connections());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// feature
pub fn get_rust_196_network_info() -> String {
    "Rust 1.96.0 网络编程特性:\n- core::range::Range 直接构造端口范围（Copy 语义可复用）\n- \
     assert_matches! 用于网络 Result/Option 断言测试\n- LazyLock::from(value) 用于连接池配置初始化"
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use super::*;

    #[test]
    fn test_port_range() {
        let range = PortRange::new(1000, 2000);
        assert!(range.contains(1500));
        assert!(!range.contains(2000)); // end is exclusive
        assert!(!range.contains(999));
    }

    #[test]
    fn test_classify_port() {
        assert_eq!(classify_port(80), "well_known");
        assert_eq!(classify_port(443), "well_known");
        assert_eq!(classify_port(8080), "registered");
        assert_eq!(classify_port(50000), "dynamic");
        assert_eq!(classify_port(0), "invalid");
    }

    #[test]
    fn test_well_known_ports_reusable() {
        // core::range::Range is Copy, so we can use it multiple times
        assert!(WELL_KNOWN_PORTS.contains(&80));
        assert!(WELL_KNOWN_PORTS.contains(&443));
        assert!(!WELL_KNOWN_PORTS.contains(&1024));
    }

    #[test]
    fn test_is_valid_inclusive_port() {
        let bounds = core::range::RangeInclusive {
            start: 8000,
            last: 9000,
        };
        assert!(is_valid_inclusive_port(8500, bounds));
        assert!(is_valid_inclusive_port(8000, bounds));
        assert!(is_valid_inclusive_port(9000, bounds));
        assert!(!is_valid_inclusive_port(7999, bounds));
    }

    #[test]
    fn test_assert_matches_network_result() {
        let ok: NetworkResult<String> = Ok(String::from("data"));
        assert_matches!(ok, Ok(_));
        assert_matches!(ok, Ok(s) if s == "data");

        let err: NetworkResult<String> = Err(NetworkError::Timeout);
        assert_matches!(err, Err(NetworkError::Timeout));

        let not_found: NetworkResult<String> = Err(NetworkError::InvalidResponse(404));
        assert_matches!(not_found, Err(NetworkError::InvalidResponse(404)));
        assert_matches!(not_found, Err(NetworkError::InvalidResponse(code)) if code == 404);
    }

    #[test]
    fn test_handle_response() {
        let ok: NetworkResult<String> = Ok(String::from("payload"));
        assert_eq!(handle_response(ok), Some(String::from("payload")));

        let not_found: NetworkResult<String> = Err(NetworkError::InvalidResponse(404));
        assert_eq!(handle_response(not_found), None);
    }

    #[test]
    fn test_connection_pool() {
        let pool = ConnectionPool::from_config("test_pool", 50);
        assert_eq!(pool.name(), "test_pool");
        assert_eq!(pool.max_connections(), 50);
    }

    #[test]
    fn test_network_config() {
        let config = NetworkConfig::new("http://api.example.com", 5000);
        assert_eq!(config.endpoint(), "http://api.example.com");
        assert_eq!(config.timeout_ms(), 5000);
    }

    #[test]
    fn test_get_rust_196_network_info() {
        let info = get_rust_196_network_info();
        assert!(info.contains("core::range::Range"));
        assert!(info.contains("assert_matches!"));
    }
}
