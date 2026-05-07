//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）
//!
//! 本模块展示了 Rust 网络编程相关的关键改进。

use std::ops::RangeInclusive;

/// if let guards (Rust 1.95 稳定，非 1.96 新特性) 在网络编程中的应用
pub struct NetworkGuardExamples;

impl NetworkGuardExamples {
    /// 使用 match 嵌套处理网络响应
    pub fn check_response<T>(response: Result<Option<T>, String>) -> Result<T, String>
    where
        T: Clone,
    {
        match response {
            Ok(opt) => match opt {
                Some(value) => Ok(value),
                None => Err("空响应".to_string()),
            },
            Err(e) => Err(format!("网络错误: {}", e)),
        }
    }

    /// 使用 if let guards 处理连接状态
    pub fn connection_state(established: bool, pending_data: Option<usize>) -> &'static str {
        match (established, pending_data) {
            (false, _) => "closed",
            (true, None) => "idle",
            (true, Some(n)) if n > 0 && n < 1024 => "active",
            (true, Some(_)) => "busy",
        }
    }

    /// 使用 if let guards 处理协议版本
    pub fn protocol_version(major: u8, minor: Option<u8>) -> &'static str {
        match (major, minor) {
            (1, Some(1)) => "HTTP/1.1",
            (2, None) => "HTTP/2",
            (3, None) => "HTTP/3",
            (maj, Some(min)) if maj >= 1 && min <= 9 => "legacy",
            _ => "unknown",
        }
    }

    /// 使用 if let guards 解析网络端口
    pub fn parse_port(addr: Option<&str>) -> Result<u16, &'static str> {
        match addr {
            Some(s) if let Ok(port) = s.parse::<u16>() => {
                if port > 0 {
                    Ok(port)
                } else {
                    Err("端口不能为0")
                }
            }
            Some(_) => Err("无法解析端口"),
            None => Err("地址为空"),
        }
    }

    /// 使用 if let guards 解析重试次数
    pub fn parse_retry_count(input: Option<&str>) -> Result<u32, &'static str> {
        match input {
            Some(s) if let Ok(count) = s.parse::<u32>() => Ok(count),
            Some(_) => Err("无效的重试次数"),
            None => Ok(3), // 默认重试3次
        }
    }
}

/// RangeInclusive 在网络编程中的应用
pub struct NetworkRangeExamples;

impl NetworkRangeExamples {
    /// 使用 RangeInclusive 进行端口范围检查
    pub fn is_valid_port(port: u16) -> bool {
        (1..=65535).contains(&port)
    }

    /// 使用 RangeInclusive 进行端口分类
    pub fn port_category(port: u16) -> &'static str {
        match port {
            1..=1023 => "well_known",
            1024..=49151 => "registered",
            49152..=65535 => "dynamic",
            _ => "invalid",
        }
    }

    /// 使用 RangeInclusive 进行MTU大小检查
    pub fn mtu_category(mtu: usize) -> &'static str {
        match mtu {
            0..=576 => "minimum",
            577..=1500 => "standard",
            1501..=9000 => "jumbo",
            _ => "invalid",
        }
    }

    /// 使用 RangeInclusive 进行IP地址段匹配
    pub fn ip_range_match(ip_last_octet: u8, range: RangeInclusive<u8>) -> bool {
        range.contains(&ip_last_octet)
    }

    /// 使用 RangeInclusive 进行带宽等级划分
    pub fn bandwidth_tier(mbps: u64) -> &'static str {
        match mbps {
            0..=10 => "basic",
            11..=100 => "standard",
            101..=1000 => "fast",
            1001..=10000 => "ultra",
            _ => "extreme",
        }
    }

    /// 使用 RangeInclusive 进行重试次数控制
    pub fn retry_count_range(priority: u8) -> RangeInclusive<u8> {
        match priority {
            1..=3 => 1..=2,
            4..=7 => 2..=5,
            _ => 5..=10,
        }
    }
}

/// 元组 coercion 在网络结果处理中的应用
pub struct NetworkTupleExamples;

impl NetworkTupleExamples {
    /// 使用元组 coercion 返回网络请求结果
    pub fn request_result<T>(
        result: Result<T, String>,
        endpoint: &str,
    ) -> (Result<T, String>, String, u64, &'static str)
    where
        T: Clone,
    {
        let latency = 100;
        let status = if result.is_ok() { "success" } else { "failed" };
        (result, endpoint.to_string(), latency, status)
    }

    /// 使用元组 coercion 进行连接统计
    pub fn connection_stats(
        sent: usize,
        received: usize,
        errors: usize,
    ) -> (usize, usize, usize, f64, &'static str) {
        let total = sent + received;
        let error_rate = if total > 0 {
            (errors as f64 / total as f64) * 100.0
        } else {
            0.0
        };

        let health = if error_rate > 10.0 {
            "poor"
        } else if error_rate > 1.0 {
            "fair"
        } else {
            "good"
        };

        (sent, received, errors, error_rate, health)
    }

    /// 使用元组 coercion 返回数据包信息
    pub fn packet_info(size: usize, ttl: u8) -> (usize, u8, &'static str, bool) {
        let fragment = size > 1500;
        let priority = if ttl > 128 { "high" } else { "normal" };
        (size, ttl, priority, fragment)
    }

    /// 使用元组 coercion 返回路由信息
    pub fn route_info<T>(destination: T, hops: u8) -> (T, u8, std::time::Duration, &'static str)
    where
        T: Clone,
    {
        let latency = std::time::Duration::from_millis(hops as u64 * 10);
        (destination, hops, latency, "active")
    }
}

/// 实际网络应用示例
pub struct PracticalNetworkExamples;

impl PracticalNetworkExamples {
    /// 使用 if let guards 处理批量响应
    pub fn process_batch_responses<T>(
        responses: Vec<Result<Option<T>, String>>,
    ) -> (Vec<T>, Vec<String>)
    where
        T: Clone,
    {
        let mut successes = Vec::new();
        let mut failures = Vec::new();

        for response in responses {
            match response {
                Ok(opt) => {
                    if let Some(value) = opt {
                        successes.push(value);
                    } else {
                        failures.push("空响应".to_string());
                    }
                }
                Err(e) => failures.push(e),
            }
        }

        (successes, failures)
    }

    /// 使用 RangeInclusive 进行速率限制检查
    pub fn rate_limit_check(
        requests: u64,
        _window_ms: u64,
        limit: RangeInclusive<u64>,
    ) -> (bool, &'static str) {
        let allowed = limit.contains(&requests);
        let status = if allowed { "allowed" } else { "throttled" };
        (allowed, status)
    }

    /// 使用 RangeInclusive 进行负载均衡权重计算
    pub fn calculate_weights(server_loads: &[u8]) -> Vec<RangeInclusive<u8>> {
        let total: u8 = server_loads.iter().sum();
        if total == 0 {
            return vec![];
        }

        let mut ranges = Vec::new();
        let mut current = 0u8;

        for load in server_loads {
            let weight = ((255 - *load) as f64 / 255.0 * 100.0) as u8;
            let end = current.saturating_add(weight);
            ranges.push(current..=end);
            current = end.saturating_add(1);
        }

        ranges
    }

    /// 使用元组 coercion 返回网络监控摘要
    pub fn network_monitor_summary(
        connections: &[(&'static str, bool)],
    ) -> (usize, usize, f64, &'static str) {
        let total = connections.len();
        let healthy = connections.iter().filter(|(_, ok)| *ok).count();
        let health_rate = if total > 0 {
            (healthy as f64 / total as f64) * 100.0
        } else {
            0.0
        };

        let status = if health_rate >= 99.0 {
            "excellent"
        } else if health_rate >= 95.0 {
            "good"
        } else if health_rate >= 80.0 {
            "degraded"
        } else {
            "critical"
        };

        (total, healthy, health_rate, status)
    }
}

/// 网络连接池管理器
pub struct ConnectionPoolManager {
    connection_ranges: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl ConnectionPoolManager {
    /// 创建新的连接池管理器
    pub fn new(connection_count: usize, pool_size: usize) -> Self {
        let mut ranges = Vec::new();
        let mut start = 0;

        while start < connection_count {
            let end = (start + pool_size - 1).min(connection_count - 1);
            ranges.push(start..=end);
            start = end + 1;
        }

        Self {
            connection_ranges: ranges.clone(),
            active_range: 0..=ranges.len().saturating_sub(1),
        }
    }

    /// 获取连接范围
    pub fn get_connection_range(&self, pool_id: usize) -> Option<&RangeInclusive<usize>> {
        self.connection_ranges.get(pool_id)
    }

    /// 检查池是否活跃
    pub fn is_pool_active(&self, pool_id: usize) -> bool {
        self.active_range.contains(&pool_id)
    }

    /// 获取所有连接范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.connection_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 网络编程特性演示");
    println!("========================================\n");

    // if let guards 演示
    println!("=== if let guards 演示 ===");
    let state = NetworkGuardExamples::connection_state(true, Some(500));
    println!("连接状态(已连接,500字节待处理): {}", state);

    let version = NetworkGuardExamples::protocol_version(2, None);
    println!("协议版本(2,None): {}", version);

    // Range 类型演示
    println!("\n=== Range 类型演示 ===");
    let valid = NetworkRangeExamples::is_valid_port(8080);
    println!("端口8080有效: {}", valid);

    let category = NetworkRangeExamples::port_category(8080);
    println!("端口8080类别: {}", category);

    let mtu_cat = NetworkRangeExamples::mtu_category(1500);
    println!("MTU 1500类别: {}", mtu_cat);

    let in_range = NetworkRangeExamples::ip_range_match(100, 50..=150);
    println!("IP尾字节100在[50..=150]内: {}", in_range);

    let tier = NetworkRangeExamples::bandwidth_tier(500);
    println!("带宽500Mbps等级: {}", tier);

    let retry_range = NetworkRangeExamples::retry_count_range(5);
    println!("优先级5重试范围: {:?}", retry_range);

    // 元组 coercion 演示
    println!("\n=== 元组 coercion 演示 ===");
    let (_result, endpoint, latency, status) =
        NetworkTupleExamples::request_result(Ok("data"), "/api/test");
    println!(
        "请求结果: endpoint={}, latency={}ms, status={}",
        endpoint, latency, status
    );

    let (sent, recv, errors, err_rate, health) =
        NetworkTupleExamples::connection_stats(1000, 950, 5);
    println!(
        "连接统计: 发送={}, 接收={}, 错误={}, 错误率={:.2}%, 健康={}",
        sent, recv, errors, err_rate, health
    );

    // 连接池演示
    println!("\n=== 连接池管理演示 ===");
    let manager = ConnectionPoolManager::new(50, 10);
    println!("连接池范围: {:?}", manager.get_all_ranges());
    println!("池0是否活跃: {}", manager.is_pool_active(0));

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 Rust 网络特性信息
pub fn get_rust_196_network_info() -> String {
    "Rust 1.95+ 网络编程特性:\n- if let guards for response handling\n- RangeInclusive for port \
     and MTU management\n- Tuple coercion for network results\n- Better rate limiting with \
     ranges\n- Improved connection pool management"
        .to_string()
}

// ============================================================================
// Rust 1.96 稳定新特性
// ============================================================================

use std::path::MAIN_SEPARATOR_STR;

/// `std::path::MAIN_SEPARATOR_STR` 在网络配置路径处理中的应用
///
/// Rust 1.96 稳定了 `MAIN_SEPARATOR_STR`，它是平台主路径分隔符的字符串字面量。
/// 在跨平台网络服务中，可用于构建配置文件路径字符串。
pub struct CrossPlatformConfigPath;

impl CrossPlatformConfigPath {
    /// 构建跨平台配置文件路径字符串
    ///
    /// 使用 `MAIN_SEPARATOR_STR` 替代硬编码的 `/` 或 `\\`，
    /// 确保路径在 Windows 和 Unix 系统上都能正确显示。
    pub fn config_path(service: &str, filename: &str) -> String {
        format!(
            "etc{}{}{}{}",
            MAIN_SEPARATOR_STR, service, MAIN_SEPARATOR_STR, filename
        )
    }

    /// 构建跨平台日志目录路径
    pub fn log_dir(service: &str) -> String {
        format!(
            "var{}log{}{}",
            MAIN_SEPARATOR_STR, MAIN_SEPARATOR_STR, service
        )
    }

    /// 获取当前平台分隔符
    pub fn separator() -> &'static str {
        MAIN_SEPARATOR_STR
    }
}

/// `impl From<bool> for {f32, f64}` 在网络协议标志中的应用
///
/// Rust 1.96 为 `f32` 和 `f64` 实现了 `From<bool>`：
/// - `true` 转换为 `1.0`
/// - `false` 转换为 `0.0`
///
/// 在网络编程中，布尔协议标志可快速转换为浮点权重，用于负载均衡算法。
pub struct ProtocolFlagConverter;

impl ProtocolFlagConverter {
    /// 将压缩标志转换为带宽权重系数
    pub fn compression_weight(enabled: bool) -> f32 {
        f32::from(enabled)
    }

    /// 将加密标志转换为延迟权重系数
    pub fn encryption_weight(enabled: bool) -> f64 {
        f64::from(enabled)
    }

    /// 根据多个布尔标志计算综合协议权重
    pub fn combined_protocol_weight(flags: &[bool]) -> f64 {
        if flags.is_empty() {
            return 0.0;
        }
        let sum: f64 = flags.iter().copied().map(f64::from).sum();
        sum / flags.len() as f64
    }
}

/// 演示 Rust 1.96 新特性
pub fn demonstrate_rust_196_new_features() {
    println!("\n=== Rust 1.96 新特性演示 ===");

    // MAIN_SEPARATOR_STR
    println!(
        "配置文件路径: {}",
        CrossPlatformConfigPath::config_path("httpd", "config.toml")
    );
    println!("日志目录: {}", CrossPlatformConfigPath::log_dir("httpd"));
    println!("平台分隔符: {:?}", CrossPlatformConfigPath::separator());

    // From<bool> for f32/f64
    println!(
        "压缩权重(true): {}",
        ProtocolFlagConverter::compression_weight(true)
    );
    println!(
        "加密权重(false): {}",
        ProtocolFlagConverter::encryption_weight(false)
    );
    let flags = vec![true, false, true];
    println!(
        "综合协议权重: {}",
        ProtocolFlagConverter::combined_protocol_weight(&flags)
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_check_response() {
        assert_eq!(NetworkGuardExamples::check_response(Ok(Some(42))), Ok(42));
        assert!(NetworkGuardExamples::check_response::<i32>(Ok(None)).is_err());
    }

    #[test]
    fn test_connection_state() {
        assert_eq!(
            NetworkGuardExamples::connection_state(false, None),
            "closed"
        );
        assert_eq!(NetworkGuardExamples::connection_state(true, None), "idle");
        assert_eq!(
            NetworkGuardExamples::connection_state(true, Some(500)),
            "active"
        );
        assert_eq!(
            NetworkGuardExamples::connection_state(true, Some(2000)),
            "busy"
        );
    }

    #[test]
    fn test_protocol_version() {
        assert_eq!(
            NetworkGuardExamples::protocol_version(1, Some(1)),
            "HTTP/1.1"
        );
        assert_eq!(NetworkGuardExamples::protocol_version(2, None), "HTTP/2");
        assert_eq!(NetworkGuardExamples::protocol_version(3, None), "HTTP/3");
        assert_eq!(NetworkGuardExamples::protocol_version(1, Some(0)), "legacy");
    }

    #[test]
    fn test_is_valid_port() {
        assert!(NetworkRangeExamples::is_valid_port(80));
        assert!(NetworkRangeExamples::is_valid_port(8080));
        assert!(!NetworkRangeExamples::is_valid_port(0));
        assert!(NetworkRangeExamples::is_valid_port(65535));
    }

    #[test]
    fn test_port_category() {
        assert_eq!(NetworkRangeExamples::port_category(80), "well_known");
        assert_eq!(NetworkRangeExamples::port_category(8080), "registered");
        assert_eq!(NetworkRangeExamples::port_category(50000), "dynamic");
    }

    #[test]
    fn test_mtu_category() {
        assert_eq!(NetworkRangeExamples::mtu_category(576), "minimum");
        assert_eq!(NetworkRangeExamples::mtu_category(1500), "standard");
        assert_eq!(NetworkRangeExamples::mtu_category(9000), "jumbo");
    }

    #[test]
    fn test_bandwidth_tier() {
        assert_eq!(NetworkRangeExamples::bandwidth_tier(5), "basic");
        assert_eq!(NetworkRangeExamples::bandwidth_tier(50), "standard");
        assert_eq!(NetworkRangeExamples::bandwidth_tier(500), "fast");
        assert_eq!(NetworkRangeExamples::bandwidth_tier(5000), "ultra");
    }

    #[test]
    fn test_connection_stats() {
        // Test case: 10 errors out of 1900 total = 0.526% error rate -> "good"
        let (sent, recv, errors, err_rate, health) =
            NetworkTupleExamples::connection_stats(1000, 900, 10);
        assert_eq!(sent, 1000);
        assert_eq!(recv, 900);
        assert_eq!(errors, 10);
        assert!(err_rate > 0.0);
        assert_eq!(health, "good");

        // Test case: 20 errors out of 1000 total = 2% error rate -> "fair"
        let (_, _, _, _, health2) = NetworkTupleExamples::connection_stats(500, 500, 20);
        assert_eq!(health2, "fair");

        // Test case: 200 errors out of 1000 total = 20% error rate -> "poor"
        let (_, _, _, _, health3) = NetworkTupleExamples::connection_stats(500, 500, 200);
        assert_eq!(health3, "poor");
    }

    #[test]
    fn test_rate_limit_check() {
        let (allowed, status) = PracticalNetworkExamples::rate_limit_check(50, 1000, 0..=100);
        assert!(allowed);
        assert_eq!(status, "allowed");

        let (allowed, status) = PracticalNetworkExamples::rate_limit_check(150, 1000, 0..=100);
        assert!(!allowed);
        assert_eq!(status, "throttled");
    }

    #[test]
    fn test_network_monitor_summary() {
        // Test case: 2/3 healthy = 66.67% -> "critical"
        let connections = vec![("conn1", true), ("conn2", true), ("conn3", false)];
        let (total, healthy, rate, status) =
            PracticalNetworkExamples::network_monitor_summary(&connections);
        assert_eq!(total, 3);
        assert_eq!(healthy, 2);
        assert!((rate - 66.67).abs() < 1.0);
        assert_eq!(status, "critical");

        // Test case: 4/5 healthy = 80% -> "degraded"
        let connections2 = vec![
            ("conn1", true),
            ("conn2", true),
            ("conn3", true),
            ("conn4", true),
            ("conn5", false),
        ];
        let (_, _, _, status2) = PracticalNetworkExamples::network_monitor_summary(&connections2);
        assert_eq!(status2, "degraded");

        // Test case: all healthy -> "excellent"
        let connections3 = vec![("conn1", true), ("conn2", true)];
        let (_, _, _, status3) = PracticalNetworkExamples::network_monitor_summary(&connections3);
        assert_eq!(status3, "excellent");
    }

    #[test]
    fn test_connection_pool_manager() {
        let manager = ConnectionPoolManager::new(50, 10);
        assert_eq!(manager.get_all_ranges().len(), 5);
        assert!(manager.is_pool_active(0));
        assert!(manager.get_connection_range(0).is_some());
    }

    #[test]
    fn test_parse_port() {
        assert_eq!(NetworkGuardExamples::parse_port(Some("8080")), Ok(8080));
        assert_eq!(
            NetworkGuardExamples::parse_port(Some("0")),
            Err("端口不能为0")
        );
        assert_eq!(
            NetworkGuardExamples::parse_port(Some("abc")),
            Err("无法解析端口")
        );
        assert_eq!(NetworkGuardExamples::parse_port(None), Err("地址为空"));
    }

    #[test]
    fn test_parse_retry_count() {
        assert_eq!(NetworkGuardExamples::parse_retry_count(Some("5")), Ok(5));
        assert_eq!(
            NetworkGuardExamples::parse_retry_count(Some("abc")),
            Err("无效的重试次数")
        );
        assert_eq!(NetworkGuardExamples::parse_retry_count(None), Ok(3));
    }

    #[test]
    fn test_get_rust_196_network_info() {
        let info = get_rust_196_network_info();
        assert!(!info.is_empty());
    }

    // Rust 1.96 新特性测试
    #[test]
    fn test_cross_platform_config_path() {
        let path = CrossPlatformConfigPath::config_path("httpd", "config.toml");
        assert!(path.contains("httpd"));
        assert!(path.contains("config.toml"));
        assert_eq!(CrossPlatformConfigPath::separator(), MAIN_SEPARATOR_STR);
    }

    #[test]
    fn test_protocol_flag_converter() {
        assert_eq!(ProtocolFlagConverter::compression_weight(true), 1.0_f32);
        assert_eq!(ProtocolFlagConverter::compression_weight(false), 0.0_f32);
        assert_eq!(ProtocolFlagConverter::encryption_weight(true), 1.0_f64);
        assert_eq!(ProtocolFlagConverter::encryption_weight(false), 0.0_f64);
    }

    #[test]
    fn test_combined_protocol_weight() {
        assert_eq!(
            ProtocolFlagConverter::combined_protocol_weight(&[true, true]),
            1.0
        );
        assert_eq!(
            ProtocolFlagConverter::combined_protocol_weight(&[true, false]),
            0.5
        );
        assert_eq!(ProtocolFlagConverter::combined_protocol_weight(&[]), 0.0);
    }
}

/// 网络端口反模式与边界情况专题
pub mod anti_patterns_and_edge_cases {
    /// 展示网络端口处理中的反模式和边界情况
    pub struct PortValidationAntiPatterns;

    impl PortValidationAntiPatterns {
        /// ❌ 不推荐：接受 0 作为有效端口或忽略范围检查
        pub fn dangerous_port_accept(port: u16) -> Result<u16, &'static str> {
            // ❌ 反例：0 是保留端口（表示让系统分配），不应作为显式目标端口
            // 但这里不做任何检查，直接接受所有 u16 值
            Ok(port)
        }

        /// ✅ 推荐：严格验证端口范围并拒绝 0
        pub fn safe_port_validation(port: u16) -> Result<u16, &'static str> {
            match port {
                0 => Err("port 0 is reserved (ephemeral binding only)"),
                1..=65535 => Ok(port),
            }
        }

        /// ⚠️ 边界情况：知名端口 (1-1023) 需要特权
        pub fn port_privilege_boundary(port: u16) -> &'static str {
            // ⚠️ 边界情况：1-1023 通常需要 root/admin 权限
            match port {
                0 => "invalid",
                1..=1023 => "privileged",
                1024..=49151 => "registered",
                49152..=65535 => "dynamic/private",
            }
        }

        /// ⚠️ 边界情况：端口范围的端点值验证
        pub fn validate_port_range(
            start: u16,
            end: u16,
        ) -> Result<std::ops::RangeInclusive<u16>, &'static str> {
            // ⚠️ 边界情况：确保范围有效且不包含 0
            if start == 0 || end == 0 {
                return Err("range must not include port 0");
            }
            if start > end {
                return Err("start must be <= end");
            }
            Ok(start..=end)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_dangerous_port_accept() {
            // ❌ 反例：错误地接受 0
            assert_eq!(PortValidationAntiPatterns::dangerous_port_accept(0), Ok(0));
        }

        #[test]
        fn test_safe_port_validation() {
            assert_eq!(
                PortValidationAntiPatterns::safe_port_validation(0),
                Err("port 0 is reserved (ephemeral binding only)")
            );
            assert_eq!(PortValidationAntiPatterns::safe_port_validation(80), Ok(80));
            assert_eq!(
                PortValidationAntiPatterns::safe_port_validation(65535),
                Ok(65535)
            );
        }

        #[test]
        fn test_port_privilege_boundary() {
            assert_eq!(
                PortValidationAntiPatterns::port_privilege_boundary(0),
                "invalid"
            );
            assert_eq!(
                PortValidationAntiPatterns::port_privilege_boundary(80),
                "privileged"
            );
            assert_eq!(
                PortValidationAntiPatterns::port_privilege_boundary(8080),
                "registered"
            );
            assert_eq!(
                PortValidationAntiPatterns::port_privilege_boundary(50000),
                "dynamic/private"
            );
            assert_eq!(
                PortValidationAntiPatterns::port_privilege_boundary(65535),
                "dynamic/private"
            );
        }

        #[test]
        fn test_validate_port_range() {
            assert_eq!(
                PortValidationAntiPatterns::validate_port_range(80, 443),
                Ok(80..=443)
            );
            assert_eq!(
                PortValidationAntiPatterns::validate_port_range(0, 100),
                Err("range must not include port 0")
            );
            assert_eq!(
                PortValidationAntiPatterns::validate_port_range(200, 100),
                Err("start must be <= end")
            );
        }
    }
}
