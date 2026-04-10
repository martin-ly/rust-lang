//! # Rust 1.96.0 网络编程新特性实现模块
//!
//! 本模块展示了 Rust 1.96.0 中网络编程相关的关键改进。

use std::ops::RangeInclusive;

/// if let guards 在网络编程中的应用
pub struct NetworkGuardExamples;

impl NetworkGuardExamples {
    /// 使用 if let guards 检查网络响应
    pub fn check_response<T>(
        response: Result<Option<T>, String>,
    ) -> Result<T, String>
    where
        T: Clone,
    {
        match response {
            Ok(opt) if let Some(value) = opt => Ok(value),
            Ok(_) => Err("空响应".to_string()),
            Err(e) => Err(format!("网络错误: {}", e)),
        }
    }

    /// 使用 if let guards 处理连接状态
    pub fn connection_state(
        established: bool,
        pending_data: Option<usize>,
    ) -> &'static str {
        match (established, pending_data) {
            (false, _) => "closed",
            (true, None) => "idle",
            (true, Some(n)) if let true = n > 0 && n < 1024 => "active",
            (true, Some(_)) => "busy",
        }
    }

    /// 使用 if let guards 处理协议版本
    pub fn protocol_version(major: u8, minor: Option<u8>) -> &'static str {
        match (major, minor) {
            (1, Some(1)) => "HTTP/1.1",
            (2, None) => "HTTP/2",
            (3, None) => "HTTP/3",
            (maj, Some(min)) if let true = maj >= 1 && min <= 9 => "legacy",
            _ => "unknown",
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
    pub fn packet_info(
        size: usize,
        ttl: u8,
    ) -> (usize, u8, &'static str, bool) {
        let fragment = size > 1500;
        let priority = if ttl > 128 { "high" } else { "normal" };
        (size, ttl, priority, fragment)
    }

    /// 使用元组 coercion 返回路由信息
    pub fn route_info<T>(
        destination: T,
        hops: u8,
    ) -> (T, u8, std::time::Duration, &'static str)
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
                Ok(opt) if let Some(value) = opt => successes.push(value),
                Ok(_) => failures.push("空响应".to_string()),
                Err(e) => failures.push(e),
            }
        }

        (successes, failures)
    }

    /// 使用 RangeInclusive 进行速率限制检查
    pub fn rate_limit_check(
        requests: u64,
        window_ms: u64,
        limit: RangeInclusive<u64>,
    ) -> (bool, &'static str) {
        let allowed = limit.contains(&requests);
        let status = if allowed {
            "allowed"
        } else {
            "throttled"
        };
        (allowed, status)
    }

    /// 使用 RangeInclusive 进行负载均衡权重计算
    pub fn calculate_weights(
        server_loads: &[u8],
    ) -> Vec<RangeInclusive<u8>> {
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
    println!("   Rust 1.96.0 网络编程新特性演示");
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
    let (result, endpoint, latency, status) =
        NetworkTupleExamples::request_result(Ok("data"), "/api/test");
    println!("请求结果: endpoint={}, latency={}ms, status={}", endpoint, latency, status);

    let (sent, recv, errors, err_rate, health) =
        NetworkTupleExamples::connection_stats(1000, 950, 5);
    println!("连接统计: 发送={}, 接收={}, 错误={}, 错误率={:.2}%, 健康={}",
             sent, recv, errors, err_rate, health);

    // 连接池演示
    println!("\n=== 连接池管理演示 ===");
    let manager = ConnectionPoolManager::new(50, 10);
    println!("连接池范围: {:?}", manager.get_all_ranges());
    println!("池0是否活跃: {}", manager.is_pool_active(0));

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 Rust 1.96.0 网络特性信息
pub fn get_rust_196_network_info() -> String {
    "Rust 1.96.0 网络编程新特性:\n\
        - if let guards for response handling\n\
        - RangeInclusive for port and MTU management\n\
        - Tuple coercion for network results\n\
        - Better rate limiting with ranges\n\
        - Improved connection pool management"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_check_response() {
        assert_eq!(
            NetworkGuardExamples::check_response(Ok(Some(42))),
            Ok(42)
        );
        assert!(NetworkGuardExamples::check_response(Ok(None)).is_err());
    }

    #[test]
    fn test_connection_state() {
        assert_eq!(NetworkGuardExamples::connection_state(false, None), "closed");
        assert_eq!(NetworkGuardExamples::connection_state(true, None), "idle");
        assert_eq!(NetworkGuardExamples::connection_state(true, Some(500)), "active");
        assert_eq!(NetworkGuardExamples::connection_state(true, Some(2000)), "busy");
    }

    #[test]
    fn test_protocol_version() {
        assert_eq!(NetworkGuardExamples::protocol_version(1, Some(1)), "HTTP/1.1");
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
        let (sent, recv, errors, err_rate, health) =
            NetworkTupleExamples::connection_stats(1000, 900, 10);
        assert_eq!(sent, 1000);
        assert_eq!(recv, 900);
        assert_eq!(errors, 10);
        assert!(err_rate > 0.0);
        assert_eq!(health, "fair");
    }

    #[test]
    fn test_rate_limit_check() {
        let (allowed, status) =
            PracticalNetworkExamples::rate_limit_check(50, 1000, 0..=100);
        assert!(allowed);
        assert_eq!(status, "allowed");

        let (allowed, status) =
            PracticalNetworkExamples::rate_limit_check(150, 1000, 0..=100);
        assert!(!allowed);
        assert_eq!(status, "throttled");
    }

    #[test]
    fn test_network_monitor_summary() {
        let connections = vec![
            ("conn1", true),
            ("conn2", true),
            ("conn3", false),
        ];
        let (total, healthy, rate, status) =
            PracticalNetworkExamples::network_monitor_summary(&connections);
        assert_eq!(total, 3);
        assert_eq!(healthy, 2);
        assert!((rate - 66.67).abs() < 1.0);
        assert_eq!(status, "degraded");
    }

    #[test]
    fn test_connection_pool_manager() {
        let manager = ConnectionPoolManager::new(50, 10);
        assert_eq!(manager.get_all_ranges().len(), 5);
        assert!(manager.is_pool_active(0));
        assert!(manager.get_connection_range(0).is_some());
    }

    #[test]
    fn test_get_rust_196_network_info() {
        let info = get_rust_196_network_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
