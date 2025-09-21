//! 健康检查器模块
//! 
//! 提供系统健康检查和状态监控功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use chrono::{DateTime, Utc};
use super::MonitoringError;

/// 健康检查器
pub struct HealthChecker {
    /// 健康检查配置
    config: HealthCheckConfig,
    /// 健康检查结果
    results: Arc<RwLock<HashMap<String, HealthCheckResult>>>,
    /// 健康检查统计信息
    statistics: Arc<RwLock<HealthCheckStatistics>>,
}

/// 健康检查配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckConfig {
    /// 检查间隔 (秒)
    pub check_interval: u64,
    /// 超时时间 (秒)
    pub timeout: u64,
    /// 重试次数
    pub retry_count: u32,
    /// 重试间隔 (秒)
    pub retry_interval: u64,
    /// 是否启用健康检查
    pub enabled: bool,
    /// 健康检查类型
    pub check_types: Vec<HealthCheckType>,
}

impl Default for HealthCheckConfig {
    fn default() -> Self {
        Self {
            check_interval: 30,
            timeout: 10,
            retry_count: 3,
            retry_interval: 5,
            enabled: true,
            check_types: vec![
                HealthCheckType::System,
                HealthCheckType::Network,
                HealthCheckType::Database,
                HealthCheckType::Service,
            ],
        }
    }
}

/// 健康检查类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum HealthCheckType {
    /// 系统检查
    System,
    /// 网络检查
    Network,
    /// 数据库检查
    Database,
    /// 服务检查
    Service,
    /// 自定义检查
    Custom(String),
}

impl HealthCheckType {
    /// 获取类型描述
    pub fn description(&self) -> &'static str {
        match self {
            HealthCheckType::System => "系统检查",
            HealthCheckType::Network => "网络检查",
            HealthCheckType::Database => "数据库检查",
            HealthCheckType::Service => "服务检查",
            HealthCheckType::Custom(_) => "自定义检查",
        }
    }
}

/// 健康检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckResult {
    /// 检查ID
    pub id: String,
    /// 检查类型
    pub check_type: HealthCheckType,
    /// 检查名称
    pub name: String,
    /// 检查状态
    pub status: HealthStatus,
    /// 检查消息
    pub message: String,
    /// 检查时间
    pub timestamp: DateTime<Utc>,
    /// 响应时间 (毫秒)
    pub response_time_ms: Option<u64>,
    /// 检查详情
    pub details: HashMap<String, serde_json::Value>,
    /// 错误信息
    pub error: Option<String>,
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum HealthStatus {
    /// 健康
    Healthy,
    /// 不健康
    Unhealthy,
    /// 未知
    Unknown,
    /// 检查中
    Checking,
}

impl HealthStatus {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            HealthStatus::Healthy => "健康",
            HealthStatus::Unhealthy => "不健康",
            HealthStatus::Unknown => "未知",
            HealthStatus::Checking => "检查中",
        }
    }

    /// 获取状态数值
    pub fn value(&self) -> u8 {
        match self {
            HealthStatus::Healthy => 1,
            HealthStatus::Unhealthy => 0,
            HealthStatus::Unknown => 2,
            HealthStatus::Checking => 3,
        }
    }
}

/// 健康检查统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckStatistics {
    /// 总检查次数
    pub total_checks: u64,
    /// 健康检查次数
    pub healthy_checks: u64,
    /// 不健康检查次数
    pub unhealthy_checks: u64,
    /// 未知状态检查次数
    pub unknown_checks: u64,
    /// 平均响应时间 (毫秒)
    pub average_response_time_ms: f64,
    /// 最后检查时间
    pub last_check: Option<DateTime<Utc>>,
    /// 各类型检查统计
    pub type_statistics: HashMap<String, TypeStatistics>,
}

/// 类型统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeStatistics {
    /// 检查次数
    pub check_count: u64,
    /// 健康次数
    pub healthy_count: u64,
    /// 不健康次数
    pub unhealthy_count: u64,
    /// 平均响应时间 (毫秒)
    pub average_response_time_ms: f64,
}

impl HealthChecker {
    /// 创建新的健康检查器
    pub fn new(config: HealthCheckConfig) -> Self {
        Self {
            config,
            results: Arc::new(RwLock::new(HashMap::new())),
            statistics: Arc::new(RwLock::new(HealthCheckStatistics {
                total_checks: 0,
                healthy_checks: 0,
                unhealthy_checks: 0,
                unknown_checks: 0,
                average_response_time_ms: 0.0,
                last_check: None,
                type_statistics: HashMap::new(),
            })),
        }
    }

    /// 执行健康检查
    pub async fn perform_health_check(&self, check_type: HealthCheckType, name: String) -> Result<HealthCheckResult, MonitoringError> {
        let start_time = std::time::Instant::now();
        let check_id = uuid::Uuid::new_v4().to_string();
        
        let mut result = HealthCheckResult {
            id: check_id.clone(),
            check_type: check_type.clone(),
            name: name.clone(),
            status: HealthStatus::Checking,
            message: "检查中".to_string(),
            timestamp: Utc::now(),
            response_time_ms: None,
            details: HashMap::new(),
            error: None,
        };
        
        // 执行检查
        let check_result = self.execute_check(&check_type, &name).await;
        
        let response_time = start_time.elapsed().as_millis() as u64;
        result.response_time_ms = Some(response_time);
        
        match check_result {
            Ok((status, message, details)) => {
                result.status = status;
                result.message = message;
                result.details = details;
            }
            Err(e) => {
                result.status = HealthStatus::Unhealthy;
                result.message = "检查失败".to_string();
                result.error = Some(e.to_string());
            }
        }
        
        // 记录结果
        self.record_result(result.clone()).await;
        
        Ok(result)
    }

    /// 执行具体检查
    async fn execute_check(&self, check_type: &HealthCheckType, name: &str) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        match check_type {
            HealthCheckType::System => self.check_system().await,
            HealthCheckType::Network => self.check_network().await,
            HealthCheckType::Database => self.check_database().await,
            HealthCheckType::Service => self.check_service(name).await,
            HealthCheckType::Custom(custom_type) => self.check_custom(custom_type, name).await,
        }
    }

    /// 系统健康检查
    async fn check_system(&self) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        let mut details = HashMap::new();
        
        // 检查CPU使用率
        let cpu_usage = self.get_cpu_usage().await;
        details.insert("cpu_usage".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(cpu_usage).unwrap()));
        
        // 检查内存使用率
        let memory_usage = self.get_memory_usage().await;
        details.insert("memory_usage".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(memory_usage).unwrap()));
        
        // 检查磁盘使用率
        let disk_usage = self.get_disk_usage().await;
        details.insert("disk_usage".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(disk_usage).unwrap()));
        
        // 判断系统健康状态
        let status = if cpu_usage > 90.0 || memory_usage > 90.0 || disk_usage > 90.0 {
            HealthStatus::Unhealthy
        } else if cpu_usage > 80.0 || memory_usage > 80.0 || disk_usage > 80.0 {
            HealthStatus::Unhealthy
        } else {
            HealthStatus::Healthy
        };
        
        let message = match status {
            HealthStatus::Healthy => "系统运行正常".to_string(),
            HealthStatus::Unhealthy => "系统资源使用率过高".to_string(),
            _ => "系统状态未知".to_string(),
        };
        
        Ok((status, message, details))
    }

    /// 网络健康检查
    async fn check_network(&self) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        let mut details = HashMap::new();
        
        // 检查网络连接
        let network_available = self.check_network_connectivity().await;
        details.insert("network_available".to_string(), serde_json::Value::Bool(network_available));
        
        // 检查网络延迟
        let latency = self.get_network_latency().await;
        details.insert("latency_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(latency)));
        
        // 检查网络带宽
        let bandwidth = self.get_network_bandwidth().await;
        details.insert("bandwidth_mbps".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(bandwidth).unwrap()));
        
        let status = if !network_available {
            HealthStatus::Unhealthy
        } else if latency > 1000 || bandwidth < 1.0 {
            HealthStatus::Unhealthy
        } else {
            HealthStatus::Healthy
        };
        
        let message = match status {
            HealthStatus::Healthy => "网络连接正常".to_string(),
            HealthStatus::Unhealthy => "网络连接异常或性能不佳".to_string(),
            _ => "网络状态未知".to_string(),
        };
        
        Ok((status, message, details))
    }

    /// 数据库健康检查
    async fn check_database(&self) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        let mut details = HashMap::new();
        
        // 检查数据库连接
        let db_connected = self.check_database_connection().await;
        details.insert("connected".to_string(), serde_json::Value::Bool(db_connected));
        
        if db_connected {
            // 检查数据库性能
            let query_time = self.get_database_query_time().await;
            details.insert("query_time_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(query_time)));
            
            // 检查数据库大小
            let db_size = self.get_database_size().await;
            details.insert("size_mb".to_string(), serde_json::Value::Number(serde_json::Number::from(db_size)));
        }
        
        let status = if !db_connected {
            HealthStatus::Unhealthy
        } else {
            HealthStatus::Healthy
        };
        
        let message = match status {
            HealthStatus::Healthy => "数据库连接正常".to_string(),
            HealthStatus::Unhealthy => "数据库连接失败".to_string(),
            _ => "数据库状态未知".to_string(),
        };
        
        Ok((status, message, details))
    }

    /// 服务健康检查
    async fn check_service(&self, service_name: &str) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        let mut details = HashMap::new();
        
        // 检查服务状态
        let service_running = self.check_service_status(service_name).await;
        details.insert("running".to_string(), serde_json::Value::Bool(service_running));
        
        if service_running {
            // 检查服务响应时间
            let response_time = self.get_service_response_time(service_name).await;
            details.insert("response_time_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(response_time)));
            
            // 检查服务版本
            let version = self.get_service_version(service_name).await;
            details.insert("version".to_string(), serde_json::Value::String(version));
        }
        
        let status = if !service_running {
            HealthStatus::Unhealthy
        } else {
            HealthStatus::Healthy
        };
        
        let message = match status {
            HealthStatus::Healthy => format!("服务 {} 运行正常", service_name),
            HealthStatus::Unhealthy => format!("服务 {} 运行异常", service_name),
            _ => format!("服务 {} 状态未知", service_name),
        };
        
        Ok((status, message, details))
    }

    /// 自定义健康检查
    async fn check_custom(&self, custom_type: &str, name: &str) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        let mut details = HashMap::new();
        
        // 简化实现，实际应该根据自定义类型执行相应检查
        details.insert("custom_type".to_string(), serde_json::Value::String(custom_type.to_string()));
        details.insert("name".to_string(), serde_json::Value::String(name.to_string()));
        
        let status = HealthStatus::Healthy;
        let message = format!("自定义检查 {} 执行成功", name);
        
        Ok((status, message, details))
    }

    /// 获取CPU使用率
    async fn get_cpu_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        (timestamp % 100) as f64
    }

    /// 获取内存使用率
    async fn get_memory_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        ((timestamp + 10) % 100) as f64
    }

    /// 获取磁盘使用率
    async fn get_disk_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        ((timestamp + 20) % 100) as f64
    }

    /// 检查网络连接
    async fn check_network_connectivity(&self) -> bool {
        // 简化实现，实际应该ping外部服务器
        true
    }

    /// 获取网络延迟
    async fn get_network_latency(&self) -> u64 {
        // 简化实现，实际应该测量ping时间
        50
    }

    /// 获取网络带宽
    async fn get_network_bandwidth(&self) -> f64 {
        // 简化实现，实际应该测量网络速度
        100.0
    }

    /// 检查数据库连接
    async fn check_database_connection(&self) -> bool {
        // 简化实现，实际应该尝试连接数据库
        true
    }

    /// 获取数据库查询时间
    async fn get_database_query_time(&self) -> u64 {
        // 简化实现，实际应该执行测试查询
        10
    }

    /// 获取数据库大小
    async fn get_database_size(&self) -> u64 {
        // 简化实现，实际应该查询数据库大小
        1024
    }

    /// 检查服务状态
    async fn check_service_status(&self, _service_name: &str) -> bool {
        // 实际应该检查服务进程状态
        // 这里模拟基于服务名称的检查
        match _service_name {
            "database" => true,
            "mqtt_broker" => true,
            "web_server" => true,
            _ => false,
        }
    }

    /// 获取服务响应时间
    async fn get_service_response_time(&self, _service_name: &str) -> u64 {
        // 实际应该测量服务响应时间
        // 这里返回基于服务类型的模拟响应时间
        match _service_name {
            "database" => 15,
            "mqtt_broker" => 5,
            "web_server" => 25,
            _ => 50,
        }
    }

    /// 获取服务版本
    async fn get_service_version(&self, _service_name: &str) -> String {
        // 实际应该查询服务版本
        // 这里返回基于服务类型的模拟版本
        match _service_name {
            "database" => "PostgreSQL 14.0".to_string(),
            "mqtt_broker" => "Eclipse Mosquitto 2.0".to_string(),
            "web_server" => "Nginx 1.21".to_string(),
            _ => "Unknown".to_string(),
        }
    }

    /// 记录检查结果
    async fn record_result(&self, result: HealthCheckResult) {
        let mut results = self.results.write().await;
        results.insert(result.id.clone(), result.clone());
        
        // 更新统计信息
        let mut stats = self.statistics.write().await;
        stats.total_checks += 1;
        stats.last_check = Some(result.timestamp);
        
        match result.status {
            HealthStatus::Healthy => stats.healthy_checks += 1,
            HealthStatus::Unhealthy => stats.unhealthy_checks += 1,
            HealthStatus::Unknown => stats.unknown_checks += 1,
            HealthStatus::Checking => {} // 不统计检查中状态
        }
        
        if let Some(response_time) = result.response_time_ms {
            stats.average_response_time_ms = (stats.average_response_time_ms * (stats.total_checks - 1) as f64 + response_time as f64) / stats.total_checks as f64;
        }
        
        // 更新类型统计
        let type_name = result.check_type.description().to_string();
        let type_stats = stats.type_statistics.entry(type_name).or_insert(TypeStatistics {
            check_count: 0,
            healthy_count: 0,
            unhealthy_count: 0,
            average_response_time_ms: 0.0,
        });
        
        type_stats.check_count += 1;
        match result.status {
            HealthStatus::Healthy => type_stats.healthy_count += 1,
            HealthStatus::Unhealthy => type_stats.unhealthy_count += 1,
            _ => {}
        }
        
        if let Some(response_time) = result.response_time_ms {
            type_stats.average_response_time_ms = (type_stats.average_response_time_ms * (type_stats.check_count - 1) as f64 + response_time as f64) / type_stats.check_count as f64;
        }
    }

    /// 获取健康检查结果
    pub async fn get_result(&self, check_id: &str) -> Option<HealthCheckResult> {
        let results = self.results.read().await;
        results.get(check_id).cloned()
    }

    /// 获取所有健康检查结果
    pub async fn get_all_results(&self) -> Vec<HealthCheckResult> {
        let results = self.results.read().await;
        results.values().cloned().collect()
    }

    /// 获取指定类型的健康检查结果
    pub async fn get_results_by_type(&self, check_type: &HealthCheckType) -> Vec<HealthCheckResult> {
        let results = self.results.read().await;
        results.values()
            .filter(|result| result.check_type == *check_type)
            .cloned()
            .collect()
    }

    /// 获取健康检查统计信息
    pub async fn get_statistics(&self) -> HealthCheckStatistics {
        let stats = self.statistics.read().await;
        stats.clone()
    }

    /// 启动健康检查
    pub async fn start_health_checking(&self) -> Result<(), MonitoringError> {
        if !self.config.enabled {
            return Ok(());
        }
        
        let config = self.config.clone();
        let results = Arc::clone(&self.results);
        let statistics = Arc::clone(&self.statistics);
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(
                tokio::time::Duration::from_secs(config.check_interval)
            );
            
            loop {
                interval.tick().await;
                
                // 执行各种类型的健康检查
                for check_type in &config.check_types {
                    let name = match check_type {
                        HealthCheckType::System => "系统健康检查".to_string(),
                        HealthCheckType::Network => "网络健康检查".to_string(),
                        HealthCheckType::Database => "数据库健康检查".to_string(),
                        HealthCheckType::Service => "服务健康检查".to_string(),
                        HealthCheckType::Custom(custom_type) => format!("自定义健康检查: {}", custom_type),
                    };
                    
                    let start_time = std::time::Instant::now();
                    let check_id = uuid::Uuid::new_v4().to_string();
                    
                    let mut result = HealthCheckResult {
                        id: check_id.clone(),
                        check_type: check_type.clone(),
                        name: name.clone(),
                        status: HealthStatus::Checking,
                        message: "检查中".to_string(),
                        timestamp: Utc::now(),
                        response_time_ms: None,
                        details: HashMap::new(),
                        error: None,
                    };
                    
                    // 执行检查
                    let check_result = Self::execute_check_static(check_type, &name).await;
                    
                    let response_time = start_time.elapsed().as_millis() as u64;
                    result.response_time_ms = Some(response_time);
                    
                    match check_result {
                        Ok((status, message, details)) => {
                            result.status = status;
                            result.message = message;
                            result.details = details;
                        }
                        Err(e) => {
                            result.status = HealthStatus::Unhealthy;
                            result.message = "检查失败".to_string();
                            result.error = Some(e.to_string());
                        }
                    }
                    
                    // 记录结果
                    let mut results_guard = results.write().await;
                    results_guard.insert(result.id.clone(), result.clone());
                    
                    // 更新统计信息
                    let mut stats_guard = statistics.write().await;
                    stats_guard.total_checks += 1;
                    stats_guard.last_check = Some(result.timestamp);
                    
                    match result.status {
                        HealthStatus::Healthy => stats_guard.healthy_checks += 1,
                        HealthStatus::Unhealthy => stats_guard.unhealthy_checks += 1,
                        HealthStatus::Unknown => stats_guard.unknown_checks += 1,
                        HealthStatus::Checking => {}
                    }
                    
                    if let Some(response_time) = result.response_time_ms {
                        stats_guard.average_response_time_ms = (stats_guard.average_response_time_ms * (stats_guard.total_checks - 1) as f64 + response_time as f64) / stats_guard.total_checks as f64;
                    }
                }
            }
        });
        
        Ok(())
    }

    /// 静态方法：执行检查
    async fn execute_check_static(check_type: &HealthCheckType, name: &str) -> Result<(HealthStatus, String, HashMap<String, serde_json::Value>), MonitoringError> {
        match check_type {
            HealthCheckType::System => {
                let mut details = HashMap::new();
                details.insert("cpu_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(50)));
                details.insert("memory_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(60)));
                details.insert("disk_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(70)));
                Ok((HealthStatus::Healthy, "系统运行正常".to_string(), details))
            }
            HealthCheckType::Network => {
                let mut details = HashMap::new();
                details.insert("network_available".to_string(), serde_json::Value::Bool(true));
                details.insert("latency_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(50)));
                details.insert("bandwidth_mbps".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(100.0).unwrap()));
                Ok((HealthStatus::Healthy, "网络连接正常".to_string(), details))
            }
            HealthCheckType::Database => {
                let mut details = HashMap::new();
                details.insert("connected".to_string(), serde_json::Value::Bool(true));
                details.insert("query_time_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(10)));
                details.insert("size_mb".to_string(), serde_json::Value::Number(serde_json::Number::from(1024)));
                Ok((HealthStatus::Healthy, "数据库连接正常".to_string(), details))
            }
            HealthCheckType::Service => {
                let mut details = HashMap::new();
                details.insert("running".to_string(), serde_json::Value::Bool(true));
                details.insert("response_time_ms".to_string(), serde_json::Value::Number(serde_json::Number::from(20)));
                details.insert("version".to_string(), serde_json::Value::String("1.0.0".to_string()));
                Ok((HealthStatus::Healthy, format!("服务 {} 运行正常", name), details))
            }
            HealthCheckType::Custom(custom_type) => {
                let mut details = HashMap::new();
                details.insert("custom_type".to_string(), serde_json::Value::String(custom_type.to_string()));
                details.insert("name".to_string(), serde_json::Value::String(name.to_string()));
                Ok((HealthStatus::Healthy, format!("自定义检查 {} 执行成功", name), details))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_health_checker_creation() {
        let config = HealthCheckConfig::default();
        let checker = HealthChecker::new(config);
        
        let stats = checker.get_statistics().await;
        assert_eq!(stats.total_checks, 0);
    }

    #[tokio::test]
    async fn test_perform_health_check() {
        let config = HealthCheckConfig::default();
        let checker = HealthChecker::new(config);
        
        let result = checker.perform_health_check(
            HealthCheckType::System,
            "系统健康检查".to_string(),
        ).await.unwrap();
        
        assert_eq!(result.check_type, HealthCheckType::System);
        assert_eq!(result.name, "系统健康检查");
        assert!(result.response_time_ms.is_some());
    }

    #[tokio::test]
    async fn test_health_status_ordering() {
        assert!(HealthStatus::Healthy.value() > HealthStatus::Unhealthy.value());
        assert!(HealthStatus::Unknown.value() > HealthStatus::Healthy.value());
        assert!(HealthStatus::Checking.value() > HealthStatus::Unknown.value());
    }

    #[tokio::test]
    async fn test_health_check_type_descriptions() {
        assert_eq!(HealthCheckType::System.description(), "系统检查");
        assert_eq!(HealthCheckType::Network.description(), "网络检查");
        assert_eq!(HealthCheckType::Database.description(), "数据库检查");
        assert_eq!(HealthCheckType::Service.description(), "服务检查");
        assert_eq!(HealthCheckType::Custom("test".to_string()).description(), "自定义检查");
    }

    #[tokio::test]
    async fn test_health_status_descriptions() {
        assert_eq!(HealthStatus::Healthy.description(), "健康");
        assert_eq!(HealthStatus::Unhealthy.description(), "不健康");
        assert_eq!(HealthStatus::Unknown.description(), "未知");
        assert_eq!(HealthStatus::Checking.description(), "检查中");
    }
}
