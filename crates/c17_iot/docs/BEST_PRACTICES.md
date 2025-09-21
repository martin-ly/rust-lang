# c17_iot 最佳实践指南

## 概述

本文档提供了使用 `c17_iot` 库的最佳实践建议，帮助开发者构建高质量、可维护的 IoT 应用程序。

## 架构设计

### 1. 模块化设计

```rust
// 好的设计：清晰的模块分离
use c17_iot::{
    device_management::DeviceManager,
    sensor_network::SensorNetwork,
    edge_computing::RuleEngine,
    security::DeviceAuthenticator,
    monitoring::MonitoringDashboard,
};

// 不好的设计：混合关注点
struct IoTApp {
    devices: Vec<Device>,
    sensors: Vec<Sensor>,
    rules: Vec<Rule>,
    auth: AuthSystem,
    dashboard: Dashboard,
}
```

### 2. 依赖注入

```rust
// 好的设计：使用依赖注入
struct IoTApplication {
    device_manager: DeviceManager,
    sensor_network: SensorNetwork,
    rule_engine: RuleEngine,
    authenticator: DeviceAuthenticator,
}

impl IoTApplication {
    fn new(
        device_manager: DeviceManager,
        sensor_network: SensorNetwork,
        rule_engine: RuleEngine,
        authenticator: DeviceAuthenticator,
    ) -> Self {
        Self {
            device_manager,
            sensor_network,
            rule_engine,
            authenticator,
        }
    }
}

// 不好的设计：硬编码依赖
struct IoTApplication {
    // 直接创建依赖，难以测试和替换
}
```

### 3. 配置管理

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct AppConfig {
    pub device_manager: DeviceManagerConfig,
    pub sensor_network: SensorNetworkConfig,
    pub security: SecurityConfig,
    pub monitoring: MonitoringConfig,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DeviceManagerConfig {
    pub max_devices: usize,
    pub device_timeout: std::time::Duration,
    pub auto_cleanup: bool,
}

impl AppConfig {
    pub fn from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        let config: AppConfig = serde_json::from_str(&content)?;
        Ok(config)
    }
    
    pub fn to_file(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let content = serde_json::to_string_pretty(self)?;
        std::fs::write(path, content)?;
        Ok(())
    }
}
```

## 错误处理

### 1. 统一错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum IoTError {
    #[error("设备管理错误: {0}")]
    DeviceManagement(#[from] c17_iot::device_management::DeviceManagementError),
    
    #[error("传感器网络错误: {0}")]
    SensorNetwork(#[from] c17_iot::sensor_network::SensorNetworkError),
    
    #[error("安全错误: {0}")]
    Security(#[from] c17_iot::security::SecurityError),
    
    #[error("配置错误: {0}")]
    Configuration(String),
    
    #[error("网络错误: {0}")]
    Network(String),
}

pub type IoTResult<T> = Result<T, IoTError>;
```

### 2. 错误传播

```rust
// 好的错误处理
async fn process_sensor_data(
    sensor_network: &mut SensorNetwork,
    device_manager: &mut DeviceManager,
) -> IoTResult<()> {
    let data = sensor_network.get_latest_data("sensor_001").await?;
    
    if data.value > 30.0 {
        let status = device_manager.get_device_status("sensor_001").await?;
        if status.status == DeviceStatus::Active {
            // 处理高温情况
            handle_high_temperature(data.value).await?;
        }
    }
    
    Ok(())
}

// 不好的错误处理
async fn process_sensor_data_bad(
    sensor_network: &mut SensorNetwork,
    device_manager: &mut DeviceManager,
) -> Result<(), Box<dyn std::error::Error>> {
    let data = sensor_network.get_latest_data("sensor_001").await
        .map_err(|e| format!("获取传感器数据失败: {}", e))?;
    
    if data.value > 30.0 {
        let status = device_manager.get_device_status("sensor_001").await
            .map_err(|e| format!("获取设备状态失败: {}", e))?;
        // ...
    }
    
    Ok(())
}
```

### 3. 错误恢复

```rust
use tokio::time::{sleep, Duration};

async fn resilient_operation<F, T>(mut operation: F, max_retries: u32) -> IoTResult<T>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = IoTResult<T>> + Send>>,
{
    let mut retries = 0;
    
    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if retries < max_retries => {
                retries += 1;
                let delay = Duration::from_millis(100 * 2_u64.pow(retries));
                log::warn!("操作失败，{}ms后重试 (第{}次): {}", delay.as_millis(), retries, e);
                sleep(delay).await;
            }
            Err(e) => return Err(e),
        }
    }
}
```

## 资源管理

### 1. 生命周期管理

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct IoTApplication {
    device_manager: Arc<Mutex<DeviceManager>>,
    sensor_network: Arc<Mutex<SensorNetwork>>,
    rule_engine: Arc<Mutex<RuleEngine>>,
    shutdown_tx: tokio::sync::oneshot::Sender<()>,
}

impl IoTApplication {
    pub async fn new() -> Self {
        let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel();
        
        Self {
            device_manager: Arc::new(Mutex::new(DeviceManager::new())),
            sensor_network: Arc::new(Mutex::new(SensorNetwork::new())),
            rule_engine: Arc::new(Mutex::new(RuleEngine::new().0)),
            shutdown_tx,
        }
    }
    
    pub async fn run(&self) -> IoTResult<()> {
        // 启动后台任务
        let device_manager = self.device_manager.clone();
        let sensor_network = self.sensor_network.clone();
        let rule_engine = self.rule_engine.clone();
        
        tokio::spawn(async move {
            loop {
                // 处理设备管理任务
                if let Ok(mut dm) = device_manager.lock().await {
                    // 执行设备管理操作
                }
                
                tokio::time::sleep(Duration::from_secs(1)).await;
            }
        });
        
        // 等待关闭信号
        Ok(())
    }
    
    pub fn shutdown(self) {
        let _ = self.shutdown_tx.send(());
    }
}

impl Drop for IoTApplication {
    fn drop(&mut self) {
        log::info!("IoT应用正在关闭...");
        // 清理资源
    }
}
```

### 2. 内存管理

```rust
use std::collections::HashMap;

// 好的设计：使用适当的数据结构
pub struct DataBuffer {
    data: HashMap<String, Vec<DataPoint>>,
    max_size: usize,
}

impl DataBuffer {
    pub fn new(max_size: usize) -> Self {
        Self {
            data: HashMap::new(),
            max_size,
        }
    }
    
    pub fn add_data(&mut self, device_id: String, data_point: DataPoint) {
        let buffer = self.data.entry(device_id).or_insert_with(Vec::new);
        buffer.push(data_point);
        
        // 保持缓冲区大小限制
        if buffer.len() > self.max_size {
            buffer.drain(0..buffer.len() - self.max_size);
        }
    }
    
    pub fn get_latest_data(&self, device_id: &str) -> Option<&DataPoint> {
        self.data.get(device_id)?.last()
    }
}

// 不好的设计：无限制的内存使用
pub struct BadDataBuffer {
    data: Vec<DataPoint>, // 会无限增长
}
```

### 3. 连接池管理

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

pub struct ConnectionPool {
    semaphore: Arc<Semaphore>,
    max_connections: usize,
}

impl ConnectionPool {
    pub fn new(max_connections: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_connections)),
            max_connections,
        }
    }
    
    pub async fn acquire(&self) -> ConnectionGuard {
        let permit = self.semaphore.acquire().await.unwrap();
        ConnectionGuard { permit }
    }
}

pub struct ConnectionGuard {
    permit: tokio::sync::SemaphorePermit,
}

impl Drop for ConnectionGuard {
    fn drop(&mut self) {
        // 自动释放连接
    }
}
```

## 性能优化

### 1. 异步编程

```rust
// 好的设计：并发处理
async fn process_multiple_sensors(
    sensor_network: &mut SensorNetwork,
    device_ids: Vec<String>,
) -> IoTResult<Vec<SensorData>> {
    let futures: Vec<_> = device_ids
        .into_iter()
        .map(|device_id| {
            let mut sensor_network = sensor_network.clone();
            async move {
                sensor_network.get_latest_data(&device_id).await
            }
        })
        .collect();
    
    let results = futures::future::join_all(futures).await;
    
    // 处理结果
    let mut sensor_data = Vec::new();
    for result in results {
        match result {
            Ok(data) => sensor_data.push(data),
            Err(e) => log::warn!("获取传感器数据失败: {}", e),
        }
    }
    
    Ok(sensor_data)
}

// 不好的设计：顺序处理
async fn process_multiple_sensors_bad(
    sensor_network: &mut SensorNetwork,
    device_ids: Vec<String>,
) -> IoTResult<Vec<SensorData>> {
    let mut sensor_data = Vec::new();
    
    for device_id in device_ids {
        let data = sensor_network.get_latest_data(&device_id).await?;
        sensor_data.push(data);
    }
    
    Ok(sensor_data)
}
```

### 2. 批处理操作

```rust
// 好的设计：批量操作
pub struct BatchProcessor {
    batch_size: usize,
    buffer: Vec<DataPoint>,
}

impl BatchProcessor {
    pub fn new(batch_size: usize) -> Self {
        Self {
            batch_size,
            buffer: Vec::with_capacity(batch_size),
        }
    }
    
    pub async fn add_data(&mut self, data_point: DataPoint) -> IoTResult<()> {
        self.buffer.push(data_point);
        
        if self.buffer.len() >= self.batch_size {
            self.flush().await?;
        }
        
        Ok(())
    }
    
    pub async fn flush(&mut self) -> IoTResult<()> {
        if !self.buffer.is_empty() {
            // 批量处理数据
            self.process_batch(std::mem::take(&mut self.buffer)).await?;
        }
        Ok(())
    }
    
    async fn process_batch(&self, batch: Vec<DataPoint>) -> IoTResult<()> {
        // 批量处理逻辑
        Ok(())
    }
}

// 不好的设计：单个处理
pub struct SingleProcessor;

impl SingleProcessor {
    pub async fn add_data(&self, data_point: DataPoint) -> IoTResult<()> {
        // 每次单独处理，效率低
        self.process_single(data_point).await?;
        Ok(())
    }
}
```

### 3. 缓存策略

```rust
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct Cache<T> {
    data: HashMap<String, CacheEntry<T>>,
    ttl: Duration,
}

struct CacheEntry<T> {
    value: T,
    created_at: Instant,
}

impl<T> Cache<T> {
    pub fn new(ttl: Duration) -> Self {
        Self {
            data: HashMap::new(),
            ttl,
        }
    }
    
    pub fn get(&mut self, key: &str) -> Option<&T> {
        if let Some(entry) = self.data.get(key) {
            if entry.created_at.elapsed() < self.ttl {
                return Some(&entry.value);
            } else {
                self.data.remove(key);
            }
        }
        None
    }
    
    pub fn set(&mut self, key: String, value: T) {
        self.data.insert(key, CacheEntry {
            value,
            created_at: Instant::now(),
        });
    }
    
    pub fn cleanup_expired(&mut self) {
        self.data.retain(|_, entry| entry.created_at.elapsed() < self.ttl);
    }
}
```

## 安全最佳实践

### 1. 输入验证

```rust
use regex::Regex;

pub struct InputValidator {
    device_id_pattern: Regex,
    sensor_type_pattern: Regex,
}

impl InputValidator {
    pub fn new() -> Self {
        Self {
            device_id_pattern: Regex::new(r"^[a-zA-Z0-9_-]{1,64}$").unwrap(),
            sensor_type_pattern: Regex::new(r"^[a-zA-Z0-9_-]{1,32}$").unwrap(),
        }
    }
    
    pub fn validate_device_id(&self, device_id: &str) -> IoTResult<()> {
        if !self.device_id_pattern.is_match(device_id) {
            return Err(IoTError::Configuration(
                "设备ID格式无效".to_string()
            ));
        }
        Ok(())
    }
    
    pub fn validate_sensor_type(&self, sensor_type: &str) -> IoTResult<()> {
        if !self.sensor_type_pattern.is_match(sensor_type) {
            return Err(IoTError::Configuration(
                "传感器类型格式无效".to_string()
            ));
        }
        Ok(())
    }
}

// 使用验证器
pub async fn register_device_safe(
    device_manager: &mut DeviceManager,
    validator: &InputValidator,
    device_id: &str,
    device_type: &str,
    location: &str,
) -> IoTResult<()> {
    // 验证输入
    validator.validate_device_id(device_id)?;
    validator.validate_sensor_type(device_type)?;
    
    // 执行操作
    device_manager.register_device(device_id, device_type, location).await?;
    
    Ok(())
}
```

### 2. 安全配置

```rust
use std::env;

pub struct SecurityConfig {
    pub enable_tls: bool,
    pub cert_path: Option<String>,
    pub key_path: Option<String>,
    pub ca_cert_path: Option<String>,
    pub token_secret: String,
    pub session_timeout: Duration,
}

impl SecurityConfig {
    pub fn from_env() -> Self {
        Self {
            enable_tls: env::var("ENABLE_TLS").unwrap_or_default() == "true",
            cert_path: env::var("CERT_PATH").ok(),
            key_path: env::var("KEY_PATH").ok(),
            ca_cert_path: env::var("CA_CERT_PATH").ok(),
            token_secret: env::var("TOKEN_SECRET")
                .unwrap_or_else(|_| "default_secret".to_string()),
            session_timeout: Duration::from_secs(
                env::var("SESSION_TIMEOUT")
                    .unwrap_or_default()
                    .parse()
                    .unwrap_or(3600)
            ),
        }
    }
    
    pub fn validate(&self) -> IoTResult<()> {
        if self.enable_tls {
            if self.cert_path.is_none() || self.key_path.is_none() {
                return Err(IoTError::Configuration(
                    "启用TLS时必须提供证书和密钥路径".to_string()
                ));
            }
        }
        
        if self.token_secret == "default_secret" {
            log::warn!("使用默认令牌密钥，生产环境中应使用强密钥");
        }
        
        Ok(())
    }
}
```

### 3. 审计日志

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct AuditLog {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub user_id: Option<String>,
    pub device_id: Option<String>,
    pub action: String,
    pub resource: String,
    pub result: AuditResult,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
    pub details: HashMap<String, String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub enum AuditResult {
    Success,
    Failure,
    Error,
}

pub struct AuditLogger {
    logs: Vec<AuditLog>,
    max_logs: usize,
}

impl AuditLogger {
    pub fn new(max_logs: usize) -> Self {
        Self {
            logs: Vec::with_capacity(max_logs),
            max_logs,
        }
    }
    
    pub fn log(&mut self, log: AuditLog) {
        self.logs.push(log);
        
        // 保持日志数量限制
        if self.logs.len() > self.max_logs {
            self.logs.drain(0..self.logs.len() - self.max_logs);
        }
    }
    
    pub fn export_logs(&self) -> Vec<AuditLog> {
        self.logs.clone()
    }
}
```

## 监控和可观测性

### 1. 指标收集

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

pub struct Metrics {
    pub devices_registered: AtomicU64,
    pub sensors_active: AtomicU64,
    pub rules_evaluated: AtomicU64,
    pub errors_total: AtomicU64,
    pub requests_total: AtomicU64,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            devices_registered: AtomicU64::new(0),
            sensors_active: AtomicU64::new(0),
            rules_evaluated: AtomicU64::new(0),
            errors_total: AtomicU64::new(0),
            requests_total: AtomicU64::new(0),
        }
    }
    
    pub fn increment_devices_registered(&self) {
        self.devices_registered.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn increment_sensors_active(&self) {
        self.sensors_active.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn increment_rules_evaluated(&self) {
        self.rules_evaluated.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn increment_errors(&self) {
        self.errors_total.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn increment_requests(&self) {
        self.requests_total.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn get_metrics(&self) -> HashMap<String, u64> {
        let mut metrics = HashMap::new();
        metrics.insert("devices_registered".to_string(), self.devices_registered.load(Ordering::Relaxed));
        metrics.insert("sensors_active".to_string(), self.sensors_active.load(Ordering::Relaxed));
        metrics.insert("rules_evaluated".to_string(), self.rules_evaluated.load(Ordering::Relaxed));
        metrics.insert("errors_total".to_string(), self.errors_total.load(Ordering::Relaxed));
        metrics.insert("requests_total".to_string(), self.requests_total.load(Ordering::Relaxed));
        metrics
    }
}
```

### 2. 健康检查

```rust
pub struct HealthChecker {
    components: HashMap<String, Box<dyn HealthCheckable>>,
}

pub trait HealthCheckable: Send + Sync {
    async fn health_check(&self) -> HealthStatus;
}

#[derive(Debug, Clone)]
pub struct HealthStatus {
    pub status: HealthState,
    pub message: String,
    pub details: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub enum HealthState {
    Healthy,
    Degraded,
    Unhealthy,
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {
            components: HashMap::new(),
        }
    }
    
    pub fn register_component(&mut self, name: String, component: Box<dyn HealthCheckable>) {
        self.components.insert(name, component);
    }
    
    pub async fn check_all(&self) -> HashMap<String, HealthStatus> {
        let mut results = HashMap::new();
        
        for (name, component) in &self.components {
            let status = component.health_check().await;
            results.insert(name.clone(), status);
        }
        
        results
    }
    
    pub async fn overall_health(&self) -> HealthState {
        let results = self.check_all().await;
        
        let mut has_unhealthy = false;
        let mut has_degraded = false;
        
        for (_, status) in results {
            match status.status {
                HealthState::Unhealthy => has_unhealthy = true,
                HealthState::Degraded => has_degraded = true,
                HealthState::Healthy => {}
            }
        }
        
        if has_unhealthy {
            HealthState::Unhealthy
        } else if has_degraded {
            HealthState::Degraded
        } else {
            HealthState::Healthy
        }
    }
}
```

### 3. 日志记录

```rust
use log::{info, warn, error, debug};
use env_logger;

pub fn setup_logging() {
    env_logger::Builder::from_default_env()
        .filter_level(log::LevelFilter::Info)
        .format(|buf, record| {
            writeln!(
                buf,
                "{} [{}] {}: {}",
                chrono::Utc::now().format("%Y-%m-%d %H:%M:%S%.3f"),
                record.level(),
                record.target(),
                record.args()
            )
        })
        .init();
}

// 结构化日志
pub struct StructuredLogger;

impl StructuredLogger {
    pub fn log_device_event(
        device_id: &str,
        event_type: &str,
        details: HashMap<String, String>,
    ) {
        let log_data = serde_json::json!({
            "device_id": device_id,
            "event_type": event_type,
            "timestamp": chrono::Utc::now(),
            "details": details
        });
        
        info!("device_event: {}", log_data);
    }
    
    pub fn log_sensor_data(
        sensor_id: &str,
        value: f64,
        unit: &str,
    ) {
        let log_data = serde_json::json!({
            "sensor_id": sensor_id,
            "value": value,
            "unit": unit,
            "timestamp": chrono::Utc::now()
        });
        
        debug!("sensor_data: {}", log_data);
    }
    
    pub fn log_rule_evaluation(
        rule_id: &str,
        triggered: bool,
        context: HashMap<String, String>,
    ) {
        let log_data = serde_json::json!({
            "rule_id": rule_id,
            "triggered": triggered,
            "context": context,
            "timestamp": chrono::Utc::now()
        });
        
        info!("rule_evaluation: {}", log_data);
    }
}
```

## 测试策略

### 1. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;

    #[tokio::test]
    async fn test_device_registration() {
        let mut device_manager = DeviceManager::new();
        
        // 测试正常注册
        let result = device_manager.register_device("device_001", "sensor", "room1").await;
        assert!(result.is_ok());
        
        // 测试重复注册
        let result = device_manager.register_device("device_001", "sensor", "room1").await;
        assert!(matches!(result, Err(DeviceManagementError::DeviceAlreadyExists)));
    }
    
    #[test]
    fn test_input_validation() {
        let validator = InputValidator::new();
        
        // 测试有效输入
        assert!(validator.validate_device_id("device_001").is_ok());
        assert!(validator.validate_sensor_type("temperature").is_ok());
        
        // 测试无效输入
        assert!(validator.validate_device_id("").is_err());
        assert!(validator.validate_device_id("device with spaces").is_err());
    }
}
```

### 2. 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;

    #[tokio::test]
    async fn test_complete_workflow() {
        // 设置测试环境
        let mut device_manager = DeviceManager::new();
        let mut sensor_network = SensorNetwork::new();
        let (mut rule_engine, _) = RuleEngine::new();
        
        // 注册设备
        device_manager.register_device("sensor_001", "temperature", "room1").await.unwrap();
        
        // 添加传感器
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        
        // 添加规则
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new("temp_alert".to_string(), "温度告警".to_string(), condition, action, 1);
        rule_engine.add_rule(rule).await.unwrap();
        
        // 开始数据采集
        sensor_network.start_data_collection().await.unwrap();
        
        // 等待数据采集
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 验证数据
        let data = sensor_network.get_latest_data("sensor_001").await.unwrap();
        assert!(data.value.is_finite());
        
        // 验证规则评估
        let context = RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(data.value).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results = rule_engine.evaluate_rules(context).await.unwrap();
        if data.value > 30.0 {
            assert_eq!(results.len(), 1);
        } else {
            assert_eq!(results.len(), 0);
        }
    }
}
```

### 3. 性能测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[tokio::test]
    async fn test_device_registration_performance() {
        let mut device_manager = DeviceManager::new();
        
        let start = Instant::now();
        
        // 批量注册设备
        for i in 0..1000 {
            device_manager.register_device(
                &format!("device_{}", i),
                "sensor",
                "room1"
            ).await.unwrap();
        }
        
        let duration = start.elapsed();
        println!("注册1000个设备耗时: {:?}", duration);
        
        // 验证性能要求
        assert!(duration.as_secs() < 1);
    }
    
    #[tokio::test]
    async fn test_concurrent_operations() {
        let device_manager = Arc::new(Mutex::new(DeviceManager::new()));
        
        let start = Instant::now();
        
        // 并发注册设备
        let futures: Vec<_> = (0..100)
            .map(|i| {
                let device_manager = device_manager.clone();
                async move {
                    let mut dm = device_manager.lock().await;
                    dm.register_device(
                        &format!("device_{}", i),
                        "sensor",
                        "room1"
                    ).await
                }
            })
            .collect();
        
        let results = futures::future::join_all(futures).await;
        
        let duration = start.elapsed();
        println!("并发注册100个设备耗时: {:?}", duration);
        
        // 验证所有操作都成功
        for result in results {
            assert!(result.is_ok());
        }
        
        // 验证性能要求
        assert!(duration.as_secs() < 1);
    }
}
```

## 部署和运维

### 1. 容器化

```dockerfile
# Dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bullseye-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/c17_iot /usr/local/bin/c17_iot
EXPOSE 8080
CMD ["c17_iot"]
```

### 2. 配置管理

```yaml
# docker-compose.yml
version: '3.8'
services:
  c17_iot:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - ENABLE_TLS=true
      - CERT_PATH=/certs/server.crt
      - KEY_PATH=/certs/server.key
    volumes:
      - ./config:/app/config
      - ./certs:/certs
    depends_on:
      - redis
      - postgres
  
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
  
  postgres:
    image: postgres:15-alpine
    environment:
      - POSTGRES_DB=c17_iot
      - POSTGRES_USER=c17_iot
      - POSTGRES_PASSWORD=password
    volumes:
      - postgres_data:/var/lib/postgresql/data

volumes:
  postgres_data:
```

### 3. 监控配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'c17_iot'
    static_configs:
      - targets: ['c17_iot:8080']
    metrics_path: '/metrics'
    scrape_interval: 5s
```

## 总结

本最佳实践指南涵盖了使用 `c17_iot` 库的关键方面：

1. **架构设计** - 模块化、依赖注入、配置管理
2. **错误处理** - 统一错误处理、错误传播、错误恢复
3. **资源管理** - 生命周期管理、内存管理、连接池
4. **性能优化** - 异步编程、批处理、缓存策略
5. **安全最佳实践** - 输入验证、安全配置、审计日志
6. **监控和可观测性** - 指标收集、健康检查、日志记录
7. **测试策略** - 单元测试、集成测试、性能测试
8. **部署和运维** - 容器化、配置管理、监控配置

遵循这些最佳实践可以帮助开发者构建高质量、可维护、高性能的 IoT 应用程序。
