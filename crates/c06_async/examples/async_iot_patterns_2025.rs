use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, broadcast, mpsc};
use tokio::time::sleep;
use tracing::{debug, error, info, warn};
//use std::sync::atomic::{AtomicUsize, AtomicU64, AtomicBool, Ordering};

/// 2025年异步物联网模式演示
/// 展示最新的物联网异步编程模式和最佳实践

/// 1. 异步物联网设备管理器
#[derive(Debug, Clone)]
pub struct AsyncIoTDeviceManager {
    devices: Arc<RwLock<HashMap<String, IoTDevice>>>,
    device_groups: Arc<RwLock<HashMap<String, DeviceGroup>>>,
    device_stats: Arc<RwLock<DeviceManagerStats>>,
    event_broadcaster: broadcast::Sender<DeviceEvent>,
    command_sender: mpsc::UnboundedSender<DeviceCommand>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IoTDevice {
    pub id: String,
    pub name: String,
    pub device_type: DeviceType,
    pub location: String,
    pub status: DeviceStatus,
    pub capabilities: Vec<DeviceCapability>,
    pub last_seen: u64,
    pub battery_level: Option<f32>,
    pub firmware_version: String,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DeviceType {
    Sensor,
    Actuator,
    Camera,
    Gateway,
    Controller,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DeviceStatus {
    Online,
    Offline,
    Error,
    Maintenance,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceCapability {
    pub name: String,
    pub data_type: String,
    pub unit: Option<String>,
    pub min_value: Option<f64>,
    pub max_value: Option<f64>,
}

#[derive(Debug, Clone)]
pub struct DeviceGroup {
    pub id: String,
    pub name: String,
    pub description: String,
    pub device_ids: Vec<String>,
    pub rules: Vec<GroupRule>,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub struct GroupRule {
    pub id: String,
    pub condition: RuleCondition,
    pub action: RuleAction,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum RuleCondition {
    DeviceStatus(String, DeviceStatus),
    SensorValue(String, String, f64, ComparisonOp),
    BatteryLevel(String, f32, ComparisonOp),
    TimeRange(u8, u8), // 小时范围
}

#[derive(Debug, Clone)]
pub enum RuleAction {
    SendNotification(String),
    ControlDevice(String, String, String), // device_id, command, value
    TriggerScene(String),
    LogEvent(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ComparisonOp {
    GreaterThan,
    LessThan,
    Equal,
    NotEqual,
}

#[derive(Debug, Clone)]
pub enum DeviceEvent {
    DeviceOnline(String),
    DeviceOffline(String),
    SensorDataReceived(String, SensorData),
    DeviceError(String, String),
    BatteryLow(String, f32),
    CommandExecuted(String, String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorData {
    pub sensor_id: String,
    pub data_type: String,
    pub value: f64,
    pub unit: Option<String>,
    pub timestamp: u64,
    pub quality: DataQuality,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DataQuality {
    Good,
    Warning,
    Error,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct DeviceCommand {
    pub device_id: String,
    pub command: String,
    pub parameters: HashMap<String, String>,
    pub priority: CommandPriority,
    pub timeout: Duration,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CommandPriority {
    Low,
    Normal,
    High,
    Critical,
}

#[derive(Debug, Clone, Default)]
pub struct DeviceManagerStats {
    pub total_devices: usize,
    pub online_devices: usize,
    pub offline_devices: usize,
    pub error_devices: usize,
    pub total_groups: usize,
    pub commands_sent: usize,
    pub commands_executed: usize,
    pub events_processed: usize,
}

impl AsyncIoTDeviceManager {
    pub fn new() -> Self {
        let (event_broadcaster, _) = broadcast::channel(1000);
        let (command_sender, mut command_receiver) = mpsc::unbounded_channel();

        let manager = Self {
            devices: Arc::new(RwLock::new(HashMap::new())),
            device_groups: Arc::new(RwLock::new(HashMap::new())),
            device_stats: Arc::new(RwLock::new(DeviceManagerStats::default())),
            event_broadcaster: event_broadcaster.clone(),
            command_sender,
        };

        // 启动命令处理任务
        let manager_clone = manager.clone();
        tokio::spawn(async move {
            while let Some(command) = command_receiver.recv().await {
                if let Err(e) = manager_clone.execute_device_command(command).await {
                    error!("设备命令执行失败: {}", e);
                }
            }
        });

        manager
    }

    pub async fn register_device(&self, device: IoTDevice) -> Result<()> {
        let mut devices = self.devices.write().await;
        devices.insert(device.id.clone(), device.clone());

        let mut stats = self.device_stats.write().await;
        stats.total_devices += 1;
        if device.status == DeviceStatus::Online {
            stats.online_devices += 1;
        }

        // 广播设备上线事件
        let _ = self
            .event_broadcaster
            .send(DeviceEvent::DeviceOnline(device.id.clone()));

        info!("注册IoT设备: {} ({})", device.name, device.id);
        Ok(())
    }

    pub async fn create_device_group(&self, group: DeviceGroup) -> Result<()> {
        let mut groups = self.device_groups.write().await;
        groups.insert(group.id.clone(), group.clone());

        let mut stats = self.device_stats.write().await;
        stats.total_groups += 1;

        info!("创建设备组: {} ({})", group.name, group.id);
        Ok(())
    }

    pub async fn send_device_command(&self, command: DeviceCommand) -> Result<()> {
        let _ = self.command_sender.send(command.clone());

        let mut stats = self.device_stats.write().await;
        stats.commands_sent += 1;

        info!("发送设备命令: {} -> {}", command.device_id, command.command);
        Ok(())
    }

    async fn execute_device_command(&self, command: DeviceCommand) -> Result<()> {
        let mut devices = self.devices.write().await;
        if let Some(device) = devices.get_mut(&command.device_id) {
            // 模拟命令执行
            sleep(Duration::from_millis(100)).await;

            device.last_seen = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();

            // 广播命令执行事件
            let _ = self.event_broadcaster.send(DeviceEvent::CommandExecuted(
                command.device_id.clone(),
                command.command.clone(),
            ));

            let mut stats = self.device_stats.write().await;
            stats.commands_executed += 1;

            info!(
                "设备命令执行成功: {} -> {}",
                command.device_id, command.command
            );
        } else {
            return Err(anyhow::anyhow!("设备 {} 未找到", command.device_id));
        }

        Ok(())
    }

    pub async fn process_sensor_data(&self, data: SensorData) -> Result<()> {
        // 广播传感器数据事件
        let _ = self.event_broadcaster.send(DeviceEvent::SensorDataReceived(
            data.sensor_id.clone(),
            data.clone(),
        ));

        // 处理设备组规则
        self.process_group_rules(&data).await;

        let mut stats = self.device_stats.write().await;
        stats.events_processed += 1;

        debug!("处理传感器数据: {} = {}", data.sensor_id, data.value);
        Ok(())
    }

    #[allow(unused_variables)]
    async fn process_group_rules(&self, sensor_data: &SensorData) {
        let groups = self.device_groups.read().await;
        let devices = self.devices.read().await;

        for group in groups.values() {
            for rule in &group.rules {
                if !rule.enabled {
                    continue;
                }

                let should_trigger = match &rule.condition {
                    RuleCondition::SensorValue(device_id, data_type, threshold, op) => {
                        if device_id == &sensor_data.sensor_id
                            && data_type == &sensor_data.data_type
                        {
                            match op {
                                ComparisonOp::GreaterThan => sensor_data.value > *threshold,
                                ComparisonOp::LessThan => sensor_data.value < *threshold,
                                ComparisonOp::Equal => (sensor_data.value - threshold).abs() < 0.01,
                                ComparisonOp::NotEqual => {
                                    (sensor_data.value - threshold).abs() >= 0.01
                                }
                            }
                        } else {
                            false
                        }
                    }
                    _ => false,
                };

                if should_trigger {
                    self.execute_rule_action(&rule.action).await;
                    info!("触发规则: {} 在组 {}", rule.id, group.name);
                }
            }
        }
    }

    #[allow(unused_variables)]
    async fn execute_rule_action(&self, action: &RuleAction) {
        match action {
            RuleAction::SendNotification(message) => {
                info!("发送通知: {}", message);
            }
            RuleAction::ControlDevice(device_id, command, value) => {
                let cmd = DeviceCommand {
                    device_id: device_id.clone(),
                    command: command.clone(),
                    parameters: [("value".to_string(), value.clone())]
                        .iter()
                        .cloned()
                        .collect(),
                    priority: CommandPriority::Normal,
                    timeout: Duration::from_secs(30),
                };
                let _ = self.send_device_command(cmd).await;
            }
            RuleAction::TriggerScene(scene_id) => {
                info!("触发场景: {}", scene_id);
            }
            RuleAction::LogEvent(message) => {
                info!("记录事件: {}", message);
            }
        }
    }

    pub async fn get_device_stats(&self) -> DeviceManagerStats {
        self.device_stats.read().await.clone()
    }

    pub async fn get_online_devices(&self) -> Vec<IoTDevice> {
        let devices = self.devices.read().await;
        devices
            .values()
            .filter(|device| device.status == DeviceStatus::Online)
            .cloned()
            .collect()
    }
}

/// 2. 异步物联网数据处理管道
#[derive(Debug, Clone)]
pub struct AsyncIoTDataPipeline {
    data_processors: Arc<RwLock<Vec<DataProcessor>>>,
    data_queue: Arc<RwLock<Vec<SensorData>>>,
    processed_data: Arc<RwLock<Vec<ProcessedData>>>,
    pipeline_stats: Arc<RwLock<PipelineStats>>,
}

#[derive(Debug, Clone)]
pub struct DataProcessor {
    pub id: String,
    pub name: String,
    pub processor_type: ProcessorType,
    pub config: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub enum ProcessorType {
    Filter,
    Aggregator,
    Transformer,
    Validator,
    Analyzer,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessedData {
    pub id: String,
    pub original_data: SensorData,
    pub processed_value: f64,
    pub processing_steps: Vec<String>,
    pub timestamp: u64,
    pub confidence: f32,
}

#[derive(Debug, Clone, Default)]
pub struct PipelineStats {
    pub total_processed: usize,
    pub successful_processing: usize,
    pub failed_processing: usize,
    pub average_processing_time: Duration,
}

impl AsyncIoTDataPipeline {
    pub fn new() -> Self {
        Self {
            data_processors: Arc::new(RwLock::new(Vec::new())),
            data_queue: Arc::new(RwLock::new(Vec::new())),
            processed_data: Arc::new(RwLock::new(Vec::new())),
            pipeline_stats: Arc::new(RwLock::new(PipelineStats::default())),
        }
    }

    pub async fn add_processor(&self, processor: DataProcessor) -> Result<()> {
        let mut processors = self.data_processors.write().await;
        processors.push(processor.clone());
        info!("添加数据处理器: {} ({})", processor.name, processor.id);
        Ok(())
    }

    pub async fn process_sensor_data(&self, data: SensorData) -> Result<ProcessedData> {
        let start_time = Instant::now();

        // 添加到队列
        {
            let mut queue = self.data_queue.write().await;
            queue.push(data.clone());
        }

        // 获取处理器
        let processors = self.data_processors.read().await;
        let mut current_value = data.value;
        let mut processing_steps = Vec::new();

        // 按顺序处理数据
        for processor in processors.iter() {
            current_value = self
                .execute_processor(processor, current_value, &data)
                .await?;
            processing_steps.push(format!("{}: {}", processor.name, current_value));
        }

        let processing_time = start_time.elapsed();

        // 创建处理后的数据
        let processed_data = ProcessedData {
            id: format!(
                "processed_{}",
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ),
            original_data: data.clone(),
            processed_value: current_value,
            processing_steps,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            confidence: self.calculate_confidence(&data, current_value),
        };

        // 保存处理后的数据
        {
            let mut processed = self.processed_data.write().await;
            processed.push(processed_data.clone());
        }

        // 更新统计
        let mut stats = self.pipeline_stats.write().await;
        stats.total_processed += 1;
        stats.successful_processing += 1;
        stats.average_processing_time = Duration::from_millis(
            ((stats.average_processing_time.as_millis() + processing_time.as_millis()) / 2) as u64,
        );

        info!(
            "数据处理完成: {} -> {:.2}",
            data.sensor_id, processed_data.processed_value
        );
        Ok(processed_data)
    }

    async fn execute_processor(
        &self,
        processor: &DataProcessor,
        input_value: f64,
        original_data: &SensorData,
    ) -> Result<f64> {
        sleep(Duration::from_millis(10)).await;

        match processor.processor_type {
            ProcessorType::Filter => {
                // 简单的过滤逻辑
                if let Some(min_value) = processor.config.get("min_value") {
                    let min: f64 = min_value.parse().unwrap_or(f64::NEG_INFINITY);
                    if input_value < min {
                        return Ok(f64::NAN);
                    }
                }
                if let Some(max_value) = processor.config.get("max_value") {
                    let max: f64 = max_value.parse().unwrap_or(f64::INFINITY);
                    if input_value > max {
                        return Ok(f64::NAN);
                    }
                }
                Ok(input_value)
            }
            ProcessorType::Aggregator => {
                // 简单的聚合逻辑
                if let Some(aggregation_type) = processor.config.get("type") {
                    match aggregation_type.as_str() {
                        "moving_average" => {
                            // 模拟移动平均
                            Ok(input_value * 0.8 + original_data.value * 0.2)
                        }
                        "sum" => Ok(input_value + original_data.value),
                        _ => Ok(input_value),
                    }
                } else {
                    Ok(input_value)
                }
            }
            ProcessorType::Transformer => {
                // 简单的转换逻辑
                if let Some(transform_type) = processor.config.get("type") {
                    match transform_type.as_str() {
                        "scale" => {
                            let factor: f64 = processor
                                .config
                                .get("factor")
                                .and_then(|s| s.parse().ok())
                                .unwrap_or(1.0);
                            Ok(input_value * factor)
                        }
                        "offset" => {
                            let offset: f64 = processor
                                .config
                                .get("offset")
                                .and_then(|s| s.parse().ok())
                                .unwrap_or(0.0);
                            Ok(input_value + offset)
                        }
                        _ => Ok(input_value),
                    }
                } else {
                    Ok(input_value)
                }
            }
            ProcessorType::Validator => {
                // 简单的验证逻辑
                if input_value.is_nan() || input_value.is_infinite() {
                    Err(anyhow::anyhow!("无效的数据值"))
                } else {
                    Ok(input_value)
                }
            }
            ProcessorType::Analyzer => {
                // 简单的分析逻辑
                Ok(input_value.abs())
            }
        }
    }

    fn calculate_confidence(&self, original_data: &SensorData, processed_value: f64) -> f32 {
        // 简化的置信度计算
        let quality_factor = match original_data.quality {
            DataQuality::Good => 1.0,
            DataQuality::Warning => 0.8,
            DataQuality::Error => 0.3,
            DataQuality::Unknown => 0.5,
        };

        let processing_factor = if processed_value.is_nan() || processed_value.is_infinite() {
            0.0
        } else {
            1.0
        };

        (quality_factor * processing_factor) as f32
    }

    pub async fn get_pipeline_stats(&self) -> PipelineStats {
        self.pipeline_stats.read().await.clone()
    }
}

/// 3. 异步物联网监控和告警系统
#[derive(Debug, Clone)]
pub struct AsyncIoTSurveillanceSystem {
    alerts: Arc<RwLock<Vec<Alert>>>,
    alert_rules: Arc<RwLock<Vec<AlertRule>>>,
    surveillance_stats: Arc<RwLock<SurveillanceStats>>,
    alert_sender: mpsc::UnboundedSender<Alert>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    pub id: String,
    pub severity: AlertSeverity,
    pub message: String,
    pub device_id: String,
    pub alert_type: AlertType,
    pub timestamp: u64,
    pub acknowledged: bool,
    pub resolved: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AlertSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AlertType {
    DeviceOffline,
    SensorAnomaly,
    BatteryLow,
    TemperatureHigh,
    SecurityBreach,
    PerformanceIssue,
}

#[derive(Debug, Clone)]
pub struct AlertRule {
    pub id: String,
    pub name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
    pub enabled: bool,
    pub cooldown: Duration,
    pub last_triggered: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum AlertCondition {
    DeviceOfflineFor(Duration),
    SensorValueOutOfRange(String, f64, f64),
    BatteryBelow(f32),
    TemperatureAbove(f64),
    MultipleFailures(usize),
}

#[derive(Debug, Clone, Default)]
pub struct SurveillanceStats {
    pub total_alerts: usize,
    pub active_alerts: usize,
    pub acknowledged_alerts: usize,
    pub resolved_alerts: usize,
    pub critical_alerts: usize,
}

impl AsyncIoTSurveillanceSystem {
    pub fn new() -> Self {
        let (alert_sender, mut alert_receiver) = mpsc::unbounded_channel();

        let system = Self {
            alerts: Arc::new(RwLock::new(Vec::new())),
            alert_rules: Arc::new(RwLock::new(Vec::new())),
            surveillance_stats: Arc::new(RwLock::new(SurveillanceStats::default())),
            alert_sender,
        };

        // 启动告警处理任务
        let system_clone = system.clone();
        tokio::spawn(async move {
            while let Some(alert) = alert_receiver.recv().await {
                if let Err(e) = system_clone.process_alert(alert).await {
                    error!("告警处理失败: {}", e);
                }
            }
        });

        system
    }

    pub async fn add_alert_rule(&self, rule: AlertRule) -> Result<()> {
        let mut rules = self.alert_rules.write().await;
        rules.push(rule.clone());
        info!("添加告警规则: {}", rule.name);
        Ok(())
    }

    pub async fn check_device_status(&self, device_id: &str, status: DeviceStatus, last_seen: u64) {
        let rules = self.alert_rules.read().await;

        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }

            // 检查冷却期
            if let Some(last_triggered) = rule.last_triggered {
                if last_triggered.elapsed() < rule.cooldown {
                    continue;
                }
            }

            let should_alert = match &rule.condition {
                AlertCondition::DeviceOfflineFor(duration) => {
                    status == DeviceStatus::Offline
                        && (std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            - last_seen)
                            > duration.as_secs()
                }
                _ => false,
            };

            if should_alert {
                let alert = Alert {
                    id: format!("alert_{}", Instant::now().elapsed().as_nanos()),
                    severity: rule.severity.clone(),
                    message: format!("设备 {} 离线超过 {:?}", device_id, rule.cooldown),
                    device_id: device_id.to_string(),
                    alert_type: AlertType::DeviceOffline,
                    timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                    acknowledged: false,
                    resolved: false,
                };

                let _ = self.alert_sender.send(alert);
            }
        }
    }

    pub async fn check_sensor_data(&self, sensor_data: &SensorData) {
        let rules = self.alert_rules.read().await;

        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }

            let should_alert = match &rule.condition {
                AlertCondition::SensorValueOutOfRange(sensor_id, min, max) => {
                    sensor_id == &sensor_data.sensor_id
                        && (sensor_data.value < *min || sensor_data.value > *max)
                }
                AlertCondition::TemperatureAbove(threshold) => {
                    sensor_data.data_type == "temperature" && sensor_data.value > *threshold
                }
                _ => false,
            };

            if should_alert {
                let alert = Alert {
                    id: format!("alert_{}", Instant::now().elapsed().as_nanos()),
                    severity: rule.severity.clone(),
                    message: format!(
                        "传感器 {} 值异常: {:.2}",
                        sensor_data.sensor_id, sensor_data.value
                    ),
                    device_id: sensor_data.sensor_id.clone(),
                    alert_type: AlertType::SensorAnomaly,
                    timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                    acknowledged: false,
                    resolved: false,
                };

                let _ = self.alert_sender.send(alert);
            }
        }
    }

    async fn process_alert(&self, alert: Alert) -> Result<()> {
        let mut alerts = self.alerts.write().await;
        alerts.push(alert.clone());

        let mut stats = self.surveillance_stats.write().await;
        stats.total_alerts += 1;
        stats.active_alerts += 1;

        match alert.severity {
            AlertSeverity::Critical => stats.critical_alerts += 1,
            _ => {}
        }

        // 根据严重程度处理告警
        match alert.severity {
            AlertSeverity::Critical => {
                error!("🚨 严重告警: {}", alert.message);
                // 这里可以发送紧急通知
            }
            AlertSeverity::Error => {
                error!("⚠️ 错误告警: {}", alert.message);
            }
            AlertSeverity::Warning => {
                warn!("⚠️ 警告: {}", alert.message);
            }
            AlertSeverity::Info => {
                info!("ℹ️ 信息: {}", alert.message);
            }
        }

        Ok(())
    }

    pub async fn acknowledge_alert(&self, alert_id: &str) -> Result<()> {
        let mut alerts = self.alerts.write().await;
        if let Some(alert) = alerts.iter_mut().find(|a| a.id == alert_id) {
            alert.acknowledged = true;

            let mut stats = self.surveillance_stats.write().await;
            stats.acknowledged_alerts += 1;

            info!("告警已确认: {}", alert_id);
        }
        Ok(())
    }

    pub async fn get_surveillance_stats(&self) -> SurveillanceStats {
        self.surveillance_stats.read().await.clone()
    }

    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        let alerts = self.alerts.read().await;
        alerts
            .iter()
            .filter(|alert| !alert.resolved)
            .cloned()
            .collect()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    info!("🚀 开始 2025 年异步物联网模式演示");

    // 1. 演示异步物联网设备管理器
    info!("🏠 演示异步物联网设备管理器");
    let device_manager = AsyncIoTDeviceManager::new();

    // 注册一些设备
    let devices = vec![
        IoTDevice {
            id: "sensor_001".to_string(),
            name: "温度传感器".to_string(),
            device_type: DeviceType::Sensor,
            location: "客厅".to_string(),
            status: DeviceStatus::Online,
            capabilities: vec![DeviceCapability {
                name: "temperature".to_string(),
                data_type: "float".to_string(),
                unit: Some("°C".to_string()),
                min_value: Some(-40.0),
                max_value: Some(85.0),
            }],
            last_seen: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            battery_level: Some(85.0),
            firmware_version: "1.2.3".to_string(),
            metadata: HashMap::new(),
        },
        IoTDevice {
            id: "actuator_001".to_string(),
            name: "智能开关".to_string(),
            device_type: DeviceType::Actuator,
            location: "卧室".to_string(),
            status: DeviceStatus::Online,
            capabilities: vec![DeviceCapability {
                name: "power_control".to_string(),
                data_type: "boolean".to_string(),
                unit: None,
                min_value: Some(0.0),
                max_value: Some(1.0),
            }],
            last_seen: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            battery_level: None,
            firmware_version: "2.1.0".to_string(),
            metadata: HashMap::new(),
        },
    ];

    for device in devices {
        device_manager.register_device(device).await?;
    }

    // 创建设备组
    let group = DeviceGroup {
        id: "living_room_group".to_string(),
        name: "客厅设备组".to_string(),
        description: "客厅内的所有智能设备".to_string(),
        device_ids: vec!["sensor_001".to_string()],
        rules: vec![GroupRule {
            id: "temp_high_rule".to_string(),
            condition: RuleCondition::SensorValue(
                "sensor_001".to_string(),
                "temperature".to_string(),
                30.0,
                ComparisonOp::GreaterThan,
            ),
            action: RuleAction::SendNotification("客厅温度过高".to_string()),
            enabled: true,
        }],
        created_at: std::time::Instant::now(),
    };

    device_manager.create_device_group(group).await?;

    // 发送设备命令
    let command = DeviceCommand {
        device_id: "actuator_001".to_string(),
        command: "turn_on".to_string(),
        parameters: HashMap::new(),
        priority: CommandPriority::Normal,
        timeout: Duration::from_secs(30),
    };

    device_manager.send_device_command(command).await?;

    // 处理传感器数据
    let sensor_data = SensorData {
        sensor_id: "sensor_001".to_string(),
        data_type: "temperature".to_string(),
        value: 32.5,
        unit: Some("°C".to_string()),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        quality: DataQuality::Good,
    };

    device_manager.process_sensor_data(sensor_data).await?;

    let device_stats = device_manager.get_device_stats().await;
    info!(
        "设备管理统计: 总设备 {}, 在线 {}, 命令发送 {}",
        device_stats.total_devices, device_stats.online_devices, device_stats.commands_sent
    );

    // 2. 演示异步物联网数据处理管道
    info!("🔄 演示异步物联网数据处理管道");
    let data_pipeline = AsyncIoTDataPipeline::new();

    // 添加数据处理器
    let processors = vec![
        DataProcessor {
            id: "filter_1".to_string(),
            name: "温度过滤器".to_string(),
            processor_type: ProcessorType::Filter,
            config: [
                ("min_value".to_string(), "-50".to_string()),
                ("max_value".to_string(), "100".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        },
        DataProcessor {
            id: "transformer_1".to_string(),
            name: "单位转换器".to_string(),
            processor_type: ProcessorType::Transformer,
            config: [
                ("type".to_string(), "scale".to_string()),
                ("factor".to_string(), "1.8".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        },
        DataProcessor {
            id: "validator_1".to_string(),
            name: "数据验证器".to_string(),
            processor_type: ProcessorType::Validator,
            config: HashMap::new(),
        },
    ];

    for processor in processors {
        data_pipeline.add_processor(processor).await?;
    }

    // 处理传感器数据
    for i in 0..5 {
        let data = SensorData {
            sensor_id: format!("sensor_{:03}", i),
            data_type: "temperature".to_string(),
            value: 20.0 + i as f64 * 2.0,
            unit: Some("°C".to_string()),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            quality: DataQuality::Good,
        };

        let processed = data_pipeline.process_sensor_data(data).await?;
        info!(
            "数据处理结果: {} -> {:.2} (置信度: {:.2})",
            processed.original_data.sensor_id, processed.processed_value, processed.confidence
        );
    }

    let pipeline_stats = data_pipeline.get_pipeline_stats().await;
    info!(
        "管道统计: 总处理 {}, 成功 {}, 平均处理时间 {:?}",
        pipeline_stats.total_processed,
        pipeline_stats.successful_processing,
        pipeline_stats.average_processing_time
    );

    // 3. 演示异步物联网监控和告警系统
    info!("🚨 演示异步物联网监控和告警系统");
    let surveillance_system = AsyncIoTSurveillanceSystem::new();

    // 添加告警规则
    let alert_rules = vec![
        AlertRule {
            id: "device_offline_rule".to_string(),
            name: "设备离线告警".to_string(),
            condition: AlertCondition::DeviceOfflineFor(Duration::from_secs(300)),
            severity: AlertSeverity::Warning,
            enabled: true,
            cooldown: Duration::from_secs(600),
            last_triggered: None,
        },
        AlertRule {
            id: "temp_high_rule".to_string(),
            name: "温度过高告警".to_string(),
            condition: AlertCondition::TemperatureAbove(35.0),
            severity: AlertSeverity::Critical,
            enabled: true,
            cooldown: Duration::from_secs(300),
            last_triggered: None,
        },
    ];

    for rule in alert_rules {
        surveillance_system.add_alert_rule(rule).await?;
    }

    // 检查设备状态
    surveillance_system
        .check_device_status(
            "sensor_001",
            DeviceStatus::Online,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        )
        .await;

    // 检查传感器数据
    let high_temp_data = SensorData {
        sensor_id: "sensor_001".to_string(),
        data_type: "temperature".to_string(),
        value: 38.0,
        unit: Some("°C".to_string()),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        quality: DataQuality::Good,
    };

    surveillance_system.check_sensor_data(&high_temp_data).await;

    // 等待告警处理
    sleep(Duration::from_millis(100)).await;

    let surveillance_stats = surveillance_system.get_surveillance_stats().await;
    let active_alerts = surveillance_system.get_active_alerts().await;

    info!(
        "监控统计: 总告警 {}, 活跃告警 {}, 严重告警 {}",
        surveillance_stats.total_alerts,
        surveillance_stats.active_alerts,
        surveillance_stats.critical_alerts
    );

    for alert in active_alerts.iter().take(3) {
        info!("活跃告警: {:?} - {}", alert.severity, alert.message);
    }

    info!("✅ 2025 年异步物联网模式演示完成!");

    Ok(())
}
