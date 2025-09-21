//! 完整IoT应用示例
//! 
//! 本示例展示了一个完整的IoT应用，包括设备管理、数据采集、边缘计算、
//! 通信协议、数据存储、安全认证和监控告警等功能。

use super::{Example, ExampleParameter, ParameterType};
use crate::device_management::{DeviceManager, DeviceConfig, DeviceType, Protocol, DeviceData};
use crate::device_management::device_manager::DeviceStatusUpdate;
use crate::device_management::{SensorCollector, SensorConfig, SensorType, SensorReading, TemperatureSensor};
use crate::edge_computing::{RuleEngine, Rule, Condition, Action};
use crate::edge_computing::rule_engine::{Operator, AlertLevel, RuleContext};
use tokio::sync::mpsc;
use crate::communication::{CommunicationManager, ProtocolType, Message, MessagePriority};
use crate::data_storage::{StorageManager, StorageType, DataPoint, StorageConfig};
use crate::security::DeviceAuthenticator;
use crate::security::authentication::DeviceCertificate;
use crate::monitoring::{MetricsCollector, AlertManager, AlertNotification};
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;

/// 完整IoT应用示例
pub struct CompleteIoTAppExample {
    device_manager: DeviceManager,
    #[allow(dead_code)]
    device_data_receiver: mpsc::UnboundedReceiver<DeviceData>,
    #[allow(dead_code)]
    device_status_receiver: mpsc::UnboundedReceiver<DeviceStatusUpdate>,
    sensor_collector: SensorCollector,
    #[allow(dead_code)]
    sensor_data_receiver: mpsc::UnboundedReceiver<SensorReading>,
    rule_engine: RuleEngine,
    #[allow(dead_code)]
    action_receiver: mpsc::UnboundedReceiver<Action>,
    communication_manager: CommunicationManager,
    storage_manager: StorageManager,
    authenticator: DeviceAuthenticator,
    #[allow(dead_code)]
    metrics_collector: MetricsCollector,
    #[allow(dead_code)]
    alert_manager: AlertManager,
    #[allow(dead_code)]
    alert_notification_receiver: mpsc::UnboundedReceiver<AlertNotification>,
}

impl CompleteIoTAppExample {
    /// 创建新的完整IoT应用示例
    pub fn new() -> Self {
        let (device_manager, device_data_receiver, device_status_receiver) = DeviceManager::new(Default::default());
        let (sensor_collector, sensor_data_receiver) = SensorCollector::new();
        let rule_engine = RuleEngine::new();
        let (alert_manager, alert_notification_receiver) = AlertManager::new(Default::default());
        let (_, action_receiver) = mpsc::unbounded_channel::<Action>();
        
        Self {
            device_manager,
            device_data_receiver,
            device_status_receiver,
            sensor_collector,
            sensor_data_receiver,
            rule_engine,
            action_receiver,
            communication_manager: CommunicationManager::new(),
            storage_manager: StorageManager::new(),
            authenticator: DeviceAuthenticator::new(Default::default()),
            metrics_collector: MetricsCollector::new(Default::default()),
            alert_manager,
            alert_notification_receiver,
        }
    }

    /// 初始化IoT应用
    async fn initialize(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🚀 初始化IoT应用...");

        // 初始化各个组件
        // 注意：某些组件可能不需要显式初始化
        self.communication_manager.initialize().await?;
        self.storage_manager.initialize().await?;
        // self.metrics_collector.initialize().await?;
        // self.alert_manager.initialize().await?;

        println!("✅ IoT应用初始化完成");
        Ok(())
    }

    /// 设置设备
    async fn setup_devices(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📱 设置IoT设备...");

        // 创建设备配置
        let device_configs = vec![
            DeviceConfig {
                id: "sensor_001".to_string(),
                name: "温度传感器".to_string(),
                device_type: DeviceType::Sensor,
                protocol: Protocol::MQTT,
                endpoint: "mqtt://broker:1883".to_string(),
                location: Some("Building A - Room 101".to_string()),
                metadata: HashMap::new(),
                description: Some("温度传感器设备".to_string()),
                manufacturer: Some("IoT Corp".to_string()),
                model: Some("TEMP-001".to_string()),
                firmware_version: Some("1.0.0".to_string()),
            },
            DeviceConfig {
                id: "sensor_002".to_string(),
                name: "湿度传感器".to_string(),
                device_type: DeviceType::Sensor,
                protocol: Protocol::MQTT,
                endpoint: "mqtt://broker:1883".to_string(),
                location: Some("Building A - Room 102".to_string()),
                metadata: HashMap::new(),
                description: Some("湿度传感器设备".to_string()),
                manufacturer: Some("IoT Corp".to_string()),
                model: Some("HUMID-001".to_string()),
                firmware_version: Some("1.0.0".to_string()),
            },
            DeviceConfig {
                id: "actuator_001".to_string(),
                name: "空调控制器".to_string(),
                device_type: DeviceType::Actuator,
                protocol: Protocol::MQTT,
                endpoint: "mqtt://broker:1883".to_string(),
                location: Some("Building A - Room 101".to_string()),
                metadata: HashMap::new(),
                description: Some("空调控制器设备".to_string()),
                manufacturer: Some("IoT Corp".to_string()),
                model: Some("AC-001".to_string()),
                firmware_version: Some("1.0.0".to_string()),
            },
        ];

        // 注册设备
        for config in device_configs {
            self.device_manager.register_device(config).await?;
        }

        println!("✅ 设备设置完成");
        Ok(())
    }

    /// 设置传感器
    async fn setup_sensors(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🌡️ 设置传感器...");

        // 创建传感器配置
        let sensor_configs = vec![
            SensorConfig {
                id: "temp_001".to_string(),
                sensor_type: SensorType::Temperature,
                address: 0x48,
                sampling_rate: Duration::from_secs(1),
                calibration: None,
                enabled: true,
            },
            SensorConfig {
                id: "humidity_001".to_string(),
                sensor_type: SensorType::Humidity,
                address: 0x49,
                sampling_rate: Duration::from_secs(2),
                calibration: None,
                enabled: true,
            },
        ];

        // 添加传感器
        for config in sensor_configs {
            let sensor = TemperatureSensor::new(config);
            self.sensor_collector.add_sensor(sensor);
        }

        println!("✅ 传感器设置完成");
        Ok(())
    }

    /// 设置规则引擎
    async fn setup_rules(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🧠 设置规则引擎...");

        // 创建温度告警规则
        let temperature_rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            Condition::Simple {
                field: "temperature".to_string(),
                operator: Operator::GreaterThan,
                value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
            },
            Action::SendAlert {
                message: "温度过高，需要开启空调".to_string(),
                recipients: vec!["admin@example.com".to_string()],
                level: AlertLevel::Warning,
            },
            1,
        ).with_description("温度超过30度时发送告警".to_string());

        // 创建湿度告警规则
        let humidity_rule = Rule::new(
            "humidity_alert".to_string(),
            "湿度告警".to_string(),
            Condition::Simple {
                field: "humidity".to_string(),
                operator: Operator::GreaterThan,
                value: serde_json::Value::Number(serde_json::Number::from_f64(80.0).unwrap()),
            },
            Action::AdjustDevice {
                device_id: "actuator_001".to_string(),
                parameter: "mode".to_string(),
                value: serde_json::Value::String("dehumidify".to_string()),
            },
            2,
        ).with_description("湿度超过80%时调整设备".to_string());

        // 添加规则
        self.rule_engine.add_rule(temperature_rule).await?;
        self.rule_engine.add_rule(humidity_rule).await?;

        println!("✅ 规则引擎设置完成");
        Ok(())
    }

    /// 设置通信协议
    async fn setup_communication(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📡 设置通信协议...");

        // 连接MQTT
        self.communication_manager.connect(
            ProtocolType::MQTT,
            "mqtt://broker:1883".to_string()
        ).await?;

        // 连接HTTP
        self.communication_manager.connect(
            ProtocolType::HTTP,
            "http://api.example.com".to_string()
        ).await?;

        println!("✅ 通信协议设置完成");
        Ok(())
    }

    /// 设置数据存储
    async fn setup_storage(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("💾 设置数据存储...");

        // 配置时间序列数据库
        let timeseries_config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string()
        ).with_database_name("iot_timeseries".to_string());

        // 配置关系型数据库
        let relational_config = StorageConfig::new(
            StorageType::Relational,
            "postgresql://localhost:5432".to_string()
        ).with_database_name("iot_metadata".to_string());

        // 添加存储配置
        self.storage_manager.add_storage_config(timeseries_config);
        self.storage_manager.add_storage_config(relational_config);

        // 连接存储
        self.storage_manager.connect_storage(StorageType::TimeSeries).await?;
        self.storage_manager.connect_storage(StorageType::Relational).await?;

        println!("✅ 数据存储设置完成");
        Ok(())
    }

    /// 设置安全认证
    async fn setup_security(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔐 设置安全认证...");

        // 生成设备证书
        let certificate = DeviceCertificate::new(
            "sensor_001".to_string(),
            vec![1, 2, 3, 4], // 模拟公钥
            "iot_ca".to_string(),
            365, // 有效期365天
        );

        // 添加受信任的证书
        self.authenticator.add_trusted_certificate(certificate.clone())?;

        // 验证设备证书
        let is_valid = self.authenticator.verify_device_certificate(&certificate)?;
        if !is_valid {
            return Err("设备证书验证失败".into());
        }

        println!("✅ 安全认证设置完成");
        Ok(())
    }

    /// 运行IoT应用
    async fn run_application(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔄 运行IoT应用...");

        // 启动数据采集
        let sensor_handle = tokio::spawn({
            let collector = self.sensor_collector.clone();
            async move {
                collector.start_collection().await
            }
        });

        // 启动数据处理
        // 注意：由于组件不能克隆，暂时注释掉这个异步任务
        // let processing_handle = tokio::spawn({
        //     // 注意：由于组件不能克隆，这里使用引用
        //     let mut rule_engine = self.rule_engine.clone();
        //     let mut storage_manager = self.storage_manager.clone();
        //     let mut communication_manager = self.communication_manager.clone();
        //     
        //     async move {
        //         loop {
        //             // 模拟传感器数据
        //             let data_point = DataPoint::new("sensor_data".to_string())
        //                 .with_tag("device_id".to_string(), "sensor_001".to_string())
        //                 .with_tag("location".to_string(), "Building A".to_string())
        //                 .with_field("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(25.5).unwrap()))
        //                 .with_field("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(60.0).unwrap()));

        //             // 存储数据
        //             if let Err(e) = storage_manager.insert_data(StorageType::TimeSeries, data_point.clone()).await {
        //                 eprintln!("数据存储失败: {}", e);
        //             }

        //             // 评估规则
        //             let context = RuleContext {
        //                 data: data_point.fields.clone(),
        //                 timestamp: chrono::Utc::now(),
        //                 device_id: "sensor_001".to_string(),
        //                 event_type: Some("sensor_data".to_string()),
        //                 metadata: HashMap::new(),
        //             };

        //             if let Ok(actions) = rule_engine.evaluate_rules(context).await {
        //                 for action in actions {
        //                     // 执行动作
        //                     match action {
        //                         Action::SendAlert { message, recipients, level } => {
        //                             println!("🚨 发送告警: {} 给: {:?} (级别: {:?})", message, recipients, level);
        //                         }
        //                         Action::AdjustDevice { device_id, parameter, value } => {
        //                             println!("🔧 调整设备 {} 的 {} 为 {:?}", device_id, parameter, value);
        //                         }
        //                         _ => {}
        //                     }
        //                 }
        //             }

        //             // 发送数据到云端
        //             let message = Message::new(
        //                 ProtocolType::MQTT,
        //                 "sensor/data".to_string(),
        //                 serde_json::to_vec(&data_point).unwrap(),
        //             ).with_priority(MessagePriority::Normal);

        //             if let Err(e) = communication_manager.send_message(message).await {
        //                 eprintln!("消息发送失败: {}", e);
        //             }

        //             sleep(Duration::from_secs(5)).await;
        //         }
        //     };
        // });

        // 模拟数据处理（简化版本）
        println!("🔄 开始模拟数据处理...");
        for i in 0..6 {
            // 模拟传感器数据
            let data_point = DataPoint::new("sensor_data".to_string())
                .with_tag("device_id".to_string(), "sensor_001".to_string())
                .with_tag("location".to_string(), "Building A".to_string())
                .with_field("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(25.5 + i as f64).unwrap()))
                .with_field("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(60.0 + i as f64).unwrap()));

            // 存储数据
            if let Err(e) = self.storage_manager.insert_data(StorageType::TimeSeries, data_point.clone()).await {
                eprintln!("数据存储失败: {}", e);
            }

            // 评估规则
            let context = RuleContext {
                data: data_point.fields.clone(),
                timestamp: chrono::Utc::now(),
                device_id: Some("sensor_001".to_string()),
                location: Some("Building A".to_string()),
                event_type: Some("sensor_data".to_string()),
                metadata: HashMap::new(),
            };

            if let Ok(actions) = self.rule_engine.evaluate_rules(context).await {
                for action in actions {
                    // 执行动作
                    match action {
                        Action::SendAlert { message, recipients, level } => {
                            println!("🚨 发送告警: {} 给: {:?} (级别: {:?})", message, recipients, level);
                        }
                        Action::AdjustDevice { device_id, parameter, value } => {
                            println!("🔧 调整设备 {} 的 {} 为 {:?}", device_id, parameter, value);
                        }
                        _ => {}
                    }
                }
            }

            // 发送数据到云端
            let message = Message::new(
                ProtocolType::MQTT,
                "sensor/data".to_string(),
                serde_json::to_vec(&data_point).unwrap(),
            ).with_priority(MessagePriority::Normal);

            if let Err(e) = self.communication_manager.send_message(message).await {
                eprintln!("消息发送失败: {}", e);
            }

            println!("📊 处理第 {} 批数据", i + 1);
            sleep(Duration::from_secs(5)).await;
        }

        // 运行一段时间
        sleep(Duration::from_secs(30)).await;

        // 停止任务
        sensor_handle.abort();
        // processing_handle.abort();

        println!("✅ IoT应用运行完成");
        Ok(())
    }

    /// 生成报告
    async fn generate_report(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📊 生成IoT应用报告...");

        // 获取设备信息
        let devices = self.device_manager.get_all_devices().await;
        println!("设备数量: {}", devices.len());

        // 获取传感器信息
        let sensor_count = self.sensor_collector.sensor_count();
        println!("传感器数量: {}", sensor_count);

        // 获取通信统计
        let comm_stats = self.communication_manager.get_stats();
        println!("发送消息数: {}", comm_stats.total_messages_sent);
        println!("接收消息数: {}", comm_stats.total_messages_received);

        // 获取存储统计
        let storage_stats = self.storage_manager.get_storage_stats(StorageType::TimeSeries).await?;
        println!("存储记录数: {}", storage_stats.total_records);

        println!("✅ 报告生成完成");
        Ok(())
    }
}

impl Example for CompleteIoTAppExample {
    fn name(&self) -> &'static str {
        "complete_iot_app"
    }

    fn description(&self) -> &'static str {
        "完整的IoT应用示例，展示设备管理、数据采集、边缘计算、通信协议、数据存储、安全认证和监控告警等功能"
    }

    fn parameters(&self) -> Vec<ExampleParameter> {
        vec![
            ExampleParameter {
                name: "broker_url".to_string(),
                description: "MQTT代理URL".to_string(),
                parameter_type: ParameterType::String,
                default_value: Some("mqtt://localhost:1883".to_string()),
                required: false,
            },
            ExampleParameter {
                name: "demo_duration".to_string(),
                description: "演示持续时间（秒）".to_string(),
                parameter_type: ParameterType::Integer,
                default_value: Some("60".to_string()),
                required: false,
            },
        ]
    }

    fn run(&mut self, _parameters: std::collections::HashMap<String, String>) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error>>> + Send {
        async move {
            let mut app = CompleteIoTAppExample::new();

            // 初始化应用
            app.initialize().await?;

            // 设置各个组件
            app.setup_devices().await?;
            app.setup_sensors().await?;
            app.setup_rules().await?;
            app.setup_communication().await?;
            app.setup_storage().await?;
            app.setup_security().await?;

            // 运行应用
            app.run_application().await?;

            // 生成报告
            app.generate_report().await?;

            Ok(())
        }
    }

}

impl Default for CompleteIoTAppExample {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_complete_iot_app_creation() {
        let app = CompleteIoTAppExample::new();
        assert_eq!(app.name(), "complete_iot_app");
        assert!(!app.description().is_empty());
    }

    #[tokio::test]
    async fn test_complete_iot_app_parameters() {
        let app = CompleteIoTAppExample::new();
        let parameters = app.parameters();
        assert!(!parameters.is_empty());
        
        let broker_param = parameters.iter().find(|p| p.name == "broker_url");
        assert!(broker_param.is_some());
        assert_eq!(broker_param.unwrap().parameter_type, ParameterType::Url);
    }
}
