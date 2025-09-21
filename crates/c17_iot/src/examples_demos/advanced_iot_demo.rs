//! 高级IoT演示示例
//! 
//! 本示例展示了一个高级IoT应用，包括：
//! - 多协议通信
//! - 边缘计算和机器学习
//! - 高级安全认证
//! - 实时监控和告警
//! - 数据分析和可视化

use super::{Example, ExampleParameter, ParameterType};
use crate::communication::{CommunicationManager, ProtocolType, Message};
use crate::edge_computing::{RuleEngine, Rule, Condition, Action};
use crate::edge_computing::rule_engine::{Operator, AlertLevel, RuleContext, MLModel, MLModelType};
use crate::security::{DeviceAuthenticator, SecurityError};
use crate::security::authentication::{AuthenticationConfig, AccessPolicy, AccessRule, AccessEffect, MFAMethod};
use crate::monitoring::{MetricsCollector, AlertManager, MonitoringDashboard};
use crate::monitoring::dashboard::{DashboardConfig, ExportFormat};
use crate::data_storage::{StorageManager, StorageType, DataPoint, StorageConfig};
use crate::data_storage::cache::{CacheSystem, RedisCache, CacheConfig, CacheStrategy};
use crate::data_storage::traits::StorageInterface;
use crate::hardware_abstraction::gpio::{GPIOManager, PinConfig, PinMode, PinState, DriveStrength};
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use chrono::Utc;
use serde_json::Value;

/// 高级IoT演示示例
pub struct AdvancedIoTDemo {
    communication_manager: CommunicationManager,
    rule_engine: RuleEngine,
    authenticator: DeviceAuthenticator,
    metrics_collector: MetricsCollector,
    #[allow(dead_code)]
    alert_manager: AlertManager,
    dashboard: MonitoringDashboard,
    storage_manager: StorageManager,
    cache_system: RedisCache,
    gpio_manager: GPIOManager,
    is_running: bool,
}

impl AdvancedIoTDemo {
    /// 创建新的高级IoT演示
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // 初始化通信管理器
        let communication_manager = CommunicationManager::new();

        // 初始化规则引擎
        let rule_engine = RuleEngine::new();

        // 初始化认证器
        let auth_config = AuthenticationConfig {
            token_expiry_hours: 24,
            max_active_tokens: 1000,
            enable_token_refresh: true,
            refresh_token_expiry_days: 30,
            enable_mfa: true,
        };
        let authenticator = DeviceAuthenticator::new(auth_config);

        // 初始化监控组件
        let metrics_collector = MetricsCollector::new(Default::default());
        let (alert_manager, _alert_receiver) = AlertManager::new(Default::default());
        let dashboard_config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(dashboard_config);

        // 初始化存储管理器
        let _storage_config = StorageConfig {
            storage_type: StorageType::Embedded,
            connection_string: "memory://".to_string(),
            database_name: "iot_data".to_string(),
            username: None,
            password: None,
            max_connections: Some(10),
            connection_timeout: Some(Duration::from_secs(30)),
            query_timeout: Some(Duration::from_secs(10)),
            enable_ssl: false,
            enable_compression: true,
            backup_enabled: false,
            backup_interval: None,
            retention_policy: None,
        };
        let storage_manager = StorageManager::new();

        // 初始化缓存系统
        let _cache_config = CacheConfig {
            max_size: 10000,
            default_ttl: 3600,
            strategy: CacheStrategy::LRU,
            enable_compression: true,
            enable_persistence: false,
            cleanup_interval: 300,
        };
        let cache_system = RedisCache::new(
            "redis://localhost:6379".to_string(),
            0,
        );

        // 初始化GPIO管理器
        let gpio_manager = GPIOManager::new();

        Ok(Self {
            communication_manager,
            rule_engine,
            authenticator,
            metrics_collector,
            alert_manager,
            dashboard,
            storage_manager,
            cache_system,
            gpio_manager,
            is_running: false,
        })
    }

    /// 运行高级IoT演示
    pub async fn run(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🚀 启动高级IoT演示...");

        // 初始化所有组件
        self.initialize_components().await?;

        // 设置演示场景
        self.setup_demo_scenarios().await?;

        // 启动数据流处理
        self.start_data_processing().await?;

        // 运行演示循环
        self.run_demo_loop().await?;

        println!("✅ 高级IoT演示完成");
        Ok(())
    }

    /// 初始化所有组件
    async fn initialize_components(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔧 初始化组件...");

        // 初始化通信管理器
        self.communication_manager.initialize().await?;
        println!("✅ 通信管理器已初始化");

        // 初始化存储管理器
        self.storage_manager.initialize().await?;
        println!("✅ 存储管理器已初始化");

        // 初始化缓存系统
        self.cache_system.connect().await?;
        println!("✅ 缓存系统已连接");

        // 初始化GPIO管理器
        self.gpio_manager.initialize().await?;
        println!("✅ GPIO管理器已初始化");

        Ok(())
    }

    /// 设置演示场景
    async fn setup_demo_scenarios(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🎭 设置演示场景...");

        // 连接MQTT协议
        self.communication_manager.connect(ProtocolType::MQTT, "localhost:1883".to_string()).await?;
        println!("✅ MQTT协议已连接");

        // 连接CoAP协议
        self.communication_manager.connect(ProtocolType::CoAP, "localhost:5683".to_string()).await?;
        println!("✅ CoAP协议已连接");

        // 添加机器学习模型
        let ml_model = MLModel {
            id: "temp_anomaly_detector".to_string(),
            name: "温度异常检测模型".to_string(),
            model_type: MLModelType::AnomalyDetection,
            version: "1.0.0".to_string(),
            accuracy: 0.95,
            training_data_size: 1000,
            last_trained: Utc::now(),
            parameters: HashMap::new(),
            input_features: vec!["temperature".to_string(), "humidity".to_string()],
            output_labels: vec!["normal".to_string(), "anomaly".to_string()],
        };
        self.rule_engine.add_ml_model(ml_model).await?;
        println!("✅ 机器学习模型已添加");

        // 添加智能规则
        self.add_smart_rules().await?;
        println!("✅ 智能规则已添加");

        // 设置安全策略
        self.setup_security_policies().await?;
        println!("✅ 安全策略已设置");

        // 配置GPIO引脚
        self.configure_gpio_pins().await?;
        println!("✅ GPIO引脚已配置");

        Ok(())
    }

    /// 添加智能规则
    async fn add_smart_rules(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 温度异常检测规则
        let temp_anomaly_condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(35.0).unwrap()),
        };

        let temp_anomaly_action = Action::SendAlert {
            message: "温度异常：超过35°C".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Critical,
        };

        let temp_anomaly_rule = Rule::new(
            "temp_anomaly".to_string(),
            "温度异常检测".to_string(),
            temp_anomaly_condition,
            temp_anomaly_action,
            1,
        );

        self.rule_engine.add_rule(temp_anomaly_rule).await?;

        // 湿度监控规则
        let humidity_condition = Condition::Simple {
            field: "humidity".to_string(),
            operator: Operator::LessThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };

        let humidity_action = Action::SendAlert {
            message: "湿度过低：低于30%".to_string(),
            recipients: vec!["operator@example.com".to_string()],
            level: AlertLevel::Warning,
        };

        let humidity_rule = Rule::new(
            "humidity_low".to_string(),
            "湿度监控".to_string(),
            humidity_condition,
            humidity_action,
            2,
        );

        self.rule_engine.add_rule(humidity_rule).await?;

        // 设备离线检测规则
        let offline_condition = Condition::TimeCondition {
            start_time: Some(Utc::now() - chrono::Duration::minutes(5)),
            end_time: None,
            days_of_week: vec![1, 2, 3, 4, 5], // 工作日
        };

        let offline_action = Action::SendAlert {
            message: "设备离线：超过5分钟未收到数据".to_string(),
            recipients: vec!["maintenance@example.com".to_string()],
            level: AlertLevel::Error,
        };

        let offline_rule = Rule::new(
            "device_offline".to_string(),
            "设备离线检测".to_string(),
            offline_condition,
            offline_action,
            3,
        );

        self.rule_engine.add_rule(offline_rule).await?;

        Ok(())
    }

    /// 设置安全策略
    async fn setup_security_policies(&mut self) -> Result<(), SecurityError> {
        // 创建访问控制策略
        let access_rule = AccessRule {
            resource: "sensors/*".to_string(),
            action: "read".to_string(),
            effect: AccessEffect::Allow,
            conditions: vec![],
        };

        let access_policy = AccessPolicy {
            id: "sensor_access".to_string(),
            name: "传感器访问策略".to_string(),
            description: "允许访问传感器数据".to_string(),
            rules: vec![access_rule],
            priority: 1,
            enabled: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        self.authenticator.add_access_policy(access_policy)?;

        // 启用多因素认证
        let mfa_methods = vec![MFAMethod::TOTP, MFAMethod::SMS];
        self.authenticator.enable_mfa(mfa_methods);

        Ok(())
    }

    /// 配置GPIO引脚
    async fn configure_gpio_pins(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 配置LED控制引脚
        let led_config = PinConfig {
            mode: PinMode::Output,
            initial_state: Some(PinState::Low),
            interrupt_trigger: None,
            debounce_time: None,
        };
        self.gpio_manager.configure_pin(18, led_config).await?;

        // 配置传感器输入引脚
        let sensor_config = PinConfig {
            mode: PinMode::Input,
            initial_state: None,
            interrupt_trigger: Some(crate::hardware_abstraction::gpio::InterruptTrigger::Rising),
            debounce_time: Some(Duration::from_millis(50)),
        };
        self.gpio_manager.configure_pin(24, sensor_config).await?;

        // 设置驱动强度
        self.gpio_manager.set_pin_drive_strength(18, DriveStrength::EightMilliamps).await?;

        Ok(())
    }

    /// 启动数据流处理
    async fn start_data_processing(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📊 启动数据流处理...");

        // 启动模拟数据生成
        self.start_simulated_data_generation().await?;

        // 启动规则引擎处理
        self.start_rule_processing().await?;

        // 启动监控数据收集
        self.start_monitoring_data_collection().await?;

        Ok(())
    }

    /// 启动模拟数据生成
    async fn start_simulated_data_generation(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut communication_manager = self.communication_manager.clone();
        let mut storage_manager = self.storage_manager.clone();
        let mut cache_system = self.cache_system.clone();

        tokio::spawn(async move {
            let mut counter = 0;
            loop {
                // 生成模拟传感器数据
                let temperature = 20.0 + (counter as f64 * 0.1) % 20.0;
                let humidity = 40.0 + (counter as f64 * 0.2) % 40.0;

                // 发送MQTT消息
                let temp_message = Message::new(
                    ProtocolType::MQTT,
                    "sensors/room1/temperature".to_string(),
                    temperature.to_string().into_bytes(),
                );

                let humidity_message = Message::new(
                    ProtocolType::MQTT,
                    "sensors/room1/humidity".to_string(),
                    humidity.to_string().into_bytes(),
                );

                let _ = communication_manager.send_message(temp_message).await;
                let _ = communication_manager.send_message(humidity_message).await;

                // 发送CoAP消息
                let coap_message = Message::new(
                    ProtocolType::CoAP,
                    "/sensors/data".to_string(),
                    serde_json::json!({
                        "temperature": temperature,
                        "humidity": humidity,
                        "timestamp": Utc::now()
                    }).to_string().into_bytes(),
                );

                let _ = communication_manager.send_message(coap_message).await;

                // 存储数据
                let mut fields = HashMap::new();
                fields.insert("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(temperature).unwrap()));
                fields.insert("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(humidity).unwrap()));
                
                let mut tags = HashMap::new();
                tags.insert("device_id".to_string(), "room1_sensor".to_string());
                
                let data_point = DataPoint {
                    timestamp: Utc::now(),
                    measurement: "sensor_data".to_string(),
                    tags,
                    fields,
                };

                let _ = storage_manager.store_data(data_point).await;

                // 缓存数据
                let cache_key = format!("sensor_data_{}", counter);
                let cache_value = serde_json::json!({
                    "temperature": temperature,
                    "humidity": humidity
                }).to_string();

                let _ = cache_system.set(&cache_key, &cache_value, Some(300)).await;

                counter += 1;
                sleep(Duration::from_secs(5)).await;
            }
        });

        Ok(())
    }

    /// 启动规则引擎处理
    async fn start_rule_processing(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut rule_engine = self.rule_engine.clone();

        tokio::spawn(async move {
            loop {
                // 创建规则上下文
                let context = RuleContext {
                    data: HashMap::new(),
                    timestamp: Utc::now(),
                    device_id: Some("demo_device".to_string()),
                    location: Some("Demo Location".to_string()),
                    event_type: Some("sensor_data".to_string()),
                    metadata: HashMap::new(),
                };

                // 评估规则
                let _ = rule_engine.evaluate_rules(context).await;

                sleep(Duration::from_secs(10)).await;
            }
        });

        Ok(())
    }

    /// 启动监控数据收集
    async fn start_monitoring_data_collection(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let metrics_collector = self.metrics_collector.clone();
        let dashboard = self.dashboard.clone();

        tokio::spawn(async move {
            loop {
                // 收集系统指标
                let _ = metrics_collector.collect_system_metrics().await;
                let _ = metrics_collector.collect_application_metrics().await;

                // 更新仪表盘
                let _ = dashboard.refresh_data().await;

                sleep(Duration::from_secs(30)).await;
            }
        });

        Ok(())
    }

    /// 运行演示循环
    async fn run_demo_loop(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔄 开始演示循环...");
        self.is_running = true;

        let mut demo_step = 0;
        while self.is_running && demo_step < 20 {
            match demo_step {
                0..=4 => {
                    // 演示MQTT通信
                    self.demonstrate_mqtt_communication().await?;
                }
                5..=9 => {
                    // 演示CoAP通信
                    self.demonstrate_coap_communication().await?;
                }
                10..=14 => {
                    // 演示边缘计算
                    self.demonstrate_edge_computing().await?;
                }
                15..=19 => {
                    // 演示安全认证
                    self.demonstrate_security_authentication().await?;
                }
                _ => break,
            }

            demo_step += 1;
            sleep(Duration::from_secs(2)).await;
        }

        Ok(())
    }

    /// 演示MQTT通信
    async fn demonstrate_mqtt_communication(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📡 演示MQTT通信...");

        // 发送测试消息
        let test_message = Message::new(
            ProtocolType::MQTT,
            "demo/test".to_string(),
            "Hello from Advanced IoT Demo!".to_string().into_bytes(),
        );

        self.communication_manager.send_message(test_message).await?;

        // 获取连接状态
        let connection_status = self.communication_manager.get_connection_status(ProtocolType::MQTT);
        println!("MQTT连接状态: {:?}", connection_status);

        // 获取统计信息
        let stats = self.communication_manager.get_stats();
        println!("通信统计信息: {:?}", stats);

        Ok(())
    }

    /// 演示CoAP通信
    async fn demonstrate_coap_communication(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🌐 演示CoAP通信...");

        // 发送GET请求
        let get_message = Message::new(
            ProtocolType::CoAP,
            "/.well-known/core".to_string(),
            vec![],
        );

        let _ = self.communication_manager.send_message(get_message).await?;
        println!("CoAP GET请求已发送");

        // 发送POST请求
        let post_message = Message::new(
            ProtocolType::CoAP,
            "/sensors/update".to_string(),
            serde_json::json!({
                "status": "active",
                "timestamp": Utc::now()
            }).to_string().into_bytes(),
        );

        let _ = self.communication_manager.send_message(post_message).await?;
        println!("CoAP POST请求已发送");

        // 获取连接状态
        let connection_status = self.communication_manager.get_connection_status(ProtocolType::CoAP);
        println!("CoAP连接状态: {:?}", connection_status);

        Ok(())
    }

    /// 演示边缘计算
    async fn demonstrate_edge_computing(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🧠 演示边缘计算...");

        // 使用机器学习模型进行预测
        let _input_data = HashMap::from([
            ("temperature".to_string(), Value::Number(serde_json::Number::from_f64(25.5).unwrap())),
            ("humidity".to_string(), Value::Number(serde_json::Number::from_f64(60.0).unwrap())),
        ]);

        // 将输入数据转换为 f64 数组
        let input_array: Vec<f64> = vec![25.5, 60.0]; // 温度, 湿度
        let prediction = self.rule_engine.predict_with_model("temp_anomaly_detector", &input_array).await?;
        println!("ML模型预测结果: {:?}", prediction);

        // 获取规则性能指标
        match self.rule_engine.get_rule_performance_metrics("temp_anomaly").await {
            Ok(metrics) => println!("规则性能指标: {:?}", metrics),
            Err(e) => println!("获取规则性能指标失败: {}", e),
        }

        // 优化规则执行顺序
        self.rule_engine.optimize_rule_order().await?;
        println!("规则执行顺序已优化");

        Ok(())
    }

    /// 演示安全认证
    async fn demonstrate_security_authentication(&mut self) -> Result<(), SecurityError> {
        println!("🔐 演示安全认证...");

        // 创建会话
        let session = self.authenticator.create_session(
            "demo_device".to_string(),
            Some("demo_user".to_string()),
            Some("192.168.1.100".to_string()),
            Some("Advanced IoT Demo".to_string()),
        );
        println!("创建会话: {:?}", session);

        // 检查访问权限
        let has_access = self.authenticator.check_access("demo_device", "sensors/temperature", "read");
        println!("访问权限检查: {}", has_access);

        // 验证多因素认证
        let mfa_valid = self.authenticator.verify_mfa("demo_device", &MFAMethod::TOTP, "123456");
        println!("MFA验证结果: {}", mfa_valid);

        // 获取安全统计信息
        let security_stats = self.authenticator.get_security_stats();
        println!("安全统计信息: {:?}", security_stats);

        Ok(())
    }

    /// 停止演示
    pub fn stop(&mut self) {
        println!("🛑 停止高级IoT演示...");
        self.is_running = false;
    }

    /// 获取演示状态
    pub fn is_running(&self) -> bool {
        self.is_running
    }

    /// 导出演示数据
    pub async fn export_demo_data(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        // 导出仪表盘数据
        let dashboard_data = self.dashboard.export_data(ExportFormat::Json).await?;

        // 导出规则配置
        let rules_data = self.rule_engine.export_rules(crate::edge_computing::rule_engine::ExportFormat::Json).await?;

        // 导出安全配置
        let security_data = self.authenticator.export_security_config()?;

        // 合并所有数据
        let combined_data = serde_json::json!({
            "dashboard": serde_json::from_slice::<Value>(&dashboard_data)?,
            "rules": serde_json::from_slice::<Value>(&rules_data)?,
            "security": serde_json::from_slice::<Value>(&security_data)?,
            "export_timestamp": Utc::now(),
        });

        Ok(serde_json::to_vec(&combined_data)?)
    }
}

impl Example for AdvancedIoTDemo {
    fn name(&self) -> &'static str {
        "高级IoT演示"
    }

    fn description(&self) -> &'static str {
        "展示高级IoT功能，包括多协议通信、边缘计算、机器学习、安全认证等"
    }

    fn parameters(&self) -> Vec<ExampleParameter> {
        vec![
            ExampleParameter {
                name: "mqtt_broker".to_string(),
                description: "MQTT代理地址".to_string(),
                parameter_type: ParameterType::String,
                default_value: Some("localhost".to_string()),
                required: false,
            },
            ExampleParameter {
                name: "coap_server".to_string(),
                description: "CoAP服务器地址".to_string(),
                parameter_type: ParameterType::String,
                default_value: Some("localhost".to_string()),
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

    fn run(&mut self, _parameters: HashMap<String, String>) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error>>> + Send {
        async move {
            self.run().await
        }
    }
}

impl Default for AdvancedIoTDemo {
    fn default() -> Self {
        Self::new().expect("Failed to create AdvancedIoTDemo")
    }
}
