# c17_iot 用户指南

## 快速开始

### 安装

将 `c17_iot` 添加到你的 `Cargo.toml` 文件中：

```toml
[dependencies]
c17_iot = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
chrono = { version = "0.4", features = ["serde"] }
```

### 基础使用

```rust
use c17_iot::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建设备管理器
    let mut device_manager = device_management::DeviceManager::new();
    
    // 注册设备
    device_manager.register_device("sensor_001", "temperature", "room1").await?;
    
    // 创建传感器网络
    let mut sensor_network = sensor_network::SensorNetwork::new();
    sensor_network.add_sensor("temp_001", "temperature", "room1").await?;
    
    // 开始数据采集
    sensor_network.start_data_collection().await?;
    
    println!("IoT 应用启动成功！");
    Ok(())
}
```

## 设备管理

### 注册设备

```rust
use c17_iot::device_management::DeviceManager;

let mut device_manager = DeviceManager::new();

// 注册温度传感器
device_manager.register_device(
    "temp_sensor_001", 
    "temperature_sensor", 
    "living_room"
).await?;

// 注册湿度传感器
device_manager.register_device(
    "humidity_sensor_001", 
    "humidity_sensor", 
    "bedroom"
).await?;
```

### 设备状态监控

```rust
// 获取设备状态
let status = device_manager.get_device_status("temp_sensor_001").await?;
println!("设备状态: {:?}", status);

// 获取所有设备
let devices = device_manager.get_all_devices().await?;
for device in devices {
    println!("设备: {} - 类型: {} - 位置: {}", 
        device.id, device.device_type, device.location);
}
```

### 设备配置管理

```rust
use c17_iot::device_management::DeviceConfig;

// 创建设备配置
let config = DeviceConfig {
    sampling_interval: std::time::Duration::from_secs(30),
    data_retention_days: 30,
    alert_thresholds: std::collections::HashMap::new(),
    custom_settings: std::collections::HashMap::new(),
};

// 更新设备配置
device_manager.update_device_config("temp_sensor_001", config).await?;
```

## 传感器数据采集

### 添加传感器

```rust
use c17_iot::sensor_network::SensorNetwork;

let mut sensor_network = SensorNetwork::new();

// 添加温度传感器
sensor_network.add_sensor("temp_001", "temperature", "room1").await?;

// 添加湿度传感器
sensor_network.add_sensor("humidity_001", "humidity", "room1").await?;

// 添加压力传感器
sensor_network.add_sensor("pressure_001", "pressure", "room1").await?;
```

### 数据采集配置

```rust
use c17_iot::sensor_network::SensorConfig;

// 配置传感器
let config = SensorConfig {
    sampling_rate: 1.0, // 每秒采样一次
    data_format: "json".to_string(),
    calibration_offset: 0.0,
    calibration_scale: 1.0,
    alert_thresholds: std::collections::HashMap::new(),
};

sensor_network.configure_sensor("temp_001", config).await?;
```

### 数据采集控制

```rust
// 开始数据采集
sensor_network.start_data_collection().await?;

// 暂停数据采集
sensor_network.pause_data_collection().await?;

// 恢复数据采集
sensor_network.resume_data_collection().await?;

// 停止数据采集
sensor_network.stop_data_collection().await?;
```

### 获取传感器数据

```rust
// 获取最新数据
let latest_data = sensor_network.get_latest_data("temp_001").await?;
println!("最新温度: {}°C", latest_data.value);

// 获取历史数据
let historical_data = sensor_network.get_historical_data(
    "temp_001", 
    chrono::Utc::now() - chrono::Duration::hours(1),
    chrono::Utc::now()
).await?;

for data_point in historical_data {
    println!("时间: {}, 值: {}", data_point.timestamp, data_point.value);
}
```

## 边缘计算和规则引擎

### 创建规则

```rust
use c17_iot::edge_computing::{RuleEngine, Rule, Condition, Action};
use c17_iot::edge_computing::rule_engine::{Operator, AlertLevel};

let (mut rule_engine, _) = RuleEngine::new();

// 创建温度告警规则
let temp_condition = Condition::Simple {
    field: "temperature".to_string(),
    operator: Operator::GreaterThan,
    value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
};

let temp_action = Action::SendAlert {
    message: "温度过高，请检查空调".to_string(),
    recipients: vec!["admin@example.com".to_string()],
    level: AlertLevel::Warning,
};

let temp_rule = Rule::new(
    "high_temperature_alert".to_string(),
    "高温告警".to_string(),
    temp_condition,
    temp_action,
    1, // 优先级
);

rule_engine.add_rule(temp_rule).await?;
```

### 复合条件规则

```rust
// 创建复合条件规则
let humidity_condition = Condition::Simple {
    field: "humidity".to_string(),
    operator: Operator::LessThan,
    value: serde_json::Value::Number(serde_json::Number::from_f64(20.0).unwrap()),
};

let combined_condition = Condition::And {
    conditions: vec![temp_condition, humidity_condition],
};

let combined_action = Action::SendAlert {
    message: "温度和湿度异常".to_string(),
    recipients: vec!["operator@example.com".to_string()],
    level: AlertLevel::Critical,
};

let combined_rule = Rule::new(
    "temp_humidity_alert".to_string(),
    "温湿度异常告警".to_string(),
    combined_condition,
    combined_action,
    2,
);

rule_engine.add_rule(combined_rule).await?;
```

### 规则评估

```rust
use c17_iot::edge_computing::rule_engine::RuleContext;

// 创建规则上下文
let context = RuleContext {
    data: std::collections::HashMap::from([
        ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(32.0).unwrap())),
        ("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(15.0).unwrap())),
    ]),
    timestamp: chrono::Utc::now(),
    device_id: "sensor_001".to_string(),
    event_type: Some("sensor_data".to_string()),
    metadata: std::collections::HashMap::new(),
};

// 评估规则
let results = rule_engine.evaluate_rules(context).await?;
for result in results {
    println!("规则 {} 触发: {}", result.rule_id, result.message);
}
```

## 安全认证

### 设备认证

```rust
use c17_iot::security::{DeviceAuthenticator, SecurityError};
use c17_iot::security::authentication::{AuthenticationConfig, DeviceCertificate};

// 创建认证器
let auth_config = AuthenticationConfig {
    token_expiry_hours: 24,
    max_active_tokens: 1000,
    enable_token_refresh: true,
    refresh_token_expiry_days: 30,
    enable_mfa: true,
};
let mut authenticator = DeviceAuthenticator::new(auth_config);

// 创建设备证书
let certificate = DeviceCertificate {
    device_id: "device_001".to_string(),
    public_key: "device_public_key".to_string().into_bytes(),
    issued_at: chrono::Utc::now(),
    expires_at: chrono::Utc::now() + chrono::Duration::days(365),
    issuer: "IoT_CA".to_string(),
    signature: vec![],
    certificate_chain: vec![],
    extensions: std::collections::HashMap::new(),
};

// 认证设备
let token = authenticator.authenticate_device("device_001", &certificate)?;
println!("设备认证成功，令牌: {}", token);
```

### 访问控制

```rust
use c17_iot::security::authentication::{AccessPolicy, AccessRule, AccessEffect};

// 创建访问控制策略
let access_rule = AccessRule {
    resource: "sensors/temperature".to_string(),
    action: "read".to_string(),
    effect: AccessEffect::Allow,
    conditions: vec![],
};

let access_policy = AccessPolicy {
    id: "sensor_read_policy".to_string(),
    name: "传感器读取策略".to_string(),
    description: "允许读取温度传感器数据".to_string(),
    rules: vec![access_rule],
    priority: 1,
    enabled: true,
    created_at: chrono::Utc::now(),
    updated_at: chrono::Utc::now(),
};

authenticator.add_access_policy(access_policy)?;

// 检查访问权限
let has_access = authenticator.check_access("device_001", "sensors/temperature", "read");
println!("访问权限: {}", has_access);
```

### 会话管理

```rust
// 创建会话
let session = authenticator.create_session(
    "device_001".to_string(),
    Some("user_001".to_string()),
    Some("192.168.1.100".to_string()),
    Some("IoT_Client".to_string()),
);

println!("会话创建成功: {}", session.id);

// 更新会话活动
authenticator.update_session_activity(&session.id)?;

// 终止会话
authenticator.terminate_session(&session.id)?;
```

## 监控和告警

### 监控仪表盘

```rust
use c17_iot::monitoring::dashboard::{MonitoringDashboard, DashboardConfig};

// 创建监控仪表盘
let config = DashboardConfig::default();
let mut dashboard = MonitoringDashboard::new(config);

// 更新系统状态
dashboard.update_system_status().await?;

// 获取实时数据
let realtime_data = dashboard.get_realtime_data().await?;
println!("系统状态: {:?}", realtime_data.system_status);
```

### 告警管理

```rust
use c17_iot::monitoring::{AlertManager, AlertNotification, AlertLevel};

let mut alert_manager = AlertManager::new(Default::default());

// 创建告警通知
let notification = AlertNotification {
    id: "alert_001".to_string(),
    title: "温度异常".to_string(),
    message: "温度超过阈值".to_string(),
    level: AlertLevel::Warning,
    source: "temperature_sensor".to_string(),
    timestamp: chrono::Utc::now(),
    acknowledged: false,
    metadata: std::collections::HashMap::new(),
};

// 发送告警
alert_manager.send_alert(notification).await?;
```

### 数据导出

```rust
use c17_iot::monitoring::dashboard::ExportFormat;

// 导出JSON格式数据
let json_data = dashboard.export_data(ExportFormat::Json).await?;
std::fs::write("dashboard_data.json", json_data)?;

// 导出CSV格式数据
let csv_data = dashboard.export_data(ExportFormat::Csv).await?;
std::fs::write("dashboard_data.csv", csv_data)?;
```

## 通信协议

### MQTT通信

```rust
use c17_iot::communication::{CommunicationManager, ProtocolType, Message};

let mut comm_manager = CommunicationManager::new();
comm_manager.initialize().await?;

// 连接MQTT
comm_manager.connect(ProtocolType::MQTT, "localhost:1883".to_string()).await?;

// 发送消息
let message = Message::new(
    ProtocolType::MQTT,
    "sensors/temperature".to_string(),
    "25.5".to_string().into_bytes(),
);
comm_manager.send_message(message).await?;

// 接收消息
let received_message = comm_manager.receive_message(ProtocolType::MQTT).await?;
println!("收到消息: {}", String::from_utf8_lossy(&received_message.payload));
```

### CoAP通信

```rust
// 连接CoAP
comm_manager.connect(ProtocolType::CoAP, "localhost:5683".to_string()).await?;

// 发送CoAP请求
let coap_message = Message::new(
    ProtocolType::CoAP,
    "/sensors/data".to_string(),
    serde_json::json!({"temperature": 25.5}).to_string().into_bytes(),
);
comm_manager.send_message(coap_message).await?;
```

## 数据存储

### 数据存储配置

```rust
use c17_iot::data_storage::{StorageManager, StorageType, StorageConfig};

let config = StorageConfig {
    storage_type: StorageType::InMemory,
    connection_string: "memory://".to_string(),
    max_connections: 10,
    timeout: std::time::Duration::from_secs(30),
};
let mut storage_manager = StorageManager::new(config);
storage_manager.initialize().await?;
```

### 存储数据

```rust
use c17_iot::data_storage::DataPoint;

let data_point = DataPoint {
    id: "data_001".to_string(),
    timestamp: chrono::Utc::now(),
    device_id: "sensor_001".to_string(),
    data: serde_json::json!({
        "temperature": 25.5,
        "humidity": 60.0
    }),
    tags: std::collections::HashMap::new(),
};

storage_manager.store_data(data_point).await?;
```

### 查询数据

```rust
use c17_iot::data_storage::Query;

let query = Query {
    device_ids: vec!["sensor_001".to_string()],
    start_time: Some(chrono::Utc::now() - chrono::Duration::hours(1)),
    end_time: Some(chrono::Utc::now()),
    limit: Some(100),
    offset: Some(0),
};

let results = storage_manager.query_data(query).await?;
for data_point in results {
    println!("数据: {:?}", data_point);
}
```

## 硬件抽象

### GPIO控制

```rust
use c17_iot::hardware_abstraction::gpio::{GPIOManager, PinConfig, PinMode, PinState};

let mut gpio_manager = GPIOManager::new();
gpio_manager.initialize().await?;

// 配置输出引脚
let output_config = PinConfig {
    mode: PinMode::Output,
    initial_state: Some(PinState::Low),
    interrupt_trigger: None,
    debounce_time: None,
};
gpio_manager.configure_pin(18, output_config).await?;

// 设置引脚状态
gpio_manager.set_pin_state(18, PinState::High).await?;

// 配置输入引脚
let input_config = PinConfig {
    mode: PinMode::Input,
    initial_state: None,
    interrupt_trigger: Some(c17_iot::hardware_abstraction::gpio::InterruptTrigger::Rising),
    debounce_time: Some(std::time::Duration::from_millis(50)),
};
gpio_manager.configure_pin(24, input_config).await?;

// 读取引脚状态
let pin_state = gpio_manager.get_pin_state(24).await?;
println!("引脚24状态: {:?}", pin_state);
```

## 示例应用

### 完整IoT应用

```rust
use c17_iot::examples_demos::CompleteIoTAppExample;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut app = CompleteIoTAppExample::new().await?;
    app.run().await?;
    Ok(())
}
```

### 高级演示

```rust
use c17_iot::examples_demos::AdvancedIoTDemo;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut demo = AdvancedIoTDemo::new()?;
    demo.run().await?;
    Ok(())
}
```

## 最佳实践

### 1. 错误处理

```rust
use c17_iot::device_management::DeviceManagementError;

match device_manager.register_device("device_001", "sensor", "room1").await {
    Ok(()) => println!("设备注册成功"),
    Err(DeviceManagementError::DeviceAlreadyExists) => {
        println!("设备已存在，跳过注册");
    }
    Err(e) => {
        eprintln!("设备注册失败: {}", e);
        return Err(e.into());
    }
}
```

### 2. 资源清理

```rust
use c17_iot::sensor_network::SensorNetwork;

let mut sensor_network = SensorNetwork::new();

// 使用完成后清理资源
defer! {
    if let Err(e) = sensor_network.stop_data_collection().await {
        eprintln!("停止数据采集失败: {}", e);
    }
}

sensor_network.start_data_collection().await?;
// ... 使用传感器网络
```

### 3. 配置管理

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct AppConfig {
    device_manager: DeviceManagerConfig,
    sensor_network: SensorNetworkConfig,
    storage: StorageConfig,
}

#[derive(Debug, Serialize, Deserialize)]
struct DeviceManagerConfig {
    max_devices: usize,
    device_timeout: u64,
}

// 从文件加载配置
let config: AppConfig = serde_json::from_str(&std::fs::read_to_string("config.json")?)?;
```

### 4. 日志记录

```rust
use log::{info, warn, error};

// 启用日志
env_logger::init();

info!("启动IoT应用");
warn!("设备连接超时");
error!("数据存储失败");
```

### 5. 性能优化

```rust
// 使用批处理操作
let mut data_points = Vec::new();
for i in 0..1000 {
    data_points.push(DataPoint {
        id: format!("data_{}", i),
        timestamp: chrono::Utc::now(),
        device_id: "sensor_001".to_string(),
        data: serde_json::json!({"value": i}),
        tags: std::collections::HashMap::new(),
    });
}

// 批量存储
storage_manager.store_data_batch(data_points).await?;
```

## 故障排除

### 常见问题

1. **设备连接失败**
   - 检查网络连接
   - 验证设备配置
   - 查看错误日志

2. **数据采集异常**
   - 检查传感器状态
   - 验证数据格式
   - 确认采样率设置

3. **规则引擎不工作**
   - 检查规则语法
   - 验证条件逻辑
   - 确认数据字段名称

4. **认证失败**
   - 检查证书有效性
   - 验证令牌状态
   - 确认访问权限

### 调试技巧

```rust
// 启用详细日志
std::env::set_var("RUST_LOG", "debug");

// 使用调试模式
#[cfg(debug_assertions)]
{
    println!("调试信息: {:?}", debug_data);
}

// 性能分析
let start = std::time::Instant::now();
// ... 执行操作
let duration = start.elapsed();
println!("操作耗时: {:?}", duration);
```

## 支持和帮助

- 查看 [API 参考文档](API_REFERENCE.md)
- 阅读 [最佳实践指南](BEST_PRACTICES.md)
- 查看 [示例代码](../src/examples_demos/)
- 提交 [Issue](https://github.com/your-repo/c17_iot/issues)
