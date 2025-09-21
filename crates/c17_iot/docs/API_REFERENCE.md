# c17_iot API 参考文档

## 概述

`c17_iot` 是一个基于 Rust 1.90 的完整 IoT 开发解决方案，提供了从嵌入式系统到云端的全方位功能支持。

## 核心模块

### 1. 设备管理 (Device Management)

#### DeviceManager

设备管理器负责管理 IoT 设备的状态、配置和生命周期。

```rust
use c17_iot::device_management::DeviceManager;

// 创建设备管理器
let mut device_manager = DeviceManager::new();

// 注册设备
device_manager.register_device("device_001", "temperature_sensor", "room1").await?;

// 获取设备状态
let status = device_manager.get_device_status("device_001").await?;
```

#### 主要方法

- `register_device(device_id, device_type, location)` - 注册新设备
- `unregister_device(device_id)` - 注销设备
- `get_device_status(device_id)` - 获取设备状态
- `update_device_config(device_id, config)` - 更新设备配置
- `get_all_devices()` - 获取所有设备列表

### 2. 传感器网络 (Sensor Network)

#### SensorNetwork

传感器网络管理器处理传感器数据的采集、处理和传输。

```rust
use c17_iot::sensor_network::SensorNetwork;

// 创建传感器网络
let mut sensor_network = SensorNetwork::new();

// 添加传感器
sensor_network.add_sensor("temp_001", "temperature", "room1").await?;

// 开始数据采集
sensor_network.start_data_collection().await?;
```

#### 主要方法

- `add_sensor(sensor_id, sensor_type, location)` - 添加传感器
- `remove_sensor(sensor_id)` - 移除传感器
- `start_data_collection()` - 开始数据采集
- `stop_data_collection()` - 停止数据采集
- `get_sensor_data(sensor_id)` - 获取传感器数据

### 3. 边缘计算 (Edge Computing)

#### RuleEngine

规则引擎提供智能决策和自动化控制功能。

```rust
use c17_iot::edge_computing::{RuleEngine, Rule, Condition, Action};
use c17_iot::edge_computing::rule_engine::{Operator, AlertLevel};

// 创建规则引擎
let (mut rule_engine, _) = RuleEngine::new();

// 创建规则
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

let rule = Rule::new(
    "temp_alert".to_string(),
    "温度告警".to_string(),
    condition,
    action,
    1,
);

// 添加规则
rule_engine.add_rule(rule).await?;
```

#### 主要方法

- `add_rule(rule)` - 添加规则
- `remove_rule(rule_id)` - 移除规则
- `evaluate_rules(context)` - 评估规则
- `add_ml_model(model)` - 添加机器学习模型
- `predict_with_model(model_id, input_data)` - 使用模型预测

### 4. 安全认证 (Security)

#### DeviceAuthenticator

设备认证器提供设备身份验证和访问控制功能。

```rust
use c17_iot::security::DeviceAuthenticator;
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
    public_key: "public_key_data".to_string().into_bytes(),
    issued_at: chrono::Utc::now(),
    expires_at: chrono::Utc::now() + chrono::Duration::days(365),
    issuer: "CA".to_string(),
    signature: vec![],
    certificate_chain: vec![],
    extensions: std::collections::HashMap::new(),
};

// 认证设备
let token = authenticator.authenticate_device("device_001", &certificate)?;
```

#### 主要方法

- `authenticate_device(device_id, certificate)` - 认证设备
- `verify_token(token)` - 验证令牌
- `refresh_token(token)` - 刷新令牌
- `check_access(device_id, resource, action)` - 检查访问权限
- `create_session(device_id, user_id, ip_address, user_agent)` - 创建会话

### 5. 监控 (Monitoring)

#### MonitoringDashboard

监控仪表盘提供系统状态的可视化和监控功能。

```rust
use c17_iot::monitoring::dashboard::{MonitoringDashboard, DashboardConfig};

// 创建监控仪表盘
let config = DashboardConfig::default();
let mut dashboard = MonitoringDashboard::new(config);

// 更新系统状态
dashboard.update_system_status().await?;

// 获取实时数据
let realtime_data = dashboard.get_realtime_data().await?;

// 导出数据
let json_data = dashboard.export_data(c17_iot::monitoring::dashboard::ExportFormat::Json).await?;
```

#### 主要方法

- `update_system_status()` - 更新系统状态
- `get_realtime_data()` - 获取实时数据
- `get_historical_data(start_time, end_time)` - 获取历史数据
- `export_data(format)` - 导出数据
- `set_alert_thresholds(thresholds)` - 设置告警阈值

### 6. 通信协议 (Communication)

#### CommunicationManager

通信管理器统一管理各种通信协议。

```rust
use c17_iot::communication::{CommunicationManager, ProtocolType, Message};

// 创建通信管理器
let mut comm_manager = CommunicationManager::new();

// 初始化
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
```

#### 主要方法

- `initialize()` - 初始化通信管理器
- `connect(protocol, endpoint)` - 连接协议
- `disconnect(protocol)` - 断开协议连接
- `send_message(message)` - 发送消息
- `receive_message(protocol)` - 接收消息

### 7. 数据存储 (Data Storage)

#### StorageManager

存储管理器提供数据持久化和缓存功能。

```rust
use c17_iot::data_storage::{StorageManager, StorageType, StorageConfig, DataPoint};

// 创建存储管理器
let config = StorageConfig {
    storage_type: StorageType::InMemory,
    connection_string: "memory://".to_string(),
    max_connections: 10,
    timeout: std::time::Duration::from_secs(30),
};
let mut storage_manager = StorageManager::new(config);

// 初始化
storage_manager.initialize().await?;

// 存储数据
let data_point = DataPoint {
    id: "data_001".to_string(),
    timestamp: chrono::Utc::now(),
    device_id: "device_001".to_string(),
    data: serde_json::json!({"temperature": 25.5}),
    tags: std::collections::HashMap::new(),
};
storage_manager.store_data(data_point).await?;
```

#### 主要方法

- `initialize()` - 初始化存储管理器
- `store_data(data_point)` - 存储数据
- `retrieve_data(data_id)` - 检索数据
- `query_data(query)` - 查询数据
- `backup_data()` - 备份数据

### 8. 硬件抽象 (Hardware Abstraction)

#### GPIOManager

GPIO管理器提供硬件接口的抽象和控制。

```rust
use c17_iot::hardware_abstraction::gpio::{GPIOManager, PinConfig, PinMode, PinState};

// 创建GPIO管理器
let mut gpio_manager = GPIOManager::new();

// 初始化
gpio_manager.initialize().await?;

// 配置引脚
let pin_config = PinConfig {
    mode: PinMode::Output,
    initial_state: Some(PinState::Low),
    interrupt_trigger: None,
    debounce_time: None,
};
gpio_manager.configure_pin(18, pin_config).await?;

// 设置引脚状态
gpio_manager.set_pin_state(18, PinState::High).await?;
```

#### 主要方法

- `initialize()` - 初始化GPIO管理器
- `configure_pin(pin, config)` - 配置引脚
- `set_pin_state(pin, state)` - 设置引脚状态
- `get_pin_state(pin)` - 获取引脚状态
- `get_pin_info(pin)` - 获取引脚信息

## 示例和演示

### 基础示例

```rust
use c17_iot::examples_demos::CompleteIoTAppExample;

// 创建完整IoT应用示例
let mut app = CompleteIoTAppExample::new().await?;

// 运行示例
app.run().await?;
```

### 高级演示

```rust
use c17_iot::examples_demos::AdvancedIoTDemo;

// 创建高级IoT演示
let mut demo = AdvancedIoTDemo::new()?;

// 运行演示
demo.run().await?;
```

### 性能基准测试

```rust
use c17_iot::examples_demos::PerformanceBenchmark;

// 创建性能基准测试
let mut benchmark = PerformanceBenchmark::new()?;

// 运行基准测试
let results = benchmark.run_full_benchmark().await?;
```

### 安全测试

```rust
use c17_iot::examples_demos::SecurityTest;

// 创建安全测试
let mut security_test = SecurityTest::new()?;

// 运行安全测试
let results = security_test.run_security_tests().await?;
```

## 配置选项

### 功能特性

可以通过 `Cargo.toml` 中的 features 来启用特定功能：

```toml
[dependencies.c17_iot]
version = "0.1.0"
features = [
    "kafka",           # Kafka 支持
    "influx",          # InfluxDB 支持
    "openssl-examples" # OpenSSL 示例
]
```

### 环境变量

- `C17_IOT_LOG_LEVEL` - 日志级别 (debug, info, warn, error)
- `C17_IOT_CONFIG_PATH` - 配置文件路径
- `C17_IOT_DATA_PATH` - 数据存储路径

## 错误处理

所有模块都使用统一的错误处理机制：

```rust
use c17_iot::device_management::DeviceManagementError;

match device_manager.register_device("device_001", "sensor", "room1").await {
    Ok(()) => println!("设备注册成功"),
    Err(DeviceManagementError::DeviceAlreadyExists) => println!("设备已存在"),
    Err(e) => eprintln!("注册失败: {}", e),
}
```

## 最佳实践

1. **资源管理**: 确保在使用完组件后正确清理资源
2. **错误处理**: 始终处理可能的错误情况
3. **配置管理**: 使用配置文件管理应用设置
4. **日志记录**: 启用适当的日志级别进行调试
5. **性能优化**: 使用缓存和批处理操作提高性能

## 许可证

本项目采用 MIT 许可证。详见 [LICENSE](LICENSE) 文件。

## 贡献

欢迎贡献代码！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解详细信息。

## 支持

如有问题或建议，请通过以下方式联系：

- 创建 Issue: [GitHub Issues](https://github.com/your-repo/c17_iot/issues)
- 邮件: <support@example.com>
- 文档: [项目文档](https://docs.example.com/c17_iot)
