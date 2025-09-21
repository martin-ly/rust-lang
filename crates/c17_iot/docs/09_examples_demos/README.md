# 09_examples_demos - 示例和演示

本文件夹包含Rust 1.90版本在IoT领域的完整示例和演示项目。

## 🎯 示例项目分类

### 1. 基础示例

- **设备管理**: 设备注册、配置、监控
- **数据采集**: 传感器数据收集和处理
- **通信协议**: MQTT、CoAP、HTTP等协议使用
- **硬件控制**: GPIO、I2C、SPI等硬件接口

### 2. 高级示例

- **边缘计算**: 本地数据处理和决策
- **机器学习**: 模型推理和训练
- **安全认证**: 设备身份验证和加密
- **云平台集成**: AWS IoT、Azure IoT Hub等

### 3. 完整应用

- **智能家居**: 完整的智能家居系统
- **工业监控**: 工业设备监控系统
- **环境监测**: 环境数据采集和分析
- **智慧城市**: 城市基础设施监控

## 🚀 快速开始示例

### 基础设备管理

```rust
use c17_iot::prelude::*;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建设备管理器
    let mut device_manager = DeviceManager::new();
    
    // 注册设备
    let device_config = DeviceConfig {
        device_id: "sensor_001".to_string(),
        device_type: DeviceType::Sensor,
        protocol: Protocol::MQTT,
        endpoint: "mqtt://broker.example.com:1883".to_string(),
    };
    
    let device = device_manager.register_device(device_config).await?;
    println!("设备注册成功: {}", device.id());
    
    // 启动设备
    device.start().await?;
    
    // 模拟数据采集
    loop {
        let sensor_data = SensorData {
            device_id: device.id().clone(),
            timestamp: chrono::Utc::now(),
            temperature: 25.5,
            humidity: 60.0,
        };
        
        device.send_data(&sensor_data).await?;
        println!("发送数据: {:?}", sensor_data);
        
        sleep(Duration::from_secs(60)).await;
    }
}
```

### MQTT通信示例

```rust
use c17_iot::protocols::mqtt::MqttClient;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct SensorData {
    device_id: String,
    timestamp: chrono::DateTime<chrono::Utc>,
    temperature: f64,
    humidity: f64,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建MQTT客户端
    let mut client = MqttClient::new("mqtt://broker.example.com:1883").await?;
    
    // 连接到代理
    client.connect().await?;
    
    // 订阅主题
    client.subscribe("sensors/+/data").await?;
    
    // 发布消息
    let message = SensorData {
        device_id: "sensor_001".to_string(),
        timestamp: chrono::Utc::now(),
        temperature: 25.5,
        humidity: 60.0,
    };
    
    client.publish("sensors/sensor_001/data", &message).await?;
    
    // 接收消息
    while let Some(msg) = client.receive().await? {
        println!("收到消息: {:?}", msg);
        
        // 处理消息
        if let Ok(data) = serde_json::from_str::<SensorData>(&msg.payload) {
            println!("解析数据: {:?}", data);
        }
    }
    
    Ok(())
}
```

### GPIO控制示例

```rust
use c17_iot::hardware::gpio::GpioController;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建GPIO控制器
    let mut gpio = GpioController::new().await?;
    
    // 配置引脚
    gpio.set_pin_mode(18, PinMode::Output).await?; // LED
    gpio.set_pin_mode(24, PinMode::Input).await?;  // 按钮
    
    // LED闪烁
    loop {
        // 检查按钮状态
        let button_state = gpio.read_pin(24).await?;
        
        if button_state == PinState::High {
            // 按钮按下，LED闪烁
            for _ in 0..5 {
                gpio.write_pin(18, PinState::High).await?;
                sleep(Duration::from_millis(100)).await;
                gpio.write_pin(18, PinState::Low).await?;
                sleep(Duration::from_millis(100)).await;
            }
        } else {
            // 按钮未按下，LED常亮
            gpio.write_pin(18, PinState::High).await?;
        }
        
        sleep(Duration::from_millis(50)).await;
    }
}
```

### 边缘计算示例

```rust
use c17_iot::edge::EdgeProcessor;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct ProcessingRule {
    name: String,
    condition: String,
    action: Action,
}

#[derive(Debug, Serialize, Deserialize)]
enum Action {
    SendAlert { message: String, recipients: Vec<String> },
    AdjustDevice { device_id: String, parameter: String, value: f64 },
    LogEvent { level: String, message: String },
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建边缘处理器
    let mut processor = EdgeProcessor::new();
    
    // 注册处理规则
    processor.add_rule(ProcessingRule {
        name: "temperature_alert".to_string(),
        condition: "temperature > 30.0".to_string(),
        action: Action::SendAlert {
            message: "高温警报".to_string(),
            recipients: vec!["admin@example.com".to_string()],
        },
    });
    
    processor.add_rule(ProcessingRule {
        name: "humidity_control".to_string(),
        condition: "humidity < 40.0".to_string(),
        action: Action::AdjustDevice {
            device_id: "humidifier_001".to_string(),
            parameter: "power".to_string(),
            value: 80.0,
        },
    });
    
    // 启动边缘计算
    processor.start().await?;
    
    // 模拟数据流
    let mut data_stream = get_sensor_data_stream().await?;
    while let Some(data) = data_stream.next().await {
        // 处理数据
        let result = processor.process(data).await?;
        
        if let Some(action) = result {
            match action {
                Action::SendAlert { message, recipients } => {
                    println!("发送告警: {} 给: {:?}", message, recipients);
                }
                Action::AdjustDevice { device_id, parameter, value } => {
                    println!("调整设备 {} 的 {} 为 {}", device_id, parameter, value);
                }
                Action::LogEvent { level, message } => {
                    println!("记录事件 [{}]: {}", level, message);
                }
            }
        }
    }
    
    Ok(())
}
```

## 🏗️ 完整应用示例

### 智能家居系统

```rust
use c17_iot::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
struct SmartHome {
    devices: HashMap<String, Device>,
    rules: Vec<AutomationRule>,
    hub: Hub,
}

#[derive(Debug, Serialize, Deserialize)]
struct AutomationRule {
    name: String,
    trigger: Trigger,
    action: Action,
    enabled: bool,
}

#[derive(Debug, Serialize, Deserialize)]
enum Trigger {
    Time { hour: u8, minute: u8 },
    Sensor { device_id: String, condition: String },
    Manual { button_id: String },
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建智能家居系统
    let mut smart_home = SmartHome::new();
    
    // 添加设备
    smart_home.add_device(Device::new(
        "living_room_light".to_string(),
        DeviceType::Light,
        "192.168.1.100".to_string(),
    ));
    
    smart_home.add_device(Device::new(
        "living_room_sensor".to_string(),
        DeviceType::Sensor,
        "192.168.1.101".to_string(),
    ));
    
    // 添加自动化规则
    smart_home.add_rule(AutomationRule {
        name: "evening_light".to_string(),
        trigger: Trigger::Time { hour: 18, minute: 0 },
        action: Action::TurnOn { device_id: "living_room_light".to_string() },
        enabled: true,
    });
    
    smart_home.add_rule(AutomationRule {
        name: "motion_light".to_string(),
        trigger: Trigger::Sensor {
            device_id: "living_room_sensor".to_string(),
            condition: "motion_detected == true".to_string(),
        },
        action: Action::TurnOn { device_id: "living_room_light".to_string() },
        enabled: true,
    });
    
    // 启动系统
    smart_home.start().await?;
    
    // 运行主循环
    loop {
        smart_home.process_events().await?;
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}
```

### 工业监控系统

```rust
use c17_iot::prelude::*;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct IndustrialMonitor {
    machines: Vec<Machine>,
    alerts: Vec<Alert>,
    dashboard: Dashboard,
}

#[derive(Debug, Serialize, Deserialize)]
struct Machine {
    id: String,
    name: String,
    status: MachineStatus,
    sensors: Vec<Sensor>,
    last_maintenance: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
enum MachineStatus {
    Running,
    Stopped,
    Maintenance,
    Error,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建工业监控系统
    let mut monitor = IndustrialMonitor::new();
    
    // 添加机器
    monitor.add_machine(Machine {
        id: "machine_001".to_string(),
        name: "生产线1".to_string(),
        status: MachineStatus::Running,
        sensors: vec![
            Sensor::new("temperature".to_string(), "°C".to_string()),
            Sensor::new("vibration".to_string(), "mm/s".to_string()),
            Sensor::new("pressure".to_string(), "bar".to_string()),
        ],
        last_maintenance: chrono::Utc::now(),
    });
    
    // 启动监控
    monitor.start().await?;
    
    // 数据采集循环
    loop {
        for machine in &mut monitor.machines {
            // 读取传感器数据
            for sensor in &mut machine.sensors {
                let value = sensor.read().await?;
                
                // 检查告警条件
                if let Some(alert) = check_alert_conditions(sensor, value) {
                    monitor.add_alert(alert);
                }
                
                // 更新仪表盘
                monitor.dashboard.update_sensor_data(sensor.id(), value);
            }
            
            // 更新机器状态
            machine.status = determine_machine_status(&machine.sensors);
        }
        
        // 发送数据到云端
        monitor.send_to_cloud().await?;
        
        tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
    }
}
```

## 📊 性能测试示例

### 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use c17_iot::prelude::*;

fn benchmark_device_processing(c: &mut Criterion) {
    c.bench_function("device_data_processing", |b| {
        b.iter(|| {
            let data = SensorData {
                device_id: black_box("sensor_001".to_string()),
                timestamp: black_box(chrono::Utc::now()),
                temperature: black_box(25.5),
                humidity: black_box(60.0),
            };
            
            process_sensor_data(black_box(data))
        })
    });
}

fn benchmark_mqtt_publish(c: &mut Criterion) {
    c.bench_function("mqtt_publish", |b| {
        b.iter(|| {
            let message = "test message".to_string();
            publish_mqtt_message(black_box("test/topic"), black_box(&message))
        })
    });
}

criterion_group!(benches, benchmark_device_processing, benchmark_mqtt_publish);
criterion_main!(benches);
```

## 🧪 测试示例

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio_test;

    #[tokio::test]
    async fn test_device_registration() {
        let mut manager = DeviceManager::new();
        let config = DeviceConfig {
            device_id: "test_device".to_string(),
            device_type: DeviceType::Sensor,
            protocol: Protocol::MQTT,
            endpoint: "mqtt://test:1883".to_string(),
        };
        
        let device = manager.register_device(config).await.unwrap();
        assert_eq!(device.id(), "test_device");
    }

    #[tokio::test]
    async fn test_sensor_data_processing() {
        let data = SensorData {
            device_id: "sensor_001".to_string(),
            timestamp: chrono::Utc::now(),
            temperature: 25.5,
            humidity: 60.0,
        };
        
        let result = process_sensor_data(data).await;
        assert!(result.is_ok());
    }

    #[test]
    fn test_automation_rule_creation() {
        let rule = AutomationRule {
            name: "test_rule".to_string(),
            trigger: Trigger::Time { hour: 18, minute: 0 },
            action: Action::TurnOn { device_id: "light_001".to_string() },
            enabled: true,
        };
        
        assert_eq!(rule.name, "test_rule");
        assert!(rule.enabled);
    }
}
```

## 📚 学习资源

### 示例项目

- [Rust IoT Examples](https://github.com/rust-iot/examples)
- [Embedded Rust Examples](https://github.com/rust-embedded/rust-raspberrypi-OS-tutorials)
- [Tokio Examples](https://github.com/tokio-rs/tokio/tree/master/examples)

### 教程和指南

- [Rust IoT Tutorial](https://github.com/rust-iot/tutorial)
- [Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [Async Rust Tutorial](https://rust-lang.github.io/async-book/)

## 🔄 持续更新

本文件夹将持续跟踪：

- 新示例项目的添加
- 现有示例的优化
- 最佳实践的更新
- 性能改进和bug修复

## 📝 贡献指南

欢迎提交：

- 新的示例项目
- 现有示例的改进
- 测试用例和基准测试
- 文档和注释的完善
