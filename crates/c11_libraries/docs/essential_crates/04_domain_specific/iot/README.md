# IoT - 物联网开发

## 📋 目录

- [IoT - 物联网开发](#iot---物联网开发)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [嵌入式硬件](#嵌入式硬件)
    - [embedded-hal](#embedded-hal)
    - [Raspberry Pi GPIO](#raspberry-pi-gpio)
  - [传感器通信](#传感器通信)
    - [I2C 通信](#i2c-通信)
    - [串口通信](#串口通信)
  - [MQTT](#mqtt)
    - [发布/订阅](#发布订阅)
    - [异步 MQTT](#异步-mqtt)
  - [实战示例](#实战示例)
    - [温度监控系统](#温度监控系统)
  - [参考资源](#参考资源)

---

## 概述

Rust 在物联网和嵌入式领域表现出色，提供零成本抽象和内存安全。

### 核心依赖

```toml
[dependencies]
# 嵌入式核心
embedded-hal = "1.0"
embedded-io = "0.6"

# MQTT
rumqttc = "0.24"

# 串口通信
serialport = "4.3"

# GPIO
rppal = "0.17"  # Raspberry Pi
```

---

## 嵌入式硬件

### embedded-hal

```rust
use embedded_hal::digital::OutputPin;

struct Led<P: OutputPin> {
    pin: P,
}

impl<P: OutputPin> Led<P> {
    fn new(pin: P) -> Self {
        Self { pin }
    }
    
    fn on(&mut self) {
        self.pin.set_high().ok();
    }
    
    fn off(&mut self) {
        self.pin.set_low().ok();
    }
    
    fn toggle(&mut self) {
        self.pin.toggle().ok();
    }
}
```

### Raspberry Pi GPIO

```rust
use rppal::gpio::Gpio;
use std::thread;
use std::time::Duration;

fn blink_led() -> Result<(), Box<dyn std::error::Error>> {
    let gpio = Gpio::new()?;
    let mut pin = gpio.get(23)?.into_output();
    
    for _ in 0..10 {
        pin.set_high();
        thread::sleep(Duration::from_millis(500));
        
        pin.set_low();
        thread::sleep(Duration::from_millis(500));
    }
    
    Ok(())
}
```

---

## 传感器通信

### I2C 通信

```rust
use rppal::i2c::I2c;

fn read_sensor() -> Result<(), Box<dyn std::error::Error>> {
    let mut i2c = I2c::new()?;
    i2c.set_slave_address(0x48)?;  // 传感器地址
    
    // 读取数据
    let mut buffer = [0u8; 2];
    i2c.read(&mut buffer)?;
    
    let value = u16::from_be_bytes(buffer);
    println!("传感器值: {}", value);
    
    Ok(())
}
```

### 串口通信

```rust
use serialport::{SerialPort, SerialPortBuilder};
use std::time::Duration;

fn serial_communication() -> Result<(), Box<dyn std::error::Error>> {
    let mut port = serialport::new("/dev/ttyUSB0", 9600)
        .timeout(Duration::from_millis(10))
        .open()?;
    
    // 发送数据
    port.write(b"Hello, IoT!")?;
    
    // 读取数据
    let mut buffer = [0u8; 32];
    match port.read(&mut buffer) {
        Ok(n) => {
            println!("收到 {} 字节: {:?}", n, &buffer[..n]);
        }
        Err(e) => eprintln!("读取错误: {}", e),
    }
    
    Ok(())
}
```

---

## MQTT

### 发布/订阅

```rust
use rumqttc::{MqttOptions, Client, QoS};
use std::time::Duration;

fn mqtt_example() -> Result<(), Box<dyn std::error::Error>> {
    // 配置
    let mut mqttoptions = MqttOptions::new("rust_client", "broker.hivemq.com", 1883);
    mqttoptions.set_keep_alive(Duration::from_secs(5));
    
    let (mut client, mut connection) = Client::new(mqttoptions, 10);
    
    // 订阅主题
    client.subscribe("sensors/temperature", QoS::AtMostOnce)?;
    
    // 发布消息
    client.publish(
        "sensors/temperature",
        QoS::AtLeastOnce,
        false,
        b"22.5"
    )?;
    
    // 处理消息
    for (i, notification) in connection.iter().enumerate() {
        println!("通知 {}: {:?}", i, notification);
        
        if i > 10 {
            break;
        }
    }
    
    Ok(())
}
```

### 异步 MQTT

```rust
use rumqttc::{AsyncClient, MqttOptions, QoS, Event, Packet};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut mqttoptions = MqttOptions::new("async_client", "broker.hivemq.com", 1883);
    mqttoptions.set_keep_alive(std::time::Duration::from_secs(5));
    
    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);
    
    client.subscribe("sensors/#", QoS::AtMostOnce).await?;
    
    tokio::task::spawn(async move {
        loop {
            client.publish(
                "sensors/temp",
                QoS::AtLeastOnce,
                false,
                b"25.5"
            ).await.ok();
            
            tokio::time::sleep(std::time::Duration::from_secs(5)).await;
        }
    });
    
    while let Ok(notification) = eventloop.poll().await {
        if let Event::Incoming(Packet::Publish(p)) = notification {
            println!(
                "主题: {}, 负载: {:?}",
                p.topic,
                String::from_utf8_lossy(&p.payload)
            );
        }
    }
    
    Ok(())
}
```

---

## 实战示例

### 温度监控系统

```rust
use rumqttc::{AsyncClient, MqttOptions, QoS};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct SensorData {
    device_id: String,
    temperature: f32,
    humidity: f32,
    timestamp: i64,
}

async fn temperature_monitor() -> Result<(), Box<dyn std::error::Error>> {
    let mut mqttoptions = MqttOptions::new("temp_monitor", "localhost", 1883);
    mqttoptions.set_keep_alive(std::time::Duration::from_secs(5));
    
    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);
    
    // 模拟传感器数据采集
    tokio::task::spawn(async move {
        loop {
            let data = SensorData {
                device_id: "sensor_01".to_string(),
                temperature: 20.0 + rand::random::<f32>() * 10.0,
                humidity: 40.0 + rand::random::<f32>() * 20.0,
                timestamp: chrono::Utc::now().timestamp(),
            };
            
            let json = serde_json::to_string(&data).unwrap();
            client.publish(
                "home/living_room/sensors",
                QoS::AtLeastOnce,
                false,
                json.as_bytes()
            ).await.ok();
            
            tokio::time::sleep(std::time::Duration::from_secs(10)).await;
        }
    });
    
    // 处理事件
    loop {
        eventloop.poll().await?;
    }
}
```

---

## 参考资源

- [embedded-hal 文档](https://docs.rs/embedded-hal/)
- [rumqttc GitHub](https://github.com/bytebeamio/rumqtt)
- [Rust Embedded Book](https://rust-embedded.github.io/book/)
