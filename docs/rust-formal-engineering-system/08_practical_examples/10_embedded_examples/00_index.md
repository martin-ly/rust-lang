# 嵌入式示例（Embedded Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [嵌入式示例（Embedded Examples）索引](#嵌入式示例embedded-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 微控制器编程（Microcontroller Programming）](#1-微控制器编程microcontroller-programming)
    - [2. 硬件抽象层（Hardware Abstraction Layer）](#2-硬件抽象层hardware-abstraction-layer)
    - [3. 传感器集成（Sensor Integration）](#3-传感器集成sensor-integration)
    - [4. 通信协议（Communication Protocols）](#4-通信协议communication-protocols)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c18_embedded/src/`](#cratesc18_embeddedsrc)
      - [`crates/c17_iot/src/`](#cratesc17_iotsrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 嵌入式开发的实用示例，涵盖微控制器编程、硬件抽象层、传感器集成和通信协议等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **嵌入式开发**: 专注于嵌入式系统开发实践
- **最佳实践**: 基于 Rust 社区最新嵌入式实践
- **完整覆盖**: 涵盖多个嵌入式开发场景
- **易于理解**: 提供详细的嵌入式开发说明和代码示例

## 📚 核心示例

### 1. 微控制器编程（Microcontroller Programming）

**推荐库**: `cortex-m`, `avr-hal`, `riscv`, `rtfm`

- **ARM Cortex-M 编程**: STM32、Nordic nRF 等
- **AVR 微控制器编程**: Arduino、ATmega 等
- **RISC-V 微控制器编程**: RISC-V 架构支持
- **实时操作系统集成**: RTIC、FreeRTOS 集成

**相关资源**:

- [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [cortex-m 文档](https://docs.rs/cortex-m/)
- [avr-hal 文档](https://docs.rs/avr-hal/)

### 2. 硬件抽象层（Hardware Abstraction Layer）

**推荐库**: `embedded-hal`, `nb`, `embedded-time`

- **GPIO 操作**: 数字输入输出、中断处理
- **串口通信**: UART、USART 通信
- **SPI/I2C 通信**: SPI、I2C 总线通信
- **定时器使用**: 定时器、PWM 输出

**相关资源**:

- [embedded-hal 文档](https://docs.rs/embedded-hal/)
- [nb 文档](https://docs.rs/nb/)
- [embedded-time 文档](https://docs.rs/embedded-time/)

### 3. 传感器集成（Sensor Integration）

**推荐库**: `embedded-sensors`, `bme280`, `mpu6050`

- **温度传感器**: DS18B20、LM35 等
- **加速度计**: MPU6050、ADXL345 等
- **陀螺仪**: MPU6050、LSM6DS3 等
- **环境传感器**: BME280、DHT22 等

**相关资源**:

- [embedded-sensors 文档](https://docs.rs/embedded-sensors/)
- [bme280 文档](https://docs.rs/bme280/)
- [mpu6050 文档](https://docs.rs/mpu6050/)

### 4. 通信协议（Communication Protocols）

**推荐库**: `embedded-can`, `modbus`, `embedded-wireless`

- **UART 通信**: 串口通信、RS-485
- **CAN 总线**: CAN 总线通信
- **Modbus 协议**: Modbus RTU/TCP
- **无线通信**: WiFi、蓝牙、LoRa

**相关资源**:

- [embedded-can 文档](https://docs.rs/embedded-can/)
- [modbus 文档](https://docs.rs/modbus/)
- [embedded-wireless 文档](https://docs.rs/embedded-wireless/)

## 💻 实践与样例

### 代码示例位置

- **嵌入式示例**: [crates/c18_embedded](../../../crates/c18_embedded/)
- **IoT 开发**: [crates/c17_iot](../../../crates/c17_iot/)
- **传感器网络**: [crates/c19_sensors](../../../crates/c19_sensors/)

### 文件级清单（精选）

#### `crates/c18_embedded/src/`

- `microcontroller_programming.rs` - 微控制器编程示例
- `hardware_abstraction.rs` - 硬件抽象层示例
- `sensor_integration.rs` - 传感器集成示例
- `communication_protocols.rs` - 通信协议示例

#### `crates/c17_iot/src/`

- `iot_devices.rs` - IoT 设备示例
- `edge_computing.rs` - 边缘计算示例
- `device_management.rs` - 设备管理示例

### 快速开始示例

```rust
// 嵌入式 HAL 示例
use embedded_hal::digital::v2::OutputPin;

fn blink_led<P: OutputPin>(led: &mut P) {
    loop {
        led.set_high().unwrap();
        delay_ms(500);
        led.set_low().unwrap();
        delay_ms(500);
    }
}
```

```rust
// 传感器读取示例
use bme280::Bme280;

fn read_sensor() -> (f32, f32, f32) {
    let mut sensor = Bme280::new(i2c, 0x76);
    sensor.init().unwrap();
    let measurements = sensor.measure().unwrap();
    (measurements.temperature, measurements.humidity, measurements.pressure)
}
```

---

## 🔗 相关索引

- **理论基础（内存安全）**: [`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- **编程范式（并发）**: [`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- **应用领域（IoT）**: [`../../04_application_domains/03_iot/00_index.md`](../../04_application_domains/03_iot/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **系统示例**: [`../09_system_examples/00_index.md`](../09_system_examples/00_index.md)
- **数据库示例**: [`../11_database_examples/00_index.md`](../11_database_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
