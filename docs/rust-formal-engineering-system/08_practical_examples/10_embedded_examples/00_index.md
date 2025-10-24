# 嵌入式示例（Embedded Examples）索引


## 📊 目录

- [目的](#目的)
- [核心示例](#核心示例)
  - [微控制器编程](#微控制器编程)
  - [硬件抽象层](#硬件抽象层)
  - [传感器集成](#传感器集成)
  - [通信协议](#通信协议)
- [实践与样例](#实践与样例)
  - [文件级清单（精选）](#文件级清单精选)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 提供 Rust 嵌入式开发的实用示例。
- 展示如何构建嵌入式系统应用。

## 核心示例

### 微控制器编程

- ARM Cortex-M 编程
- AVR 微控制器编程
- RISC-V 微控制器编程
- 实时操作系统集成

### 硬件抽象层

- GPIO 操作示例
- 串口通信示例
- SPI/I2C 通信示例
- 定时器使用示例

### 传感器集成

- 温度传感器示例
- 加速度计示例
- 陀螺仪示例
- 环境传感器示例

### 通信协议

- UART 通信示例
- CAN 总线示例
- Modbus 协议示例
- 无线通信示例

## 实践与样例

- 嵌入式示例：参见 [crates/c18_embedded](../../../crates/c18_embedded/)
- IoT 开发：[crates/c17_iot](../../../crates/c17_iot/)
- 传感器网络：[crates/c19_sensors](../../../crates/c19_sensors/)

### 文件级清单（精选）

- `crates/c18_embedded/src/`：
  - `microcontroller_programming.rs`：微控制器编程示例
  - `hardware_abstraction.rs`：硬件抽象层示例
  - `sensor_integration.rs`：传感器集成示例
  - `communication_protocols.rs`：通信协议示例
- `crates/c17_iot/src/`：
  - `iot_devices.rs`：IoT 设备示例
  - `edge_computing.rs`：边缘计算示例
  - `device_management.rs`：设备管理示例

## 相关索引

- 理论基础（内存安全）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 应用领域（IoT）：[`../../04_application_domains/03_iot/00_index.md`](../../04_application_domains/03_iot/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 系统示例：[`../09_system_examples/00_index.md`](../09_system_examples/00_index.md)
- 数据库示例：[`../11_database_examples/00_index.md`](../11_database_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
