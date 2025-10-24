# 系统示例（System Examples）索引


## 📊 目录

- [系统示例（System Examples）索引](#系统示例system-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [系统调用](#系统调用)
    - [设备驱动](#设备驱动)
    - [系统工具](#系统工具)
    - [操作系统](#操作系统)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)


## 目的

- 提供 Rust 系统编程的实用示例。
- 展示如何构建系统级应用。

## 核心示例

### 系统调用

- 文件系统操作
- 进程管理
- 网络系统调用
- 内存管理

### 设备驱动

- 字符设备驱动
- 块设备驱动
- 网络设备驱动
- 输入设备驱动

### 系统工具

- 命令行工具
- 系统监控工具
- 性能分析工具
- 调试工具

### 操作系统

- 内核模块
- 引导程序
- 系统服务
- 系统库

## 实践与样例

- 系统示例：参见 [crates/c75_system_programming](../../../crates/c75_system_programming/)
- 嵌入式系统：[crates/c18_embedded](../../../crates/c18_embedded/)
- 操作系统：[crates/c76_operating_system](../../../crates/c76_operating_system/)

### 文件级清单（精选）

- `crates/c75_system_programming/src/`：
  - `system_calls.rs`：系统调用示例
  - `device_drivers.rs`：设备驱动示例
  - `system_tools.rs`：系统工具示例
  - `os_components.rs`：操作系统组件示例
- `crates/c18_embedded/src/`：
  - `embedded_systems.rs`：嵌入式系统示例
  - `real_time_systems.rs`：实时系统示例
  - `iot_devices.rs`：IoT 设备示例

## 相关索引

- 理论基础（内存安全）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 应用领域（嵌入式）：[`../../04_application_domains/03_iot/00_index.md`](../../04_application_domains/03_iot/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- Web 示例：[`../08_web_examples/00_index.md`](../08_web_examples/00_index.md)
- 嵌入式示例：[`../10_embedded_examples/00_index.md`](../10_embedded_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
