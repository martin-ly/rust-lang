# 01_embedded_os - 嵌入式操作系统

本文件夹包含Rust 1.90版本在嵌入式操作系统领域的最新成熟方案。

## 🎯 主要嵌入式操作系统

### 1. TockOS

- **描述**: 专为无线传感器网络节点设计的开源实时操作系统
- **特点**:
  - 内核采用Rust编写，提供类型安全和模块化接口
  - 支持多种微控制器架构（ARM Cortex-M系列等）
  - 提供实时内核、硬件内存保护、低功耗支持
- **适用场景**: 对安全性和性能有高要求的IoT应用
- **GitHub**: <https://github.com/tock/tock>
- **文档**: <https://book.tockos.org/>

### 2. RIOT

- **描述**: 面向物联网设备的低内存占用操作系统
- **特点**:
  - 支持多种硬件平台（TI MSP430、ARM7、ARM Cortex-M系列等）
  - 微内核架构，支持多线程
  - 支持IPv6、6LoWPAN等通信协议栈
- **适用场景**: 资源受限的IoT设备
- **GitHub**: <https://github.com/RIOT-OS/RIOT>
- **文档**: <https://doc.riot-os.org/>

### 3. Hubris

- **描述**: 新开源的嵌入式实时操作系统
- **特点**:
  - 提供高效的实时性能和安全性
  - 专为嵌入式系统设计
- **适用场景**: 需要高实时性能的嵌入式应用
- **GitHub**: <https://github.com/oxidecomputer/hubris>

### 4. OpenHarmony

- **描述**: 由开放原子开源基金会运营的开源项目
- **特点**:
  - 支持多种硬件平台（ARM Cortex-M、RISC-V 32位等）
  - 适用于物联网、智能手表、机器人等设备
- **适用场景**: 多设备生态系统的IoT应用
- **官网**: <https://www.openharmony.cn/>

## 🔧 相关Rust库

### 嵌入式框架

- **RTIC (Real-Time Interrupt-driven Concurrency)**: 嵌入式并发框架，已发布1.0版本
- **Embassy**: 嵌入式异步框架，支持STM32、nRF、RP2040等平台

### 网络协议栈

- **smoltcp**: 嵌入式TCP/IP协议栈，轻量级网络协议支持

### 图形库

- **embedded-graphics**: 嵌入式图形库，支持no_std环境下的2D图形绘制

## 📚 学习资源

### 官方文档

- [TockOS Book](https://book.tockos.org/)
- [RIOT Documentation](https://doc.riot-os.org/)
- [Rust Embedded Book](https://docs.rust-embedded.org/book/)

### 教程和示例

- [Rust Embedded Discovery](https://docs.rust-embedded.org/discovery/)
- [Embedded Rust by Example](https://docs.rust-embedded.org/embedonomicon/)

## 🚀 快速开始

### 使用TockOS

```bash
# 克隆TockOS仓库
git clone https://github.com/tock/tock.git
cd tock

# 构建内核
make

# 运行示例应用
make flash
```

### 使用RIOT

```bash
# 克隆RIOT仓库
git clone https://github.com/RIOT-OS/RIOT.git
cd RIOT

# 构建示例
make BOARD=native

# 运行
make term
```

## 🔄 持续更新

本文件夹将持续跟踪以下内容：

- 各操作系统的版本更新
- 新功能的发布
- 性能优化和安全性改进
- 社区贡献和最佳实践

## 📝 贡献指南

欢迎提交以下内容：

- 新的嵌入式操作系统信息
- 使用经验和最佳实践
- 性能测试和基准数据
- 问题报告和解决方案
