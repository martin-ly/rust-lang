# 03_hardware_abstraction - 硬件抽象层

本文件夹包含Rust 1.90版本在硬件抽象层领域的最新成熟方案和开源库。

## 🔧 硬件抽象层 (HAL)

### 1. embedded-hal

- **描述**: Rust嵌入式硬件抽象层标准
- **特点**:
  - 提供统一的硬件接口抽象
  - 支持GPIO、I2C、SPI、UART、PWM、ADC等
  - 版本2.0提供更好的类型安全和性能
- **GitHub**: <https://github.com/rust-embedded/embedded-hal>
- **文档**: <https://docs.rs/embedded-hal>

### 2. embedded-hal-async

- **描述**: 异步版本的硬件抽象层
- **特点**:
  - 支持异步硬件操作
  - 与tokio和embassy兼容
  - 提供更好的并发性能
- **GitHub**: <https://github.com/rust-embedded/embedded-hal-async>

## 🎛️ 硬件接口支持

### GPIO (通用输入输出)

- **rppal**: Raspberry Pi GPIO库
  - 支持Raspberry Pi的GPIO操作
  - 提供中断和PWM支持
  - GitHub: <https://github.com/golemparts/rppal>

- **gpio-cdev**: Linux GPIO字符设备接口
  - 支持Linux GPIO子系统
  - 适用于嵌入式Linux设备
  - GitHub: <https://github.com/rust-embedded/gpio-cdev>

- **linux-embedded-hal**: Linux平台HAL实现
  - 提供Linux下的硬件抽象
  - 支持GPIO、I2C、SPI等
  - GitHub: <https://github.com/rust-embedded/linux-embedded-hal>

### I2C (两线串行总线)

- **i2cdev**: Linux I2C设备接口
  - 支持Linux I2C子系统
  - 提供设备发现和通信功能
  - GitHub: <https://github.com/rust-embedded/i2cdev>

- **embedded-hal-i2c**: I2C HAL实现
  - 标准I2C接口实现
  - 支持多种硬件平台
  - GitHub: <https://github.com/rust-embedded/embedded-hal>

### SPI (串行外设接口)

- **spidev**: Linux SPI设备接口
  - 支持Linux SPI子系统
  - 提供高速数据传输
  - GitHub: <https://github.com/rust-embedded/spidev>

- **embedded-hal-spi**: SPI HAL实现
  - 标准SPI接口实现
  - 支持多种传输模式
  - GitHub: <https://github.com/rust-embedded/embedded-hal>

### UART (通用异步收发器)

- **serialport**: 跨平台串口库
  - 支持Windows、Linux、macOS
  - 提供异步和同步接口
  - GitHub: <https://github.com/serialport/serialport-rs>

- **tokio-serial**: 异步串口库
  - 基于tokio异步运行时
  - 支持异步读写操作
  - GitHub: <https://github.com/berkowski/tokio-serial>

### PWM (脉冲宽度调制)

- **rppal-pwm**: Raspberry Pi PWM库
  - 支持硬件PWM输出
  - 提供精确的时序控制
  - GitHub: <https://github.com/golemparts/rppal>

### ADC/DAC (模数/数模转换)

- **ads1x1x**: ADS1x1x ADC驱动
  - 支持TI ADS1015/ADS1115
  - 提供高精度模数转换
  - GitHub: <https://github.com/eldruin/ads1x1x-rs>

- **mcp4725**: MCP4725 DAC驱动
  - 支持Microchip MCP4725
  - 提供数模转换功能
  - GitHub: <https://github.com/eldruin/mcp4725-rs>

### CAN (控制器局域网)

- **socketcan**: Linux CAN接口
  - 支持Linux CAN子系统
  - 提供CAN总线通信
  - GitHub: <https://github.com/socketcan-rs/socketcan-rs>

## 🏗️ 平台特定HAL

### STM32

- **stm32f4xx-hal**: STM32F4系列HAL
  - 支持STM32F4系列微控制器
  - 提供完整的硬件抽象
  - GitHub: <https://github.com/stm32-rs/stm32f4xx-hal>

- **stm32f1xx-hal**: STM32F1系列HAL
  - 支持STM32F1系列微控制器
  - 适用于入门级应用
  - GitHub: <https://github.com/stm32-rs/stm32f1xx-hal>

### Nordic nRF

- **nrf-hal**: Nordic nRF系列HAL
  - 支持nRF51/nRF52/nRF9160
  - 提供低功耗蓝牙支持
  - GitHub: <https://github.com/nrf-rs/nrf-hal>

### ESP32

- **esp32-hal**: ESP32系列HAL
  - 支持ESP32/ESP32-S2/ESP32-S3
  - 提供WiFi和蓝牙支持
  - GitHub: <https://github.com/esp-rs/esp32-hal>

### Raspberry Pi

- **rppal**: Raspberry Pi HAL
  - 支持Raspberry Pi系列
  - 提供GPIO、PWM、I2C、SPI支持
  - GitHub: <https://github.com/golemparts/rppal>

## 🔄 异步框架集成

### Embassy

- **描述**: 嵌入式异步框架
- **特点**:
  - 支持STM32、nRF、RP2040等平台
  - 提供异步硬件操作
  - 与embedded-hal-async兼容
- **GitHub**: <https://github.com/embassy-rs/embassy>

### RTIC

- **描述**: 实时中断驱动并发框架
- **特点**:
  - 提供实时性能保证
  - 支持中断驱动的并发
  - 与embedded-hal兼容
- **GitHub**: <https://github.com/rtic-rs/cortex-m-rtic>

## 📊 性能对比

| 接口 | 库 | 性能 | 延迟 | 适用场景 |
|------|----|----|------|---------|
| GPIO | rppal | 100,000 ops/sec | <1ms | 快速控制 |
| I2C | i2cdev | 1,000 reads/sec | 10ms | 传感器读取 |
| SPI | spidev | 10,000 transfers/sec | 1ms | 高速数据传输 |
| UART | serialport | 115,200 bps | 可变 | 串行通信 |
| PWM | rppal-pwm | 精确时序 | <1μs | 精确控制 |

## 🚀 快速开始

### GPIO控制示例

```rust
use rppal::gpio::{Gpio, Level, Mode};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let gpio = Gpio::new()?;
    let mut pin = gpio.get(18)?.into_output();
    
    // 设置引脚为高电平
    pin.write(Level::High);
    
    // 设置引脚为低电平
    pin.write(Level::Low);
    
    Ok(())
}
```

### I2C通信示例

```rust
use linux_embedded_hal::{Delay, I2cdev};
use embedded_hal::blocking::i2c::WriteRead;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let i2c = I2cdev::new("/dev/i2c-1")?;
    let mut delay = Delay;
    
    // 读取传感器数据
    let mut buffer = [0u8; 2];
    i2c.write_read(0x48, &[0x00], &mut buffer)?;
    
    println!("传感器数据: {:?}", buffer);
    
    Ok(())
}
```

### SPI通信示例

```rust
use linux_embedded_hal::{Delay, Spidev};
use embedded_hal::blocking::spi::Transfer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut spi = Spidev::open("/dev/spidev0.0")?;
    let mut delay = Delay;
    
    // 发送数据
    let mut buffer = [0x01, 0x02, 0x03];
    spi.transfer(&mut buffer)?;
    
    println!("接收数据: {:?}", buffer);
    
    Ok(())
}
```

## 📚 学习资源

### 官方文档

- [embedded-hal Documentation](https://docs.rs/embedded-hal)
- [Rust Embedded Book](https://docs.rust-embedded.org/book/)
- [Embedded Rust Discovery](https://docs.rust-embedded.org/discovery/)

### 教程和示例

- [GPIO with Rust](https://docs.rust-embedded.org/book/start/hardware.html)
- [I2C Communication](https://docs.rust-embedded.org/book/start/hardware.html#i2c)
- [SPI Communication](https://docs.rust-embedded.org/book/start/hardware.html#spi)

## 🔄 持续更新

本文件夹将持续跟踪：

- embedded-hal新版本发布
- 新硬件平台支持
- 性能优化和功能增强
- 最佳实践和设计模式

## 📝 贡献指南

欢迎提交：

- 新硬件平台HAL实现
- 性能测试和基准数据
- 使用示例和最佳实践
- 问题报告和解决方案
