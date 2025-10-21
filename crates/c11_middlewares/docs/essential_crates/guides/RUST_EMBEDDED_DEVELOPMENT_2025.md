# Rust 嵌入式开发指南 (2025)

> **目标读者**: 希望使用 Rust 进行嵌入式系统开发、IoT 设备编程，或了解裸机编程的开发者。

## 📋 目录

- [Rust 嵌入式开发指南 (2025)](#rust-嵌入式开发指南-2025)
  - [📋 目录](#-目录)
  - [1. 嵌入式 Rust 概述](#1-嵌入式-rust-概述)
    - [1.1 为什么选择 Rust?](#11-为什么选择-rust)
    - [1.2 核心概念](#12-核心概念)
    - [1.3 开发环境搭建](#13-开发环境搭建)
  - [2. 裸机编程基础](#2-裸机编程基础)
    - [2.1 #!\[no\_std\] 环境](#21-no_std-环境)
    - [2.2 启动流程](#22-启动流程)
    - [2.3 内存布局](#23-内存布局)
  - [3. HAL 抽象层](#3-hal-抽象层)
    - [3.1 embedded-hal](#31-embedded-hal)
    - [3.2 GPIO 操作](#32-gpio-操作)
    - [3.3 外设驱动](#33-外设驱动)
  - [4. RTOS 集成](#4-rtos-集成)
    - [4.1 RTIC 实时框架](#41-rtic-实时框架)
    - [4.2 Embassy 异步框架](#42-embassy-异步框架)
    - [4.3 任务调度](#43-任务调度)
  - [5. 通信协议](#5-通信协议)
    - [5.1 UART 串口通信](#51-uart-串口通信)
    - [5.2 I2C 总线](#52-i2c-总线)
    - [5.3 SPI 接口](#53-spi-接口)
  - [6. 电源管理](#6-电源管理)
    - [6.1 低功耗模式](#61-低功耗模式)
    - [6.2 睡眠唤醒](#62-睡眠唤醒)
    - [6.3 电池优化](#63-电池优化)
  - [7. 调试与测试](#7-调试与测试)
    - [7.1 probe-rs 调试](#71-probe-rs-调试)
    - [7.2 单元测试](#72-单元测试)
    - [7.3 硬件在环测试](#73-硬件在环测试)
  - [8. 实战案例](#8-实战案例)
    - [8.1 案例1: LED 闪烁 (Hello World)](#81-案例1-led-闪烁-hello-world)
    - [8.2 案例2: 温湿度传感器](#82-案例2-温湿度传感器)
    - [8.3 案例3: 物联网设备](#83-案例3-物联网设备)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 常见问题](#10-常见问题)
  - [11. 参考资源](#11-参考资源)

---

## 1. 嵌入式 Rust 概述

### 1.1 为什么选择 Rust?

```text
┌────────────────────────────────────────────────────────────┐
│           Rust vs C/C++ (嵌入式开发对比)                   │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  ✅ Rust 优势:                                             │
│     - 内存安全 (无空指针/缓冲区溢出)                       │
│     - 线程安全 (编译时检测数据竞争)                        │
│     - 零成本抽象 (性能等同 C)                              │
│     - 现代工具链 (Cargo, 包管理)                           │
│     - 强大的类型系统 (减少运行时错误)                      │
│                                                            │
│  ⚠️  挑战:                                                  │
│     - 学习曲线陡峭                                         │
│     - 编译时间较长                                         │
│     - 生态系统仍在发展                                     │
│     - 部分硬件缺少官方支持                                 │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

### 1.2 核心概念

**嵌入式 Rust 技术栈**:

```text
┌──────────────────────────────────────────────────────────────┐
│              嵌入式 Rust 技术栈                              │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌────────────────────────────────────────────────────┐     │
│  │           应用层 (Application)                     │     │
│  │  - 业务逻辑                                        │     │
│  │  - 协议栈 (MQTT, CoAP)                             │     │
│  │  - 数据处理                                        │     │
│  └────────────────────────────────────────────────────┘     │
│                       │                                      │
│                       ▼                                      │
│  ┌────────────────────────────────────────────────────┐     │
│  │          RTOS 层 (Real-Time OS)                    │     │
│  │  - RTIC (中断驱动)                                 │     │
│  │  - Embassy (异步运行时)                            │     │
│  │  - FreeRTOS 绑定                                   │     │
│  └────────────────────────────────────────────────────┘     │
│                       │                                      │
│                       ▼                                      │
│  ┌────────────────────────────────────────────────────┐     │
│  │          HAL 层 (Hardware Abstraction)             │     │
│  │  - GPIO, UART, I2C, SPI                            │     │
│  │  - 定时器, ADC, PWM                                │     │
│  │  - 芯片特定 HAL (stm32, nrf, esp)                  │     │
│  └────────────────────────────────────────────────────┘     │
│                       │                                      │
│                       ▼                                      │
│  ┌────────────────────────────────────────────────────┐     │
│  │          PAC 层 (Peripheral Access Crate)          │     │
│  │  - 寄存器访问                                      │     │
│  │  - 由 svd2rust 生成                                │     │
│  └────────────────────────────────────────────────────┘     │
│                       │                                      │
│                       ▼                                      │
│  ┌────────────────────────────────────────────────────┐     │
│  │          硬件层 (Hardware)                         │     │
│  │  - MCU (STM32, nRF52, ESP32)                       │     │
│  │  - 外设 (传感器, 显示屏, 通信模块)                │     │
│  └────────────────────────────────────────────────────┘     │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 1.3 开发环境搭建

**安装工具链**:

```bash
# 1. 安装 Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 2. 添加目标平台 (以 ARM Cortex-M 为例)
rustup target add thumbv7em-none-eabihf  # Cortex-M4F/M7F
rustup target add thumbv6m-none-eabi     # Cortex-M0/M0+
rustup target add thumbv7m-none-eabi     # Cortex-M3

# 3. 安装 cargo-binutils
cargo install cargo-binutils
rustup component add llvm-tools-preview

# 4. 安装 probe-rs (调试工具)
cargo install probe-rs --features cli

# 5. 安装 cargo-embed
cargo install cargo-embed

# 6. 安装 cargo-flash
cargo install cargo-flash
```

**创建嵌入式项目**:

```bash
# 使用模板创建项目
cargo install cargo-generate
cargo generate --git https://github.com/rust-embedded/cortex-m-quickstart

# 或手动创建
cargo new --bin blinky
cd blinky
```

---

## 2. 裸机编程基础

### 2.1 #![no_std] 环境

**最小化 main.rs**:

```rust
// src/main.rs
#![no_std]
#![no_main]

use panic_halt as _;  // Panic 处理器

use cortex_m_rt::entry;

#[entry]
fn main() -> ! {
    // 主程序逻辑
    
    loop {
        // 无限循环 (嵌入式程序不应退出)
    }
}
```

**Cargo.toml 配置**:

```toml
[package]
name = "blinky"
version = "0.1.0"
edition = "2021"

[dependencies]
cortex-m = "0.7"
cortex-m-rt = "0.7"
panic-halt = "0.2"

# 芯片特定的 HAL
stm32f4xx-hal = { version = "0.21", features = ["stm32f401"] }

[[bin]]
name = "blinky"
test = false
bench = false

[profile.release]
opt-level = "z"        # 优化大小
lto = true             # 链接时优化
codegen-units = 1      # 单编译单元
strip = true           # 移除调试信息
```

**.cargo/config.toml**:

```toml
[target.thumbv7em-none-eabihf]
runner = "probe-rs run --chip STM32F401RETx"
rustflags = [
  "-C", "link-arg=-Tlink.x",
]

[build]
target = "thumbv7em-none-eabihf"
```

### 2.2 启动流程

**启动代码 (由 cortex-m-rt 提供)**:

```text
┌──────────────────────────────────────────────────────────────┐
│                嵌入式 Rust 启动流程                          │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 复位向量 (Reset Vector)                                  │
│     - CPU 复位后跳转到 Reset_Handler                         │
│           │                                                  │
│           ▼                                                  │
│  2. Reset_Handler                                            │
│     - 初始化 .data 段 (从 Flash 复制到 RAM)                  │
│     - 清零 .bss 段                                           │
│     - 调用 __pre_init (可选)                                 │
│           │                                                  │
│           ▼                                                  │
│  3. main 函数 (标记为 #[entry])                              │
│     - 执行用户代码                                           │
│     - 进入无限循环                                           │
│           │                                                  │
│           ▼                                                  │
│  4. 异常处理                                                 │
│     - HardFault (硬件故障)                                   │
│     - SysTick (系统滴答定时器)                               │
│     - 外部中断                                               │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

**自定义异常处理器**:

```rust
use cortex_m_rt::exception;

#[exception]
fn HardFault(ef: &cortex_m_rt::ExceptionFrame) -> ! {
    // 硬件故障处理
    panic!("HardFault: {:?}", ef);
}

#[exception]
fn DefaultHandler(irqn: i16) {
    // 默认中断处理
    panic!("Unhandled IRQ: {}", irqn);
}
```

### 2.3 内存布局

**链接脚本 (memory.x)**:

```ld
MEMORY
{
  /* STM32F401 内存布局 */
  FLASH : ORIGIN = 0x08000000, LENGTH = 512K
  RAM   : ORIGIN = 0x20000000, LENGTH = 96K
}

_stack_start = ORIGIN(RAM) + LENGTH(RAM);

SECTIONS
{
  .vector_table ORIGIN(FLASH) :
  {
    LONG(_stack_start);
    KEEP(*(.vector_table.reset_vector));
  } > FLASH

  .text :
  {
    *(.text .text.*);
  } > FLASH

  .rodata :
  {
    *(.rodata .rodata.*);
  } > FLASH

  .data : AT(ADDR(.rodata) + SIZEOF(.rodata))
  {
    _sdata = .;
    *(.data .data.*);
    _edata = .;
  } > RAM

  .bss :
  {
    _sbss = .;
    *(.bss .bss.*);
    _ebss = .;
  } > RAM
}
```

---

## 3. HAL 抽象层

### 3.1 embedded-hal

**通用 Trait 定义**:

```rust
// embedded-hal 核心 Trait
pub trait OutputPin {
    type Error;
    
    fn set_high(&mut self) -> Result<(), Self::Error>;
    fn set_low(&mut self) -> Result<(), Self::Error>;
}

pub trait InputPin {
    type Error;
    
    fn is_high(&self) -> Result<bool, Self::Error>;
    fn is_low(&self) -> Result<bool, Self::Error>;
}

pub trait DelayMs<U> {
    fn delay_ms(&mut self, ms: U);
}

pub trait DelayUs<U> {
    fn delay_us(&mut self, us: U);
}
```

### 3.2 GPIO 操作

**GPIO 基本用法**:

```rust
use stm32f4xx_hal::{pac, prelude::*};

#[entry]
fn main() -> ! {
    // 1. 获取外设句柄
    let dp = pac::Peripherals::take().unwrap();
    
    // 2. 配置时钟
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    // 3. 获取 GPIO 端口
    let gpioa = dp.GPIOA.split();
    
    // 4. 配置 GPIO 引脚
    let mut led = gpioa.pa5.into_push_pull_output();  // 输出模式
    let button = gpioa.pa0.into_pull_up_input();      // 输入模式
    
    // 5. GPIO 操作
    loop {
        if button.is_high() {
            led.set_high();
        } else {
            led.set_low();
        }
    }
}
```

**PWM 控制 (呼吸灯)**:

```rust
use stm32f4xx_hal::{pac, prelude::*, timer};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpioa = dp.GPIOA.split();
    let led_pin = gpioa.pa5.into_alternate();
    
    // 配置 PWM
    let mut pwm = dp.TIM2.pwm_hz(led_pin, 1.kHz(), &clocks);
    pwm.enable();
    
    let max_duty = pwm.get_max_duty();
    let mut duty = 0u16;
    let mut direction = true;
    
    loop {
        pwm.set_duty(duty);
        
        if direction {
            duty += max_duty / 100;
            if duty >= max_duty {
                direction = false;
            }
        } else {
            duty -= max_duty / 100;
            if duty == 0 {
                direction = true;
            }
        }
        
        cortex_m::asm::delay(100_000);
    }
}
```

### 3.3 外设驱动

**ADC 读取 (模拟传感器)**:

```rust
use stm32f4xx_hal::{adc::Adc, pac, prelude::*};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpioa = dp.GPIOA.split();
    let analog_pin = gpioa.pa0.into_analog();
    
    // 配置 ADC
    let mut adc = Adc::adc1(dp.ADC1, true, Default::default());
    
    loop {
        // 读取 ADC 值 (0-4095)
        let sample: u16 = adc.read(&mut analog_pin).unwrap();
        
        // 转换为电压 (假设参考电压 3.3V)
        let voltage = (sample as f32 / 4095.0) * 3.3;
        
        // 这里可以通过 UART 输出或 LCD 显示
        
        cortex_m::asm::delay(1_000_000);
    }
}
```

---

## 4. RTOS 集成

### 4.1 RTIC 实时框架

**RTIC 架构**:

```text
┌──────────────────────────────────────────────────────────────┐
│                  RTIC 架构原理                               │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  中断优先级驱动:                                             │
│                                                              │
│  ┌────────────────┐                                         │
│  │ 硬件中断       │  Priority 15 (最高)                      │
│  │ (Critical)     │                                         │
│  └────────────────┘                                         │
│         │                                                    │
│         ▼                                                    │
│  ┌────────────────┐                                         │
│  │ 任务 Task1     │  Priority 10                            │
│  └────────────────┘                                         │
│         │                                                    │
│         ▼                                                    │
│  ┌────────────────┐                                         │
│  │ 任务 Task2     │  Priority 5                             │
│  └────────────────┘                                         │
│         │                                                    │
│         ▼                                                    │
│  ┌────────────────┐                                         │
│  │ 空闲任务 Idle  │  Priority 0 (最低)                      │
│  └────────────────┘                                         │
│                                                              │
│  ✅ 优势:                                                    │
│     - 零成本抽象 (编译时调度)                                │
│     - 无竞态条件 (基于优先级的互斥)                          │
│     - 低延迟 (直接中断响应)                                  │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

**RTIC 示例**:

```rust
#![no_std]
#![no_main]

use panic_halt as _;
use rtic::app;
use stm32f4xx_hal::{pac, prelude::*};

#[app(device = stm32f4xx_hal::pac, peripherals = true)]
mod app {
    use super::*;

    #[shared]
    struct Shared {
        // 共享资源
        counter: u32,
    }

    #[local]
    struct Local {
        // 局部资源
        led: stm32f4xx_hal::gpio::PA5<stm32f4xx_hal::gpio::Output>,
    }

    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        // 初始化硬件
        let dp = cx.device;
        let rcc = dp.RCC.constrain();
        let _clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
        
        let gpioa = dp.GPIOA.split();
        let led = gpioa.pa5.into_push_pull_output();
        
        // 配置定时器中断
        let mut timer = dp.TIM2.counter_hz(&clocks);
        timer.start(1.Hz()).unwrap();
        timer.listen(timer::Event::Update);
        
        (
            Shared { counter: 0 },
            Local { led },
        )
    }

    #[task(binds = TIM2, shared = [counter], local = [led])]
    fn timer_task(mut cx: timer_task::Context) {
        // 每秒触发一次
        
        cx.shared.counter.lock(|counter| {
            *counter += 1;
        });
        
        // 切换 LED 状态
        cx.local.led.toggle();
    }

    #[idle]
    fn idle(_: idle::Context) -> ! {
        // 空闲任务
        loop {
            cortex_m::asm::wfi();  // 等待中断
        }
    }
}
```

### 4.2 Embassy 异步框架

**Embassy 架构**:

```rust
#![no_std]
#![no_main]

use defmt::*;
use embassy_executor::Spawner;
use embassy_stm32::gpio::{Level, Output, Speed};
use embassy_time::Timer;
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    let mut led = Output::new(p.PA5, Level::High, Speed::Low);

    loop {
        info!("LED ON");
        led.set_high();
        Timer::after_secs(1).await;
        
        info!("LED OFF");
        led.set_low();
        Timer::after_secs(1).await;
    }
}
```

**多任务并发**:

```rust
use embassy_executor::Spawner;
use embassy_time::Timer;

#[embassy_executor::task]
async fn blink_task() {
    loop {
        // 闪烁 LED
        Timer::after_millis(500).await;
    }
}

#[embassy_executor::task]
async fn sensor_task() {
    loop {
        // 读取传感器
        Timer::after_secs(1).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    spawner.spawn(blink_task()).unwrap();
    spawner.spawn(sensor_task()).unwrap();
    
    loop {
        Timer::after_secs(60).await;
    }
}
```

### 4.3 任务调度

**优先级配置**:

```rust
// RTIC 优先级
#[task(binds = TIM2, priority = 3)]
fn high_priority_task(cx: high_priority_task::Context) {
    // 高优先级任务
}

#[task(binds = TIM3, priority = 1)]
fn low_priority_task(cx: low_priority_task::Context) {
    // 低优先级任务
}

// Embassy 优先级 (通过执行器配置)
use embassy_executor::Executor;

static EXECUTOR_HIGH: StaticCell<Executor> = StaticCell::new();
static EXECUTOR_LOW: StaticCell<Executor> = StaticCell::new();

#[entry]
fn main() -> ! {
    let executor_high = EXECUTOR_HIGH.init(Executor::new());
    let executor_low = EXECUTOR_LOW.init(Executor::new());
    
    executor_high.run(|spawner| {
        spawner.spawn(critical_task()).unwrap();
    });
}
```

---

## 5. 通信协议

### 5.1 UART 串口通信

**UART 发送**:

```rust
use stm32f4xx_hal::{pac, prelude::*, serial};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpioa = dp.GPIOA.split();
    let tx_pin = gpioa.pa2.into_alternate();
    let rx_pin = gpioa.pa3.into_alternate();
    
    // 配置 UART (115200 baud)
    let mut serial = serial::Serial::new(
        dp.USART2,
        (tx_pin, rx_pin),
        serial::Config::default()
            .baudrate(115200.bps())
            .wordlength_8()
            .parity_none(),
        &clocks,
    ).unwrap();
    
    loop {
        // 发送字符串
        for byte in b"Hello, Embedded Rust!\r\n" {
            nb::block!(serial.write(*byte)).unwrap();
        }
        
        cortex_m::asm::delay(10_000_000);
    }
}
```

**UART 接收 (中断)**:

```rust
use rtic::app;

#[app(device = stm32f4xx_hal::pac)]
mod app {
    use super::*;
    
    #[shared]
    struct Shared {
        buffer: heapless::Vec<u8, 64>,
    }
    
    #[local]
    struct Local {
        serial: Serial<USART2>,
    }
    
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        let mut serial = /* 初始化 UART */;
        serial.listen(serial::Event::Rxne);  // 启用接收中断
        
        (
            Shared { buffer: heapless::Vec::new() },
            Local { serial },
        )
    }
    
    #[task(binds = USART2, shared = [buffer], local = [serial])]
    fn uart_rx(mut cx: uart_rx::Context) {
        if let Ok(byte) = cx.local.serial.read() {
            cx.shared.buffer.lock(|buffer| {
                buffer.push(byte).ok();
            });
        }
    }
}
```

### 5.2 I2C 总线

**I2C 读取传感器**:

```rust
use stm32f4xx_hal::{i2c::I2c, pac, prelude::*};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpiob = dp.GPIOB.split();
    let scl = gpiob.pb8.into_alternate_open_drain();
    let sda = gpiob.pb9.into_alternate_open_drain();
    
    // 配置 I2C (100 kHz)
    let mut i2c = I2c::new(
        dp.I2C1,
        (scl, sda),
        100.kHz(),
        &clocks,
    );
    
    let sensor_addr = 0x76;  // 传感器地址
    let reg_temp = 0xFA;     // 温度寄存器
    
    loop {
        let mut buffer = [0u8; 2];
        
        // 读取温度 (2 字节)
        i2c.write_read(sensor_addr, &[reg_temp], &mut buffer).unwrap();
        
        let temp_raw = u16::from_be_bytes(buffer);
        let temperature = (temp_raw as f32) / 100.0;
        
        // 这里可以通过 UART 输出或显示
        
        cortex_m::asm::delay(10_000_000);
    }
}
```

### 5.3 SPI 接口

**SPI 驱动 OLED 显示屏**:

```rust
use stm32f4xx_hal::{pac, prelude::*, spi};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpioa = dp.GPIOA.split();
    let sck = gpioa.pa5.into_alternate();
    let miso = gpioa.pa6.into_alternate();
    let mosi = gpioa.pa7.into_alternate();
    let mut cs = gpioa.pa4.into_push_pull_output();
    
    // 配置 SPI (1 MHz)
    let mut spi = spi::Spi::new(
        dp.SPI1,
        (sck, miso, mosi),
        spi::Mode {
            polarity: spi::Polarity::IdleLow,
            phase: spi::Phase::CaptureOnFirstTransition,
        },
        1.MHz(),
        &clocks,
    );
    
    loop {
        // 选中从设备
        cs.set_low();
        
        // 发送数据
        let data = [0x01, 0x02, 0x03];
        spi.write(&data).unwrap();
        
        // 取消选中
        cs.set_high();
        
        cortex_m::asm::delay(10_000_000);
    }
}
```

---

## 6. 电源管理

### 6.1 低功耗模式

**STM32 低功耗模式**:

```rust
use stm32f4xx_hal::{pac, prelude::*};
use cortex_m::peripheral::SCB;

#[entry]
fn main() -> ! {
    let mut dp = pac::Peripherals::take().unwrap();
    let cp = cortex_m::Peripherals::take().unwrap();
    
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let mut scb = cp.SCB;
    let mut pwr = dp.PWR;
    
    loop {
        // 执行任务
        do_work();
        
        // 进入睡眠模式
        pwr.cr.modify(|_, w| w.lpds().set_bit());  // 低功耗深度睡眠
        scb.set_sleepdeep();
        cortex_m::asm::wfi();  // 等待中断唤醒
    }
}

fn do_work() {
    // 工作逻辑
}
```

### 6.2 睡眠唤醒

**定时器唤醒**:

```rust
use stm32f4xx_hal::{pac, prelude::*, rtc};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    // 配置 RTC (实时时钟)
    let mut rtc = rtc::Rtc::new(dp.RTC, &mut dp.PWR);
    rtc.set_wakeup_interrupt(rtc::WakeupDuration::Seconds(10));
    
    loop {
        // 工作
        work();
        
        // 睡眠 10 秒 (由 RTC 唤醒)
        sleep();
    }
}
```

### 6.3 电池优化

**电池寿命计算**:

```text
┌────────────────────────────────────────────────────────────┐
│                电池寿命估算                                │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  假设:                                                     │
│    - 电池容量: 2000 mAh                                    │
│    - 工作电流: 50 mA (10% 时间)                            │
│    - 睡眠电流: 10 µA (90% 时间)                            │
│                                                            │
│  计算平均电流:                                             │
│    Iavg = 50mA * 0.1 + 0.01mA * 0.9                        │
│         = 5mA + 0.009mA                                    │
│         = 5.009mA                                          │
│                                                            │
│  电池寿命:                                                 │
│    T = 2000mAh / 5.009mA                                   │
│      = 399.3 小时                                          │
│      ≈ 16.6 天                                             │
│                                                            │
│  优化后 (睡眠电流降至 1 µA):                               │
│    Iavg = 50mA * 0.1 + 0.001mA * 0.9                       │
│         = 5.0009mA                                         │
│    T ≈ 400 小时 ≈ 16.7 天 (提升微小)                       │
│                                                            │
│  ✅ 关键: 降低工作时间比例或工作电流                       │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

---

## 7. 调试与测试

### 7.1 probe-rs 调试

**配置 Embed.toml**:

```toml
[default.general]
chip = "STM32F401RETx"

[default.reset]
enabled = true
halt_afterwards = false

[default.rtt]
enabled = true

[default.gdb]
enabled = true
```

**RTT 日志输出**:

```rust
use rtt_target::{rprintln, rtt_init_print};

#[entry]
fn main() -> ! {
    rtt_init_print!();
    
    rprintln!("系统启动");
    
    loop {
        rprintln!("计数: {}", counter);
        counter += 1;
        
        cortex_m::asm::delay(10_000_000);
    }
}
```

**运行和调试**:

```bash
# 烧录并运行
cargo embed --release

# GDB 调试
cargo embed --release --gdb
```

### 7.2 单元测试

**测试工具: defmt-test**:

```rust
#[defmt_test::tests]
mod tests {
    use super::*;
    
    #[test]
    fn test_gpio() {
        let led = /* 初始化 GPIO */;
        led.set_high();
        assert!(led.is_set_high());
    }
    
    #[test]
    fn test_adc() {
        let adc = /* 初始化 ADC */;
        let value = adc.read();
        assert!(value < 4096);
    }
}
```

### 7.3 硬件在环测试

**HIL 测试架构**:

```text
┌──────────────────────────────────────────────────────────────┐
│              硬件在环 (HIL) 测试架构                          │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────┐                                           │
│  │   PC (Host)  │                                           │
│  │              │                                           │
│  │ - 测试脚本   │                                           │
│  │ - pytest     │                                           │
│  └──────┬───────┘                                           │
│         │ USB                                               │
│         ▼                                                    │
│  ┌──────────────┐                                           │
│  │ 调试器 (J-Link) │                                        │
│  └──────┬───────┘                                           │
│         │ SWD                                               │
│         ▼                                                    │
│  ┌──────────────┐     GPIO     ┌──────────────┐            │
│  │   MCU        │ ◄────────────► 测试外设     │            │
│  │  (DUT)       │     I2C      │ (传感器, LED)│            │
│  └──────────────┘              └──────────────┘            │
│                                                              │
│  测试流程:                                                   │
│    1. PC 烧录固件到 MCU                                      │
│    2. MCU 执行测试代码                                       │
│    3. PC 读取测试结果 (通过 RTT/UART)                        │
│    4. PC 验证外设状态 (通过逻辑分析仪)                       │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

---

## 8. 实战案例

### 8.1 案例1: LED 闪烁 (Hello World)

```rust
#![no_std]
#![no_main]

use panic_halt as _;
use cortex_m_rt::entry;
use stm32f4xx_hal::{pac, prelude::*};

#[entry]
fn main() -> ! {
    let dp = pac::Peripherals::take().unwrap();
    
    let rcc = dp.RCC.constrain();
    let _clocks = rcc.cfgr.sysclk(84.MHz()).freeze();
    
    let gpioa = dp.GPIOA.split();
    let mut led = gpioa.pa5.into_push_pull_output();
    
    loop {
        led.set_high();
        cortex_m::asm::delay(10_000_000);
        
        led.set_low();
        cortex_m::asm::delay(10_000_000);
    }
}
```

### 8.2 案例2: 温湿度传感器

**DHT22 驱动 (单总线协议)**:

```rust
use stm32f4xx_hal::{pac, prelude::*, gpio};

struct Dht22<PIN> {
    pin: PIN,
}

impl<PIN> Dht22<PIN>
where
    PIN: gpio::PinExt,
{
    fn new(pin: PIN) -> Self {
        Self { pin }
    }
    
    fn read(&mut self) -> Result<(f32, f32), ()> {
        // 1. 发送起始信号 (拉低 18ms)
        let mut output = self.pin.into_push_pull_output();
        output.set_low();
        delay_ms(18);
        
        // 2. 释放总线 (拉高 40us)
        output.set_high();
        delay_us(40);
        
        // 3. 切换为输入模式
        let input = output.into_floating_input();
        
        // 4. 等待 DHT22 响应 (拉低 80us + 拉高 80us)
        wait_for_low(&input, 100)?;
        wait_for_high(&input, 100)?;
        
        // 5. 读取 40 位数据
        let mut data = [0u8; 5];
        for byte in data.iter_mut() {
            for bit in (0..8).rev() {
                wait_for_low(&input, 100)?;
                wait_for_high(&input, 100)?;
                
                // 高电平持续时间决定 0/1
                delay_us(30);
                if input.is_high() {
                    *byte |= 1 << bit;
                }
            }
        }
        
        // 6. 验证校验和
        let checksum = data[0].wrapping_add(data[1])
            .wrapping_add(data[2])
            .wrapping_add(data[3]);
        if checksum != data[4] {
            return Err(());
        }
        
        // 7. 计算温湿度
        let humidity = ((data[0] as u16) << 8 | data[1] as u16) as f32 / 10.0;
        let temperature = ((data[2] as u16) << 8 | data[3] as u16) as f32 / 10.0;
        
        Ok((temperature, humidity))
    }
}
```

### 8.3 案例3: 物联网设备

**MQTT + WiFi (ESP32)**:

```rust
use esp_idf_svc::{
    eventloop::EspSystemEventLoop,
    hal::prelude::*,
    mqtt::client::{EspMqttClient, MqttClientConfiguration},
    wifi::{BlockingWifi, ClientConfiguration, Configuration, EspWifi},
};

fn main() -> anyhow::Result<()> {
    esp_idf_svc::sys::link_patches();
    
    let peripherals = Peripherals::take().unwrap();
    let sys_loop = EspSystemEventLoop::take()?;
    
    // 1. 连接 WiFi
    let mut wifi = BlockingWifi::wrap(
        EspWifi::new(peripherals.modem, sys_loop.clone(), None)?,
        sys_loop,
    )?;
    
    wifi.set_configuration(&Configuration::Client(ClientConfiguration {
        ssid: "YourSSID".into(),
        password: "YourPassword".into(),
        ..Default::default()
    }))?;
    
    wifi.start()?;
    wifi.connect()?;
    wifi.wait_netif_up()?;
    
    println!("WiFi 已连接");
    
    // 2. 连接 MQTT Broker
    let mqtt_config = MqttClientConfiguration::default();
    
    let mut client = EspMqttClient::new(
        "mqtt://broker.hivemq.com:1883",
        &mqtt_config,
        move |message| {
            println!("收到消息: {:?}", message);
        },
    )?;
    
    // 3. 订阅主题
    client.subscribe("sensors/temperature", mqtt::QoS::AtMostOnce)?;
    
    // 4. 发布消息
    loop {
        let temperature = read_sensor();
        let payload = format!("{{\"temp\": {}}}", temperature);
        
        client.publish(
            "sensors/temperature",
            mqtt::QoS::AtMostOnce,
            false,
            payload.as_bytes(),
        )?;
        
        std::thread::sleep(std::time::Duration::from_secs(10));
    }
}
```

---

## 9. 最佳实践

**1. 内存管理**:

- ✅ 使用 `heapless` 进行静态分配
- ✅ 避免动态内存分配 (`alloc`)
- ✅ 栈大小合理配置 (`.cargo/config.toml`)

**2. 错误处理**:

- ✅ 使用 `Result` 而非 `panic!`
- ✅ 配置合适的 panic 处理器 (`panic-halt`, `panic-semihosting`)
- ✅ 使用 RTT 或 UART 输出调试信息

**3. 实时性**:

- ✅ 关键任务使用高优先级中断
- ✅ 避免在中断处理中执行长时间操作
- ✅ 使用 RTIC/Embassy 进行任务调度

**4. 功耗优化**:

- ✅ 使用低功耗模式 (睡眠/待机)
- ✅ 降低时钟频率
- ✅ 关闭未使用的外设

**5. 代码优化**:

- ✅ 启用 LTO (Link-Time Optimization)
- ✅ 使用 `#[inline]` 优化关键函数
- ✅ 优化循环和算法

---

## 10. 常见问题

**Q1: 如何选择开发板?**

| 开发板 | MCU | 特点 | 适用场景 |
|--------|-----|------|----------|
| **STM32 Nucleo** | STM32F4 | 丰富的外设, 成熟的生态 | 通用嵌入式开发 |
| **nRF52840 DK** | nRF52840 | 低功耗, 蓝牙 5.0 | 无线传感器, 可穿戴设备 |
| **ESP32-C3** | ESP32-C3 | WiFi + 低成本 | IoT 设备 |
| **Raspberry Pi Pico** | RP2040 | 便宜, 易用 | 学习和原型开发 |

**Q2: 如何处理 `#[no_std]` 环境下的缺失功能?**

- 使用 `heapless::Vec` 代替 `std::vec::Vec`
- 使用 `arrayvec::ArrayVec` 进行固定大小集合
- 使用 `libm` 进行浮点数学运算
- 使用 `embedded-hal` 进行硬件抽象

**Q3: 如何优化二进制大小?**

```toml
[profile.release]
opt-level = "z"        # 优化大小
lto = true             # 链接时优化
codegen-units = 1      # 单编译单元
strip = true           # 移除调试信息
panic = "abort"        # Panic 时直接 abort
```

**Q4: 如何实现跨平台驱动?**

使用 `embedded-hal` Trait:

```rust
use embedded_hal::digital::v2::OutputPin;

struct LedDriver<PIN: OutputPin> {
    pin: PIN,
}

impl<PIN: OutputPin> LedDriver<PIN> {
    pub fn new(pin: PIN) -> Self {
        Self { pin }
    }
    
    pub fn turn_on(&mut self) {
        self.pin.set_high().ok();
    }
}

// 适用于任何实现 OutputPin 的 GPIO
```

**Q5: 如何进行 OTA 固件升级?**

1. **Bootloader**: 实现双区引导
2. **传输**: 通过 UART/WiFi/BLE 下载固件
3. **验证**: 校验固件签名和 CRC
4. **切换**: 更新引导标志并重启

---

## 11. 参考资源

**官方文档**:

- [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [embedded-hal](https://docs.rs/embedded-hal/)
- [RTIC Book](https://rtic.rs/)
- [Embassy](https://embassy.dev/)

**硬件支持**:

- [stm32-rs](https://github.com/stm32-rs) - STM32 HAL
- [nrf-rs](https://github.com/nrf-rs) - nRF HAL
- [esp-rs](https://github.com/esp-rs) - ESP32 HAL
- [rp-rs](https://github.com/rp-rs) - RP2040 HAL

**工具**:

- [probe-rs](https://probe.rs/) - 调试和烧录工具
- [cargo-embed](https://probe.rs/docs/tools/cargo-embed/) - 嵌入式开发工具
- [defmt](https://defmt.ferrous-systems.com/) - 高效日志框架

**社区**:

- [Rust Embedded Community](https://github.com/rust-embedded/wg)
- [Awesome Embedded Rust](https://github.com/rust-embedded/awesome-embedded-rust)

---

**总结**:

Rust 嵌入式开发结合了系统级性能和内存安全保障，是构建可靠嵌入式系统的绝佳选择。
通过本指南，您可以掌握从裸机编程到 RTOS 集成的完整技术栈，开发出高质量的嵌入式应用! 🦀
