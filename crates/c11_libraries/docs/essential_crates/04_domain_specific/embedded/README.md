# 嵌入式系统 (Embedded Systems)

**类别**: 领域特定 - 嵌入式  
**重要程度**: ⭐⭐⭐⭐⭐ (嵌入式开发必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [嵌入式系统 (Embedded Systems)](#嵌入式系统-embedded-systems)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. embedded-hal (硬件抽象层 ⭐⭐⭐⭐⭐)](#1-embedded-hal-硬件抽象层-)
      - [核心特性](#核心特性)
      - [基础 trait](#基础-trait)
      - [I2C 通信](#i2c-通信)
    - [2. rtic (实时并发框架 ⭐⭐⭐⭐⭐)](#2-rtic-实时并发框架-)
      - [核心特性2](#核心特性2)
      - [基础示例](#基础示例)
    - [3. embassy (异步嵌入式 ⭐⭐⭐⭐⭐)](#3-embassy-异步嵌入式-)
      - [核心特性3](#核心特性3)
      - [基础示例3](#基础示例3)
      - [多任务示例](#多任务示例)
    - [4. probe-rs (调试工具 ⭐⭐⭐⭐⭐)](#4-probe-rs-调试工具-)
      - [核心特性4](#核心特性4)
      - [使用命令](#使用命令)
      - [RTT 日志](#rtt-日志)
  - [💡 最佳实践](#-最佳实践)
    - [1. 内存管理](#1-内存管理)
    - [2. 中断安全](#2-中断安全)
    - [3. 低功耗模式](#3-低功耗模式)
  - [📊 工具对比](#-工具对比)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 温度传感器读取](#场景1-温度传感器读取)
    - [场景2: PWM 控制](#场景2-pwm-控制)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

Rust 在嵌入式领域表现出色，提供内存安全、零成本抽象和优秀的性能。
Rust 嵌入式生态已经非常成熟，广泛应用于 IoT、机器人、航空航天等领域。

---

## 🔧 核心工具

### 1. embedded-hal (硬件抽象层 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add embedded-hal`  
**用途**: 嵌入式硬件抽象层标准

#### 核心特性

- ✅ 硬件无关API
- ✅ 跨平台支持
- ✅ 无运行时开销
- ✅ trait 驱动设计

#### 基础 trait

```rust
use embedded_hal::digital::v2::{InputPin, OutputPin};
use embedded_hal::blocking::delay::DelayMs;

// LED 闪烁示例
pub fn blink_led<P, D>(pin: &mut P, delay: &mut D, duration_ms: u32) 
where
    P: OutputPin,
    D: DelayMs<u32>,
{
    loop {
        pin.set_high().ok();
        delay.delay_ms(duration_ms);
        
        pin.set_low().ok();
        delay.delay_ms(duration_ms);
    }
}

// 按钮读取示例
pub fn read_button<P>(button: &P) -> bool 
where
    P: InputPin,
{
    button.is_high().unwrap_or(false)
}
```

#### I2C 通信

```rust
use embedded_hal::blocking::i2c::{Write, WriteRead};

pub struct Sensor<I2C> {
    i2c: I2C,
    address: u8,
}

impl<I2C, E> Sensor<I2C>
where
    I2C: Write<Error = E> + WriteRead<Error = E>,
{
    pub fn new(i2c: I2C, address: u8) -> Self {
        Self { i2c, address }
    }
    
    pub fn read_register(&mut self, register: u8) -> Result<u8, E> {
        let mut buffer = [0u8; 1];
        self.i2c.write_read(self.address, &[register], &mut buffer)?;
        Ok(buffer[0])
    }
    
    pub fn write_register(&mut self, register: u8, value: u8) -> Result<(), E> {
        self.i2c.write(self.address, &[register, value])
    }
}
```

---

### 2. rtic (实时并发框架 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add rtic`  
**用途**: 实时中断驱动并发框架

#### 核心特性2

- ✅ 零开销并发
- ✅ 硬件任务调度
- ✅ 消息传递
- ✅ 资源共享

#### 基础示例

```rust
#![no_std]
#![no_main]

use rtic::app;

#[app(device = stm32f4::stm32f401, peripherals = true)]
mod app {
    use systick_monotonic::{Systick, fugit::ExtU32};
    
    #[shared]
    struct Shared {
        counter: u32,
    }
    
    #[local]
    struct Local {
        led: LED,
    }
    
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        let led = LED::new(cx.device.GPIOC);
        
        (
            Shared { counter: 0 },
            Local { led },
        )
    }
    
    #[task(shared = [counter], local = [led])]
    fn blink(mut cx: blink::Context) {
        cx.shared.counter.lock(|counter| {
            *counter += 1;
        });
        
        cx.local.led.toggle();
    }
    
    #[task(binds = EXTI0, shared = [counter])]
    fn button_press(mut cx: button_press::Context) {
        cx.shared.counter.lock(|counter| {
            *counter = 0;
        });
    }
}
```

---

### 3. embassy (异步嵌入式 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add embassy-executor embassy-time`  
**用途**: 现代化异步嵌入式框架

#### 核心特性3

- ✅ async/await 支持
- ✅ 时间驱动
- ✅ 低功耗
- ✅ HAL 集成

#### 基础示例3

```rust
#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]

use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};
use embassy_stm32::gpio::{Level, Output, Speed};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    
    let mut led = Output::new(p.PA5, Level::High, Speed::Low);
    
    loop {
        led.set_high();
        Timer::after(Duration::from_millis(500)).await;
        
        led.set_low();
        Timer::after(Duration::from_millis(500)).await;
    }
}
```

#### 多任务示例

```rust
use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};

#[embassy_executor::task]
async fn blink_task(led: Pin) {
    loop {
        led.toggle();
        Timer::after(Duration::from_millis(500)).await;
    }
}

#[embassy_executor::task]
async fn uart_task(uart: Uart) {
    loop {
        let data = uart.read().await;
        uart.write(b"Received: ").await;
        uart.write(&data).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    
    spawner.spawn(blink_task(p.PA5)).unwrap();
    spawner.spawn(uart_task(p.USART1)).unwrap();
}
```

---

### 4. probe-rs (调试工具 ⭐⭐⭐⭐⭐)

**安装**: `cargo install probe-rs`  
**用途**: 嵌入式调试和烧录工具

#### 核心特性4

- ✅ 多种探针支持 (ST-Link, J-Link, CMSIS-DAP)
- ✅ GDB 服务器
- ✅ RTT 日志
- ✅ 烧录和调试

#### 使用命令

```bash
# 列出连接的探针
probe-rs list

# 烧录程序
probe-rs run --chip STM32F401 target/thumbv7em-none-eabihf/release/app

# 启动 GDB 服务器
probe-rs gdb --chip STM32F401

# RTT 日志输出
probe-rs attach --chip STM32F401
```

#### RTT 日志

```rust
use rtt_target::{rtt_init_print, rprintln};

#[entry]
fn main() -> ! {
    rtt_init_print!();
    
    rprintln!("Hello from embedded Rust!");
    
    loop {
        rprintln!("Counter: {}", counter);
        delay.delay_ms(1000);
    }
}
```

---

## 💡 最佳实践

### 1. 内存管理

```rust
// 使用静态分配避免堆
static mut BUFFER: [u8; 1024] = [0; 1024];

// 使用 heapless 集合
use heapless::Vec;

let mut vec: Vec<u8, 32> = Vec::new();
vec.push(42).unwrap();
```

### 2. 中断安全

```rust
use core::sync::atomic::{AtomicBool, Ordering};
use cortex_m::interrupt;

static FLAG: AtomicBool = AtomicBool::new(false);

// 在中断中设置标志
#[interrupt]
fn EXTI0() {
    FLAG.store(true, Ordering::Relaxed);
}

// 在主循环中检查
fn main() -> ! {
    loop {
        if FLAG.load(Ordering::Relaxed) {
            FLAG.store(false, Ordering::Relaxed);
            // 处理事件
        }
    }
}
```

### 3. 低功耗模式

```rust
use cortex_m::asm;

fn enter_sleep_mode() {
    // 进入 WFI (Wait For Interrupt)
    asm::wfi();
}

fn main() -> ! {
    loop {
        if !has_work_to_do() {
            enter_sleep_mode();
        }
    }
}
```

---

## 📊 工具对比

| 工具 | 用途 | 学习曲线 | 性能 | 推荐度 |
|------|------|---------|------|--------|
| **embedded-hal** | HAL 标准 | 中等 | ⭐⭐⭐⭐⭐ | 🌟 必备 |
| **rtic** | 实时框架 | 中等 | ⭐⭐⭐⭐⭐ | 🌟 强推 |
| **embassy** | 异步框架 | 中等 | ⭐⭐⭐⭐⭐ | 🌟 强推 |
| **probe-rs** | 调试工具 | 低 | ⭐⭐⭐⭐⭐ | 🌟 必备 |

---

## 🎯 实战场景

### 场景1: 温度传感器读取

```rust
use embedded_hal::blocking::i2c::WriteRead;

struct TemperatureSensor<I2C> {
    i2c: I2C,
    address: u8,
}

impl<I2C, E> TemperatureSensor<I2C>
where
    I2C: WriteRead<Error = E>,
{
    pub fn read_temperature(&mut self) -> Result<f32, E> {
        let mut buffer = [0u8; 2];
        self.i2c.write_read(self.address, &[0x00], &mut buffer)?;
        
        let raw = u16::from_be_bytes(buffer);
        let temp = (raw as f32) * 0.0625;  // 根据传感器规格转换
        
        Ok(temp)
    }
}
```

### 场景2: PWM 控制

```rust
use embedded_hal::PwmPin;

pub struct ServoControl<PWM> {
    pwm: PWM,
}

impl<PWM> ServoControl<PWM>
where
    PWM: PwmPin<Duty = u16>,
{
    pub fn set_angle(&mut self, angle: u8) {
        // 0-180度映射到PWM占空比
        let duty = (angle as u16 * 1000 / 180) + 1000;
        self.pwm.set_duty(duty);
    }
}
```

---

## 🔗 相关资源

- [Embedded Rust Book](https://rust-embedded.github.io/book/)
- [Discovery Book](https://docs.rust-embedded.org/discovery/)
- [Awesome Embedded Rust](https://github.com/rust-embedded/awesome-embedded-rust)
- [embedded-hal Documentation](https://docs.rs/embedded-hal/)

---

**导航**: [返回领域特定](../README.md) | [下一领域：科学计算](../science/README.md)
