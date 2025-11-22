# 嵌入式编程基础（Embedded Programming Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [嵌入式编程基础](#嵌入式编程基础embedded-programming-basics)
  - [概述](#概述)
  - [嵌入式 Rust 基础](#嵌入式-rust-基础)
  - [硬件抽象层](#硬件抽象层)
  - [中断处理](#中断处理)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Rust 在嵌入式系统开发中具有显著优势，包括内存安全、零成本抽象和强大的类型系统。本示例展示 Rust 嵌入式编程的基础知识。

## 嵌入式 Rust 基础

### no_std 环境

```rust
#![no_std]
#![no_main]

use panic_halt as _;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 嵌入式程序入口
    loop {
        // 主循环
    }
}
```

### 内存管理

```rust
#![no_std]

use core::alloc::{GlobalAlloc, Layout};

// 简单的堆分配器
pub struct BumpAllocator {
    heap_start: usize,
    heap_end: usize,
    next: usize,
}

unsafe impl GlobalAlloc for BumpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // 简单的 bump 分配器实现
        let ptr = self.next;
        self.next = (self.next + layout.size()).max(self.next);
        ptr as *mut u8
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // Bump 分配器不需要释放
    }
}
```

## 硬件抽象层

### GPIO 控制

```rust
// 简化的 GPIO 抽象
pub struct GpioPin {
    port: u8,
    pin: u8,
}

impl GpioPin {
    pub fn new(port: u8, pin: u8) -> Self {
        GpioPin { port, pin }
    }

    pub fn set_high(&self) {
        // 设置引脚为高电平
        unsafe {
            // 硬件寄存器操作
        }
    }

    pub fn set_low(&self) {
        // 设置引脚为低电平
        unsafe {
            // 硬件寄存器操作
        }
    }

    pub fn read(&self) -> bool {
        // 读取引脚状态
        unsafe {
            // 硬件寄存器操作
            false
        }
    }
}
```

### UART 通信

```rust
pub struct Uart {
    base_address: usize,
}

impl Uart {
    pub fn new(base_address: usize) -> Self {
        Uart { base_address }
    }

    pub fn write_byte(&self, byte: u8) {
        unsafe {
            // 写入 UART 数据寄存器
            let ptr = self.base_address as *mut u8;
            ptr.write_volatile(byte);
        }
    }

    pub fn read_byte(&self) -> Option<u8> {
        unsafe {
            // 读取 UART 数据寄存器
            let ptr = self.base_address as *mut u8;
            Some(ptr.read_volatile())
        }
    }

    pub fn write_str(&self, s: &str) {
        for byte in s.bytes() {
            self.write_byte(byte);
        }
    }
}
```

## 中断处理

### 中断服务例程

```rust
use cortex_m::interrupt;

// 全局中断处理
#[interrupt]
fn TIM2() {
    // 定时器中断处理
    static mut COUNTER: u32 = 0;
    *COUNTER += 1;
}

// 中断使能/禁用
pub fn enable_interrupts() {
    unsafe {
        cortex_m::interrupt::enable();
    }
}

pub fn disable_interrupts() {
    cortex_m::interrupt::disable();
}
```

### 临界区

```rust
use cortex_m::interrupt;

pub fn critical_section<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    interrupt::free(|_| {
        f()
    })
}
```

## 实践示例

### 示例 1：LED 闪烁

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;
use panic_halt as _;

#[entry]
fn main() -> ! {
    let mut led = GpioPin::new(0, 13);  // 假设 LED 在 PA13

    loop {
        led.set_high();
        delay_ms(500);
        led.set_low();
        delay_ms(500);
    }
}

fn delay_ms(ms: u32) {
    // 简单的延时实现
    for _ in 0..ms * 1000 {
        cortex_m::asm::nop();
    }
}
```

### 示例 2：串口通信

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;

#[entry]
fn main() -> ! {
    let uart = Uart::new(0x4000_3800);  // USART1 基地址

    uart.write_str("Hello from embedded Rust!\r\n");

    loop {
        if let Some(byte) = uart.read_byte() {
            uart.write_byte(byte);  // 回显
        }
    }
}
```

### 示例 3：传感器读取

```rust
pub struct Sensor {
    i2c: I2c,
    address: u8,
}

impl Sensor {
    pub fn new(i2c: I2c, address: u8) -> Self {
        Sensor { i2c, address }
    }

    pub fn read_temperature(&mut self) -> Result<f32, SensorError> {
        // 读取温度传感器数据
        let data = self.i2c.read(self.address, 0x00, 2)?;
        let raw = ((data[0] as u16) << 8) | data[1] as u16;
        Ok(raw as f32 / 256.0)
    }
}

pub struct I2c {
    base_address: usize,
}

impl I2c {
    pub fn read(&self, address: u8, register: u8, len: usize) -> Result<Vec<u8>, SensorError> {
        // I2C 读取实现
        Ok(vec![0; len])
    }
}

#[derive(Debug)]
pub enum SensorError {
    I2cError,
    Timeout,
}
```

## 最佳实践

### 1. 使用 embedded-hal

```rust
use embedded_hal::digital::v2::OutputPin;

pub fn blink_led<P>(mut led: P)
where
    P: OutputPin,
{
    loop {
        led.set_high().unwrap();
        delay_ms(500);
        led.set_low().unwrap();
        delay_ms(500);
    }
}
```

### 2. 错误处理

```rust
use core::fmt;

pub trait EmbeddedError: fmt::Debug {
    fn kind(&self) -> ErrorKind;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    Timeout,
    Busy,
    InvalidParameter,
    HardwareError,
}
```

### 3. 资源管理

```rust
use core::ops::Drop;

pub struct Resource {
    // 资源数据
}

impl Resource {
    pub fn new() -> Self {
        Resource {}
    }
}

impl Drop for Resource {
    fn drop(&mut self) {
        // 清理资源
    }
}
```

## 参考资料

- [嵌入式示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [embedded-hal 文档](https://docs.rs/embedded-hal/)
- [cortex-m 文档](https://docs.rs/cortex-m/)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
