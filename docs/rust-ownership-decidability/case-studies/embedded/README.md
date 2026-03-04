# Rust 嵌入式/物联网开发完全指南

> 本指南深入探讨如何在资源受限的嵌入式环境中利用Rust的所有权系统和零成本抽象构建安全、高效的物联网应用。

---

## 目录

- [Rust 嵌入式/物联网开发完全指南](#rust-嵌入式物联网开发完全指南)
  - [目录](#目录)
  - [一、嵌入式Rust概述](#一嵌入式rust概述)
    - [1.1 no\_std环境](#11-no_std环境)
      - [no\_std的限制与替代方案](#no_std的限制与替代方案)
    - [1.2 内存约束下的所有权管理](#12-内存约束下的所有权管理)
      - [编译期内存布局验证](#编译期内存布局验证)
    - [1.3 零成本抽象的重要性](#13-零成本抽象的重要性)
  - [二、嵌入式开发环境](#二嵌入式开发环境)
    - [2.1 工具链安装](#21-工具链安装)
    - [2.2 cargo-embed配置](#22-cargo-embed配置)
    - [2.3 probe-rs使用](#23-probe-rs使用)
    - [2.4 交叉编译设置](#24-交叉编译设置)
      - [内存布局链接脚本 (`memory.x`)](#内存布局链接脚本-memoryx)
  - [三、硬件抽象层(HAL)](#三硬件抽象层hal)
    - [3.1 embedded-hal Trait系统](#31-embedded-hal-trait系统)
    - [3.2 GPIO示例](#32-gpio示例)
    - [3.3 UART串口通信](#33-uart串口通信)
    - [3.4 SPI总线通信](#34-spi总线通信)
    - [3.5 I2C总线通信](#35-i2c总线通信)
  - [四、实时操作系统(RTOS)](#四实时操作系统rtos)
    - [4.1 RTIC框架](#41-rtic框架)
    - [4.2 Embassy异步运行时](#42-embassy异步运行时)
    - [4.3 任务调度与优先级](#43-任务调度与优先级)
  - [五、内存管理](#五内存管理)
    - [5.1 静态分配策略](#51-静态分配策略)
    - [5.2 内存池](#52-内存池)
    - [5.3 栈溢出保护](#53-栈溢出保护)
  - [六、中断处理](#六中断处理)
    - [6.1 安全的中断处理](#61-安全的中断处理)
    - [6.2 临界区管理](#62-临界区管理)
    - [6.3 无锁数据结构](#63-无锁数据结构)
  - [七、物联网协议](#七物联网协议)
    - [7.1 MQTT客户端](#71-mqtt客户端)
    - [7.2 CoAP协议](#72-coap协议)
    - [7.3 LoRaWAN协议](#73-lorawan协议)
  - [八、电源管理](#八电源管理)
    - [8.1 低功耗模式](#81-低功耗模式)
    - [8.2 睡眠状态管理](#82-睡眠状态管理)
  - [九、完整示例：温度传感器数据采集系统](#九完整示例温度传感器数据采集系统)
    - [9.1 系统架构](#91-系统架构)
    - [9.2 完整代码实现](#92-完整代码实现)
  - [十、调试技术](#十调试技术)
    - [10.1 RTT (Real-Time Transfer)](#101-rtt-real-time-transfer)
    - [10.2 ITM (Instrumentation Trace Macrocell)](#102-itm-instrumentation-trace-macrocell)
    - [10.3 日志系统](#103-日志系统)
    - [10.4 调试配置总结](#104-调试配置总结)
  - [附录](#附录)
    - [常用嵌入式Rust Crate](#常用嵌入式rust-crate)
    - [资源链接](#资源链接)

---

## 一、嵌入式Rust概述

### 1.1 no_std环境

嵌入式系统通常没有完整的操作系统支持，因此Rust程序需要在 `no_std` 环境下运行。
这意味着无法使用标准库(std)，只能使用核心库(core)。

```rust
#![no_std]
#![no_main]

use core::panic::PanicInfo;

///  panic处理函数 - no_std环境下必需
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {
        // 发生panic时进入无限循环
        // 实际应用中可添加LED闪烁或复位逻辑
    }
}

/// 程序入口点
#[cortex_m_rt::entry]
fn main() -> ! {
    // 初始化代码...

    loop {
        // 主循环
    }
}
```

#### no_std的限制与替代方案

| 标准库功能 | no_std替代方案 | 说明 |
|-----------|---------------|------|
| `Vec<T>` | `heapless::Vec<T, N>` | 固定容量，无堆分配 |
| `String` | `heapless::String<N>` | 固定容量字符串 |
| `HashMap` | `heapless::FnvIndexMap<K, V, N>` | FNV哈希算法 |
| `Box<T>` | 静态分配或内存池 | 避免动态堆分配 |
| `println!` | `rtt_target::rprintln!` | 通过RTT输出 |
| 动态内存 | `embedded_alloc` | 可选的嵌入式分配器 |

### 1.2 内存约束下的所有权管理

嵌入式系统的内存极其有限（通常只有几KB到几百KB），Rust的所有权系统在这种情况下特别有价值：

```rust
use heapless::Vec;

/// 传感器数据缓冲区 - 编译期确定大小，无运行时分配
struct SensorBuffer<const N: usize> {
    data: Vec<u16, N>,  // 固定容量为N的向量
}

impl<const N: usize> SensorBuffer<N> {
    const fn new() -> Self {
        Self {
            data: Vec::new(),  // 不需要堆分配
        }
    }

    /// 添加读数，所有权确保数据有效性
    fn push(&mut self, value: u16) -> Result<(), u16> {
        self.data.push(value)
    }

    /// 获取平均值 - 借用而非复制
    fn average(&self) -> Option<u16> {
        if self.data.is_empty() {
            return None;
        }
        let sum: u32 = self.data.iter().map(|&x| x as u32).sum();
        Some((sum / self.data.len() as u32) as u16)
    }
}

// 使用示例
static mut BUFFER: SensorBuffer<100> = SensorBuffer::new();
```

#### 编译期内存布局验证

```rust
/// 设备配置结构 - 使用packed布局优化内存
#[repr(C, packed)]
struct DeviceConfig {
    sensor_id: u16,
    sample_rate: u8,
    flags: u8,
    calibration: [u16; 4],
}

// 编译期验证大小
const _: () = assert!(core::mem::size_of::<DeviceConfig>() == 12);
```

### 1.3 零成本抽象的重要性

Rust的零成本抽象原则在嵌入式领域至关重要：

```rust
/// 类型状态模式 - 在编译期确保GPIO配置正确
mod gpio {
    pub struct Input;
    pub struct Output;

    pub struct Pin<MODE> {
        port: u8,
        pin: u8,
        _mode: core::marker::PhantomData<MODE>,
    }

    impl Pin<Input> {
        pub fn new_input(port: u8, pin: u8) -> Self {
            // 配置为输入模式...
            Self { port, pin, _mode: core::marker::PhantomData }
        }

        pub fn read(&self) -> bool {
            // 读取引脚状态
            true
        }
    }

    impl Pin<Output> {
        pub fn new_output(port: u8, pin: u8) -> Self {
            // 配置为输出模式...
            Self { port, pin, _mode: core::marker::PhantomData }
        }

        pub fn set_high(&mut self) {
            // 设置高电平
        }

        pub fn set_low(&mut self) {
            // 设置低电平
        }
    }
}

// 编译期防止错误操作
let input_pin = gpio::Pin::<gpio::Input>::new_input(0, 1);
let state = input_pin.read();
// input_pin.set_high();  // 编译错误！Input模式的Pin没有set_high方法
```

---

## 二、嵌入式开发环境

### 2.1 工具链安装

```bash
# 安装Rust嵌入式工具链
rustup target add thumbv7m-none-eabi      # Cortex-M3
rustup target add thumbv7em-none-eabihf   # Cortex-M4/M7 (FPU)
rustup target add thumbv6m-none-eabi      # Cortex-M0/M0+

# 安装cargo工具
cargo install cargo-embed
cargo install cargo-flash
cargo install probe-rs-cli

# LLVM工具
rustup component add llvm-tools-preview
```

### 2.2 cargo-embed配置

`Embed.toml` 配置文件：

```toml
[default.general]
chip = "STM32F407VG"
connect_under_reset = true

[default.rtt]
enabled = true
channels = [
    { up = 0, down = 0, name = "Defmt", format = "Defmt" },
    { up = 1, down = 1, name = "Logs", format = "String" },
]

[default.gdb]
enabled = true
port = 1337

[default.reset]
halt_afterwards = false
```

### 2.3 probe-rs使用

```bash
# 列出连接的设备
probe-rs list

# 擦除芯片
probe-rs erase --chip STM32F407VG

# 下载并运行程序
probe-rs run --chip STM32F407VG target/thumbv7em-none-eabihf/release/firmware

# 调试会话
probe-rs gdb --chip STM32F407VG --protocol swd
```

### 2.4 交叉编译设置

`.cargo/config.toml`：

```toml
[build]
target = "thumbv7em-none-eabihf"

[target.thumbv7em-none-eabihf]
runner = "probe-rs run --chip STM32F407VG"
rustflags = [
    "-C", "link-arg=-Tlink.x",
    "-C", "link-arg=-Tdefmt.x",
]

[env]
DEFMT_LOG = "info"
```

#### 内存布局链接脚本 (`memory.x`)

```ld
MEMORY
{
    /* Flash - 程序代码和只读数据 */
    FLASH : ORIGIN = 0x08000000, LENGTH = 1024K

    /* RAM - 栈和数据 */
    RAM : ORIGIN = 0x20000000, LENGTH = 128K

    /* CCM RAM - 仅CPU可访问，适合堆栈 */
    CCMRAM : ORIGIN = 0x10000000, LENGTH = 64K
}

/* 栈顶初始化值 */
_stack_start = ORIGIN(CCMRAM) + LENGTH(CCMRAM);
```

---

## 三、硬件抽象层(HAL)

### 3.1 embedded-hal Trait系统

`embedded-hal` 提供了一套通用的硬件抽象接口：

```rust
use embedded_hal::{
    digital::{InputPin, OutputPin, StatefulOutputPin},
    spi::{SpiBus, SpiDevice},
    i2c::I2c,
    pwm::SetDutyCycle,
    adc::OneShot,
};

/// 通用LED驱动 - 不依赖具体硬件
pub struct Led<PIN: OutputPin> {
    pin: PIN,
    state: bool,
}

impl<PIN: OutputPin> Led<PIN> {
    pub fn new(mut pin: PIN) -> Result<Self, PIN::Error> {
        pin.set_low()?;
        Ok(Self { pin, state: false })
    }

    pub fn on(&mut self) -> Result<(), PIN::Error> {
        self.pin.set_high()?;
        self.state = true;
        Ok(())
    }

    pub fn off(&mut self) -> Result<(), PIN::Error> {
        self.pin.set_low()?;
        self.state = false;
        Ok(())
    }

    pub fn toggle(&mut self) -> Result<(), PIN::Error> {
        if self.state {
            self.off()
        } else {
            self.on()
        }
    }
}
```

### 3.2 GPIO示例

```rust
use stm32f4xx_hal::{
    gpio::{self, Edge, Input, Output, PushPull, Speed},
    pac,
    prelude::*,
};

fn gpio_example() {
    let dp = pac::Peripherals::take().unwrap();
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.freeze();

    // 获取GPIO端口
    let gpioa = dp.GPIOA.split();
    let gpioc = dp.GPIOC.split();

    // 配置PA5为推挽输出（LED）
    let mut led = gpioa.pa5.into_push_pull_output();
    led.set_high();

    // 配置PC13为输入（用户按钮）
    let button = gpioc.pc13.into_pull_up_input();

    // 配置外部中断
    let mut exti = dp.EXTI;
    button.make_interrupt_source(&mut dp.SYSCFG);
    button.trigger_on_edge(&mut exti, Edge::Falling);
    button.enable_interrupt(&mut exti);

    // 主循环
    loop {
        if button.is_low() {
            led.toggle();
        }
    }
}
```

### 3.3 UART串口通信

```rust
use stm32f4xx_hal::{
    pac,
    prelude::*,
    serial::{config, Serial},
};
use heapless::spsc::Queue;

/// UART驱动结构
pub struct UartDriver<UART> {
    uart: UART,
    tx_queue: Queue<u8, 64>,
    rx_queue: Queue<u8, 64>,
}

impl UartDriver<pac::USART1> {
    pub fn new(
        usart: pac::USART1,
        tx_pin: gpio::PA9,
        rx_pin: gpio::PA10,
        clocks: &Clocks,
        baud: u32,
    ) -> Self {
        let config = config::Config::default()
            .baudrate(baud.bps())
            .word_length_8()
            .parity_none()
            .stopbits(config::StopBits::STOP1);

        let serial = Serial::new(
            usart,
            (tx_pin, rx_pin),
            config,
            clocks,
        ).unwrap();

        let (tx, rx) = serial.split();

        Self {
            uart: serial,
            tx_queue: Queue::new(),
            rx_queue: Queue::new(),
        }
    }

    /// 发送数据
    pub fn send(&mut self, data: &[u8]) -> Result<usize, ()> {
        let mut sent = 0;
        for &byte in data {
            match self.tx_queue.enqueue(byte) {
                Ok(_) => sent += 1,
                Err(_) => break,
            }
        }
        Ok(sent)
    }

    /// 处理发送中断
    pub fn handle_tx_irq(&mut self) {
        if let Ok(byte) = self.tx_queue.dequeue() {
            // 发送下一个字节
        }
    }

    /// 处理接收中断
    pub fn handle_rx_irq(&mut self, byte: u8) {
        let _ = self.rx_queue.enqueue(byte);
    }
}
```

### 3.4 SPI总线通信

```rust
use embedded_hal::spi::{Mode, Phase, Polarity};
use stm32f4xx_hal::{
    pac::SPI1,
    prelude::*,
    spi::{Spi, NoMiso},
    gpio::{PA5, PA6, PA7},
};

/// SPI模式配置
pub const SPI_MODE_0: Mode = Mode {
    polarity: Polarity::IdleLow,
    phase: Phase::CaptureOnFirstTransition,
};

/// SPI设备驱动
pub struct SpiDevice {
    spi: Spi<SPI1, (PA5, PA6, PA7)>,
    cs_pin: gpio::PA4<Output<PushPull>>,
}

impl SpiDevice {
    pub fn new(
        spi1: SPI1,
        sck: PA5,
        miso: PA6,
        mosi: PA7,
        cs: PA4,
        clocks: &Clocks,
    ) -> Self {
        let cs_pin = cs.into_push_pull_output();

        let spi = Spi::new(
            spi1,
            (sck, miso, mosi),
            SPI_MODE_0,
            1.MHz(),
            clocks,
        );

        Self { spi, cs_pin }
    }

    /// SPI事务 - 片选自动管理
    pub fn transfer(&mut self, write: &[u8], read: &mut [u8]) -> Result<(), ()> {
        self.cs_pin.set_low();

        // 同时发送和接收
        let result = self.spi.transfer(read, write);

        self.cs_pin.set_high();
        result.map_err(|_| ())
    }

    /// 仅发送命令
    pub fn write(&mut self, data: &[u8]) -> Result<(), ()> {
        self.cs_pin.set_low();
        let result = self.spi.write(data);
        self.cs_pin.set_high();
        result.map_err(|_| ())
    }
}
```

### 3.5 I2C总线通信

```rust
use stm32f4xx_hal::{
    pac::I2C1,
    prelude::*,
    i2c::I2c,
};
use embedded_hal::i2c::{I2c as _, SevenBitAddress};

/// I2C设备地址
type I2cAddress = SevenBitAddress;

/// 温度传感器驱动（I2C设备示例）
pub struct TemperatureSensor<I2C> {
    i2c: I2C,
    address: I2cAddress,
}

impl<I2C> TemperatureSensor<I2C>
where
    I2C: embedded_hal::i2c::I2c,
{
    const REG_TEMP: u8 = 0x00;
    const REG_CONFIG: u8 = 0x01;

    pub fn new(i2c: I2C, address: I2cAddress) -> Self {
        Self { i2c, address }
    }

    /// 初始化传感器
    pub fn init(&mut self) -> Result<(), I2C::Error> {
        // 配置传感器：连续转换模式，12位分辨率
        let config: [u8; 2] = [Self::REG_CONFIG, 0x60];
        self.i2c.write(self.address, &config)
    }

    /// 读取温度（摄氏度，0.0625度分辨率）
    pub fn read_temperature(&mut self) -> Result<f32, I2C::Error> {
        let mut buf = [0u8; 2];

        // 设置寄存器指针
        self.i2c.write(self.address, &[Self::REG_TEMP])?;

        // 读取2字节温度数据
        self.i2c.read(self.address, &mut buf)?;

        // 转换为温度值
        let raw = ((buf[0] as i16) << 4) | ((buf[1] as i16) >> 4);
        let temp = if raw > 0x7FF {
            (raw as f32 - 4096.0) * 0.0625
        } else {
            raw as f32 * 0.0625
        };

        Ok(temp)
    }
}
```

---

## 四、实时操作系统(RTOS)

### 4.1 RTIC框架

RTIC (Real-Time Interrupt-driven Concurrency) 是基于中断的并发框架：

```rust
#![no_std]
#![no_main]

use rtic::app;
use stm32f4xx_hal::prelude::*;
use heapless::spsc::Queue;

#[app(device = stm32f4xx_hal::pac, peripherals = true)]
mod app {
    use super::*;

    // 共享资源
    #[shared]
    struct Shared {
        sensor_data: Queue<u16, 16>,
        tx_complete: bool,
    }

    // 本地资源（每个任务独占）
    #[local]
    struct Local {
        led: gpio::PA5<Output<PushPull>>,
        uart: UART1,
    }

    // 初始化函数
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        let dp = cx.device;
        let rcc = dp.RCC.constrain();
        let clocks = rcc.cfgr.freeze();

        // 配置GPIO
        let gpioa = dp.GPIOA.split();
        let led = gpioa.pa5.into_push_pull_output();

        // 配置定时器
        let mut timer = dp.TIM2.counter_us(&clocks);
        timer.start(1.secs()).unwrap();
        timer.listen(Event::Update);

        // 启动周期性任务
        sensor_read::spawn().unwrap();

        (
            Shared {
                sensor_data: Queue::new(),
                tx_complete: true,
            },
            Local { led, uart },
        )
    }

    // 空闲任务（低功耗模式）
    #[idle]
    fn idle(_: idle::Context) -> ! {
        loop {
            rtic::export::wfi(); // 等待中断
        }
    }

    // 传感器读取任务（高优先级）
    #[task(priority = 3, shared = [sensor_data])]
    fn sensor_read(mut cx: sensor_read::Context) {
        // 读取传感器数据
        let value = read_adc();

        cx.shared.sensor_data.lock(|queue| {
            let _ = queue.enqueue(value);
        });

        // 安排下一次读取
        sensor_read::spawn_after(100.millis()).unwrap();
    }

    // 数据处理任务（中优先级）
    #[task(priority = 2, shared = [sensor_data, tx_complete])]
    fn process_data(mut cx: process_data::Context) {
        let data = cx.shared.sensor_data.lock(|queue| {
            queue.dequeue()
        });

        if let Some(value) = data {
            // 滤波处理
            let filtered = apply_filter(value);

            // 发送到传输队列
            if cx.shared.tx_complete.lock(|c| *c) {
                *cx.shared.tx_complete.lock(|c| *c) = false;
                transmit::spawn(filtered).unwrap();
            }
        }
    }

    // 数据传输任务（低优先级，可抢占）
    #[task(priority = 1, shared = [tx_complete])]
    fn transmit(mut cx: transmit::Context, data: u16) {
        // 通过无线发送数据
        send_wireless(data);

        cx.shared.tx_complete.lock(|c| *c = true);
    }

    // 硬件定时器中断绑定
    #[task(binds = TIM2, local = [led])]
    fn tim2_irq(cx: tim2_irq::Context) {
        cx.local.led.toggle();
        // 清除中断标志
    }
}
```

### 4.2 Embassy异步运行时

Embassy是现代化的异步嵌入式框架：

```rust
#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]

use embassy_executor::Spawner;
use embassy_stm32::{
    gpio::{Level, Output, Speed},
    time::Timer,
};
use embassy_time::{Duration, Instant};
use {defmt_rtt as _, panic_probe as _};

/// 传感器读取任务
#[embassy_executor::task]
async fn sensor_task(mut adc: Adc<'static>) {
    let mut interval = embassy_time::Ticker::every(Duration::from_millis(100));

    loop {
        // 读取ADC
        let value = adc.read(&mut adc_channel).await;
        defmt::info!("ADC value: {}", value);

        // 等待下一个周期
        interval.next().await;
    }
}

/// 网络通信任务
#[embassy_executor::task]
async fn network_task(stack: Stack<'static>) {
    let mut rx_buffer = [0; 1024];
    let mut tx_buffer = [0; 1024];

    loop {
        // 等待网络连接
        stack.wait_link_up().await;
        defmt::info!("Network connected");

        // 创建TCP连接
        let mut socket = TcpSocket::new(stack, &mut rx_buffer, &mut tx_buffer);

        match socket.connect(MQTT_BROKER_ADDR, 1883).await {
            Ok(()) => {
                defmt::info!("Connected to MQTT broker");

                // MQTT通信循环
                let mut mqtt = MqttClient::new(socket);

                if mqtt.connect(CLIENT_ID).await.is_ok() {
                    // 订阅主题
                    mqtt.subscribe("sensor/control").await.unwrap();

                    // 主循环
                    loop {
                        match embassy_time::with_timeout(
                            Duration::from_secs(30),
                            mqtt.run()
                        ).await {
                            Ok(Ok(())) => continue,
                            _ => break, // 超时或错误，重连
                        }
                    }
                }
            }
            Err(e) => {
                defmt::error!("Connection failed: {:?}", e);
                Timer::after(Duration::from_secs(5)).await;
            }
        }
    }
}

/// 主函数
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());

    // 配置LED
    let mut led = Output::new(p.PA5, Level::Low, Speed::Low);

    // 初始化ADC
    let adc = Adc::new(p.ADC1);

    // 初始化网络堆栈
    let stack = initialize_network_stack().await;

    // 启动任务
    spawner.spawn(sensor_task(adc)).unwrap();
    spawner.spawn(network_task(stack)).unwrap();

    // 主任务：状态指示
    let mut ticker = embassy_time::Ticker::every(Duration::from_millis(500));
    loop {
        led.toggle();
        ticker.next().await;
    }
}
```

### 4.3 任务调度与优先级

```rust
/// Embassy中的任务优先级配置
use embassy_executor::SpawnError;

// 高优先级任务池（时间关键）
#[embassy_executor::task(pool_size = 2, priority = 3)]
async fn high_priority_task(id: usize) {
    loop {
        // 处理紧急事件
        process_urgent().await;
    }
}

// 中优先级任务池（数据处理）
#[embassy_executor::task(pool_size = 4, priority = 2)]
async fn medium_priority_task(data: SensorData) {
    // 处理传感器数据
    let processed = process_data(data).await;

    // 发送结果
    RESULT_CHANNEL.send(processed).await;
}

// 低优先级任务（后台维护）
#[embassy_executor::task(priority = 1)]
async fn low_priority_task() {
    loop {
        // 日志轮转
        rotate_logs().await;
        Timer::after(Duration::from_secs(3600)).await;
    }
}

/// 带超时和取消的任务
async fn cancellable_operation(cancel: &mut CancellationToken) -> Result<(), Error> {
    select! {
        // 执行主要操作
        result = perform_operation() => result,

        // 或响应取消信号
        _ = cancel.cancelled() => {
            defmt::info!("Operation cancelled");
            Err(Error::Cancelled)
        }
    }
}

/// 资源访问控制
static SENSOR_MUTEX: Mutex<CriticalSectionRawMutex, Sensor> = Mutex::new(Sensor::new());

async fn safe_sensor_read() -> u16 {
    // 获取互斥锁，自动释放
    let mut sensor = SENSOR_MUTEX.lock().await;
    sensor.read().await
}
```

---

## 五、内存管理

### 5.1 静态分配策略

```rust
use heapless::{Vec, String, FnvIndexMap, Pool};

/// 编译期确定的静态缓冲区
#[link_section = ".uninit"]
static mut UART_TX_BUFFER: [u8; 1024] = [0; 1024];

#[link_section = ".uninit"]
static mut UART_RX_BUFFER: [u8; 1024] = [0; 1024];

/// 固定大小的数据结构
pub struct StaticConfig {
    device_id: String<32>,
    server_url: String<64>,
    params: FnvIndexMap<String<16>, i32, 16>,
}

impl StaticConfig {
    pub const fn new() -> Self {
        Self {
            device_id: String::new(),
            server_url: String::new(),
            params: FnvIndexMap::new(),
        }
    }
}

// 全局配置实例
static CONFIG: Mutex<RefCell<StaticConfig>> =
    Mutex::new(RefCell::new(StaticConfig::new()));

/// 无堆分配的日志缓冲区
pub struct LogBuffer<const N: usize> {
    entries: Vec<LogEntry, N>,
    overflow_count: u32,
}

impl<const N: usize> LogBuffer<N> {
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
            overflow_count: 0,
        }
    }

    pub fn push(&mut self, entry: LogEntry) {
        match self.entries.push(entry) {
            Ok(_) => {}
            Err(e) => {
                // 移除最旧的条目
                self.entries.remove(0);
                let _ = self.entries.push(e);
                self.overflow_count += 1;
            }
        }
    }
}
```

### 5.2 内存池

```rust
use heapless::pool::Pool;
use core::mem::MaybeUninit;

/// 内存池配置
const POOL_SIZE: usize = 8;
const BLOCK_SIZE: usize = 256;

/// 网络数据包结构
#[repr(align(4))]
pub struct Packet {
    data: [u8; BLOCK_SIZE],
    len: usize,
}

// 静态内存池存储
static mut POOL_STORAGE: [MaybeUninit<Packet>; POOL_SIZE] =
    [MaybeUninit::uninit(); POOL_SIZE];

/// 全局内存池
static mut PACKET_POOL: Pool<Packet> = Pool::new();

pub fn init_memory_pool() {
    unsafe {
        PACKET_POOL.grow(&mut POOL_STORAGE);
    }
}

/// 使用内存池的数据包处理器
pub struct PacketProcessor;

impl PacketProcessor {
    pub fn process_frame(data: &[u8]) -> Option<Box<Packet, &'static Pool<Packet>>> {
        // 从内存池分配
        let mut packet = unsafe { PACKET_POOL.alloc()? };

        // 复制数据
        let len = data.len().min(BLOCK_SIZE);
        packet.data[..len].copy_from_slice(&data[..len]);
        packet.len = len;

        // 处理完成后自动归还内存池
        Some(packet)
    }
}

/// 多池管理器
pub struct MemoryManager {
    small_pool: Pool<[u8; 64]>,
    medium_pool: Pool<[u8; 256]>,
    large_pool: Pool<[u8; 1024]>,
}

impl MemoryManager {
    pub fn alloc_for_size(&self, size: usize) -> Option<Allocation> {
        match size {
            0..=64 => self.small_pool.alloc().map(Allocation::Small),
            65..=256 => self.medium_pool.alloc().map(Allocation::Medium),
            257..=1024 => self.large_pool.alloc().map(Allocation::Large),
            _ => None,
        }
    }
}
```

### 5.3 栈溢出保护

```rust
/// 栈使用监控
pub struct StackMonitor;

impl StackMonitor {
    /// 填充栈底模式以检测溢出
    pub fn init_stack_guard() {
        extern "C" {
            static mut _sstack: u32;
            static mut _estack: u32;
        }

        unsafe {
            let stack_bottom = &mut _sstack as *mut u32;
            let stack_top = &_estack as *const u32;
            let stack_size = (stack_top as usize - stack_bottom as usize) / 4;

            // 填充0xDEADBEEF模式
            for i in 0..(stack_size / 4) {
                *stack_bottom.add(i) = 0xDEAD_BEEF;
            }
        }
    }

    /// 检查栈使用情况
    pub fn check_stack_usage() -> (usize, usize) {
        unsafe {
            let stack_bottom = &_sstack as *const u32;
            let stack_top = &_estack as *const u32;
            let total_size = stack_top as usize - stack_bottom as usize;

            // 查找第一个非0xDEADBEEF位置
            let mut used = 0usize;
            for i in 0..(total_size / 4) {
                let ptr = stack_bottom.add(i);
                if core::ptr::read_volatile(ptr) != 0xDEAD_BEEF {
                    used = total_size - (i * 4);
                    break;
                }
            }

            (used, total_size)
        }
    }
}

/// 链接脚本中的栈保护区域
/*
SECTIONS
{
    .stack_guard (NOLOAD) : {
        . = ALIGN(8);
        _sstack = .;
        . = . + 0x100;  /* 256字节保护区域 */
        KEEP(*(.stack_guard))
        _estack = .;
    } > CCMRAM
}
*/

/// 硬件MPU栈溢出保护
#[cfg(feature = "mpu_stack_protection")]
pub fn setup_mpu_stack_guard() {
    let mpu = unsafe { &*cortex_m::peripheral::MPU::ptr() };

    // 配置MPU区域覆盖栈底
    mpu.rbar.write(
        (0x20000000 & 0xFFFFFFE0) |  // 基地址
        (0 << 1) |                    // 区域有效
        (1 << 4)                      // 区域号
    );

    mpu.rasr.write(
        (0b111 << 1) |               // 全尺寸（4GB）
        (0 << 8) |                    // 禁止访问
        (1 << 0)                      // 使能
    );

    mpu.ctrl.write(0b101); // 使能MPU，背景区域使能
}
```

---

## 六、中断处理

### 6.1 安全的中断处理

```rust
use cortex_m::interrupt::{self, Mutex};
use core::cell::RefCell;

/// 中断安全的共享状态
static INTERRUPT_FLAG: Mutex<RefCell<bool>> = Mutex::new(RefCell::new(false));
static DATA_READY: Mutex<RefCell<Option<SensorData>>> = Mutex::new(RefCell::new(None));

/// 中断处理函数
#[interrupt]
fn TIM2() {
    // 快速操作：仅设置标志
    interrupt::free(|cs| {
        *INTERRUPT_FLAG.borrow(cs).borrow_mut() = true;

        // 可选：将数据存入共享缓冲区
        let data = read_sensor_hardware();
        *DATA_READY.borrow(cs).borrow_mut() = Some(data);
    });

    // 清除中断标志（硬件相关）
    unsafe {
        (*stm32f4::stm32f407::TIM2::ptr()).sr.modify(|_, w| w.uif().clear());
    }
}

/// 主循环中处理中断事件
fn process_interrupts() {
    let should_process = interrupt::free(|cs| {
        let flag = INTERRUPT_FLAG.borrow(cs).borrow().clone();
        *INTERRUPT_FLAG.borrow(cs).borrow_mut() = false;
        flag
    });

    if should_process {
        let data = interrupt::free(|cs| {
            DATA_READY.borrow(cs).borrow_mut().take()
        });

        if let Some(d) = data {
            handle_sensor_data(d);
        }
    }
}
```

### 6.2 临界区管理

```rust
use cortex_m::interrupt::{self, CriticalSection};
use critical_section::with;

/// 临界区保护的数据结构
pub struct CriticalResource<T> {
    inner: Mutex<RefCell<T>>,
}

impl<T> CriticalResource<T> {
    pub const fn new(value: T) -> Self {
        Self {
            inner: Mutex::new(RefCell::new(value)),
        }
    }

    pub fn with<R>(&self, f: impl FnOnce(&mut T) -> R) -> R {
        interrupt::free(|cs| f(&mut *self.inner.borrow(cs).borrow_mut()))
    }
}

/// 示例：临界区保护的计数器
static COUNTER: CriticalResource<u32> = CriticalResource::new(0);

fn increment_counter() {
    COUNTER.with(|c| *c += 1);
}

fn get_counter() -> u32 {
    COUNTER.with(|c| *c)
}

/// 优先级提升临界区（适用于RTOS环境）
#[cfg(feature = "rtic")]
mod rtic_critical {
    use rtic::export::Priority;

    pub struct PriorityCeiling;

    impl PriorityCeiling {
        pub fn raise<F, R>(priority: u8, f: F) -> R
        where
            F: FnOnce() -> R,
        {
            let original = Priority::current();
            Priority::set(priority);
            let result = f();
            Priority::set(original);
            result
        }
    }
}
```

### 6.3 无锁数据结构

```rust
use heapless::spsc::Queue;
use core::sync::atomic::{AtomicUsize, Ordering};

/// 单生产者单消费者无锁队列
pub struct LockFreeQueue<T, const N: usize> {
    queue: Queue<T, N>,
    head: AtomicUsize,
    tail: AtomicUsize,
}

impl<T, const N: usize> LockFreeQueue<T, N> {
    pub const fn new() -> Self {
        Self {
            queue: Queue::new(),
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
        }
    }

    /// 生产者调用（中断或任务）
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        let tail = self.tail.load(Ordering::Relaxed);
        let next = (tail + 1) % N;

        if next == self.head.load(Ordering::Acquire) {
            return Err(item); // 队列满
        }

        // 安全：只有一个生产者
        unsafe {
            let ptr = self.queue.as_ptr().add(tail) as *mut T;
            ptr.write(item);
        }

        self.tail.store(next, Ordering::Release);
        Ok(())
    }

    /// 消费者调用（主循环）
    pub fn dequeue(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);

        if head == self.tail.load(Ordering::Acquire) {
            return None; // 队列空
        }

        // 安全：只有一个消费者
        let item = unsafe {
            let ptr = self.queue.as_ptr().add(head) as *const T;
            ptr.read()
        };

        self.head.store((head + 1) % N, Ordering::Release);
        Some(item)
    }
}

/// 原子状态标志
pub struct AtomicFlags {
    flags: AtomicUsize,
}

impl AtomicFlags {
    pub const fn new() -> Self {
        Self {
            flags: AtomicUsize::new(0),
        }
    }

    /// 设置标志（ISR安全）
    pub fn set(&self, bit: u8) {
        self.flags.fetch_or(1 << bit, Ordering::SeqCst);
    }

    /// 清除并返回之前的值
    pub fn clear(&self, bit: u8) -> bool {
        let mask = 1 << bit;
        let old = self.flags.fetch_and(!mask, Ordering::SeqCst);
        (old & mask) != 0
    }

    /// 测试并清除所有标志
    pub fn test_and_clear_all(&self) -> usize {
        self.flags.swap(0, Ordering::SeqCst)
    }
}
```

---

## 七、物联网协议

### 7.1 MQTT客户端

```rust
use embassy_net::tcp::TcpSocket;
use heapless::String;

/// MQTT QoS等级
#[derive(Clone, Copy)]
pub enum QoS {
    AtMostOnce = 0,   // 最多一次
    AtLeastOnce = 1,  // 至少一次
    ExactlyOnce = 2,  // 恰好一次
}

/// MQTT客户端配置
pub struct MqttConfig<'a> {
    client_id: &'a str,
    keep_alive: u16,
    username: Option<&'a str>,
    password: Option<&'a str>,
}

/// MQTT客户端实现
pub struct MqttClient<'a, 'b> {
    socket: TcpSocket<'a>,
    buffer: &'b mut [u8],
    state: MqttState,
    packet_id: u16,
}

impl<'a, 'b> MqttClient<'a, 'b> {
    /// 连接MQTT Broker
    pub async fn connect(&mut self, config: &MqttConfig<'_>) -> Result<(), MqttError> {
        // 构建CONNECT报文
        let mut packet = heapless::Vec::<u8, 128>::new();

        // 固定报头
        packet.push(0x10); // CONNECT类型

        // 可变报头 + 有效载荷
        let mut var_header = heapless::Vec::<u8, 100>::new();

        // 协议名
        Self::encode_string(&mut var_header, "MQTT")?;
        // 协议级别
        var_header.push(4);
        // 连接标志
        let mut connect_flags = 0x02u8; // Clean session
        if config.username.is_some() { connect_flags |= 0x80; }
        if config.password.is_some() { connect_flags |= 0x40; }
        var_header.push(connect_flags);
        // Keep alive
        var_header.push((config.keep_alive >> 8) as u8);
        var_header.push(config.keep_alive as u8);
        // Client ID
        Self::encode_string(&mut var_header, config.client_id)?;
        // 认证信息
        if let Some(user) = config.username {
            Self::encode_string(&mut var_header, user)?;
        }
        if let Some(pass) = config.password {
            Self::encode_string(&mut var_header, pass)?;
        }

        // 计算剩余长度
        Self::encode_remaining_length(&mut packet, var_header.len())?;
        packet.extend_from_slice(&var_header).map_err(|_| MqttError::BufferFull)?;

        // 发送报文
        self.socket.write_all(&packet).await.map_err(|_| MqttError::Network)?;

        // 等待CONNACK
        self.wait_connack().await
    }

    /// 发布消息
    pub async fn publish(
        &mut self,
        topic: &str,
        payload: &[u8],
        qos: QoS,
        retain: bool,
    ) -> Result<(), MqttError> {
        let mut packet = heapless::Vec::<u8, 256>::new();

        // 固定报头
        let mut first_byte = 0x30u8;
        first_byte |= (qos as u8) << 1;
        if retain { first_byte |= 0x01; }
        packet.push(first_byte);

        // 可变报头
        let mut var_header = heapless::Vec::<u8, 64>::new();
        Self::encode_string(&mut var_header, topic)?;

        if qos as u8 > 0 {
            // 包标识符（QoS 1/2需要）
            self.packet_id = self.packet_id.wrapping_add(1);
            var_header.push((self.packet_id >> 8) as u8);
            var_header.push(self.packet_id as u8);
        }

        let remaining_len = var_header.len() + payload.len();
        Self::encode_remaining_length(&mut packet, remaining_len)?;
        packet.extend_from_slice(&var_header).map_err(|_| MqttError::BufferFull)?;

        // 发送
        self.socket.write_all(&packet).await.map_err(|_| MqttError::Network)?;
        self.socket.write_all(payload).await.map_err(|_| MqttError::Network)?;

        Ok(())
    }

    /// 订阅主题
    pub async fn subscribe(&mut self, topic: &str, qos: QoS) -> Result<(), MqttError> {
        let mut packet = heapless::Vec::<u8, 128>::new();
        packet.push(0x82); // SUBSCRIBE

        let mut payload = heapless::Vec::<u8, 64>::new();
        self.packet_id = self.packet_id.wrapping_add(1);
        payload.push((self.packet_id >> 8) as u8);
        payload.push(self.packet_id as u8);

        Self::encode_string(&mut payload, topic)?;
        payload.push(qos as u8);

        Self::encode_remaining_length(&mut packet, payload.len())?;
        packet.extend_from_slice(&payload).map_err(|_| MqttError::BufferFull)?;

        self.socket.write_all(&packet).await.map_err(|_| MqttError::Network)?;

        // 等待SUBACK...
        Ok(())
    }

    fn encode_string(buf: &mut impl heapless::VecExt<u8>, s: &str) -> Result<(), ()> {
        let len = s.len();
        buf.push((len >> 8) as u8)?;
        buf.push(len as u8)?;
        buf.extend_from_slice(s.as_bytes()).map_err(|_| ())
    }

    fn encode_remaining_length(buf: &mut impl heapless::VecExt<u8>, mut len: usize) -> Result<(), ()> {
        loop {
            let mut byte = (len % 128) as u8;
            len /= 128;
            if len > 0 {
                byte |= 0x80;
            }
            buf.push(byte)?;
            if len == 0 { break; }
        }
        Ok(())
    }

    async fn wait_connack(&mut self) -> Result<(), MqttError> {
        // 简化实现：读取并解析CONNACK
        let mut buf = [0u8; 4];
        self.socket.read_exact(&mut buf).await.map_err(|_| MqttError::Network)?;

        if buf[0] != 0x20 || buf[3] != 0 {
            return Err(MqttError::ConnectionRefused);
        }

        self.state = MqttState::Connected;
        Ok(())
    }
}
```

### 7.2 CoAP协议

```rust
/// CoAP消息类型
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum CoapType {
    Confirmable = 0,      // CON - 需要确认
    NonConfirmable = 1,   // NON - 无需确认
    Acknowledgement = 2,  // ACK - 确认
    Reset = 3,            // RST - 复位
}

/// CoAP方法码
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum CoapMethod {
    Get = 1,
    Post = 2,
    Put = 3,
    Delete = 4,
}

/// CoAP响应码
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum CoapResponseCode {
    Created = 0x41,       // 2.01
    Deleted = 0x42,       // 2.02
    Valid = 0x43,         // 2.03
    Changed = 0x44,       // 2.04
    Content = 0x45,       // 2.05
    BadRequest = 0x80,    // 4.00
    Unauthorized = 0x81,  // 4.01
    // ... 更多状态码
}

/// CoAP客户端
pub struct CoapClient {
    msg_id: u16,
    token: u8,
}

impl CoapClient {
    pub fn new() -> Self {
        Self {
            msg_id: 1,
            token: 0,
        }
    }

    /// 构建CoAP请求
    pub fn build_request(
        &mut self,
        method: CoapMethod,
        uri_path: &str,
        payload: Option<&[u8]>,
    ) -> heapless::Vec<u8, 512> {
        let mut packet = heapless::Vec::<u8, 512>::new();

        // 报头 (4字节)
        // Ver: 1, T: CON, TKL: 1
        packet.push(0x41).unwrap();
        // Code: 请求方法
        packet.push(method as u8).unwrap();
        // Message ID
        packet.push((self.msg_id >> 8) as u8).unwrap();
        packet.push(self.msg_id as u8).unwrap();
        self.msg_id = self.msg_id.wrapping_add(1);

        // Token
        packet.push(self.token).unwrap();
        self.token = self.token.wrapping_add(1);

        // Options: Uri-Path
        Self::add_option(&mut packet, 11, uri_path.as_bytes()); // Uri-Path = 11

        // Payload marker + payload
        if let Some(data) = payload {
            packet.push(0xFF).unwrap(); // Payload marker
            packet.extend_from_slice(data).unwrap();
        }

        packet
    }

    fn add_option(packet: &mut impl heapless::VecExt<u8>, delta: u8, value: &[u8]) {
        let delta_nibble = if delta < 13 { delta } else { 13 };
        let len_nibble = if value.len() < 13 { value.len() as u8 } else { 13 };

        packet.push((delta_nibble << 4) | len_nibble).unwrap();

        if delta >= 13 {
            packet.push(delta - 13).unwrap();
        }
        if value.len() >= 13 {
            packet.push((value.len() - 13) as u8).unwrap();
        }

        packet.extend_from_slice(value).unwrap();
    }
}
```

### 7.3 LoRaWAN协议

```rust
/// LoRaWAN区域配置
#[derive(Clone, Copy)]
pub enum LoraRegion {
    EU868,
    US915,
    AS923,
    CN470,
}

/// LoRaWAN设备类别
#[derive(Clone, Copy)]
pub enum DeviceClass {
    A, // A类：最省电，下行窗口仅在发送后
    B, // B类：增加信标同步接收窗口
    C, // C类：几乎持续接收，最耗电
}

/// LoRaWAN堆栈配置
pub struct LoraWanConfig {
    pub region: LoraRegion,
    pub device_class: DeviceClass,
    pub dev_eui: [u8; 8],
    pub app_eui: [u8; 8],
    pub app_key: [u8; 16],
}

/// LoRaWAN设备
pub struct LoraWanDevice<Radio> {
    radio: Radio,
    config: LoraWanConfig,
    session: Option<SessionState>,
    frame_counter: u32,
}

struct SessionState {
    dev_addr: [u8; 4],
    nwk_skey: [u8; 16],
    app_skey: [u8; 16],
}

impl<Radio> LoraWanDevice<Radio>
where
    Radio: LoraRadio,
{
    /// 入网（OTAA - Over-The-Air Activation）
    pub async fn join_otaa(&mut self) -> Result<(), LoraWanError> {
        // 构建Join-Request
        let join_request = self.build_join_request();

        // 配置射频参数
        self.radio.configure_channel(&self.get_join_channel()).await?;

        // 发送入网请求
        self.radio.transmit(&join_request).await?;

        // 等待Join-Accept（在接收窗口1和2）
        let response = self.receive_with_timeout(RECEIVE_DELAY1).await?;

        // 解析Join-Accept并派生密钥
        self.process_join_accept(&response).await?;

        Ok(())
    }

    /// 发送上行数据
    pub async fn send_uplink(
        &mut self,
        port: u8,
        payload: &[u8],
        confirmed: bool,
    ) -> Result<Option<Downlink>, LoraWanError> {
        let session = self.session.as_ref().ok_or(LoraWanError::NotJoined)?;

        // 构建MAC帧
        let mut frame = heapless::Vec::<u8, 256>::new();

        // MHDR
        frame.push(if confirmed { 0x80 } else { 0x40 }).unwrap();

        // FHDR
        frame.extend_from_slice(&session.dev_addr).unwrap();
        frame.push(0x00); // FCtrl
        frame.push((self.frame_counter & 0xFF) as u8).unwrap();
        frame.push(((self.frame_counter >> 8) & 0xFF) as u8).unwrap();

        // FPort
        frame.push(port).unwrap();

        // 加密FRMPayload
        let encrypted = self.encrypt_payload(payload, &session.app_skey);
        frame.extend_from_slice(&encrypted).unwrap();

        // 计算并添加MIC
        let mic = self.calculate_mic(&frame, &session.nwk_skey);
        frame.extend_from_slice(&mic).unwrap();

        // 发送
        self.radio.transmit(&frame).await?;
        self.frame_counter += 1;

        // A类设备：等待接收窗口
        if matches!(self.config.device_class, DeviceClass::A) {
            self.wait_downlink().await
        } else {
            Ok(None)
        }
    }

    fn build_join_request(&self) -> heapless::Vec<u8, 64> {
        let mut req = heapless::Vec::<u8, 64>::new();

        // MHDR (Join-Request)
        req.push(0x00).unwrap();

        // JoinEUI/AppEUI (小端序)
        for &b in self.config.app_eui.iter().rev() {
            req.push(b).unwrap();
        }

        // DevEUI (小端序)
        for &b in self.config.dev_eui.iter().rev() {
            req.push(b).unwrap();
        }

        // DevNonce
        let nonce = self.generate_dev_nonce();
        req.push((nonce & 0xFF) as u8).unwrap();
        req.push(((nonce >> 8) & 0xFF) as u8).unwrap();

        // MIC
        let mic = crypto::cmac_aes128(&self.config.app_key, &req[..])
            .map_err(|_| ())
            .unwrap();
        req.extend_from_slice(&mic[..4]).unwrap();

        req
    }

    fn encrypt_payload(&self, payload: &[u8], key: &[u8; 16]) -> heapless::Vec<u8, 256> {
        // AES-128 CTR模式加密
        let mut encrypted = heapless::Vec::<u8, 256>::new();
        // 实现略...
        encrypted
    }

    fn calculate_mic(&self, data: &[u8], key: &[u8; 16]) -> [u8; 4] {
        // AES-CMAC计算
        let cmac = crypto::cmac_aes128(key, data).unwrap();
        [cmac[0], cmac[1], cmac[2], cmac[3]]
    }
}
```

---

## 八、电源管理

### 8.1 低功耗模式

```rust
use stm32f4xx_hal::pac::PWR;
use cortex_m::peripheral::SCB;

/// 功耗模式枚举
#[derive(Clone, Copy)]
pub enum PowerMode {
    Run,           // 正常运行模式
    Sleep,         // CPU休眠，外设运行
    Stop,          // 停止模式，内存保持
    Standby,       // 待机模式，仅备份域运行
}

/// 电源管理器
pub struct PowerManager {
    pwr: PWR,
    scb: SCB,
}

impl PowerManager {
    pub fn new(pwr: PWR, scb: SCB) -> Self {
        Self { pwr, scb }
    }

    /// 进入Sleep模式
    pub fn enter_sleep(&mut self) {
        // 配置系统控制寄存器
        self.scb.clear_sleepdeep();

        // 等待中断
        cortex_m::asm::wfi();
    }

    /// 进入Stop模式
    pub fn enter_stop(&mut self, wakeup_sources: WakeupSources) {
        // 配置唤醒源
        self.configure_wakeup(wakeup_sources);

        // 进入Stop模式
        self.pwr.cr.modify(|_, w| w
            .pdds().clear_bit()  // 选择Stop模式
            .fpds().clear_bit()  //  Flash保持供电
            .lpuds().clear_bit() // 调节器正常运行
        );

        // 设置SLEEPDEEP位
        self.scb.set_sleepdeep();

        // 执行WFI
        cortex_m::asm::wfi();

        // 唤醒后恢复
        self.scb.clear_sleepdeep();
    }

    /// 进入Standby模式
    pub fn enter_standby(&mut self) {
        // 允许唤醒引脚
        self.pwr.csr.modify(|_, w| w.ewup().set_bit());

        // 选择Standby模式
        self.pwr.cr.modify(|_, w| w.pdds().set_bit());

        // 清除唤醒标志
        self.pwr.cr.modify(|_, w| w.cwuf().set_bit());

        // 设置SLEEPDEEP
        self.scb.set_sleepdeep();

        // 执行WFI
        cortex_m::asm::wfi();
    }

    /// 配置时钟以降低功耗
    pub fn reduce_clock_speed(&mut self, target_freq_mhz: u32) {
        // 降低系统时钟频率
        // 实现略...涉及PLL和分频器配置
    }

    /// 关闭未使用的外设时钟
    pub fn disable_unused_peripherals(&mut self, mask: u32) {
        let rcc = unsafe { &*stm32f4xx_hal::pac::RCC::ptr() };

        // 关闭AHB外设时钟
        rcc.ahbenr.modify(|r, w| unsafe { w.bits(r.bits() & !mask) });

        // 关闭APB1外设时钟
        rcc.apb1enr.modify(|r, w| unsafe { w.bits(r.bits() & !mask) });

        // 关闭APB2外设时钟
        rcc.apb2enr.modify(|r, w| unsafe { w.bits(r.bits() & !mask) });
    }
}
```

### 8.2 睡眠状态管理

```rust
use embassy_time::{Duration, Instant, Timer};
use core::sync::atomic::{AtomicU32, Ordering};

/// 设备运行状态
#[derive(Clone, Copy, PartialEq)]
pub enum DeviceState {
    Active,      // 全速运行
    Idle,        // 降低频率运行
    Sleep,       // 周期唤醒
    DeepSleep,   // 仅在事件时唤醒
}

/// 睡眠管理器
pub struct SleepManager {
    state: AtomicU32,  // 使用原子存储状态
    last_activity: AtomicU32,
    idle_threshold_ms: u32,
    sleep_threshold_ms: u32,
}

impl SleepManager {
    pub const fn new(idle_ms: u32, sleep_ms: u32) -> Self {
        Self {
            state: AtomicU32::new(DeviceState::Active as u32),
            last_activity: AtomicU32::new(0),
            idle_threshold_ms: idle_ms,
            sleep_threshold_ms: sleep_ms,
        }
    }

    /// 记录活动
    pub fn record_activity(&self) {
        let now = Instant::now().as_millis() as u32;
        self.last_activity.store(now, Ordering::Relaxed);
        self.state.store(DeviceState::Active as u32, Ordering::Relaxed);
    }

    /// 更新并获取当前状态
    pub fn update_state(&self) -> DeviceState {
        let now = Instant::now().as_millis() as u32;
        let last = self.last_activity.load(Ordering::Relaxed);
        let inactive = now.saturating_sub(last);

        let new_state = if inactive > self.sleep_threshold_ms {
            DeviceState::DeepSleep
        } else if inactive > self.idle_threshold_ms {
            DeviceState::Sleep
        } else {
            DeviceState::Active
        };

        self.state.store(new_state as u32, Ordering::Relaxed);
        new_state
    }

    /// 根据状态执行相应操作
    pub async fn manage_power(&self, power: &mut PowerManager) {
        match self.update_state() {
            DeviceState::Active => {
                // 全速运行，无需特殊处理
            }
            DeviceState::Idle => {
                // 降低时钟频率
                power.reduce_clock_speed(16);
            }
            DeviceState::Sleep => {
                // 设置定时器唤醒，进入Sleep模式
                power.enter_sleep();
            }
            DeviceState::DeepSleep => {
                // 配置外部中断唤醒
                power.enter_stop(WakeupSources::EXTI);
            }
        }
    }
}

/// 周期性任务调度器（支持低功耗）
pub struct LowPowerScheduler;

impl LowPowerScheduler {
    /// 调度任务，自动管理功耗
    pub async fn run_with_power_management<F>(
        interval: Duration,
        task: F,
        sleep_mgr: &SleepManager,
    ) where
        F: Future<Output = ()>,
    {
        let mut ticker = embassy_time::Ticker::every(interval);

        loop {
            // 执行任务
            task.await;

            // 记录活动
            sleep_mgr.record_activity();

            // 等待下一个周期
            ticker.next().await;
        }
    }
}
```

---

## 九、完整示例：温度传感器数据采集系统

### 9.1 系统架构

```
┌─────────────────────────────────────────────────────────────┐
│                    Temperature Sensor System                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐     │
│  │  I2C Driver │    │  ADC Driver │    │  GPIO Driver│     │
│  │  (TMP117)   │    │  (Internal) │    │  (Status LED)│    │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘     │
│         │                  │                   │            │
│         └──────────────────┼───────────────────┘            │
│                            │                                 │
│                   ┌────────▼────────┐                       │
│                   │  Sensor Manager │                       │
│                   │  (Data Fusion)  │                       │
│                   └────────┬────────┘                       │
│                            │                                 │
│         ┌──────────────────┼──────────────────┐             │
│         │                  │                  │              │
│  ┌──────▼──────┐    ┌──────▼──────┐    ┌──────▼──────┐      │
│  │  MQTT Client│    │  CoAP Client│    │  LoRaWAN   │      │
│  │  (Primary)  │    │  (Fallback) │    │  (Remote)  │      │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘      │
│         │                  │                  │              │
│         └──────────────────┼──────────────────┘              │
│                            │                                 │
│                   ┌────────▼────────┐                       │
│                   │  Power Manager  │                       │
│                   │  (Sleep/Wake)   │                       │
│                   └─────────────────┘                       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 9.2 完整代码实现

```rust
#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]

use embassy_executor::Spawner;
use embassy_stm32::{
    adc::{Adc, SampleTime},
    dma::NoDma,
    gpio::{Level, Output, Speed, Pull, Input},
    i2c::I2c,
    peripherals,
    time::Hertz,
};
use embassy_time::{Duration, Instant, Timer, Ticker};
use embassy_sync::blocking_mutex::raw::ThreadModeRawMutex;
use embassy_sync::channel::Channel;
use heapless::{String, Vec};
use serde::Serialize;

// ==================== 配置常量 ====================

const DEVICE_ID: &str = env!("DEVICE_ID", "TEMP001");
const SAMPLE_INTERVAL_MS: u64 = 5000;      // 采样间隔
const TRANSMISSION_INTERVAL_MS: u64 = 30000; // 发送间隔
const TEMP_HIGH_THRESHOLD: f32 = 30.0;     // 高温告警阈值
const TEMP_LOW_THRESHOLD: f32 = 5.0;       // 低温告警阈值

// ==================== 数据结构 ====================

/// 传感器读数
#[derive(Clone, Copy, Debug)]
struct SensorReading {
    timestamp: u64,
    temperature: f32,
    humidity: Option<f32>,
    battery_mv: u16,
}

/// 告警类型
#[derive(Clone, Copy, Debug)]
enum AlertType {
    HighTemperature,
    LowTemperature,
    SensorError,
    LowBattery,
}

/// 系统状态
#[derive(Clone, Copy, Debug)]
struct SystemStatus {
    uptime_seconds: u32,
    sample_count: u32,
    tx_success_count: u32,
    tx_failure_count: u32,
    last_temperature: f32,
    battery_percentage: u8,
}

/// MQTT消息格式
#[derive(Serialize)]
struct MqttPayload<'a> {
    device_id: &'a str,
    timestamp: u64,
    temperature: f32,
    humidity: Option<f32>,
    battery: u16,
    status: &'a str,
}

// ==================== 全局状态 ====================

static SENSOR_CHANNEL: Channel<ThreadModeRawMutex, SensorReading, 8> = Channel::new();
static ALERT_CHANNEL: Channel<ThreadModeRawMutex, AlertType, 4> = Channel::new();
static STATUS_CHANNEL: Channel<ThreadModeRawMutex, SystemStatus, 2> = Channel::new();

// ==================== 硬件驱动 ====================

/// TMP117温度传感器驱动
struct Tmp117<I2C> {
    i2c: I2C,
    address: u8,
}

impl<I2C> Tmp117<I2C>
where
    I2C: embedded_hal::i2c::I2c,
{
    const REG_TEMP: u8 = 0x00;
    const REG_CONFIG: u8 = 0x01;
    const REG_DEVICE_ID: u8 = 0x0F;

    const DEVICE_ID: u16 = 0x0117;

    pub fn new(i2c: I2C, address: u8) -> Self {
        Self { i2c, address }
    }

    /// 初始化传感器
    pub async fn init(&mut self) -> Result<(), SensorError> {
        // 验证设备ID
        let id = self.read_register(Self::REG_DEVICE_ID)?;
        if id != Self::DEVICE_ID {
            return Err(SensorError::InvalidDevice);
        }

        // 配置：连续转换模式，1秒转换周期
        self.write_register(Self::REG_CONFIG, 0x02)?;

        // 等待首次转换完成
        Timer::after(Duration::from_millis(16)).await;

        Ok(())
    }

    /// 读取温度（摄氏度）
    pub fn read_temperature(&mut self) -> Result<f32, SensorError> {
        let raw = self.read_register(Self::REG_TEMP)? as i16;
        // TMP117: 1 LSB = 0.0078125°C
        Ok(raw as f32 * 0.0078125)
    }

    fn read_register(&mut self, reg: u8) -> Result<u16, SensorError> {
        let mut buf = [0u8; 2];
        self.i2c.write_read(self.address, &[reg], &mut buf)
            .map_err(|_| SensorError::I2cError)?;
        Ok(u16::from_be_bytes(buf))
    }

    fn write_register(&mut self, reg: u8, value: u16) -> Result<(), SensorError> {
        let buf = [reg, (value >> 8) as u8, value as u8];
        self.i2c.write(self.address, &buf)
            .map_err(|_| SensorError::I2cError)
    }
}

/// 电池监控
struct BatteryMonitor<ADC> {
    adc: ADC,
    vref_channel: u8,
    vbat_channel: u8,
}

impl<ADC> BatteryMonitor<ADC>
where
    ADC: embassy_stm32::adc::AdcTrait,
{
    pub fn new(adc: ADC, vref_ch: u8, vbat_ch: u8) -> Self {
        Self {
            adc,
            vref_channel: vref_ch,
            vbat_channel: vbat_ch,
        }
    }

    /// 读取电池电压（毫伏）
    pub async fn read_voltage(&mut self) -> u16 {
        // 读取内部参考电压
        let vref_sample = self.adc.read(&mut self.get_vref_pin()).await;

        // 读取电池分压
        let vbat_sample = self.adc.read(&mut self.get_vbat_pin()).await;

        // 计算实际电压
        // Vref = 1.2V，根据数据手册计算
        let vref_cal: u16 = unsafe { core::ptr::read(0x1FFF7A2A as *const u16) };
        let vdda_mv = (3000u32 * vref_cal as u32 / vref_sample as u32) as u16;
        let vbat_mv = (vdda_mv as u32 * vbat_sample as u32 / 4095) as u16 * 2; // 考虑分压比

        vbat_mv as u16
    }

    /// 计算电池百分比
    pub fn calculate_percentage(&self, voltage_mv: u16) -> u8 {
        // 锂电池放电曲线简化计算
        // 满电4.2V = 4200mV，空电3.0V = 3000mV
        match voltage_mv {
            v if v >= 4200 => 100,
            v if v <= 3000 => 0,
            v => ((v - 3000) / 12) as u8,
        }
    }
}

// ==================== 任务实现 ====================

/// 传感器采集任务
#[embassy_executor::task]
async fn sensor_task(
    mut tmp117: Tmp117<embassy_stm32::i2c::I2c<'static>>,
    mut battery_monitor: BatteryMonitor<Adc<'static>>,
    mut status_led: Output<'static>,
) {
    let mut ticker = Ticker::every(Duration::from_millis(SAMPLE_INTERVAL_MS));
    let mut sample_count: u32 = 0;

    // 初始化传感器
    if let Err(e) = tmp117.init().await {
        defmt::error!("TMP117 init failed: {:?}", e);
        // 进入错误状态：快速闪烁LED
        loop {
            status_led.set_high();
            Timer::after(Duration::from_millis(100)).await;
            status_led.set_low();
            Timer::after(Duration::from_millis(100)).await;
        }
    }

    defmt::info!("Sensor task started");

    loop {
        // LED指示采样中
        status_led.set_high();

        let timestamp = Instant::now().as_millis();

        // 读取温度
        let temperature = match tmp117.read_temperature() {
            Ok(temp) => {
                defmt::info!("Temperature: {}°C", temp);
                temp
            }
            Err(e) => {
                defmt::error!("Temperature read failed: {:?}", e);
                ALERT_CHANNEL.send(AlertType::SensorError).await;
                continue;
            }
        };

        // 检查告警阈值
        if temperature > TEMP_HIGH_THRESHOLD {
            defmt::warn!("High temperature alert: {}°C", temperature);
            ALERT_CHANNEL.send(AlertType::HighTemperature).await;
        } else if temperature < TEMP_LOW_THRESHOLD {
            defmt::warn!("Low temperature alert: {}°C", temperature);
            ALERT_CHANNEL.send(AlertType::LowTemperature).await;
        }

        // 读取电池电压
        let battery_mv = battery_monitor.read_voltage().await;
        let battery_pct = battery_monitor.calculate_percentage(battery_mv);
        defmt::info!("Battery: {}mV ({}%)", battery_mv, battery_pct);

        if battery_pct < 20 {
            ALERT_CHANNEL.send(AlertType::LowBattery).await;
        }

        // 构建读数结构
        let reading = SensorReading {
            timestamp,
            temperature,
            humidity: None, // TMP117无湿度功能
            battery_mv,
        };

        // 发送到处理通道
        SENSOR_CHANNEL.send(reading).await;

        sample_count += 1;

        // LED熄灭
        status_led.set_low();

        // 等待下一个采样周期
        ticker.next().await;
    }
}

/// 数据处理与传输任务
#[embassy_executor::task]
async fn transmission_task() {
    let mut buffer: Vec<SensorReading, 6> = Vec::new();
    let mut last_tx = Instant::now();

    loop {
        // 等待数据或超时
        let timeout = Timer::after(Duration::from_millis(TRANSMISSION_INTERVAL_MS));

        match embassy_futures::select::select(
            SENSOR_CHANNEL.receive(),
            timeout
        ).await {
            // 接收到新数据
            embassy_futures::select::Either::First(reading) => {
                if buffer.push(reading).is_err() {
                    defmt::warn!("Buffer full, dropping oldest sample");
                    buffer.remove(0);
                    let _ = buffer.push(reading);
                }
            }
            // 传输间隔到达
            embassy_futures::select::Either::Second(_) => {}
        }

        // 检查是否需要传输
        let should_transmit = buffer.len() >= 6 ||
            (Instant::now() - last_tx).as_millis() >= TRANSMISSION_INTERVAL_MS as u64;

        if should_transmit && !buffer.is_empty() {
            // 计算平均值
            let avg_temp = buffer.iter().map(|r| r.temperature).sum::<f32>() / buffer.len() as f32;
            let avg_batt = buffer.iter().map(|r| r.battery_mv).sum::<u16>() / buffer.len() as u16;
            let last_ts = buffer.last().unwrap().timestamp;

            // 构建JSON负载
            let payload = MqttPayload {
                device_id: DEVICE_ID,
                timestamp: last_ts,
                temperature: avg_temp,
                humidity: None,
                battery: avg_batt,
                status: "ok",
            };

            // 序列化
            let mut json_buf = [0u8; 256];
            let json_str = serde_json_core::to_slice(&payload, &mut json_buf)
                .map(|len| core::str::from_utf8(&json_buf[..len]).unwrap())
                .unwrap_or("{}");

            defmt::info!("Transmitting: {}", json_str);

            // 尝试发送（简化实现）
            match transmit_data(json_str).await {
                Ok(_) => {
                    defmt::info!("Transmission successful");
                    buffer.clear();
                    last_tx = Instant::now();
                }
                Err(e) => {
                    defmt::error!("Transmission failed: {:?}", e);
                    // 保留数据，下次重试
                }
            }
        }
    }
}

/// 告警处理任务
#[embassy_executor::task]
async fn alert_task(mut buzzer: Output<'static>) {
    loop {
        let alert = ALERT_CHANNEL.receive().await;

        defmt::warn!("Alert received: {:?}", alert);

        match alert {
            AlertType::HighTemperature | AlertType::LowTemperature => {
                // 温度告警：长鸣3声
                for _ in 0..3 {
                    buzzer.set_high();
                    Timer::after(Duration::from_millis(500)).await;
                    buzzer.set_low();
                    Timer::after(Duration::from_millis(200)).await;
                }
            }
            AlertType::LowBattery => {
                // 低电量：短鸣5声
                for _ in 0..5 {
                    buzzer.set_high();
                    Timer::after(Duration::from_millis(200)).await;
                    buzzer.set_low();
                    Timer::after(Duration::from_millis(100)).await;
                }
            }
            AlertType::SensorError => {
                // 传感器错误：持续鸣叫
                buzzer.set_high();
                Timer::after(Duration::from_secs(2)).await;
                buzzer.set_low();
            }
        }

        // 立即触发传输
        // 实现略...
    }
}

/// 低功耗管理任务
#[embassy_executor::task]
async fn power_management_task() {
    let sleep_manager = SleepManager::new(10000, 60000);
    let mut last_state = DeviceState::Active;

    loop {
        let current_state = sleep_manager.update_state();

        if current_state != last_state {
            defmt::info!("Power state changed: {:?} -> {:?}", last_state, current_state);
            last_state = current_state;
        }

        match current_state {
            DeviceState::Active => {
                // 正常运行
                Timer::after(Duration::from_secs(1)).await;
            }
            DeviceState::Idle => {
                // 降低时钟，短暂休眠
                Timer::after(Duration::from_millis(100)).await;
            }
            DeviceState::Sleep | DeviceState::DeepSleep => {
                // 进入低功耗模式
                // 注意：实际实现需要硬件支持
                cortex_m::asm::wfi();
            }
        }
    }
}

/// 数据传输函数（模拟）
async fn transmit_data(data: &str) -> Result<(), TransmitError> {
    // 实际实现中会使用MQTT/CoAP/LoRaWAN客户端
    // 这里仅作模拟

    // 模拟网络延迟
    Timer::after(Duration::from_millis(500)).await;

    // 随机成功率模拟（实际应为实际网络操作结果）
    if embassy_time::Instant::now().as_ticks() % 10 < 8 {
        Ok(())
    } else {
        Err(TransmitError::NetworkError)
    }
}

// ==================== 错误类型 ====================

#[derive(Debug)]
enum SensorError {
    I2cError,
    InvalidDevice,
    Timeout,
}

#[derive(Debug)]
enum TransmitError {
    NetworkError,
    Timeout,
    BufferFull,
}

// ==================== 主函数 ====================

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    defmt::info!("Temperature Sensor System Starting...");

    // 初始化硬件
    let p = embassy_stm32::init(Default::default());

    // 配置时钟
    let mut rcc = p.RCC.constrain();
    let clocks = rcc.cfgr.freeze();

    // 配置I2C
    let scl = p.PB6;
    let sda = p.PB7;
    let i2c = I2c::new(
        p.I2C1,
        scl,
        sda,
        Hertz(100_000),
        &clocks,
    );

    // 初始化TMP117
    let tmp117 = Tmp117::new(i2c, 0x48); // TMP117默认地址

    // 配置ADC
    let adc = Adc::new(p.ADC1);
    let battery_monitor = BatteryMonitor::new(adc, 17, 18);

    // 配置LED和蜂鸣器
    let status_led = Output::new(p.PA5, Level::Low, Speed::Low);
    let buzzer = Output::new(p.PA8, Level::Low, Speed::Low);

    // 启动任务
    spawner.spawn(sensor_task(tmp117, battery_monitor, status_led)).unwrap();
    spawner.spawn(transmission_task()).unwrap();
    spawner.spawn(alert_task(buzzer)).unwrap();
    spawner.spawn(power_management_task()).unwrap();

    defmt::info!("All tasks spawned, entering main loop");

    // 主循环：状态监控
    let mut ticker = Ticker::every(Duration::from_secs(60));
    loop {
        let status = SystemStatus {
            uptime_seconds: (Instant::now().as_millis() / 1000) as u32,
            sample_count: 0, // 需要从各任务共享
            tx_success_count: 0,
            tx_failure_count: 0,
            last_temperature: 0.0,
            battery_percentage: 0,
        };

        STATUS_CHANNEL.send(status).await;
        ticker.next().await;
    }
}
```

---

## 十、调试技术

### 10.1 RTT (Real-Time Transfer)

```rust
use rtt_target::{rtt_init_print, rprintln, rdbg};

fn init_rtt() {
    rtt_init_print!();
}

fn log_examples() {
    // 基本日志
    rprintln!("System started");

    // 格式化输出
    let temp = 25.5;
    let count = 42;
    rprintln!("Temperature: {}°C, Count: {}", temp, count);

    // 调试输出
    let data = [1, 2, 3, 4, 5];
    rdbg!(data);

    // 日志级别（配合defmt）
    defmt::info!("Info message");
    defmt::warn!("Warning: value is {}", temp);
    defmt::error!("Error occurred at {}", count);
    defmt::debug!("Debug: {:?}", data);

    // 断言
    defmt::assert!(temp > 0.0, "Temperature should be positive");
}
```

### 10.2 ITM (Instrumentation Trace Macrocell)

```rust
use cortex_m::{iprintln, ITM};
use cortex_m::peripheral::ITM as ITM_Periph;

/// ITM日志宏
#[macro_export]
macro_rules! itm_print {
    ($itm:expr, $($arg:tt)*) => {
        iprintln!($itm, $($arg)*);
    };
}

/// ITM使用示例
fn itm_logging(itm: &mut ITM_Periph) {
    iprintln!(itm.stim[0], "Hello from ITM!");

    // 性能计时
    let start = cortex_m::peripheral::DWT::get_cycle_count();

    // 执行某些操作
    perform_operation();

    let end = cortex_m::peripheral::DWT::get_cycle_count();
    let cycles = end.wrapping_sub(start);
    iprintln!(itm.stim[0], "Operation took {} cycles", cycles);
}

/// ITM配置
fn configure_itm() {
    let mut cp = cortex_m::Peripherals::take().unwrap();

    // 启用DWT周期计数器
    cp.DWT.enable_cycle_counter();

    // 配置ITM
    unsafe {
        // 解锁ITM
        cp.ITM.lar.write(0xC5ACCE55);

        // 启用ITM
        cp.ITM.ter[0].write(1);  // 启用端口0
        cp.ITM.tcr.write(1);     // 使能ITM
    }
}
```

### 10.3 日志系统

```rust
use heapless::spsc::Queue;
use core::fmt::Write;

/// 日志级别
#[derive(Clone, Copy, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum LogLevel {
    Trace = 0,
    Debug = 1,
    Info = 2,
    Warn = 3,
    Error = 4,
    Fatal = 5,
    Off = 6,
}

/// 日志条目
pub struct LogEntry {
    pub timestamp: u64,
    pub level: LogLevel,
    pub module: &'static str,
    pub message: heapless::String<128>,
}

/// 嵌入式日志器
pub struct EmbeddedLogger<const N: usize> {
    queue: Queue<LogEntry, N>,
    min_level: LogLevel,
    rtt_enabled: bool,
    flash_enabled: bool,
}

impl<const N: usize> EmbeddedLogger<N> {
    pub const fn new(min_level: LogLevel) -> Self {
        Self {
            queue: Queue::new(),
            min_level,
            rtt_enabled: false,
            flash_enabled: false,
        }
    }

    /// 记录日志
    pub fn log(
        &mut self,
        level: LogLevel,
        module: &'static str,
        args: core::fmt::Arguments,
    ) {
        if level < self.min_level {
            return;
        }

        let timestamp = get_monotonic_ms();
        let mut message = heapless::String::<128>::new();
        let _ = message.write_fmt(args);

        let entry = LogEntry {
            timestamp,
            level,
            module,
            message,
        };

        // 存入队列
        if self.queue.enqueue(entry).is_err() {
            // 队列满，移除最旧的
            let _ = self.queue.dequeue();
            let _ = self.queue.enqueue(entry);
        }

        // RTT实时输出
        if self.rtt_enabled {
            self.output_rtt(&entry);
        }
    }

    /// 刷新日志到持久存储
    pub fn flush(&mut self) {
        if !self.flash_enabled {
            return;
        }

        while let Some(entry) = self.queue.dequeue() {
            self.write_to_flash(&entry);
        }
    }

    fn output_rtt(&self, entry: &LogEntry) {
        rprintln!(
            "[{}] [{}] {}: {}",
            entry.timestamp,
            level_str(entry.level),
            entry.module,
            entry.message
        );
    }

    fn write_to_flash(&self, entry: &LogEntry) {
        // 将日志写入外部Flash
        // 实现略...
    }
}

fn level_str(level: LogLevel) -> &'static str {
    match level {
        LogLevel::Trace => "TRACE",
        LogLevel::Debug => "DEBUG",
        LogLevel::Info => "INFO",
        LogLevel::Warn => "WARN",
        LogLevel::Error => "ERROR",
        LogLevel::Fatal => "FATAL",
        LogLevel::Off => "OFF",
    }
}

// 日志宏定义
#[macro_export]
macro_rules! log_info {
    ($logger:expr, $($arg:tt)*) => {
        $logger.log($crate::LogLevel::Info, module_path!(), format_args!($($arg)*))
    };
}

#[macro_export]
macro_rules! log_error {
    ($logger:expr, $($arg:tt)*) => {
        $logger.log($crate::LogLevel::Error, module_path!(), format_args!($($arg)*))
    };
}
```

### 10.4 调试配置总结

| 调试方法 | 适用场景 | 优点 | 缺点 |
|---------|---------|------|------|
| RTT | 开发阶段 | 零开销，实时，双向通信 | 需要SWD连接 |
| ITM | 性能分析 | 时间戳精确，SWO输出 | 需要SWO引脚 |
| 串口UART | 现场调试 | 无需调试器 | 占用UART资源 |
| 内部日志 | 故障排查 | 脱机记录 | 需要存储空间 |
| LED指示 | 简单状态 | 无需额外硬件 | 信息有限 |

---

## 附录

### 常用嵌入式Rust Crate

| Crate | 用途 | 版本建议 |
|-------|------|---------|
| `cortex-m` | Cortex-M核心支持 | ^0.7 |
| `cortex-m-rt` | 运行时和启动 | ^0.7 |
| `embedded-hal` | 硬件抽象接口 | ^1.0 |
| `embedded-io` | I/O trait | ^0.6 |
| `heapless` | 无堆数据结构 | ^0.8 |
| `embassy` | 异步运行时 | git |
| `rtic` | 实时中断并发 | ^2.0 |
| `defmt` | 结构化日志 | ^0.3 |
| `panic-probe` | 调试panic处理 | ^0.3 |
| `serde` | 序列化 | 默认禁用std |

### 资源链接

- [Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [Embassy Framework](https://embassy.dev/)
- [RTIC Documentation](https://rtic-rs.github.io/rtic/)
- [Probe-rs](https://probe.rs/)
- [awesome-embedded-rust](https://github.com/rust-embedded/awesome-embedded-rust)

---

*文档版本: 1.0*
*最后更新: 2026年3月*
*适用Rust版本: 1.75+*
