//! Embassy 异步嵌入式框架 —— Async/Await on Bare Metal
//! # 概述
//! #
//! 允许在 **bare-metal** 环境中使用 `async`/`await` 编写固件。
//! allow in **bare-metal** environment in `async`/`await` firmware 。
//! in **bare-metal** environment in `async`/`await` firmware 。
//! # 核心特性
//! # core feature
//! | 特性 | 说明 |
//! | feature | explain |
//! | **Async Executor** | 单线程协作式调度器，零开销抽象 |
//! | **Async Executor** | thread ，overhead |
//! | **HAL 抽象** | 跨芯片的统一异步外设接口 |
//! | **HAL ** | async outside |
//! | **Stable Rust** | MSRV 1.75，无需 nightly |
//! # 架构对比
//! # architecture to
//! | 模式 | 代码风格 | 调度方式 | 适用场景 |
//! | | | way | scenario |
//! | 裸机轮询 | 超级循环 + 状态机 | 手动 | 极简设备 |
//! | poll | circulation + state machine | | |
//! | | circulation + state machine | | |
//! | 裸机Poll | 超级circulation + state machine | 手动 | 极简设备 |
//! | RTIC | 基于硬件任务 | 优先级抢占 | 硬实时 |
//! | RTIC | hardware task | | |
//! | RTIC | Based onhardwaretask | 优先级抢占 | 硬实时 |
//! | **Embassy** | `async`/`await` | 协作式 + 中断唤醒 | 复杂协议栈 |
//! | **Embassy** | `async`/`await` | + in | complex stack |
//! # 参考
//! # reference
//! - [ embassy-rs GitHub](https://github.com/embassy-rs/embassy)

// =========================================================================
// 1. Embassy 核心概念（Host 模拟）
// =========================================================================

/// # Embassy Executor
///
/// 所有 `async` 任务共享一个调用栈，通过 `Waker` 机制在中断事件发生时恢复执行。
/// all `async` task stack ， `Waker` mechanism in in event 。
/// all `async` task stack ， `Waker` mechanism in in 。
/// ## and Tokio 差异
// | 维度 | Tokio (用户态) | Embassy (裸机) |
// |------|---------------|---------------|
// | 线程模型 | 多线程线程池 | 单线程 + 中断 |
// | 栈分配 | 每个任务独立栈 | 共享调用栈 |
// | 唤醒机制 | OS 线程调度 | 中断 + Waker |
// | 内存分配 | 堆分配（Box） | 静态分配（推荐） |
// | 阻塞操作 | 线程阻塞 | 禁止阻塞（编译错误） |
// | 标准库 | full std | no_std + alloc |
pub struct EmbassyExecutorConcept;

impl EmbassyExecutorConcept {
    /// Executor 初始化概念（真实硬件代码）
    /// Executor concept （real hardware ）
    pub fn executor_init_concept() -> &'static str {
        r#"
// main.rs (真实 Embassy 程序)
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};
use {panic_halt as _, defmt_rtt as _};

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // 初始化硬件外设
    let p = embassy_stm32::init(Default::default());

    // 启动异步任务
    spawner.spawn(blink_task(p.PB0)).unwrap();
    spawner.spawn(sensor_task(p.ADC1)).unwrap();

    // Executor 自动运行，主函数在此挂起
}

#[embassy_executor::task]
async fn blink_task(pin: AnyPin) {
    let mut led = Output::new(pin, Level::Low, Speed::Low);
    loop {
        led.toggle();
        Timer::after(Duration::from_millis(500)).await;
    }
}

#[embassy_executor::task]
async fn sensor_task(adc: ADC) {
    let mut adc = Adc::new(adc);
    loop {
        let value = adc.read(&mut adc_pin).await;
        defmt::info!("ADC: {}", value);
        Timer::after(Duration::from_secs(1)).await;
    }
}
"#
    }

    /// 任务 spawning 概念
    /// task spawning concept
    pub fn task_spawning_concept() -> &'static str {
        r#"
Embassy 任务系统:

1. #[embassy_executor::task]
   - 标记函数为异步任务
   - 任务必须是 'static（或拥有所有数据）
   - 任务返回值被忽略

2. Spawner::spawn()
   - 将任务提交到 executor
   - 返回 SpawnError（如资源不足）
   - 任务立即开始执行（协作式）

3. 静态任务 vs 动态任务:
   - 静态: 编译期分配，无运行时分配开销
   - 动态: 使用 Box::new()，需要 alloc
"#
    }
}

// =========================================================================
// 2. 异步外设 HAL
// =========================================================================

/// # Embassy HAL 抽象
// - `embassy-stm32` — STM32 全系列
// - `embassy-nrf` — Nordic nRF52/nRF53/nRF91
// - `embassy-rp` — Raspberry Pi RP2040/RP2350
// - `embassy-esp` — Espressif ESP32
///
pub struct EmbassyHalConcept;

impl EmbassyHalConcept {
    /// GPIO 异步操作概念
    /// GPIO async operation concept
    /// GPIO async concept
    pub fn async_gpio_concept() -> &'static str {
        r#"
// 异步 GPIO (Embassy HAL)
use embassy_stm32::gpio::{Input, Output, Pull, Speed};

async fn button_wait_for_press(pin: AnyPin) {
    let mut button = Input::new(pin, Pull::Up);

    // 等待下降沿（硬件中断触发，非轮询）
    button.wait_for_falling_edge().await;
    defmt::info!("Button pressed!");
}

async fn pwm_breathe(pwm: SimplePwm<'static, TIM2>) {
    loop {
        for duty in 0..=100 {
            pwm.set_duty(duty);
            Timer::after(Duration::from_millis(10)).await;
        }
        for duty in (0..=100).rev() {
            pwm.set_duty(duty);
            Timer::after(Duration::from_millis(10)).await;
        }
    }
}
"#
    }

    /// 异步 UART 概念
    /// async UART concept
    pub fn async_uart_concept() -> &'static str {
        r#"
// 异步 UART (非阻塞 + 中断驱动)
use embassy_stm32::usart::{Uart, Config};

async fn uart_echo(uart: Uart<'static, USART1>) {
    let (mut tx, mut rx) = uart.split();
    let mut buf = [0u8; 64];

    loop {
        // read() 挂起直到 UART RX 中断到达
        let n = rx.read(&mut buf).await.unwrap();
        tx.write(&buf[..n]).await.unwrap();
    }
}
"#
    }

    /// 异步 SPI + DMA 概念
    /// async SPI + DMA concept
    pub fn async_spi_dma_concept() -> &'static str {
        r#"
// 异步 SPI + DMA (零 CPU 拷贝)
use embassy_stm32::spi::{Spi, Config};

async fn spi_transfer_dma(
    spi: Spi<'static, SPI1, DMA1_CH3, DMA1_CH2>,
    tx_buf: &[u8],
    rx_buf: &mut [u8],
) {
    // DMA 传输期间 CPU 可执行其他任务
    spi.transfer(rx_buf, tx_buf).await.unwrap();
}
"#
    }
}

// =========================================================================
// 3. 异步网络协议栈
// =========================================================================

/// # Embassy-Net — 裸机 TCP/IP 栈
/// # Embassy-Net — 裸机 TCP/IP stack
// Embassy 提供了完整的 `no_std` 网络协议栈：
// - `embassy-net` — TCP/IP 栈（基于 smoltcp）
// - `embassy-usb` — USB CDC-ECM/RNDIS 以太网
// - `cyw43` — WiFi (Raspberry Pi Pico W)
// - `esp-wifi` — WiFi (ESP32)
pub struct EmbassyNetConcept;

impl EmbassyNetConcept {
    /// TCP 客户端概念
    /// TCP concept
    /// TCP 客户端concept
    pub fn tcp_client_concept() -> &'static str {
        r#"
// Embassy TCP 客户端
use embassy_net::{Stack, tcp::TcpSocket};
use embedded_nal_async::{AddrType, Dns, TcpConnect};

async fn http_get(
    stack: &'static Stack<Device>,
    host: &str,
    path: &str,
) -> Result<Vec<u8>, Error> {
    // DNS 解析
    let addr = stack.dns_query(host, AddrType::Either).await?[0];

    // 建立 TCP 连接
    let mut socket = TcpSocket::new(stack, &mut rx_buffer, &mut tx_buffer);
    socket.connect((addr, 80)).await?;

    // 发送 HTTP 请求
    let request = format!("GET {} HTTP/1.0\r\nHost: {}\r\n\r\n", path, host);
    socket.write_all(request.as_bytes()).await?;

    // 读取响应
    let mut response = vec![];
    socket.read_to_end(&mut response).await?;
    Ok(response)
}
"#
    }

    /// HTTP 服务器概念 (embassy-net + picoserve)
    /// HTTP 服务器concept (embassy-net + picoserve)
    pub fn http_server_concept() -> &'static str {
        r#"
// 嵌入式 HTTP 服务器 (picoserve + embassy)
use picoserve::routing::get;

async fn web_server(stack: &'static Stack<Device>) {
    let mut rx_buffer = [0; 4096];
    let mut tx_buffer = [0; 4096];
    let mut buf = [0; 4096];

    let app = picoserve::Router::new()
        .route("/", get(|| async { "Hello from Embassy!" }))
        .route("/temperature", get(|| async {
            let temp = read_sensor().await;
            format!("Temperature: {:.1}C", temp)
        }));

    let config = picoserve::Config::new(picoserve::Timeouts {
        start_read_request: Some(Duration::from_secs(5)),
        read_request: Some(Duration::from_secs(1)),
        write: Some(Duration::from_secs(1)),
    });

    let mut socket = TcpSocket::new(stack, &mut rx_buffer, &mut tx_buffer);
    socket.bind(80).unwrap();

    loop {
        socket.accept().await.unwrap();
        picoserve::serve(&app, &config, &mut buf, &mut socket).await;
        socket.close();
    }
}
"#
    }
}

// =========================================================================
// 4. 时间管理
// =========================================================================

/// # Embassy Time
// Embassy 提供了 `no_std` 的时间抽象：
// - `Timer::after(duration)` — 异步延迟
// - `Ticker` — 周期性定时器
// - `Instant` — 时间点
// - `Duration` — 时间间隔
///
// 时间驱动由硬件定时器（如 SysTick 或 TIMx）提供。
pub struct EmbassyTimeConcept;

impl EmbassyTimeConcept {
    /// 定时器模式对比
    /// to
    pub fn timer_patterns() -> &'static str {
        r#"
// 1. 单次延迟
Timer::after(Duration::from_millis(100)).await;

// 2. 周期性任务 (Ticker)
let mut ticker = Ticker::every(Duration::from_secs(1));
loop {
    ticker.next().await;
    do_periodic_work().await;
}

// 3. 超时包装
match with_timeout(Duration::from_secs(5), async_operation()).await {
    Ok(result) => println!("成功: {:?}", result),
    Err(TimeoutError) => println!("超时!"),
}

// 4. 截止时间
let deadline = Instant::now() + Duration::from_millis(100);
Timer::at(deadline).await;
"#
    }

    /// and RTOS tick 差异
    pub fn vs_rtos_tick() -> &'static str {
        r#"
Embassy Time vs RTOS Tick:

| 特性 | FreeRTOS Tick | Embassy Time |
|------|--------------|-------------|
// | 粒度 | 固定 tick 周期 (1ms-10ms) | 微秒级硬件定时器 |
// | 精度 | 累积抖动 | 无累积误差 |
// | 功耗 | 周期性唤醒 | 可完全休眠至下次事件 |
// | 任务延迟 | vTaskDelay(ticks) | Timer::after(duration).await |
"#
    }
}

// =========================================================================
// 5. 与 RTIC 的对比
// =========================================================================

/// # Embassy vs RTIC
// 两个框架都用于嵌入式 Rust，但设计哲学不同。
pub struct EmbassyVsRtic;

impl EmbassyVsRtic {
    pub fn comparison() -> &'static str {
        r#"
Embassy vs RTIC 对比:

| 维度 | Embassy | RTIC |
|------|---------|------|
// | 并发模型 | 协作式 async/await | 抢占式硬件任务 |
// | 调度器 | 单线程 executor | 基于 NVIC 优先级 |
// | 上下文切换 | 函数调用（零开销） | 上下文保存/恢复 |
// | 实时保证 | 软实时（任务需 yield） | 硬实时（优先级抢占） |
// | 资源共享 | async Mutex | 基于优先级的临界区 |
// | 适用场景 | 协议栈、网络、复杂状态机 | 电机控制、传感器融合 |
// | 学习曲线 | 需理解 async Rust | 需理解硬件中断 |
// | 生态丰富度 | 高（USB/TCP/BLE） | 中（专注实时控制） |

选择建议:
- 需要网络/USB/复杂协议 → Embassy
- 需要硬实时/严格 deadlines → RTIC
- 两者可组合使用（Embassy 任务 + RTIC 硬件任务）
"#
    }
}

// =========================================================================
// 6. 项目集成检查清单
// =========================================================================

/// 当需要添加真实硬件示例时，按此清单执行。
/// when real hardware example ，this 。
pub struct EmbassyIntegrationChecklist;

impl EmbassyIntegrationChecklist {
    pub fn checklist() -> Vec<(&'static str, &'static str)> {
        vec![
            ("[ ] 添加 embassy-executor 依赖", "Cargo.toml"),
            ("[ ] 添加芯片特定 HAL (embassy-stm32/nrf/rp)", "Cargo.toml"),
            ("[ ] 配置 linker script (memory.x)", "项目根目录"),
            ("[ ] 添加 panic handler (panic-halt/panic-probe)", "main.rs"),
            ("[ ] 配置 .cargo/config.toml 目标", "嵌入式目标"),
            ("[ ] 实现 #[embassy_executor::main]", "main.rs"),
            ("[ ] 定义硬件任务并 spawn", "main.rs / tasks.rs"),
            ("[ ] 配置 probe-run / probe-rs 调试", ".cargo/config.toml"),
        ]
    }
}

// =========================================================================
// 2. Embassy 任务与通信模式
// =========================================================================

/// # Embassy 任务模型
/// # Embassy task
/// Embassy 使用 `#[embassy_executor::task]` 属性定义异步任务：
/// #[embassy_executor::task]
/// async fn blink_led(mut led: Output<'static, PIN>) {
///     loop {
///         led.set_high();
///         Timer::after(Duration::from_millis(300)).await;
///         led.set_low();
///         Timer::after(Duration::from_millis(300)).await;
///     }
/// `
pub struct EmbassyTaskModel;

impl EmbassyTaskModel {
    /// 任务创建概念说明
    /// task concept explain
    pub fn task_spawn_concept() -> &'static str {
        r#"
// main.rs
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // 创建硬件外设实例
    let p = embassy_stm32::init(Default::default());
    
    // 启动多个并发任务
    spawner.spawn(blink_led(Output::new(p.PA5, Level::Low, Speed::Low))).unwrap();
    spawner.spawn(read_sensor(Adc::new(p.ADC1))).unwrap();
    spawner.spawn(network_task(p.ETH)).unwrap();
    
    // main 函数本身也可以执行异步操作
    loop {
        Timer::after(Duration::from_secs(1)).await;
        defmt::info!("heartbeat");
    }
}
"#
    }

    /// 任务间通信：Channel
    /// task ：Channel
    pub fn channel_concept() -> &'static str {
        r#"
// 静态 Channel（无堆分配）
use embassy_sync::channel::Channel;
use embassy_sync::blocking_mutex::raw::ThreadModeRawMutex;

static SENSOR_CHANNEL: Channel<ThreadModeRawMutex, SensorData, 3> = Channel::new();

#[embassy_executor::task]
async fn sensor_task() {
    loop {
        let data = read_sensor().await;
        SENSOR_CHANNEL.send(data).await;
    }
}

#[embassy_executor::task]
async fn processing_task() {
    loop {
        let data = SENSOR_CHANNEL.receive().await;
        process(data).await;
    }
}
"#
    }

    /// Embassy and RTIC to比决策
    pub fn embassy_vs_rtic() -> &'static str {
        r#"
Embassy vs RTIC 决策树：

1. 是否需要硬实时保证（确定性延迟）？
   ├── 是（< 10us 抖动要求）→ RTIC
   └── 否 → 继续 2

2. 是否需要复杂协议栈（TCP/IP, USB, BLE）？
   ├── 是 → Embassy（成熟的异步协议实现）
   └── 否 → 继续 3

3. 团队 Rust 异步经验？
   ├── 丰富 → Embassy（async/await 更自然）
   └── 有限 → RTIC（基于硬件任务，概念更简单）

4. 内存预算？
   ├── < 16KB RAM → 裸机轮询或 RTIC
   ├── 16-64KB RAM → RTIC 或 Embassy
   └── > 64KB RAM → Embassy（协议栈需要更多内存）
"#
    }
}

// =========================================================================
// 3. Embassy 网络协议栈概览
// =========================================================================

/// # Embassy 网络生态
/// # Embassy network ecosystem
/// | 协议层 | Crate | 说明 |
/// | | Crate | explain |
/// | 协议层 | Crate | explain |
/// | DHCP | embassy-net | 内置 DHCP 客户端 |
/// | DNS | embassy-net | 内置 DNS 解析 |
/// | HTTP | reqwless | 嵌入式 HTTP 客户端 |
/// | MQTT | rust-mqtt | 异步 MQTT 客户端 |
/// | MQTT | rust-mqtt | async MQTT 客户端 |
/// | BLE | nrf-softdevice / trouble | 蓝牙低功耗 |
pub struct EmbassyNetworking;

impl EmbassyNetworking {
    pub fn available_crates() -> &'static [(&'static str, &'static str)] {
        &[
            ("embassy-net", "异步 TCP/IP 协议栈"),
            ("embassy-usb", "USB 设备协议栈"),
            ("embassy-boot", "安全引导加载程序"),
            ("reqwless", "嵌入式 HTTP 客户端"),
            ("trouble-host", "BLE 主机栈"),
        ]
    }
}
