# Embassy框架完整指南

> 嵌入式Rust的异步革命

---

## 1. Embassy架构

```text
┌─────────────────────────────────────────────────────────────────┐
│                      应用代码层                                  │
│  #[embassy_executor::main]                                      │
│  async fn main(spawner: Spawner) {                              │
│      spawner.spawn(blink_task(p.PB0)).unwrap();                 │
│      spawner.spawn(sensor_task(i2c)).unwrap();                  │
│  }                                                              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Embassy Executor                              │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                  任务调度器                               │   │
│  │  - 单线程或多线程 (取决于平台)                            │   │
│  │  - 协作式调度                                            │   │
│  │  - 零开销任务创建                                        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                  时间驱动                                │   │
│  │  - TimerQueue                                            │   │
│  │  - Alarm (硬件定时器)                                    │   │
│  │  - Tickless idle                                         │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              │                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                  中断集成                                │   │
│  │  - InterruptHandler → Waker                              │   │
│  │  - 中断安全队列                                          │   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   硬件抽象层 (HAL)                               │
│  embassy-stm32 / embassy-nrf / embassy-rp                      │
│  ├── GPIO (async中断驱动)                                       │
│  ├── UART/USART (DMA + 中断)                                    │
│  ├── I2C/SPI (async传输)                                        │
│  ├── ADC (async采样)                                            │
│  └── USB (async端点)                                            │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      硬件层                                      │
│                 Cortex-M / RISC-V                                │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 核心概念

### 2.1 任务 (Tasks)

```rust
use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};
use embassy_stm32::gpio::{Level, Output, Speed};

// 任务定义
#[embassy_executor::task]
async fn blink_task(mut led: Output<'static>) {
    loop {
        led.set_high();
        Timer::after(Duration::from_millis(300)).await;

        led.set_low();
        Timer::after(Duration::from_millis(300)).await;
    }
}

#[embassy_executor::task]
async fn sensor_task(mut i2c: I2c<'static>) {
    loop {
        // 异步读取传感器
        let data = read_sensor(&mut i2c).await;
        process_data(data).await;

        Timer::after(Duration::from_secs(1)).await;
    }
}

// 主函数
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // 初始化硬件
    let p = embassy_stm32::init(Default::default());

    // 配置LED
    let led = Output::new(p.PB0, Level::Low, Speed::Low);

    // 配置I2C
    let i2c = I2c::new(
        p.I2C1,
        p.PB8,
        p.PB9,
        Irqs,
        p.DMA1_CH6,
        p.DMA1_CH7,
        Hertz(100_000),
        Default::default(),
    );

    // 启动任务
    spawner.spawn(blink_task(led)).unwrap();
    spawner.spawn(sensor_task(i2c)).unwrap();
}
```

### 2.2 时间管理

```rust
use embassy_time::{Duration, Instant, Timer};

// 延迟
async fn delay_example() {
    // 相对延迟
    Timer::after(Duration::from_millis(100)).await;

    // 绝对时间
    let deadline = Instant::now() + Duration::from_secs(1);
    Timer::at(deadline).await;

    // 周期性
    let mut ticker = embassy_time::Ticker::every(Duration::from_secs(1));
    loop {
        ticker.next().await;
        // 每秒执行
    }
}

// Timeout
use embassy_futures::select::{select, Either};

async fn with_timeout<T>(
    operation: impl Future<Output = T>,
    timeout: Duration,
) -> Option<T> {
    match select(operation, Timer::after(timeout)).await {
        Either::First(result) => Some(result),
        Either::Second(_) => None,
    }
}
```

### 2.3 中断处理

```rust
use embassy_stm32::exti::ExtiInput;
use embassy_stm32::gpio::Pull;

// 外部中断驱动的按钮
#[embassy_executor::task]
async fn button_task(mut button: ExtiInput<'static>) {
    loop {
        // 等待下降沿 (按下)
        button.wait_for_falling_edge().await;
        println!("Button pressed!");

        // 消抖
        Timer::after(Duration::from_millis(50)).await;

        // 等待上升沿 (释放)
        button.wait_for_rising_edge().await;
        println!("Button released!");
    }
}

// 在main中配置
let button = ExtiInput::new(
    Input::new(p.PA0, Pull::Up),
    p.EXTI0,
);
spawner.spawn(button_task(button)).unwrap();
```

---

## 3. 异步外设使用

### 3.1 UART with DMA

```rust
use embassy_stm32::usart::{Uart, Config};
use embassy_stm32::dma::NoDma;

#[embassy_executor::task]
async fn uart_task(mut uart: Uart<'static, DMA1_CH1, DMA1_CH2>) {
    let mut buf = [0u8; 128];

    loop {
        // 异步接收
        let n = uart.read(&mut buf).await.unwrap();

        // 处理数据
        let response = process(&buf[..n]);

        // 异步发送
        uart.write(response).await.unwrap();
    }
}

// 配置
let uart = Uart::new(
    p.USART1,
    p.PA10,  // RX
    p.PA9,   // TX
    Irqs,
    p.DMA1_CH1,  // RX DMA
    p.DMA1_CH2,  // TX DMA
    Config::default(),
);
```

### 3.2 I2C异步传输

```rust
use embassy_stm32::i2c::I2c;

// 异步传感器读取
async fn read_sensor(i2c: &mut I2c<'static>) -> Result<SensorData, Error> {
    let mut buf = [0u8; 6];

    // 写寄存器地址
    i2c.write(SENSOR_ADDR, &[0x01]).await?;

    // 读数据
    i2c.read(SENSOR_ADDR, &mut buf).await?;

    Ok(SensorData::from_bytes(&buf))
}

// 并发读取多个传感器
async fn read_all_sensors(i2c: &mut I2c<'static>) -> [SensorData; 3] {
    // 注意: I2C是独占资源，需要顺序访问
    // 使用join!并发其他不冲突的操作
    let mut results = [SensorData::default(); 3];

    for (i, addr) in [0x48, 0x49, 0x4A].iter().enumerate() {
        results[i] = read_sensor_at(i2c, *addr).await;
    }

    results
}
```

### 3.3 SPI异步传输

```rust
use embassy_stm32::spi::Spi;
use embassy_stm32::gpio::Output;

struct SpiDevice<'a> {
    spi: Spi<'static>,
    cs: Output<'a>,
}

impl<'a> SpiDevice<'a> {
    async fn transfer(&mut self, data: &[u8], rx: &mut [u8]) -> Result<(), Error> {
        self.cs.set_low();
        let result = self.spi.transfer(data, rx).await;
        self.cs.set_high();
        result
    }
}
```

---

## 4. 无堆设计 (Heapless)

### 4.1 静态任务分配

```rust
// Embassy默认不使用堆分配
// 所有任务在编译时确定

// 使用embassy-executor的静态配置
use embassy_executor::Executor;
use static_cell::StaticCell;

// 静态执行器
static EXECUTOR: StaticCell<Executor> = StaticCell::new();

#[cortex_m_rt::entry]
fn main() -> ! {
    let executor = EXECUTOR.init(Executor::new());

    executor.run(|spawner| {
        spawner.spawn(task1()).unwrap();
        spawner.spawn(task2()).unwrap();
    });
}
```

### 4.2 无堆数据结构

```rust
use heapless::Vec;
use heapless::spsc::Queue;

// 固定容量的队列
static QUEUE: Mutex<RefCell<Queue<Data, 16>>> =
    Mutex::new(RefCell::new(Queue::new()));

#[embassy_executor::task]
async fn producer() {
    loop {
        let data = produce().await;

        critical_section::with(|cs| {
            let mut queue = QUEUE.borrow_ref_mut(cs);
            queue.enqueue(data).ok(); // 可能失败（满）
        });
    }
}

#[embassy_executor::task]
async fn consumer() {
    loop {
        let data = critical_section::with(|cs| {
            QUEUE.borrow_ref_mut(cs).dequeue()
        });

        if let Some(d) = data {
            consume(d).await;
        } else {
            // 队列为空，等待
            Timer::after(Duration::from_millis(10)).await;
        }
    }
}
```

---

## 5. 电源管理

### 5.1 Tickless Idle

```rust
// Embassy自动管理tickless idle
// 当没有任务就绪时，进入WFI/低功耗模式

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // 配置低功耗
    let mut config = embassy_stm32::Config::default();
    config.rcc.enable_lsi = true;

    let p = embassy_stm32::init(config);

    // 启用RTC作为低功耗时钟源
    spawner.spawn(low_power_task()).unwrap();
}

#[embassy_executor::task]
async fn low_power_task() {
    loop {
        // 执行工作
        do_work().await;

        // 长时间休眠 - 自动进入低功耗模式
        Timer::after(Duration::from_secs(60)).await;
    }
}
```

### 5.2 深度睡眠集成

```rust
use embassy_stm32::low_power::LowPower;

async fn sleep_until_event() {
    // 配置唤醒源
    let mut exti = ExtiInput::new(...);

    loop {
        // 进入STOP模式，等待中断
        LowPower::stop_until(
            exti.wait_for_any_edge()
        ).await;

        // 被唤醒后处理
        handle_wakeup().await;
    }
}
```

---

## 6. 并发模式

### 6.1 共享资源

```rust
use embassy_sync::mutex::Mutex;
use embassy_sync::blocking_mutex::raw::ThreadModeRawMutex;

// 全局共享I2C
static I2C: StaticCell<Mutex<ThreadModeRawMutex, I2c<'static>>> = StaticCell::new();

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let i2c = I2c::new(...);
    let i2c_mutex = I2C.init(Mutex::new(i2c));

    spawner.spawn(sensor_task1(i2c_mutex)).unwrap();
    spawner.spawn(sensor_task2(i2c_mutex)).unwrap();
}

#[embassy_executor::task]
async fn sensor_task1(i2c: &'static Mutex<ThreadModeRawMutex, I2c<'static>>) {
    loop {
        // 获取锁
        let mut bus = i2c.lock().await;

        // 执行I2C操作
        bus.write_read(ADDR1, &[0x01], &mut buf).await.unwrap();

        // 锁自动释放
        drop(bus);

        Timer::after(Duration::from_secs(1)).await;
    }
}
```

### 6.2 信号量与通道

```rust
use embassy_sync::signal::Signal;
use embassy_sync::channel::{Channel, Sender, Receiver};

// 信号
static DATA_READY: Signal<ThreadModeRawMutex, Data> = Signal::new();

#[embassy_executor::task]
async fn producer() {
    loop {
        let data = acquire_data().await;
        DATA_READY.signal(data);
    }
}

#[embassy_executor::task]
async fn consumer() {
    loop {
        let data = DATA_READY.wait().await;
        process(data).await;
    }
}

// 通道
static CHANNEL: Channel<ThreadModeRawMutex, Data, 10> = Channel::new();

#[embassy_executor::task]
async fn producer_ch(sender: Sender<'static, ThreadModeRawMutex, Data, 10>) {
    loop {
        let data = acquire_data().await;
        sender.send(data).await; // 异步等待容量
    }
}

#[embassy_executor::task]
async fn consumer_ch(receiver: Receiver<'static, ThreadModeRawMutex, Data, 10>) {
    loop {
        let data = receiver.recv().await;
        process(data).await;
    }
}
```

---

## 7. USB设备开发

```rust
use embassy_usb::UsbDevice;
use embassy_usb::class::cdc_acm::CdcAcmClass;

#[embassy_executor::task]
async fn usb_task(mut usb: UsbDevice<'static>) {
    loop {
        usb.run_until_suspend().await;

        // USB被挂起，进入低功耗
        usb.wait_resume().await;
    }
}

#[embassy_executor::task]
async fn cdc_task(mut class: CdcAcmClass<'static>) {
    let mut buf = [0u8; 64];

    loop {
        // 等待连接
        class.wait_connection().await;

        loop {
            // 异步读写
            match class.read_packet(&mut buf).await {
                Ok(n) => {
                    let response = process(&buf[..n]);
                    class.write_packet(response).await.ok();
                }
                Err(_) => break, // 断开连接
            }
        }
    }
}
```

---

## 8. 调试技巧

### 8.1 defmt日志

```rust
use defmt::*;

#[embassy_executor::task]
async fn debug_task() {
    info!("Task started");

    loop {
        let value = read_sensor().await;
        debug!("Sensor value: {}", value);

        if value > THRESHOLD {
            warn!("Value exceeds threshold: {}", value);
        }

        Timer::after(Duration::from_secs(1)).await;
    }
}
```

### 8.2 堆栈分析

```toml
# Cargo.toml
[profile.release]
debug = 2
lto = true
opt-level = 'z'
```

```rust
// 检查任务堆栈使用
use embassy_executor::task;

#[task(stack_size = 4096)]  // 自定义堆栈大小
async fn stack_heavy_task() {
    // 大型数组在堆栈上
    let mut buf = [0u8; 1024];

    // 使用...
}
```

---

**参考**:

- [Embassy Documentation](https://embassy.dev/)
- [Embassy Examples](https://github.com/embassy-rs/embassy/tree/main/examples)

**维护者**: Rust Embedded Async Team
**更新日期**: 2026-03-05
