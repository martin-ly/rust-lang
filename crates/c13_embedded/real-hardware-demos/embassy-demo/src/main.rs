#![no_std]
#![no_main]

//! Embassy 异步 LED 闪烁示例 (Raspberry Pi Pico)
//! Embassy async LED 闪烁Example of (Raspberry Pi Pico)
//! 使用 Embassy 框架在 RP2040 上实现异步 LED 闪烁。
//! Embassy framework in RP2040 on async LED 。
//! # 硬件要求
//! # hardware
//! - 板载 LED 连接在 GPIO25（Pico）或 WL_GPIO0（Pico W）
//! - 板载 LED Connectin GPIO25（Pico）or WL_GPIO0（Pico W）
//! # 编译
//! #
//! ```
//! 
//! # 烧录 (probe-rs)
//! ```

use defmt::*;
use defmt_rtt as _;
use embassy_executor::Spawner;
use embassy_rp::gpio::{Level, Output};
use embassy_time::Timer;
use panic_probe as _;

/// 主入口 — Embassy Executor 自动管理 async 任务调度
/// — Embassy Executor async task
#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    info!("Embassy demo starting on RP2040!");

    // 初始化 RP2040 外设
    let p = embassy_rp::init(Default::default());

    // 配置 GPIO25 为输出（Pico 板载 LED）
    // Pico W 用户请将 p.PIN_25 改为 p.PIN_23 (WL_GPIO0) 或使用 cyw43 库
    let mut led = Output::new(p.PIN_25, Level::Low);

    info!("Entering blink loop");

    // 异步 LED 闪烁循环
    // 与裸机轮询或阻塞延迟不同，这里的 Timer::after 会让出执行权，
    // 允许 Executor 运行其他任务（如果有的话）。
    loop {
        led.set_high();
        info!("LED ON");
        Timer::after_millis(300).await;

        led.set_low();
        info!("LED OFF");
        Timer::after_millis(300).await;
    }
}
