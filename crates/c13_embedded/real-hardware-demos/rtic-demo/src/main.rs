#![no_std]
#![no_main]

//! RTIC 实时中断驱动 LED 闪烁示例 (STM32F4)
//! RTIC real-time interrupt-driven LED blink example (STM32F4)
//!
//! # 硬件要求
//! - STM32F4 Discovery (STM32F407VG) 或 Nucleo-F446RE
//! - 板载 LED 连接在 PC13 (Discovery) 或 PA5 (Nucleo)
//!
//! # 编译
//! ```bash
//! cd crates/c13_embedded/real-hardware-demos/rtic-demo
//! cargo build --release
//! ```
//!
//! # 烧录 (probe-rs)
//! ```bash
//! cargo run --release
//! ```

use panic_halt as _;
use rtic::app;

/// RTIC 应用定义
/// `device` 指定 PAC (Peripheral Access Crate)
/// `peripherals = true` 允许在 init 中访问外设
/// `dispatchers` 指定软件任务调度器使用的中断向量
#[app(device = stm32f4xx_hal::pac, peripherals = true, dispatchers = [TIM4])]
mod app {
    use stm32f4xx_hal::gpio::{GpioExt, Output};
    use stm32f4xx_hal::pac;
    use stm32f4xx_hal::prelude::*;
    use stm32f4xx_hal::rcc::Config;

    /// 共享资源（可被多个任务访问，RTIC 自动实现互斥）
    #[shared]
    struct Shared {
        // 当前暂无共享资源
    }

    /// 本地资源（绑定到特定任务，无需互斥）
    #[local]
    struct Local {
        /// LED 引脚（STM32F4 Discovery 板载绿色 LED）
        led: stm32f4xx_hal::gpio::Pin<'C', 13, Output>,
    }

    /// 初始化函数 —— 在系统启动时执行一次
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        // 获取外设访问权
        let dp: pac::Peripherals = cx.device;

        // 配置时钟系统
        let rcc = dp.RCC.constrain();
        let mut rcc = rcc.freeze(Config::default());

        // 配置 GPIO
        let gpioc = dp.GPIOC.split(&mut rcc);

        // 配置 PC13 为推挽输出并初始熄灭（PC13 低电平点亮）
        let mut led = gpioc.pc13.into_push_pull_output();
        led.set_high();

        (Shared {}, Local { led })
    }

    /// 空闲循环 —— 当没有更高优先级任务时执行
    #[idle]
    fn idle(_cx: idle::Context) -> ! {
        loop {
            // 等待中断 —— Cortex-M 的低功耗指令
            cortex_m::asm::nop();
        }
    }

    /// 硬件任务 —— 由 TIM3 中断触发，执行 LED 闪烁
    /// 生产代码中应配置 TIM3 为周期性计数器，此处为最小可编译示例
    #[task(binds = TIM3, local = [led])]
    fn tick(cx: tick::Context) {
        let led = cx.local.led;

        // 翻转 LED 状态
        if led.is_set_high() {
            led.set_low();
        } else {
            led.set_high();
        }
    }
}
