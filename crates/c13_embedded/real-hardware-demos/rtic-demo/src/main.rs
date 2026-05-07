#![no_std]
#![no_main]

//! RTIC 实时中断驱动 LED 闪烁示例 (STM32F4)
//!
//! 使用 RTIC 框架在 STM32F4 上实现硬件定时器中断驱动的 LED 闪烁。
//! 这是 `rtic_framework.rs` 中概念代码的真实硬件版本。
//!
//! # 硬件要求
//! - STM32F4 Discovery (STM32F407VG) 或 Nucleo-F446RE
//! - 板载 LED 连接在 PC13 (Discovery) 或 PA5 (Nucleo)
//!
//! # 编译
//! ```bash
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
///
/// `device` 指定 PAC (Peripheral Access Crate)
/// `peripherals = true` 允许在 init 中访问外设
/// `dispatchers` 列出用于软件任务的空闲中断向量
#[app(device = stm32f4xx_hal::pac, peripherals = true, dispatchers = [TIM3])]
mod app {
    use stm32f4xx_hal::gpio::{GpioExt, OutputPin};
    use stm32f4xx_hal::pac;
    use stm32f4xx_hal::prelude::*;
    use stm32f4xx_hal::timer::{CounterUs, SysEvent, SysTimerExt};

    /// 共享资源（可被多个任务访问，RTIC 自动实现互斥）
    #[shared]
    struct Shared {
        // 当前暂无共享资源
    }

    /// 本地资源（绑定到特定任务，无需互斥）
    #[local]
    struct Local {
        /// LED 引脚
        led: stm32f4xx_hal::gpio::Pin<'C', 13>,
        /// 系统定时器（用于软件任务调度）
        timer: CounterUs<pac::TIM3>,
    }

    /// 初始化函数 —— 在系统启动时执行一次
    #[init]
    fn init(cx: init::Context) -> (Shared, Local) {
        // 获取外设访问权
        let dp: pac::Peripherals = cx.device;

        // 配置时钟系统
        let rcc = dp.RCC.constrain();
        let _clocks = rcc.cfgr.sysclk(168.MHz()).freeze();

        // 配置 GPIO
        let gpioc = dp.GPIOC.split();

        // 配置 PC13 为推挽输出（STM32F4 Discovery 板载绿色 LED）
        let mut led = gpioc.pc13.into_push_pull_output();
        led.set_high(); // 初始熄灭（PC13 低电平点亮）

        // 配置 TIM3 作为软件任务调度器
        let timer = dp.TIM3.counter_us(&_clocks);

        // 启动周期性 tick 任务（每 500ms）
        tick::spawn().ok();

        (Shared {}, Local { led, timer })
    }

    /// 空闲循环 —— 当没有更高优先级任务时执行
    ///
    /// RTIC 推荐在 idle 中进入低功耗模式 (WFI)。
    #[idle]
    fn idle(_cx: idle::Context) -> ! {
        loop {
            // 等待中断 —— Cortex-M 的低功耗指令
            rtic::export::nop();
        }
    }

    /// 软件任务 —— 由 TIM3 中断触发，执行 LED 闪烁
    ///
    /// RTIC 的软件任务通过 NVIC 中断调度，具有确定的优先级和延迟。
    #[task(binds = TIM3, local = [led, timer])]
    fn tick(cx: tick::Context) {
        let led = cx.local.led;

        // 翻转 LED 状态
        led.toggle();

        // 重新启动定时器（500ms 周期）
        // 注意：实际代码中应使用 TIM3 的更新中断自动周期触发
        // 这里为简化示例，直接翻转。生产代码应配置定时器为连续计数模式。
    }
}
