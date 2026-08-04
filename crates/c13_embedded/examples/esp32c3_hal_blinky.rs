//! ESP32-C3 bare-metal blinky — 使用 `esp-hal` 与 `esp-println`
//!
//! 本示例面向 ESP32-C3（RISC-V IMAC 内核），通过 `esp-hal` 初始化时钟与 GPIO，
//! 并翻转 GPIO2（部分开发板板载 LED 所在引脚）。延时使用简单忙等，避免依赖
//! `unstable` feature 的 SYSTIMER API。
//!
//! 编译命令：
//! ```bash
//! rustup target add riscv32imc-unknown-none-elf
//! cargo build -p c13_embedded --target riscv32imc-unknown-none-elf \
//!   --example esp32c3_hal_blinky --features esp32c3-hal
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/21_riscv_avr_embedded.md`

#![cfg_attr(
    all(
        target_arch = "riscv32",
        target_os = "none",
        feature = "esp32c3-hal"
    ),
    no_std
)]
#![cfg_attr(
    all(
        target_arch = "riscv32",
        target_os = "none",
        feature = "esp32c3-hal"
    ),
    no_main
)]

// ---------------------------------------------------------------------------
// Host 模拟入口
// ---------------------------------------------------------------------------
#[cfg(not(all(
    target_arch = "riscv32",
    target_os = "none",
    feature = "esp32c3-hal"
)))]
fn main() {
    println!("esp32c3_hal_blinky: host 模拟模式");
    println!("真实目标编译命令:");
    println!(
        "  cargo build -p c13_embedded --target riscv32imc-unknown-none-elf \\\n    \
         --example esp32c3_hal_blinky --features esp32c3-hal"
    );
}

// ---------------------------------------------------------------------------
// ESP32-C3 真实目标入口
// ---------------------------------------------------------------------------
#[cfg(all(
    target_arch = "riscv32",
    target_os = "none",
    feature = "esp32c3-hal"
))]
mod target_impl {
    use esp_hal::clock::CpuClock;
    use esp_hal::esp_riscv_rt::entry;
    use esp_hal::gpio::{Level, Output, OutputConfig};

    #[panic_handler]
    fn panic(_info: &core::panic::PanicInfo) -> ! {
        loop {}
    }

    #[entry]
    fn main() -> ! {
        // esp-hal 1.x 推荐通过 esp_hal::init 进行全局初始化。
        let config = esp_hal::Config::default().with_cpu_clock(CpuClock::default());
        let peripherals = esp_hal::init(config);

        let mut led = Output::new(peripherals.GPIO2, Level::Low, OutputConfig::default());

        esp_println::println!("ESP32-C3 blinky started");

        loop {
            led.set_high();
            block_delay_ms(250);
            led.set_low();
            block_delay_ms(250);
        }
    }

    /// 简单软件忙等延时（约 milliseconds，按 160 MHz CPU 粗略估算）。
    fn block_delay_ms(ms: u32) {
        for _ in 0..ms {
            for _ in 0..80_000 {
                core::hint::spin_loop();
            }
        }
    }
}
