//! no_std QEMU blinky — minimal ARM Cortex-M example for `thumbv7m-none-eabi`.
//!
//! This example toggles GPIOA pin 5 (a common on-board LED location on STM32F4 and
//! Nucleo boards) in an infinite loop. The embedded code is wrapped in
//! `#[cfg(all(target_arch = "arm", target_os = "none"))]` so that
//! `cargo check --workspace` succeeds on an x86_64 host.
//!
//! # Linker script requirement
//!
//! `cortex-m-rt` needs a `memory.x` file describing the Flash/RAM layout of the
//! target chip. For this workspace crate, `build.rs` generates one automatically
//! in `OUT_DIR` when the target architecture is `arm`, so the example links out of
//! the box. In your own project, place a `memory.x` next to `Cargo.toml` or use
//! `build.rs` to emit `cargo:rustc-link-search`, for example:
//!
//! ```text
//! MEMORY
//! {
//!   FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 1024K
//!   RAM   (rwx): ORIGIN = 0x20000000, LENGTH = 128K
//! }
//! ```
//!
//! # Compile and run on QEMU
//!
//! ```bash
//! cargo build -p c13_embedded --target thumbv7m-none-eabi --example no_std_qemu_blinky
//! qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic \
//!   -kernel target/thumbv7m-none-eabi/debug/examples/no_std_qemu_blinky
//! ```

#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_std
)]
#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_main
)]

// -----------------------------------------------------------------------------
// Host fallback entry (x86_64 / Windows host)
// -----------------------------------------------------------------------------
#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
fn main() {
    println!("no_std_qemu_blinky: host simulation mode");
    println!("Build for QEMU with:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7m-none-eabi \\\n    --example \
         no_std_qemu_blinky"
    );
    println!();
    println!("Run in QEMU with:");
    println!(
        "  qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic \\\n    \
         -kernel target/thumbv7m-none-eabi/debug/examples/no_std_qemu_blinky"
    );
    println!();
    println!("The linker script is provided by this crate's build.rs for ARM targets.");
}

// -----------------------------------------------------------------------------
// ARM Cortex-M target entry
// -----------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    use core::sync::atomic::{AtomicU32, Ordering};

    // Pull in the panic handler so the no_std binary links on ARM targets.
    use panic_halt as _;

    // STM32F4 GPIOA ODR address. Real hardware should use the PAC/HAL instead
    // of raw pointer writes; this is intentionally minimal for QEMU demonstration.
    const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        // The actual infinite loop is guarded so the host target never sees it.
        #[cfg(target_arch = "arm")]
        loop {
            // Toggle PA5 (common LED pin on many STM32F4 boards).
            unsafe {
                let val = core::ptr::read_volatile(GPIOA_ODR);
                core::ptr::write_volatile(GPIOA_ODR, val ^ (1 << 5));
            }

            COUNTER.fetch_add(1, Ordering::Relaxed);

            for _ in 0..100_000 {
                cortex_m::asm::nop();
            }
        }
    }
}

// -----------------------------------------------------------------------------
// RISC-V placeholder (keeps the file valid if accidentally built for rv32)
// -----------------------------------------------------------------------------
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::wfi();
        }
    }
}
