//! no_std `defmt` + RTT logging skeleton
//!
//! Demonstrates how `defmt`, `defmt-rtt`, and `panic-probe` are wired in a
//! `#![no_std]` ARM Cortex-M program. Because these crates are not currently in
//! the workspace dependency table, the required `Cargo.toml` lines are shown in
//! comments below; uncomment them (or add equivalent versions) before building
//! for an ARM target.
//!
//! The embedded code is wrapped in `#[cfg(all(target_arch = "arm", target_os = "none"))]`,
//! so `cargo check --workspace` on x86_64 still passes.
//!
//! # Target-only dependencies to enable
//!
//! Add the following to `crates/c13_embedded/Cargo.toml` under the existing
//! `[target.'cfg(target_arch = "arm")'.dependencies]` section:
//!
//! ```toml
//! defmt = "0.3"
//! defmt-rtt = "0.4"
//! panic-probe = { version = "0.3", features = ["print-defmt"] }
//! ```
//!
//! And enable the default feature in the crate root:
//!
//! ```toml
//! [features]
//! default = ["defmt-default"]
//! ```
//!
//! # Linker script extension for defmt
//!
//! The linker script must also include `defmt.x`. Add it via `build.rs` or
//! `.cargo/config.toml` rustflags:
//!
//! ```text
//! -C link-arg=-Tdefmt.x
//! ```
//!
//! # Compile and run with probe-rs
//!
//! ```bash
//! cargo build -p c13_embedded --target thumbv7em-none-eabihf --example no_std_defmt_rtt
//! probe-rs run --chip STM32F407VG target/thumbv7em-none-eabihf/debug/examples/no_std_defmt_rtt
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

#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
fn main() {
    println!("no_std_defmt_rtt: host simulation mode");
    println!("Uncomment the defmt target-only dependencies in Cargo.toml, then build:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7em-none-eabihf \\\n    --example \
         no_std_defmt_rtt"
    );
    println!("Run on hardware with:");
    println!(
        "  probe-rs run --chip STM32F407VG \\\n    \
         target/thumbv7em-none-eabihf/debug/examples/no_std_defmt_rtt"
    );
}

// -----------------------------------------------------------------------------
// ARM Cortex-M target entry (compiled only when target_arch = "arm")
// -----------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    // These imports are resolved only after the defmt target-only dependencies
    // are uncommented in Cargo.toml.
    use defmt::*;
    use defmt_rtt as _;
    use panic_probe as _;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        info!("booting, version={}", 1);

        let sensor = 42;
        debug!("sensor reading: {}", sensor);

        loop {
            cortex_m::asm::wfi();
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
